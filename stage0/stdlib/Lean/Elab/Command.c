// Lean compiler output
// Module: Lean.Elab.Command
// Imports: Init Lean.Log Lean.Parser.Command Lean.ResolveName Lean.Meta.Reduce Lean.Elab.Term Lean.Elab.Tactic.Cache Lean.Elab.Binders Lean.Elab.SyntheticMVars Lean.Elab.DeclModifiers Lean.Elab.InfoTree Lean.Elab.SetOption
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
static lean_object* l_Lean_Elab_Command_State_infoState___default___closed__4;
static lean_object* l_Lean_Elab_Command_State_scopes___default___closed__1;
lean_object* l_Lean_Elab_ContextInfo_save___at_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_expandDeclId___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__4;
static lean_object* l_Lean_Elab_Command_withLogging___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instInhabitedState;
lean_object* l_Lean_extractMacroScopes(lean_object*);
static lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__13;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runTermElabM___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabCommandTopLevel___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_catchExceptions(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabCommandTopLevel___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__18(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instMonadCommandElabM___closed__6;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabCommand___closed__4;
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__1___closed__1;
static lean_object* l_Lean_Elab_Command_instInhabitedState___closed__12;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at_Lean_Elab_addMacroStack___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCommand___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instAddMessageContextCommandElabM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at_Lean_Elab_Command_elabCommandTopLevel___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getScope___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Command_withMacroExpansion___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapMAux___at_Lean_Elab_Command_liftTermElabM___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkInfoTree___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
uint8_t l_Lean_Elab_isAbortExceptionId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabCommandTopLevel___lambda__2___closed__1;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadTraceCommandElabM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_DocString_0__Lean_docStringExt;
LEAN_EXPORT lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_liftAttrM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_expandDeclId___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instInhabitedState___closed__3;
static lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_liftIO(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___elambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_commandElabAttribute;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Command_withMacroExpansion___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getScope___boxed(lean_object*);
static lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__2;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___closed__2;
static lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at_Lean_Elab_Command_liftTermElabM___spec__1(lean_object*);
static lean_object* l_Lean_Elab_Command_elabCommand___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_Context_macroStack___default;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___rarg___closed__1;
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Command_modifyScope___spec__1(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_runTermElabM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__4;
static lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__16;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_withLogging___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withFreshMacroScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___at_Lean_Elab_Command_expandDeclId___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_runTermElabM(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getLevelNames___boxed(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_private_to_user_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__15(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__1;
static lean_object* l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__2;
static lean_object* l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadRefCommandElabM;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_Context_cmdPos___default;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_liftTermElabM(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Command_Scope_isNoncomputable___default;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getCurrMacroScope___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_Scope_currNamespace___default;
static lean_object* l_Lean_Elab_Command_State_messages___default___closed__2;
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_runTermElabM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_liftEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addLinter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___at_Lean_Elab_Command_expandDeclId___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__4;
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2500____closed__2;
static lean_object* l_Lean_Elab_Command_instInhabitedState___closed__5;
static lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__1;
static lean_object* l_Lean_Elab_Command_State_messages___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___rarg(lean_object*);
static lean_object* l_Lean_Elab_Command_instInhabitedState___closed__7;
static lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__10;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__2___closed__2;
lean_object* l_Lean_Elab_InfoTree_substitute(lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadOptionsCommandElabM(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Command_instMonadCommandElabM___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCommandTopLevel___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withMacroExpansion___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getEntries___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_foldlM___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instMonadTraceCommandElabM___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_ioErrorToMessage(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_Scope_opts___default;
static lean_object* l_Lean_Elab_Command_State_traceState___default___closed__1;
static lean_object* l_Lean_Elab_Command_State_infoState___default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_format(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__1;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_Elab_Command_expandDeclId___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Elab_Command_elabCommandTopLevel___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
static lean_object* l_Lean_Elab_Command_instMonadCommandElabM___closed__3;
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___at_Lean_Elab_Command_expandDeclId___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getLevelNames___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instMonadRefCommandElabM___closed__2;
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x21___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getScopes___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Elab_Command_runLinters___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_modifyScope___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_State_messages___default;
uint8_t l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_101_(uint8_t, uint8_t);
static lean_object* l_Lean_Elab_Command_instMonadTraceCommandElabM___closed__2;
static lean_object* l_Lean_Elab_Command_instMonadRefCommandElabM___closed__1;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM;
lean_object* l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadCommandElabM;
static lean_object* l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__2;
static lean_object* l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__2;
extern lean_object* l_Lean_levelZero;
lean_object* l_Lean_Syntax_hasMissing(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___closed__5;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__3;
static lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getLevelNames___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCommand___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_getBracketedBinderIds___closed__7;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__13(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__1;
static lean_object* l_Lean_Elab_Command_State_ngen___default___closed__3;
static lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__3;
extern lean_object* l_Lean_maxRecDepth;
extern lean_object* l_Lean_LocalContext_empty;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2240____closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___at_Lean_Elab_Command_expandDeclId___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123____closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Command_elabCommand___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runTermElabM___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__1;
static lean_object* l_Lean_Elab_Command_getBracketedBinderIds___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at_Lean_Elab_Command_elabCommandTopLevel___spec__1___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandDeclId___closed__1;
static lean_object* l_Lean_Elab_Command_elabCommand___closed__6;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapMAux___at_Lean_Elab_Command_liftTermElabM___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_State_nextMacroScope___default___closed__1;
static lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___closed__1;
static size_t l_Lean_Elab_Command_instInhabitedState___closed__8;
LEAN_EXPORT lean_object* l_Lean_addDocString___at_Lean_Elab_Command_expandDeclId___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instInhabitedCommandElabM(lean_object*);
static lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_liftEIO___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_runLinters(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Command_elabCommand___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__2;
static lean_object* l_Lean_addDocString___at_Lean_Elab_Command_expandDeclId___spec__11___closed__1;
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkState___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__2;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__3;
static lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__2;
static lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instInhabitedState___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__9;
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapM___at_Lean_Elab_Command_liftTermElabM___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_modifyScope___closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabCommandTopLevel___spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadTraceCommandElabM___lambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_getBracketedBinderIds___closed__3;
static lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___closed__4;
static lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withFreshMacroScope(lean_object*);
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFieldsFlattened(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadQuotationCommandElabM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandDeclId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermState(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___spec__2(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Command_getBracketedBinderIds___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadOptionsCommandElabM___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__16(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_Scope_varDecls___default;
static lean_object* l_Lean_Elab_Command_elabCommand___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_Scope_openDecls___default;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_State_nextInstIdx___default;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadRefCommandElabM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermState___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__19(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instInhabitedState___closed__2;
static lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__2;
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
static lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at_Lean_Elab_Command_elabCommandTopLevel___spec__1(lean_object*);
static lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__3;
static lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__3;
static lean_object* l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__2;
static lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___closed__2;
static lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_liftCoreM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logTrace___at_Lean_Elab_Command_elabCommand___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabCommand___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_liftCoreM___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadTraceCommandElabM;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_getBracketedBinderIds___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_getBracketedBinderIds___closed__9;
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapM___at_Lean_Elab_Command_liftTermElabM___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_getBracketedBinderIds___closed__10;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Command_elabCommand___lambda__3___closed__5;
static lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__2;
static lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__2;
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123____closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addUnivLevel___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instInhabitedState___closed__6;
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2240____closed__1;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instInhabitedState___closed__13;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_expandDeclId___spec__14(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_417_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1748_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2240_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2500_(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_State_ngen___default;
extern lean_object* l_Lean_Expr_instHashableExpr;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getBracketedBinderIds(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadTraceCommandElabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__14;
static lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___closed__1;
lean_object* l_Lean_Elab_Term_addAutoBoundImplicits_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__5;
static lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___closed__3;
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123____closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_runTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_State_messages___default___closed__3;
static size_t l_Lean_Elab_Command_expandDeclId___closed__2;
static lean_object* l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__4;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__4;
uint8_t l_Lean_Name_isAtomic(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getScopes(lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___closed__3;
extern lean_object* l_Lean_protectedExt;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_Context_currRecDepth___default;
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_liftAttrM(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_liftAttrM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_State_scopes___default;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadLiftTIOCommandElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__17(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addUnivLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withLogging(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_getBracketedBinderIds___closed__2;
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadQuotationCommandElabM;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_modifyScope___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_liftIO___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_liftIO___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_modifyScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkCoreContext___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_Scope_levelNames___default;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_modifyScope___closed__1;
static lean_object* l_Lean_Elab_Command_addLinter___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Elab_Command_elabCommandTopLevel___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_liftCoreM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withMacroExpansion(lean_object*);
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2500____closed__1;
lean_object* l_Lean_InternalExceptionId_getName(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandDeclIdCore(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__16(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabCommand___lambda__3___closed__4;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__15(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonadEStateM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at_Lean_Elab_Command_liftTermElabM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__7;
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceOptions(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__16(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_Context_ref___default;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getMainModule___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_getBracketedBinderIds___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addUnivLevel(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabCommandTopLevel___spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadTraceCommandElabM___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123____closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM___lambda__1(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Command_elabCommand___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__5;
static lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Elab_Command_elabCommandTopLevel___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabCommand___lambda__3___closed__1;
static lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__17;
static lean_object* l_Lean_Elab_Command_instMonadRefCommandElabM___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at_Lean_Elab_Command_elabCommandTopLevel___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withMacroExpansion___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCommand___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___closed__6;
static lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getScope(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabCommandTopLevel___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getMainModule(lean_object*);
static lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__8;
static lean_object* l_Lean_Elab_Command_instInhabitedState___closed__11;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__13(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_modifyScope(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
uint8_t l_Lean_Name_isSuffixOf(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapM___at_Lean_Elab_Command_liftTermElabM___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Elab_Command_runLinters___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_showPartialSyntaxErrors;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_ioErrorToMessage___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_runTermElabM___rarg___lambda__2___closed__1;
static lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instInhabitedScope;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__17(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_runTermElabM___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__3;
static uint32_t l_Lean_Elab_Command_instInhabitedState___closed__4;
static lean_object* l_Lean_Elab_Command_Scope_varDecls___default___closed__1;
lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_State_infoState___default___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withScope(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getMainModule___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadLiftTIOCommandElabM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__3;
static lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadOptionsCommandElabM___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkInfoTree(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabCommand___lambda__3___closed__2;
static lean_object* l_Lean_Elab_Command_instInhabitedCommandElabM___closed__1;
static lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_expandDeclId___spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__3;
static lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___closed__1;
static lean_object* l_Lean_Elab_Command_instMonadCommandElabM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___closed__2;
static lean_object* l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__6;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM___lambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_State_ngen___default___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Elab_Command_elabCommandTopLevel___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_liftCoreM(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instInhabitedState___closed__10;
static lean_object* l_Lean_Elab_Command_instMonadCommandElabM___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadInfoTreeCommandElabM;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getLevelNames(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_Context_currMacroScope___default;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__1___closed__2;
static lean_object* l_Lean_Elab_Command_instInhabitedState___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__3;
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getMainModule___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instMonadCommandElabM___closed__4;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_Elab_Command_expandDeclId___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_State_ngen___default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instInhabitedCommandElabM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
extern lean_object* l_Lean_Expr_instBEqExpr;
lean_object* l_Lean_Elab_Term_withoutAutoBoundImplicit___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Command_elabCommand___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_getBracketedBinderIds___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getScopes___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instMonadTraceCommandElabM___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instAddMessageContextCommandElabM;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkMessageAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkCoreContext(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_State_traceState___default;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__3___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__1___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__15___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCommandTopLevel___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instInhabitedCommandElabM___closed__2;
static lean_object* l_Lean_Elab_Command_State_infoState___default___closed__1;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabCommandTopLevel___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___elambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instInhabitedCommandElabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCommand___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext;
lean_object* l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6____spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_foldlM___at_Lean_Elab_Command_elabCommandTopLevel___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__7;
static lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___closed__4;
static lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCommand___lambda__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(lean_object*);
lean_object* l_Lean_Core_resetMessageLog(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withMacroExpansion___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCommand___lambda__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_State_nextMacroScope___default;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getScope___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Elab_isFreshInstanceName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM;
static lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__12;
lean_object* lean_usize_to_nat(size_t);
static lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___closed__2;
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1___closed__1;
lean_object* l_Std_instInhabitedPersistentArrayNode(lean_object*);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
static lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getScopes___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_State_infoState___default;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__15___closed__1;
static lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__14(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCommandTopLevel___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withAutoBoundImplicit___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadOptionsCommandElabM___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabCommand___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkMessageAux(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapM___at_Lean_Elab_Command_liftTermElabM___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabCommandTopLevel___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_liftExcept___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__8___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_getBracketedBinderIds___closed__1;
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Elab_Command_getBracketedBinderIds___closed__8;
static lean_object* l_Lean_Elab_Command_instInhabitedScope___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___closed__5;
static lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__18;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_Scope_varUIds___default;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabCommand___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1___closed__2;
static lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__1;
static lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__11;
static lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadLiftTIOCommandElabM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instInhabitedScope___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__15;
LEAN_EXPORT lean_object* l_Lean_addDocString___at_Lean_Elab_Command_expandDeclId___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_runTermElabM___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_liftEIO___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapMAux___at_Lean_Elab_Command_liftTermElabM___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withMacroExpansion___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_lintersRef;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_runTermElabM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getRef___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__3___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapMAux___at_Lean_Elab_Command_liftTermElabM___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_Elab_Command_Scope_varDecls___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_Scope_varDecls___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_Scope_varDecls___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Scope_varUIds___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_Scope_varDecls___default___closed__1;
return x_1;
}
}
static uint8_t _init_l_Lean_Elab_Command_Scope_isNoncomputable___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedScope___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedScope___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_instInhabitedScope___closed__1;
x_3 = lean_box(0);
x_4 = l_Lean_Elab_Command_Scope_varDecls___default___closed__1;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set(x_6, 4, x_1);
lean_ctor_set(x_6, 5, x_4);
lean_ctor_set(x_6, 6, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*7, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedScope() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instInhabitedScope___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_messages___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_messages___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_State_messages___default___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_messages___default___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Elab_Command_State_messages___default___closed__2;
x_3 = l_Lean_Elab_Command_State_messages___default___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_messages___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_State_messages___default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_scopes___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_instInhabitedScope___closed__2;
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
x_1 = l_Lean_Elab_Command_State_scopes___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_nextMacroScope___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_firstFrontendMacroScope;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_nextMacroScope___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_State_nextMacroScope___default___closed__1;
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
static lean_object* _init_l_Lean_Elab_Command_State_ngen___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_uniq", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_ngen___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_State_ngen___default___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_ngen___default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_State_ngen___default___closed__2;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_ngen___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_State_ngen___default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_infoState___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_infoState___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_State_infoState___default___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_infoState___default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_State_infoState___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_infoState___default___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Elab_Command_State_infoState___default___closed__3;
x_3 = l_Lean_Elab_Command_State_messages___default___closed__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_infoState___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_State_infoState___default___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_traceState___default___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lean_Elab_Command_State_messages___default___closed__3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_traceState___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_State_traceState___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedState___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_State_infoState___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedState___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Elab_Command_instInhabitedState___closed__1;
x_3 = l_Lean_Elab_Command_instInhabitedState___closed__2;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static uint32_t _init_l_Lean_Elab_Command_instInhabitedState___closed__4() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedState___closed__5() {
_start:
{
uint32_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_instInhabitedState___closed__4;
x_2 = 0;
x_3 = lean_box(0);
x_4 = l_Lean_Elab_Command_Scope_varDecls___default___closed__1;
x_5 = lean_alloc_ctor(0, 5, 5);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_4);
lean_ctor_set_uint32(x_5, sizeof(void*)*5, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*5 + 4, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedState___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_instInhabitedState___closed__1;
x_2 = l_Lean_Elab_Command_instInhabitedState___closed__3;
x_3 = l_Lean_Elab_Command_Scope_varDecls___default___closed__1;
x_4 = l_Lean_Elab_Command_instInhabitedState___closed__5;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedState___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_Scope_varDecls___default___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static size_t _init_l_Lean_Elab_Command_instInhabitedState___closed__8() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedState___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; size_t x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_instInhabitedState___closed__7;
x_2 = l_Lean_Elab_Command_Scope_varDecls___default___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Elab_Command_instInhabitedState___closed__8;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set_usize(x_5, 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedState___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedState___closed__11() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Elab_Command_State_infoState___default___closed__3;
x_3 = l_Lean_Elab_Command_instInhabitedState___closed__9;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedState___closed__12() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lean_Elab_Command_instInhabitedState___closed__9;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedState___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_instInhabitedState___closed__6;
x_3 = l_Lean_Elab_Command_instInhabitedState___closed__9;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Elab_Command_instInhabitedState___closed__10;
x_6 = l_Lean_Elab_Command_instInhabitedState___closed__11;
x_7 = l_Lean_Elab_Command_instInhabitedState___closed__12;
x_8 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_1);
lean_ctor_set(x_8, 3, x_4);
lean_ctor_set(x_8, 4, x_4);
lean_ctor_set(x_8, 5, x_4);
lean_ctor_set(x_8, 6, x_5);
lean_ctor_set(x_8, 7, x_6);
lean_ctor_set(x_8, 8, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instInhabitedState___closed__13;
return x_1;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
x_8 = lean_apply_3(x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_apply_4(x_4, x_9, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
static lean_object* _init_l_Lean_Elab_Command_instMonadCommandElabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_EStateM_instMonadEStateM(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadCommandElabM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_instMonadCommandElabM___closed__1;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadCommandElabM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_instMonadCommandElabM___closed__2;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadCommandElabM___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadCommandElabM___lambda__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadCommandElabM___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadCommandElabM___lambda__2), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadCommandElabM___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lean_Elab_Command_instMonadCommandElabM___closed__3;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 1);
lean_dec(x_4);
x_5 = l_Lean_Elab_Command_instMonadCommandElabM___closed__4;
lean_ctor_set(x_2, 1, x_5);
x_6 = l_Lean_Elab_Command_instMonadCommandElabM___closed__5;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get(x_2, 4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_12 = l_Lean_Elab_Command_instMonadCommandElabM___closed__4;
x_13 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_9);
lean_ctor_set(x_13, 3, x_10);
lean_ctor_set(x_13, 4, x_11);
x_14 = l_Lean_Elab_Command_instMonadCommandElabM___closed__5;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadCommandElabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instMonadCommandElabM___closed__6;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_instMonadCommandElabM___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkState___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_4 = lean_box(0);
x_5 = l_Lean_Elab_Command_instInhabitedScope___closed__1;
x_6 = lean_box(0);
x_7 = l_Lean_Elab_Command_Scope_varDecls___default___closed__1;
x_8 = 0;
lean_inc(x_3);
x_9 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_3);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_4);
lean_ctor_set(x_9, 4, x_4);
lean_ctor_set(x_9, 5, x_7);
lean_ctor_set(x_9, 6, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*7, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
x_11 = l_Lean_Elab_Command_mkState___closed__1;
x_12 = l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(x_3, x_11);
lean_dec(x_3);
x_13 = l_Lean_Elab_Command_State_nextMacroScope___default___closed__1;
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Elab_Command_State_ngen___default___closed__3;
x_16 = l_Lean_Elab_Command_State_infoState___default___closed__4;
x_17 = l_Lean_Elab_Command_State_traceState___default___closed__1;
x_18 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_2);
lean_ctor_set(x_18, 2, x_10);
lean_ctor_set(x_18, 3, x_13);
lean_ctor_set(x_18, 4, x_12);
lean_ctor_set(x_18, 5, x_14);
lean_ctor_set(x_18, 6, x_15);
lean_ctor_set(x_18, 7, x_16);
lean_ctor_set(x_18, 8, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_417_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Elab_Command_Scope_varDecls___default___closed__1;
x_3 = lean_st_mk_ref(x_2, x_1);
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
static lean_object* _init_l_Lean_Elab_Command_addLinter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_lintersRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addLinter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = l_Lean_Elab_Command_addLinter___closed__1;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_array_push(x_5, x_1);
x_8 = lean_st_ref_set(x_3, x_7, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 7);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_ctor_get(x_8, 7);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = lean_ctor_get(x_6, 7);
x_10 = lean_apply_1(x_1, x_9);
lean_ctor_set(x_6, 7, x_10);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get(x_6, 5);
x_24 = lean_ctor_get(x_6, 6);
x_25 = lean_ctor_get(x_6, 7);
x_26 = lean_ctor_get(x_6, 8);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_27 = lean_apply_1(x_1, x_25);
x_28 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_28, 2, x_20);
lean_ctor_set(x_28, 3, x_21);
lean_ctor_set(x_28, 4, x_22);
lean_ctor_set(x_28, 5, x_23);
lean_ctor_set(x_28, 6, x_24);
lean_ctor_set(x_28, 7, x_27);
lean_ctor_set(x_28, 8, x_26);
x_29 = lean_st_ref_set(x_3, x_28, x_7);
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
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__1;
x_2 = l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadInfoTreeCommandElabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get(x_6, 5);
x_24 = lean_ctor_get(x_6, 6);
x_25 = lean_ctor_get(x_6, 7);
x_26 = lean_ctor_get(x_6, 8);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_27 = lean_apply_1(x_1, x_18);
x_28 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_28, 2, x_20);
lean_ctor_set(x_28, 3, x_21);
lean_ctor_set(x_28, 4, x_22);
lean_ctor_set(x_28, 5, x_23);
lean_ctor_set(x_28, 6, x_24);
lean_ctor_set(x_28, 7, x_25);
lean_ctor_set(x_28, 8, x_26);
x_29 = lean_st_ref_set(x_3, x_28, x_7);
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
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadEnvCommandElabM___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadEnvCommandElabM___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__1;
x_2 = l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadEnvCommandElabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_instMonadEnvCommandElabM___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_instMonadEnvCommandElabM___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadOptionsCommandElabM___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Elab_Command_instInhabitedScope;
x_8 = l_List_head_x21___rarg(x_7, x_6);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Command_instInhabitedScope;
x_14 = l_List_head_x21___rarg(x_13, x_12);
lean_dec(x_12);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadOptionsCommandElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadOptionsCommandElabM___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadOptionsCommandElabM___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_instMonadOptionsCommandElabM___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadOptionsCommandElabM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_instMonadOptionsCommandElabM(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getRef(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getRef___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_getRef(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Elab_Command_State_infoState___default___closed__3;
x_3 = l_Lean_Elab_Command_instInhabitedState___closed__2;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set(x_5, 4, x_3);
lean_ctor_set(x_5, 5, x_2);
lean_ctor_set(x_5, 6, x_2);
lean_ctor_set(x_5, 7, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*8, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_State_infoState___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___closed__2;
x_2 = l_Lean_Elab_Command_State_messages___default___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Elab_Command_instInhabitedScope;
x_14 = l_List_head_x21___rarg(x_13, x_12);
lean_dec(x_12);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___closed__1;
x_17 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___closed__3;
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_15);
x_19 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_ctor_get(x_20, 2);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Elab_Command_instInhabitedScope;
x_24 = l_List_head_x21___rarg(x_23, x_22);
lean_dec(x_22);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___closed__1;
x_27 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___closed__3;
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_25);
x_29 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_21);
return x_30;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_instAddMessageContextCommandElabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instAddMessageContextCommandElabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instAddMessageContextCommandElabM___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadRefCommandElabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 2);
x_13 = lean_ctor_get(x_4, 3);
x_14 = lean_ctor_get(x_4, 4);
x_15 = lean_ctor_get(x_4, 5);
x_16 = lean_ctor_get(x_4, 7);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_17 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_12);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set(x_17, 4, x_14);
lean_ctor_set(x_17, 5, x_15);
lean_ctor_set(x_17, 6, x_2);
lean_ctor_set(x_17, 7, x_16);
x_18 = lean_apply_3(x_3, x_17, x_5, x_6);
return x_18;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadRefCommandElabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getRef___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadRefCommandElabM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadRefCommandElabM___lambda__1), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadRefCommandElabM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_instMonadRefCommandElabM___closed__1;
x_2 = l_Lean_Elab_Command_instMonadRefCommandElabM___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadRefCommandElabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instMonadRefCommandElabM___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadTraceCommandElabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = lean_ctor_get(x_6, 8);
x_10 = lean_apply_1(x_1, x_9);
lean_ctor_set(x_6, 8, x_10);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get(x_6, 5);
x_24 = lean_ctor_get(x_6, 6);
x_25 = lean_ctor_get(x_6, 7);
x_26 = lean_ctor_get(x_6, 8);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_27 = lean_apply_1(x_1, x_26);
x_28 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_28, 2, x_20);
lean_ctor_set(x_28, 3, x_21);
lean_ctor_set(x_28, 4, x_22);
lean_ctor_set(x_28, 5, x_23);
lean_ctor_set(x_28, 6, x_24);
lean_ctor_set(x_28, 7, x_25);
lean_ctor_set(x_28, 8, x_27);
x_29 = lean_st_ref_set(x_3, x_28, x_7);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadTraceCommandElabM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 8);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_ctor_get(x_8, 8);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadTraceCommandElabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadTraceCommandElabM___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadTraceCommandElabM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadTraceCommandElabM___lambda__2___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadTraceCommandElabM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_instMonadTraceCommandElabM___closed__1;
x_2 = l_Lean_Elab_Command_instMonadTraceCommandElabM___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadTraceCommandElabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instMonadTraceCommandElabM___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadTraceCommandElabM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_instMonadTraceCommandElabM___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadTraceCommandElabM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_instMonadTraceCommandElabM___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_pp_macroStack;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("with resulting expansion", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Elab_Command_instInhabitedScope;
x_11 = l_List_head_x21___rarg(x_10, x_9);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__1;
x_14 = l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_ctor_set(x_6, 0, x_1);
return x_6;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_ctor_set(x_6, 0, x_1);
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__5;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_indentD(x_21);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_List_foldl___at_Lean_Elab_addMacroStack___spec__1(x_16, x_23, x_2);
lean_ctor_set(x_6, 0, x_24);
return x_6;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_25 = lean_ctor_get(x_6, 0);
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_6);
x_27 = lean_ctor_get(x_25, 2);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Elab_Command_instInhabitedScope;
x_29 = l_List_head_x21___rarg(x_28, x_27);
lean_dec(x_27);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__1;
x_32 = l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_26);
return x_33;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_26);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_35 = lean_ctor_get(x_2, 0);
x_36 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__2;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__5;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l_Lean_indentD(x_41);
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_List_foldl___at_Lean_Elab_addMacroStack___spec__1(x_36, x_43, x_2);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_26);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_3, 4);
lean_inc(x_6);
lean_inc(x_6);
x_7 = l_Lean_Elab_getBetterRef(x_1, x_6);
x_8 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_2, x_3, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_9, x_6, x_3, x_4, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkMessageAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = 0;
x_6 = l_Lean_Syntax_getPos_x3f(x_2, x_5);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = l_Lean_Syntax_getTailPos_x3f(x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_Elab_mkMessageCore(x_9, x_10, x_3, x_4, x_7, x_7);
lean_dec(x_7);
lean_dec(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec(x_8);
x_15 = l_Lean_Elab_mkMessageCore(x_12, x_13, x_3, x_4, x_7, x_14);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_13);
return x_15;
}
}
else
{
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
lean_dec(x_6);
x_19 = l_Lean_Elab_mkMessageCore(x_16, x_17, x_3, x_4, x_18, x_18);
lean_dec(x_18);
lean_dec(x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_22);
lean_dec(x_6);
x_23 = lean_ctor_get(x_8, 0);
lean_inc(x_23);
lean_dec(x_8);
x_24 = l_Lean_Elab_mkMessageCore(x_20, x_21, x_3, x_4, x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkMessageAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Elab_Command_mkMessageAux(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkCoreContext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 4);
x_6 = l_Lean_Elab_Command_instInhabitedScope;
x_7 = l_List_head_x21___rarg(x_6, x_4);
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 5);
x_12 = lean_ctor_get(x_1, 6);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 3);
lean_inc(x_15);
lean_dec(x_7);
x_16 = l_Lean_Core_getMaxHeartbeats(x_13);
lean_inc(x_11);
lean_inc(x_12);
lean_inc(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_17 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_9);
lean_ctor_set(x_17, 2, x_13);
lean_ctor_set(x_17, 3, x_10);
lean_ctor_set(x_17, 4, x_5);
lean_ctor_set(x_17, 5, x_12);
lean_ctor_set(x_17, 6, x_14);
lean_ctor_set(x_17, 7, x_15);
lean_ctor_set(x_17, 8, x_3);
lean_ctor_set(x_17, 9, x_16);
lean_ctor_set(x_17, 10, x_11);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkCoreContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkCoreContext(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__3(x_1, x_7, x_5);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 6);
lean_inc(x_9);
x_10 = l_Lean_replaceRef(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = 0;
x_12 = l_Lean_Syntax_getPos_x3f(x_10, x_11);
x_13 = l_Lean_Syntax_getTailPos_x3f(x_10, x_11);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = 0;
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Elab_mkMessageCore(x_14, x_15, x_16, x_19, x_20, x_20);
lean_dec(x_15);
x_22 = l_Std_PersistentArray_push___rarg(x_5, x_21);
x_3 = x_18;
x_5 = x_22;
goto _start;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
lean_dec(x_13);
x_25 = 0;
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Elab_mkMessageCore(x_14, x_15, x_16, x_25, x_26, x_24);
lean_dec(x_24);
lean_dec(x_15);
x_28 = l_Std_PersistentArray_push___rarg(x_5, x_27);
x_3 = x_18;
x_5 = x_28;
goto _start;
}
}
else
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_12, 0);
lean_inc(x_30);
lean_dec(x_12);
x_31 = 0;
x_32 = l_Lean_Elab_mkMessageCore(x_14, x_15, x_16, x_31, x_30, x_30);
lean_dec(x_30);
lean_dec(x_15);
x_33 = l_Std_PersistentArray_push___rarg(x_5, x_32);
x_3 = x_18;
x_5 = x_33;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_12, 0);
lean_inc(x_35);
lean_dec(x_12);
x_36 = lean_ctor_get(x_13, 0);
lean_inc(x_36);
lean_dec(x_13);
x_37 = 0;
x_38 = l_Lean_Elab_mkMessageCore(x_14, x_15, x_16, x_37, x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_15);
x_39 = l_Std_PersistentArray_push___rarg(x_5, x_38);
x_3 = x_18;
x_5 = x_39;
goto _start;
}
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__4(x_1, x_4, x_9, x_10, x_3);
lean_dec(x_4);
return x_11;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_13, x_13);
if (x_16 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_19 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__5(x_1, x_12, x_17, x_18, x_3);
lean_dec(x_12);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__3(x_1, x_7, x_5);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 6);
lean_inc(x_9);
x_10 = l_Lean_replaceRef(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = 0;
x_12 = l_Lean_Syntax_getPos_x3f(x_10, x_11);
x_13 = l_Lean_Syntax_getTailPos_x3f(x_10, x_11);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = 0;
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Elab_mkMessageCore(x_14, x_15, x_16, x_19, x_20, x_20);
lean_dec(x_15);
x_22 = l_Std_PersistentArray_push___rarg(x_5, x_21);
x_3 = x_18;
x_5 = x_22;
goto _start;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
lean_dec(x_13);
x_25 = 0;
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Elab_mkMessageCore(x_14, x_15, x_16, x_25, x_26, x_24);
lean_dec(x_24);
lean_dec(x_15);
x_28 = l_Std_PersistentArray_push___rarg(x_5, x_27);
x_3 = x_18;
x_5 = x_28;
goto _start;
}
}
else
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_12, 0);
lean_inc(x_30);
lean_dec(x_12);
x_31 = 0;
x_32 = l_Lean_Elab_mkMessageCore(x_14, x_15, x_16, x_31, x_30, x_30);
lean_dec(x_30);
lean_dec(x_15);
x_33 = l_Std_PersistentArray_push___rarg(x_5, x_32);
x_3 = x_18;
x_5 = x_33;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_12, 0);
lean_inc(x_35);
lean_dec(x_12);
x_36 = lean_ctor_get(x_13, 0);
lean_inc(x_36);
lean_dec(x_13);
x_37 = 0;
x_38 = l_Lean_Elab_mkMessageCore(x_14, x_15, x_16, x_37, x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_15);
x_39 = l_Std_PersistentArray_push___rarg(x_5, x_38);
x_3 = x_18;
x_5 = x_39;
goto _start;
}
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
static lean_object* _init_l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_instInhabitedPersistentArrayNode(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_usize_shift_right(x_3, x_4);
x_8 = lean_usize_to_nat(x_7);
x_9 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__2___closed__1;
x_10 = lean_array_get(x_9, x_6, x_8);
x_11 = 1;
x_12 = lean_usize_shift_left(x_11, x_4);
x_13 = lean_usize_sub(x_12, x_11);
x_14 = lean_usize_land(x_3, x_13);
x_15 = 5;
x_16 = lean_usize_sub(x_4, x_15);
lean_inc(x_1);
x_17 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__2(x_1, x_10, x_14, x_16, x_5);
lean_dec(x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_8, x_18);
lean_dec(x_8);
x_20 = lean_array_get_size(x_6);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_1);
return x_17;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_20, x_20);
if (x_22 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_1);
return x_17;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
x_23 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_24 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_25 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__6(x_1, x_6, x_23, x_24, x_17);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_usize_to_nat(x_3);
x_28 = lean_array_get_size(x_26);
x_29 = lean_nat_dec_lt(x_27, x_28);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
return x_5;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_28, x_28);
if (x_30 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
return x_5;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; 
x_31 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_32 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_33 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__7(x_1, x_26, x_31, x_32, x_5);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 6);
lean_inc(x_9);
x_10 = l_Lean_replaceRef(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = 0;
x_12 = l_Lean_Syntax_getPos_x3f(x_10, x_11);
x_13 = l_Lean_Syntax_getTailPos_x3f(x_10, x_11);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = 0;
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Elab_mkMessageCore(x_14, x_15, x_16, x_19, x_20, x_20);
lean_dec(x_15);
x_22 = l_Std_PersistentArray_push___rarg(x_5, x_21);
x_3 = x_18;
x_5 = x_22;
goto _start;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
lean_dec(x_13);
x_25 = 0;
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Elab_mkMessageCore(x_14, x_15, x_16, x_25, x_26, x_24);
lean_dec(x_24);
lean_dec(x_15);
x_28 = l_Std_PersistentArray_push___rarg(x_5, x_27);
x_3 = x_18;
x_5 = x_28;
goto _start;
}
}
else
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_12, 0);
lean_inc(x_30);
lean_dec(x_12);
x_31 = 0;
x_32 = l_Lean_Elab_mkMessageCore(x_14, x_15, x_16, x_31, x_30, x_30);
lean_dec(x_30);
lean_dec(x_15);
x_33 = l_Std_PersistentArray_push___rarg(x_5, x_32);
x_3 = x_18;
x_5 = x_33;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_12, 0);
lean_inc(x_35);
lean_dec(x_12);
x_36 = lean_ctor_get(x_13, 0);
lean_inc(x_36);
lean_dec(x_13);
x_37 = 0;
x_38 = l_Lean_Elab_mkMessageCore(x_14, x_15, x_16, x_37, x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_15);
x_39 = l_Std_PersistentArray_push___rarg(x_5, x_38);
x_3 = x_18;
x_5 = x_39;
goto _start;
}
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 6);
lean_inc(x_9);
x_10 = l_Lean_replaceRef(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = 0;
x_12 = l_Lean_Syntax_getPos_x3f(x_10, x_11);
x_13 = l_Lean_Syntax_getTailPos_x3f(x_10, x_11);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = 0;
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Elab_mkMessageCore(x_14, x_15, x_16, x_19, x_20, x_20);
lean_dec(x_15);
x_22 = l_Std_PersistentArray_push___rarg(x_5, x_21);
x_3 = x_18;
x_5 = x_22;
goto _start;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
lean_dec(x_13);
x_25 = 0;
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Elab_mkMessageCore(x_14, x_15, x_16, x_25, x_26, x_24);
lean_dec(x_24);
lean_dec(x_15);
x_28 = l_Std_PersistentArray_push___rarg(x_5, x_27);
x_3 = x_18;
x_5 = x_28;
goto _start;
}
}
else
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_12, 0);
lean_inc(x_30);
lean_dec(x_12);
x_31 = 0;
x_32 = l_Lean_Elab_mkMessageCore(x_14, x_15, x_16, x_31, x_30, x_30);
lean_dec(x_30);
lean_dec(x_15);
x_33 = l_Std_PersistentArray_push___rarg(x_5, x_32);
x_3 = x_18;
x_5 = x_33;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_12, 0);
lean_inc(x_35);
lean_dec(x_12);
x_36 = lean_ctor_get(x_13, 0);
lean_inc(x_36);
lean_dec(x_13);
x_37 = 0;
x_38 = l_Lean_Elab_mkMessageCore(x_14, x_15, x_16, x_37, x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_15);
x_39 = l_Std_PersistentArray_push___rarg(x_5, x_38);
x_3 = x_18;
x_5 = x_39;
goto _start;
}
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__11(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__10(x_1, x_7, x_5);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__12(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 6);
lean_inc(x_9);
x_10 = l_Lean_replaceRef(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = 0;
x_12 = l_Lean_Syntax_getPos_x3f(x_10, x_11);
x_13 = l_Lean_Syntax_getTailPos_x3f(x_10, x_11);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = 0;
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Elab_mkMessageCore(x_14, x_15, x_16, x_19, x_20, x_20);
lean_dec(x_15);
x_22 = l_Std_PersistentArray_push___rarg(x_5, x_21);
x_3 = x_18;
x_5 = x_22;
goto _start;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
lean_dec(x_13);
x_25 = 0;
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Elab_mkMessageCore(x_14, x_15, x_16, x_25, x_26, x_24);
lean_dec(x_24);
lean_dec(x_15);
x_28 = l_Std_PersistentArray_push___rarg(x_5, x_27);
x_3 = x_18;
x_5 = x_28;
goto _start;
}
}
else
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_12, 0);
lean_inc(x_30);
lean_dec(x_12);
x_31 = 0;
x_32 = l_Lean_Elab_mkMessageCore(x_14, x_15, x_16, x_31, x_30, x_30);
lean_dec(x_30);
lean_dec(x_15);
x_33 = l_Std_PersistentArray_push___rarg(x_5, x_32);
x_3 = x_18;
x_5 = x_33;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_12, 0);
lean_inc(x_35);
lean_dec(x_12);
x_36 = lean_ctor_get(x_13, 0);
lean_inc(x_36);
lean_dec(x_13);
x_37 = 0;
x_38 = l_Lean_Elab_mkMessageCore(x_14, x_15, x_16, x_37, x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_15);
x_39 = l_Std_PersistentArray_push___rarg(x_5, x_38);
x_3 = x_18;
x_5 = x_39;
goto _start;
}
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__11(x_1, x_4, x_9, x_10, x_3);
lean_dec(x_4);
return x_11;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_13, x_13);
if (x_16 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_19 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__12(x_1, x_12, x_17, x_18, x_3);
lean_dec(x_12);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__13(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 6);
lean_inc(x_9);
x_10 = l_Lean_replaceRef(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = 0;
x_12 = l_Lean_Syntax_getPos_x3f(x_10, x_11);
x_13 = l_Lean_Syntax_getTailPos_x3f(x_10, x_11);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = 0;
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Elab_mkMessageCore(x_14, x_15, x_16, x_19, x_20, x_20);
lean_dec(x_15);
x_22 = l_Std_PersistentArray_push___rarg(x_5, x_21);
x_3 = x_18;
x_5 = x_22;
goto _start;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
lean_dec(x_13);
x_25 = 0;
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Elab_mkMessageCore(x_14, x_15, x_16, x_25, x_26, x_24);
lean_dec(x_24);
lean_dec(x_15);
x_28 = l_Std_PersistentArray_push___rarg(x_5, x_27);
x_3 = x_18;
x_5 = x_28;
goto _start;
}
}
else
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_12, 0);
lean_inc(x_30);
lean_dec(x_12);
x_31 = 0;
x_32 = l_Lean_Elab_mkMessageCore(x_14, x_15, x_16, x_31, x_30, x_30);
lean_dec(x_30);
lean_dec(x_15);
x_33 = l_Std_PersistentArray_push___rarg(x_5, x_32);
x_3 = x_18;
x_5 = x_33;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_12, 0);
lean_inc(x_35);
lean_dec(x_12);
x_36 = lean_ctor_get(x_13, 0);
lean_inc(x_36);
lean_dec(x_13);
x_37 = 0;
x_38 = l_Lean_Elab_mkMessageCore(x_14, x_15, x_16, x_37, x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_15);
x_39 = l_Std_PersistentArray_push___rarg(x_5, x_38);
x_3 = x_18;
x_5 = x_39;
goto _start;
}
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_foldlM___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
x_8 = lean_nat_dec_le(x_7, x_4);
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_11 = lean_ctor_get_usize(x_2, 4);
lean_inc(x_1);
x_12 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__2(x_1, x_9, x_10, x_11, x_3);
lean_dec(x_9);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_array_get_size(x_13);
x_15 = lean_nat_dec_lt(x_5, x_14);
if (x_15 == 0)
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
return x_12;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_14, x_14);
if (x_16 == 0)
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
return x_12;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_19 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__8(x_1, x_13, x_17, x_18, x_12);
lean_dec(x_13);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_nat_sub(x_4, x_7);
lean_dec(x_7);
lean_dec(x_4);
x_22 = lean_array_get_size(x_20);
x_23 = lean_nat_dec_lt(x_21, x_22);
if (x_23 == 0)
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_22, x_22);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; 
x_25 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_26 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_27 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__9(x_1, x_20, x_25, x_26, x_3);
lean_dec(x_20);
return x_27;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_4);
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
lean_inc(x_1);
x_29 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__10(x_1, x_28, x_3);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
lean_dec(x_2);
x_31 = lean_array_get_size(x_30);
x_32 = lean_nat_dec_lt(x_5, x_31);
if (x_32 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_1);
return x_29;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_31, x_31);
if (x_33 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_1);
return x_29;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
x_34 = 0;
x_35 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_36 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__13(x_1, x_30, x_34, x_35, x_29);
lean_dec(x_30);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Std_PersistentArray_foldlM___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__1(x_1, x_4, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__4(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__5(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__6(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__7(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__8(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__9(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__11(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__12(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__13(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_5, 8);
lean_inc(x_9);
x_10 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore(x_1, x_8, x_9);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = l_Lean_Elab_Command_State_messages___default___closed__3;
lean_ctor_set(x_9, 0, x_13);
lean_ctor_set(x_5, 1, x_10);
x_14 = lean_st_ref_set(x_2, x_5, x_6);
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
uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get_uint8(x_9, sizeof(void*)*1);
lean_dec(x_9);
x_22 = l_Lean_Elab_Command_State_messages___default___closed__3;
x_23 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_21);
lean_ctor_set(x_5, 8, x_23);
lean_ctor_set(x_5, 1, x_10);
x_24 = lean_st_ref_set(x_2, x_5, x_6);
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
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
x_31 = lean_ctor_get(x_5, 2);
x_32 = lean_ctor_get(x_5, 3);
x_33 = lean_ctor_get(x_5, 4);
x_34 = lean_ctor_get(x_5, 5);
x_35 = lean_ctor_get(x_5, 6);
x_36 = lean_ctor_get(x_5, 7);
x_37 = lean_ctor_get(x_5, 8);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
lean_inc(x_37);
x_38 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore(x_1, x_30, x_37);
x_39 = lean_ctor_get_uint8(x_37, sizeof(void*)*1);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = l_Lean_Elab_Command_State_messages___default___closed__3;
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 1, 1);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_39);
x_43 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_43, 0, x_29);
lean_ctor_set(x_43, 1, x_38);
lean_ctor_set(x_43, 2, x_31);
lean_ctor_set(x_43, 3, x_32);
lean_ctor_set(x_43, 4, x_33);
lean_ctor_set(x_43, 5, x_34);
lean_ctor_set(x_43, 6, x_35);
lean_ctor_set(x_43, 7, x_36);
lean_ctor_set(x_43, 8, x_42);
x_44 = lean_st_ref_set(x_2, x_43, x_6);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
x_47 = lean_box(0);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_liftCoreM___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_instInhabitedState___closed__2;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_liftCoreM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_io_get_num_heartbeats(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkCoreContext(x_2, x_6, x_9);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 6);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 8);
lean_inc(x_14);
lean_dec(x_6);
x_15 = l_Lean_Elab_Command_State_nextMacroScope___default___closed__1;
x_16 = l_Lean_Elab_Command_liftCoreM___rarg___closed__1;
x_17 = l_Lean_Elab_Command_State_messages___default___closed__3;
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_13);
lean_ctor_set(x_18, 3, x_14);
lean_ctor_set(x_18, 4, x_16);
lean_ctor_set(x_18, 5, x_17);
x_69 = lean_st_mk_ref(x_18, x_10);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_70);
x_72 = lean_apply_3(x_1, x_11, x_70, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_73);
x_76 = lean_st_ref_get(x_70, x_74);
lean_dec(x_70);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_77);
x_19 = x_79;
x_20 = x_78;
goto block_68;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_80 = lean_ctor_get(x_72, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_72, 1);
lean_inc(x_81);
lean_dec(x_72);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_80);
x_83 = lean_st_ref_get(x_70, x_81);
lean_dec(x_70);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_82);
lean_ctor_set(x_86, 1, x_84);
x_19 = x_86;
x_20 = x_85;
goto block_68;
}
block_68:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_st_ref_take(x_3, x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_22, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_22, 3);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 5);
lean_inc(x_29);
lean_dec(x_22);
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_24, 1);
x_32 = lean_ctor_get(x_24, 8);
lean_dec(x_32);
x_33 = lean_ctor_get(x_24, 6);
lean_dec(x_33);
x_34 = lean_ctor_get(x_24, 0);
lean_dec(x_34);
x_35 = l_Std_PersistentArray_append___rarg(x_31, x_29);
lean_inc(x_28);
x_36 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore(x_2, x_35, x_28);
lean_ctor_set(x_24, 8, x_28);
lean_ctor_set(x_24, 6, x_27);
lean_ctor_set(x_24, 1, x_36);
lean_ctor_set(x_24, 0, x_26);
x_37 = lean_st_ref_set(x_3, x_24, x_25);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_21, 0);
lean_inc(x_40);
lean_dec(x_21);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_ctor_get(x_21, 0);
lean_inc(x_42);
lean_dec(x_21);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_37, 0);
lean_dec(x_45);
x_46 = lean_ctor_get(x_21, 0);
lean_inc(x_46);
lean_dec(x_21);
lean_ctor_set(x_37, 0, x_46);
return x_37;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_37, 1);
lean_inc(x_47);
lean_dec(x_37);
x_48 = lean_ctor_get(x_21, 0);
lean_inc(x_48);
lean_dec(x_21);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_50 = lean_ctor_get(x_24, 1);
x_51 = lean_ctor_get(x_24, 2);
x_52 = lean_ctor_get(x_24, 3);
x_53 = lean_ctor_get(x_24, 4);
x_54 = lean_ctor_get(x_24, 5);
x_55 = lean_ctor_get(x_24, 7);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_24);
x_56 = l_Std_PersistentArray_append___rarg(x_50, x_29);
lean_inc(x_28);
x_57 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore(x_2, x_56, x_28);
x_58 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_58, 0, x_26);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_58, 2, x_51);
lean_ctor_set(x_58, 3, x_52);
lean_ctor_set(x_58, 4, x_53);
lean_ctor_set(x_58, 5, x_54);
lean_ctor_set(x_58, 6, x_27);
lean_ctor_set(x_58, 7, x_55);
lean_ctor_set(x_58, 8, x_28);
x_59 = lean_st_ref_set(x_3, x_58, x_25);
if (lean_obj_tag(x_21) == 0)
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
x_62 = lean_ctor_get(x_21, 0);
lean_inc(x_62);
lean_dec(x_21);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_61;
 lean_ctor_set_tag(x_63, 1);
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
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
x_66 = lean_ctor_get(x_21, 0);
lean_inc(x_66);
lean_dec(x_21);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_liftCoreM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftCoreM___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_liftCoreM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_liftCoreM___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_ioErrorToMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_ioErrorToMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_ioErrorToMessage(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_liftEIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_liftEIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftEIO___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_liftEIO___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_liftEIO___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_liftIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_liftIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftIO___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_liftIO___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_liftIO___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadLiftTIOCommandElabM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadLiftTIOCommandElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadLiftTIOCommandElabM___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadLiftTIOCommandElabM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_instMonadLiftTIOCommandElabM___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getScope___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Elab_Command_instInhabitedScope;
x_8 = l_List_head_x21___rarg(x_7, x_6);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_Command_instInhabitedScope;
x_13 = l_List_head_x21___rarg(x_12, x_11);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getScope___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getScope___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_getScope___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getScope___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_getScope(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Command_getScope___rarg(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_ctor_get(x_8, 2);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Command_getScope___rarg(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_ctor_get(x_8, 3);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadResolveNameCommandElabM___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadResolveNameCommandElabM___lambda__2___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__1;
x_2 = l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadResolveNameCommandElabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_instMonadResolveNameCommandElabM___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_instMonadResolveNameCommandElabM___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_7);
x_9 = lean_box(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_12);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = l_Lean_Elab_Command_getScope___rarg(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 2);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
x_32 = lean_ctor_get(x_18, 2);
x_33 = lean_ctor_get(x_18, 3);
x_34 = lean_ctor_get(x_18, 4);
x_35 = lean_ctor_get(x_18, 5);
x_36 = lean_ctor_get(x_18, 6);
x_37 = lean_ctor_get(x_18, 7);
x_38 = lean_ctor_get(x_18, 8);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_39 = l_Std_PersistentArray_push___rarg(x_31, x_1);
x_40 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_40, 0, x_30);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_32);
lean_ctor_set(x_40, 3, x_33);
lean_ctor_set(x_40, 4, x_34);
lean_ctor_set(x_40, 5, x_35);
lean_ctor_set(x_40, 6, x_36);
lean_ctor_set(x_40, 7, x_37);
lean_ctor_set(x_40, 8, x_38);
x_41 = lean_st_ref_set(x_3, x_40, x_19);
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
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_46 = lean_ctor_get(x_1, 0);
x_47 = lean_ctor_get(x_1, 1);
x_48 = lean_ctor_get(x_1, 2);
x_49 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_50 = lean_ctor_get(x_1, 3);
x_51 = lean_ctor_get(x_1, 4);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_8);
lean_ctor_set(x_52, 1, x_12);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_54, 0, x_46);
lean_ctor_set(x_54, 1, x_47);
lean_ctor_set(x_54, 2, x_48);
lean_ctor_set(x_54, 3, x_50);
lean_ctor_set(x_54, 4, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*5, x_49);
x_55 = lean_st_ref_take(x_3, x_11);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_56, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_56, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_56, 4);
lean_inc(x_62);
x_63 = lean_ctor_get(x_56, 5);
lean_inc(x_63);
x_64 = lean_ctor_get(x_56, 6);
lean_inc(x_64);
x_65 = lean_ctor_get(x_56, 7);
lean_inc(x_65);
x_66 = lean_ctor_get(x_56, 8);
lean_inc(x_66);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 lean_ctor_release(x_56, 3);
 lean_ctor_release(x_56, 4);
 lean_ctor_release(x_56, 5);
 lean_ctor_release(x_56, 6);
 lean_ctor_release(x_56, 7);
 lean_ctor_release(x_56, 8);
 x_67 = x_56;
} else {
 lean_dec_ref(x_56);
 x_67 = lean_box(0);
}
x_68 = l_Std_PersistentArray_push___rarg(x_59, x_54);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 9, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_58);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_69, 2, x_60);
lean_ctor_set(x_69, 3, x_61);
lean_ctor_set(x_69, 4, x_62);
lean_ctor_set(x_69, 5, x_63);
lean_ctor_set(x_69, 6, x_64);
lean_ctor_set(x_69, 7, x_65);
lean_ctor_set(x_69, 8, x_66);
x_70 = lean_st_ref_set(x_3, x_69, x_57);
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
static lean_object* _init_l_Lean_Elab_Command_instMonadLogCommandElabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadLogCommandElabM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__2___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadLogCommandElabM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__3___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadLogCommandElabM___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadLogCommandElabM___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Command_instMonadLogCommandElabM___closed__1;
x_2 = l_Lean_Elab_Command_instMonadRefCommandElabM___closed__1;
x_3 = l_Lean_Elab_Command_instMonadLogCommandElabM___closed__2;
x_4 = l_Lean_Elab_Command_instMonadLogCommandElabM___closed__3;
x_5 = l_Lean_Elab_Command_instMonadLogCommandElabM___closed__4;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadLogCommandElabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instMonadLogCommandElabM___closed__5;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_339; uint8_t x_340; 
x_339 = 2;
x_340 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_101_(x_3, x_339);
if (x_340 == 0)
{
lean_object* x_341; 
x_341 = lean_box(0);
x_7 = x_341;
goto block_338;
}
else
{
uint8_t x_342; 
lean_inc(x_2);
x_342 = l_Lean_MessageData_hasSyntheticSorry(x_2);
if (x_342 == 0)
{
lean_object* x_343; 
x_343 = lean_box(0);
x_7 = x_343;
goto block_338;
}
else
{
lean_object* x_344; lean_object* x_345; 
lean_dec(x_2);
x_344 = lean_box(0);
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_6);
return x_345;
}
}
block_338:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
x_8 = l_Lean_Elab_Command_getRef(x_4, x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_replaceRef(x_1, x_9);
lean_dec(x_9);
x_12 = 0;
x_13 = l_Lean_Syntax_getPos_x3f(x_11, x_12);
x_14 = l_Lean_Syntax_getTailPos_x3f(x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_2, x_4, x_5, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_FileMap_toPosition(x_16, x_20);
lean_inc(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_Elab_Command_getScope___rarg(x_5, x_19);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 2);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Command_getScope___rarg(x_5, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 3);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_18);
x_33 = l_Lean_Elab_Command_instInhabitedScope___closed__1;
lean_inc(x_15);
x_34 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_34, 0, x_15);
lean_ctor_set(x_34, 1, x_21);
lean_ctor_set(x_34, 2, x_22);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_34, 4, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*5, x_3);
x_35 = lean_st_ref_take(x_5, x_29);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_36, 1);
x_40 = l_Std_PersistentArray_push___rarg(x_39, x_34);
lean_ctor_set(x_36, 1, x_40);
x_41 = lean_st_ref_set(x_5, x_36, x_37);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = lean_box(0);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_48 = lean_ctor_get(x_36, 0);
x_49 = lean_ctor_get(x_36, 1);
x_50 = lean_ctor_get(x_36, 2);
x_51 = lean_ctor_get(x_36, 3);
x_52 = lean_ctor_get(x_36, 4);
x_53 = lean_ctor_get(x_36, 5);
x_54 = lean_ctor_get(x_36, 6);
x_55 = lean_ctor_get(x_36, 7);
x_56 = lean_ctor_get(x_36, 8);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_36);
x_57 = l_Std_PersistentArray_push___rarg(x_49, x_34);
x_58 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_58, 2, x_50);
lean_ctor_set(x_58, 3, x_51);
lean_ctor_set(x_58, 4, x_52);
lean_ctor_set(x_58, 5, x_53);
lean_ctor_set(x_58, 6, x_54);
lean_ctor_set(x_58, 7, x_55);
lean_ctor_set(x_58, 8, x_56);
x_59 = lean_st_ref_set(x_5, x_58, x_37);
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
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_14);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_65 = lean_ctor_get(x_14, 0);
x_66 = lean_ctor_get(x_4, 0);
x_67 = lean_ctor_get(x_4, 1);
x_68 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_2, x_4, x_5, x_10);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_unsigned_to_nat(0u);
x_72 = l_Lean_FileMap_toPosition(x_67, x_71);
x_73 = l_Lean_FileMap_toPosition(x_67, x_65);
lean_dec(x_65);
lean_ctor_set(x_14, 0, x_73);
x_74 = l_Lean_Elab_Command_getScope___rarg(x_5, x_70);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_75, 2);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Elab_Command_getScope___rarg(x_5, x_76);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_79, 3);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_77);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_69);
x_84 = l_Lean_Elab_Command_instInhabitedScope___closed__1;
lean_inc(x_66);
x_85 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_85, 0, x_66);
lean_ctor_set(x_85, 1, x_72);
lean_ctor_set(x_85, 2, x_14);
lean_ctor_set(x_85, 3, x_84);
lean_ctor_set(x_85, 4, x_83);
lean_ctor_set_uint8(x_85, sizeof(void*)*5, x_3);
x_86 = lean_st_ref_take(x_5, x_80);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = !lean_is_exclusive(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_87, 1);
x_91 = l_Std_PersistentArray_push___rarg(x_90, x_85);
lean_ctor_set(x_87, 1, x_91);
x_92 = lean_st_ref_set(x_5, x_87, x_88);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_92, 0);
lean_dec(x_94);
x_95 = lean_box(0);
lean_ctor_set(x_92, 0, x_95);
return x_92;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_dec(x_92);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_99 = lean_ctor_get(x_87, 0);
x_100 = lean_ctor_get(x_87, 1);
x_101 = lean_ctor_get(x_87, 2);
x_102 = lean_ctor_get(x_87, 3);
x_103 = lean_ctor_get(x_87, 4);
x_104 = lean_ctor_get(x_87, 5);
x_105 = lean_ctor_get(x_87, 6);
x_106 = lean_ctor_get(x_87, 7);
x_107 = lean_ctor_get(x_87, 8);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_87);
x_108 = l_Std_PersistentArray_push___rarg(x_100, x_85);
x_109 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_109, 0, x_99);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set(x_109, 2, x_101);
lean_ctor_set(x_109, 3, x_102);
lean_ctor_set(x_109, 4, x_103);
lean_ctor_set(x_109, 5, x_104);
lean_ctor_set(x_109, 6, x_105);
lean_ctor_set(x_109, 7, x_106);
lean_ctor_set(x_109, 8, x_107);
x_110 = lean_st_ref_set(x_5, x_109, x_88);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_112 = x_110;
} else {
 lean_dec_ref(x_110);
 x_112 = lean_box(0);
}
x_113 = lean_box(0);
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_111);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_115 = lean_ctor_get(x_14, 0);
lean_inc(x_115);
lean_dec(x_14);
x_116 = lean_ctor_get(x_4, 0);
x_117 = lean_ctor_get(x_4, 1);
x_118 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_2, x_4, x_5, x_10);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_unsigned_to_nat(0u);
x_122 = l_Lean_FileMap_toPosition(x_117, x_121);
x_123 = l_Lean_FileMap_toPosition(x_117, x_115);
lean_dec(x_115);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
x_125 = l_Lean_Elab_Command_getScope___rarg(x_5, x_120);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_ctor_get(x_126, 2);
lean_inc(x_128);
lean_dec(x_126);
x_129 = l_Lean_Elab_Command_getScope___rarg(x_5, x_127);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_ctor_get(x_130, 3);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_128);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_119);
x_135 = l_Lean_Elab_Command_instInhabitedScope___closed__1;
lean_inc(x_116);
x_136 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_136, 0, x_116);
lean_ctor_set(x_136, 1, x_122);
lean_ctor_set(x_136, 2, x_124);
lean_ctor_set(x_136, 3, x_135);
lean_ctor_set(x_136, 4, x_134);
lean_ctor_set_uint8(x_136, sizeof(void*)*5, x_3);
x_137 = lean_st_ref_take(x_5, x_131);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_ctor_get(x_138, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
x_142 = lean_ctor_get(x_138, 2);
lean_inc(x_142);
x_143 = lean_ctor_get(x_138, 3);
lean_inc(x_143);
x_144 = lean_ctor_get(x_138, 4);
lean_inc(x_144);
x_145 = lean_ctor_get(x_138, 5);
lean_inc(x_145);
x_146 = lean_ctor_get(x_138, 6);
lean_inc(x_146);
x_147 = lean_ctor_get(x_138, 7);
lean_inc(x_147);
x_148 = lean_ctor_get(x_138, 8);
lean_inc(x_148);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 lean_ctor_release(x_138, 2);
 lean_ctor_release(x_138, 3);
 lean_ctor_release(x_138, 4);
 lean_ctor_release(x_138, 5);
 lean_ctor_release(x_138, 6);
 lean_ctor_release(x_138, 7);
 lean_ctor_release(x_138, 8);
 x_149 = x_138;
} else {
 lean_dec_ref(x_138);
 x_149 = lean_box(0);
}
x_150 = l_Std_PersistentArray_push___rarg(x_141, x_136);
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(0, 9, 0);
} else {
 x_151 = x_149;
}
lean_ctor_set(x_151, 0, x_140);
lean_ctor_set(x_151, 1, x_150);
lean_ctor_set(x_151, 2, x_142);
lean_ctor_set(x_151, 3, x_143);
lean_ctor_set(x_151, 4, x_144);
lean_ctor_set(x_151, 5, x_145);
lean_ctor_set(x_151, 6, x_146);
lean_ctor_set(x_151, 7, x_147);
lean_ctor_set(x_151, 8, x_148);
x_152 = lean_st_ref_set(x_5, x_151, x_139);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_154 = x_152;
} else {
 lean_dec_ref(x_152);
 x_154 = lean_box(0);
}
x_155 = lean_box(0);
if (lean_is_scalar(x_154)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_154;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_153);
return x_156;
}
}
}
else
{
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_157; 
x_157 = !lean_is_exclusive(x_13);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_158 = lean_ctor_get(x_13, 0);
x_159 = lean_ctor_get(x_4, 0);
x_160 = lean_ctor_get(x_4, 1);
x_161 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_2, x_4, x_5, x_10);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = l_Lean_FileMap_toPosition(x_160, x_158);
lean_dec(x_158);
lean_inc(x_164);
lean_ctor_set(x_13, 0, x_164);
x_165 = l_Lean_Elab_Command_getScope___rarg(x_5, x_163);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_ctor_get(x_166, 2);
lean_inc(x_168);
lean_dec(x_166);
x_169 = l_Lean_Elab_Command_getScope___rarg(x_5, x_167);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_ctor_get(x_170, 3);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_168);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_162);
x_175 = l_Lean_Elab_Command_instInhabitedScope___closed__1;
lean_inc(x_159);
x_176 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_176, 0, x_159);
lean_ctor_set(x_176, 1, x_164);
lean_ctor_set(x_176, 2, x_13);
lean_ctor_set(x_176, 3, x_175);
lean_ctor_set(x_176, 4, x_174);
lean_ctor_set_uint8(x_176, sizeof(void*)*5, x_3);
x_177 = lean_st_ref_take(x_5, x_171);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = !lean_is_exclusive(x_178);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_181 = lean_ctor_get(x_178, 1);
x_182 = l_Std_PersistentArray_push___rarg(x_181, x_176);
lean_ctor_set(x_178, 1, x_182);
x_183 = lean_st_ref_set(x_5, x_178, x_179);
x_184 = !lean_is_exclusive(x_183);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_183, 0);
lean_dec(x_185);
x_186 = lean_box(0);
lean_ctor_set(x_183, 0, x_186);
return x_183;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_183, 1);
lean_inc(x_187);
lean_dec(x_183);
x_188 = lean_box(0);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_190 = lean_ctor_get(x_178, 0);
x_191 = lean_ctor_get(x_178, 1);
x_192 = lean_ctor_get(x_178, 2);
x_193 = lean_ctor_get(x_178, 3);
x_194 = lean_ctor_get(x_178, 4);
x_195 = lean_ctor_get(x_178, 5);
x_196 = lean_ctor_get(x_178, 6);
x_197 = lean_ctor_get(x_178, 7);
x_198 = lean_ctor_get(x_178, 8);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_178);
x_199 = l_Std_PersistentArray_push___rarg(x_191, x_176);
x_200 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_200, 0, x_190);
lean_ctor_set(x_200, 1, x_199);
lean_ctor_set(x_200, 2, x_192);
lean_ctor_set(x_200, 3, x_193);
lean_ctor_set(x_200, 4, x_194);
lean_ctor_set(x_200, 5, x_195);
lean_ctor_set(x_200, 6, x_196);
lean_ctor_set(x_200, 7, x_197);
lean_ctor_set(x_200, 8, x_198);
x_201 = lean_st_ref_set(x_5, x_200, x_179);
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_203 = x_201;
} else {
 lean_dec_ref(x_201);
 x_203 = lean_box(0);
}
x_204 = lean_box(0);
if (lean_is_scalar(x_203)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_203;
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_202);
return x_205;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_206 = lean_ctor_get(x_13, 0);
lean_inc(x_206);
lean_dec(x_13);
x_207 = lean_ctor_get(x_4, 0);
x_208 = lean_ctor_get(x_4, 1);
x_209 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_2, x_4, x_5, x_10);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = l_Lean_FileMap_toPosition(x_208, x_206);
lean_dec(x_206);
lean_inc(x_212);
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_212);
x_214 = l_Lean_Elab_Command_getScope___rarg(x_5, x_211);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_ctor_get(x_215, 2);
lean_inc(x_217);
lean_dec(x_215);
x_218 = l_Lean_Elab_Command_getScope___rarg(x_5, x_216);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_221 = lean_ctor_get(x_219, 3);
lean_inc(x_221);
lean_dec(x_219);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_217);
lean_ctor_set(x_222, 1, x_221);
x_223 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_210);
x_224 = l_Lean_Elab_Command_instInhabitedScope___closed__1;
lean_inc(x_207);
x_225 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_225, 0, x_207);
lean_ctor_set(x_225, 1, x_212);
lean_ctor_set(x_225, 2, x_213);
lean_ctor_set(x_225, 3, x_224);
lean_ctor_set(x_225, 4, x_223);
lean_ctor_set_uint8(x_225, sizeof(void*)*5, x_3);
x_226 = lean_st_ref_take(x_5, x_220);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec(x_226);
x_229 = lean_ctor_get(x_227, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_227, 1);
lean_inc(x_230);
x_231 = lean_ctor_get(x_227, 2);
lean_inc(x_231);
x_232 = lean_ctor_get(x_227, 3);
lean_inc(x_232);
x_233 = lean_ctor_get(x_227, 4);
lean_inc(x_233);
x_234 = lean_ctor_get(x_227, 5);
lean_inc(x_234);
x_235 = lean_ctor_get(x_227, 6);
lean_inc(x_235);
x_236 = lean_ctor_get(x_227, 7);
lean_inc(x_236);
x_237 = lean_ctor_get(x_227, 8);
lean_inc(x_237);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 lean_ctor_release(x_227, 2);
 lean_ctor_release(x_227, 3);
 lean_ctor_release(x_227, 4);
 lean_ctor_release(x_227, 5);
 lean_ctor_release(x_227, 6);
 lean_ctor_release(x_227, 7);
 lean_ctor_release(x_227, 8);
 x_238 = x_227;
} else {
 lean_dec_ref(x_227);
 x_238 = lean_box(0);
}
x_239 = l_Std_PersistentArray_push___rarg(x_230, x_225);
if (lean_is_scalar(x_238)) {
 x_240 = lean_alloc_ctor(0, 9, 0);
} else {
 x_240 = x_238;
}
lean_ctor_set(x_240, 0, x_229);
lean_ctor_set(x_240, 1, x_239);
lean_ctor_set(x_240, 2, x_231);
lean_ctor_set(x_240, 3, x_232);
lean_ctor_set(x_240, 4, x_233);
lean_ctor_set(x_240, 5, x_234);
lean_ctor_set(x_240, 6, x_235);
lean_ctor_set(x_240, 7, x_236);
lean_ctor_set(x_240, 8, x_237);
x_241 = lean_st_ref_set(x_5, x_240, x_228);
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_243 = x_241;
} else {
 lean_dec_ref(x_241);
 x_243 = lean_box(0);
}
x_244 = lean_box(0);
if (lean_is_scalar(x_243)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_243;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_242);
return x_245;
}
}
else
{
lean_object* x_246; uint8_t x_247; 
x_246 = lean_ctor_get(x_13, 0);
lean_inc(x_246);
lean_dec(x_13);
x_247 = !lean_is_exclusive(x_14);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_248 = lean_ctor_get(x_14, 0);
x_249 = lean_ctor_get(x_4, 0);
x_250 = lean_ctor_get(x_4, 1);
x_251 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_2, x_4, x_5, x_10);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_254 = l_Lean_FileMap_toPosition(x_250, x_246);
lean_dec(x_246);
x_255 = l_Lean_FileMap_toPosition(x_250, x_248);
lean_dec(x_248);
lean_ctor_set(x_14, 0, x_255);
x_256 = l_Lean_Elab_Command_getScope___rarg(x_5, x_253);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_259 = lean_ctor_get(x_257, 2);
lean_inc(x_259);
lean_dec(x_257);
x_260 = l_Lean_Elab_Command_getScope___rarg(x_5, x_258);
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec(x_260);
x_263 = lean_ctor_get(x_261, 3);
lean_inc(x_263);
lean_dec(x_261);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_259);
lean_ctor_set(x_264, 1, x_263);
x_265 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_252);
x_266 = l_Lean_Elab_Command_instInhabitedScope___closed__1;
lean_inc(x_249);
x_267 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_267, 0, x_249);
lean_ctor_set(x_267, 1, x_254);
lean_ctor_set(x_267, 2, x_14);
lean_ctor_set(x_267, 3, x_266);
lean_ctor_set(x_267, 4, x_265);
lean_ctor_set_uint8(x_267, sizeof(void*)*5, x_3);
x_268 = lean_st_ref_take(x_5, x_262);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = !lean_is_exclusive(x_269);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_272 = lean_ctor_get(x_269, 1);
x_273 = l_Std_PersistentArray_push___rarg(x_272, x_267);
lean_ctor_set(x_269, 1, x_273);
x_274 = lean_st_ref_set(x_5, x_269, x_270);
x_275 = !lean_is_exclusive(x_274);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; 
x_276 = lean_ctor_get(x_274, 0);
lean_dec(x_276);
x_277 = lean_box(0);
lean_ctor_set(x_274, 0, x_277);
return x_274;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_274, 1);
lean_inc(x_278);
lean_dec(x_274);
x_279 = lean_box(0);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_278);
return x_280;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_281 = lean_ctor_get(x_269, 0);
x_282 = lean_ctor_get(x_269, 1);
x_283 = lean_ctor_get(x_269, 2);
x_284 = lean_ctor_get(x_269, 3);
x_285 = lean_ctor_get(x_269, 4);
x_286 = lean_ctor_get(x_269, 5);
x_287 = lean_ctor_get(x_269, 6);
x_288 = lean_ctor_get(x_269, 7);
x_289 = lean_ctor_get(x_269, 8);
lean_inc(x_289);
lean_inc(x_288);
lean_inc(x_287);
lean_inc(x_286);
lean_inc(x_285);
lean_inc(x_284);
lean_inc(x_283);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_269);
x_290 = l_Std_PersistentArray_push___rarg(x_282, x_267);
x_291 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_291, 0, x_281);
lean_ctor_set(x_291, 1, x_290);
lean_ctor_set(x_291, 2, x_283);
lean_ctor_set(x_291, 3, x_284);
lean_ctor_set(x_291, 4, x_285);
lean_ctor_set(x_291, 5, x_286);
lean_ctor_set(x_291, 6, x_287);
lean_ctor_set(x_291, 7, x_288);
lean_ctor_set(x_291, 8, x_289);
x_292 = lean_st_ref_set(x_5, x_291, x_270);
x_293 = lean_ctor_get(x_292, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 x_294 = x_292;
} else {
 lean_dec_ref(x_292);
 x_294 = lean_box(0);
}
x_295 = lean_box(0);
if (lean_is_scalar(x_294)) {
 x_296 = lean_alloc_ctor(0, 2, 0);
} else {
 x_296 = x_294;
}
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_293);
return x_296;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_297 = lean_ctor_get(x_14, 0);
lean_inc(x_297);
lean_dec(x_14);
x_298 = lean_ctor_get(x_4, 0);
x_299 = lean_ctor_get(x_4, 1);
x_300 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_2, x_4, x_5, x_10);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_303 = l_Lean_FileMap_toPosition(x_299, x_246);
lean_dec(x_246);
x_304 = l_Lean_FileMap_toPosition(x_299, x_297);
lean_dec(x_297);
x_305 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_305, 0, x_304);
x_306 = l_Lean_Elab_Command_getScope___rarg(x_5, x_302);
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
lean_dec(x_306);
x_309 = lean_ctor_get(x_307, 2);
lean_inc(x_309);
lean_dec(x_307);
x_310 = l_Lean_Elab_Command_getScope___rarg(x_5, x_308);
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 1);
lean_inc(x_312);
lean_dec(x_310);
x_313 = lean_ctor_get(x_311, 3);
lean_inc(x_313);
lean_dec(x_311);
x_314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_314, 0, x_309);
lean_ctor_set(x_314, 1, x_313);
x_315 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_301);
x_316 = l_Lean_Elab_Command_instInhabitedScope___closed__1;
lean_inc(x_298);
x_317 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_317, 0, x_298);
lean_ctor_set(x_317, 1, x_303);
lean_ctor_set(x_317, 2, x_305);
lean_ctor_set(x_317, 3, x_316);
lean_ctor_set(x_317, 4, x_315);
lean_ctor_set_uint8(x_317, sizeof(void*)*5, x_3);
x_318 = lean_st_ref_take(x_5, x_312);
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec(x_318);
x_321 = lean_ctor_get(x_319, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_319, 1);
lean_inc(x_322);
x_323 = lean_ctor_get(x_319, 2);
lean_inc(x_323);
x_324 = lean_ctor_get(x_319, 3);
lean_inc(x_324);
x_325 = lean_ctor_get(x_319, 4);
lean_inc(x_325);
x_326 = lean_ctor_get(x_319, 5);
lean_inc(x_326);
x_327 = lean_ctor_get(x_319, 6);
lean_inc(x_327);
x_328 = lean_ctor_get(x_319, 7);
lean_inc(x_328);
x_329 = lean_ctor_get(x_319, 8);
lean_inc(x_329);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 lean_ctor_release(x_319, 2);
 lean_ctor_release(x_319, 3);
 lean_ctor_release(x_319, 4);
 lean_ctor_release(x_319, 5);
 lean_ctor_release(x_319, 6);
 lean_ctor_release(x_319, 7);
 lean_ctor_release(x_319, 8);
 x_330 = x_319;
} else {
 lean_dec_ref(x_319);
 x_330 = lean_box(0);
}
x_331 = l_Std_PersistentArray_push___rarg(x_322, x_317);
if (lean_is_scalar(x_330)) {
 x_332 = lean_alloc_ctor(0, 9, 0);
} else {
 x_332 = x_330;
}
lean_ctor_set(x_332, 0, x_321);
lean_ctor_set(x_332, 1, x_331);
lean_ctor_set(x_332, 2, x_323);
lean_ctor_set(x_332, 3, x_324);
lean_ctor_set(x_332, 4, x_325);
lean_ctor_set(x_332, 5, x_326);
lean_ctor_set(x_332, 6, x_327);
lean_ctor_set(x_332, 7, x_328);
lean_ctor_set(x_332, 8, x_329);
x_333 = lean_st_ref_set(x_5, x_332, x_320);
x_334 = lean_ctor_get(x_333, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_335 = x_333;
} else {
 lean_dec_ref(x_333);
 x_335 = lean_box(0);
}
x_336 = lean_box(0);
if (lean_is_scalar(x_335)) {
 x_337 = lean_alloc_ctor(0, 2, 0);
} else {
 x_337 = x_335;
}
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_334);
return x_337;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Elab_Command_runLinters___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2(x_7, x_1, x_2, x_3, x_4, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("internal exception: ", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_instInhabitedScope___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2(x_5, x_6, x_7, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_5);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_dec(x_11);
x_12 = l_Lean_Elab_isAbortExceptionId(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Lean_InternalExceptionId_getName(x_10, x_4);
lean_dec(x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
lean_free_object(x_1);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__3;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = 2;
x_22 = l_Lean_log___at_Lean_Elab_Command_runLinters___spec__3(x_20, x_21, x_2, x_3, x_15);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_2, 6);
lean_inc(x_25);
lean_dec(x_2);
x_26 = lean_io_error_to_string(x_24);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_28);
lean_ctor_set(x_1, 0, x_25);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_31 = lean_ctor_get(x_2, 6);
lean_inc(x_31);
lean_dec(x_2);
x_32 = lean_io_error_to_string(x_29);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_free_object(x_1);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_4);
return x_37;
}
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_dec(x_1);
x_39 = l_Lean_Elab_isAbortExceptionId(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = l_Lean_InternalExceptionId_getName(x_38, x_4);
lean_dec(x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_43, 0, x_41);
x_44 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__2;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__3;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = 2;
x_49 = l_Lean_log___at_Lean_Elab_Command_runLinters___spec__3(x_47, x_48, x_2, x_3, x_42);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_3);
x_50 = lean_ctor_get(x_40, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_40, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_52 = x_40;
} else {
 lean_dec_ref(x_40);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_2, 6);
lean_inc(x_53);
lean_dec(x_2);
x_54 = lean_io_error_to_string(x_50);
x_55 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_56);
if (lean_is_scalar(x_52)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_52;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_51);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_38);
lean_dec(x_3);
lean_dec(x_2);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_4);
return x_60;
}
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_5);
x_23 = lean_st_ref_get(x_7, x_8);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_array_uget(x_2, x_4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_27 = lean_apply_4(x_26, x_1, x_6, x_7, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_st_ref_take(x_7, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_24, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_24, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_24, 4);
lean_inc(x_35);
x_36 = lean_ctor_get(x_24, 5);
lean_inc(x_36);
x_37 = lean_ctor_get(x_24, 6);
lean_inc(x_37);
x_38 = lean_ctor_get(x_24, 7);
lean_inc(x_38);
x_39 = lean_ctor_get(x_24, 8);
lean_inc(x_39);
lean_dec(x_24);
x_40 = !lean_is_exclusive(x_30);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_41 = lean_ctor_get(x_30, 8);
lean_dec(x_41);
x_42 = lean_ctor_get(x_30, 7);
lean_dec(x_42);
x_43 = lean_ctor_get(x_30, 6);
lean_dec(x_43);
x_44 = lean_ctor_get(x_30, 5);
lean_dec(x_44);
x_45 = lean_ctor_get(x_30, 4);
lean_dec(x_45);
x_46 = lean_ctor_get(x_30, 3);
lean_dec(x_46);
x_47 = lean_ctor_get(x_30, 2);
lean_dec(x_47);
x_48 = lean_ctor_get(x_30, 0);
lean_dec(x_48);
lean_ctor_set(x_30, 8, x_39);
lean_ctor_set(x_30, 7, x_38);
lean_ctor_set(x_30, 6, x_37);
lean_ctor_set(x_30, 5, x_36);
lean_ctor_set(x_30, 4, x_35);
lean_ctor_set(x_30, 3, x_34);
lean_ctor_set(x_30, 2, x_33);
lean_ctor_set(x_30, 0, x_32);
x_49 = lean_st_ref_set(x_7, x_30, x_31);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
x_52 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4___closed__1;
lean_ctor_set(x_49, 0, x_52);
x_11 = x_49;
goto block_22;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4___closed__1;
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_11 = x_55;
goto block_22;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_30, 1);
lean_inc(x_56);
lean_dec(x_30);
x_57 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_57, 0, x_32);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_33);
lean_ctor_set(x_57, 3, x_34);
lean_ctor_set(x_57, 4, x_35);
lean_ctor_set(x_57, 5, x_36);
lean_ctor_set(x_57, 6, x_37);
lean_ctor_set(x_57, 7, x_38);
lean_ctor_set(x_57, 8, x_39);
x_58 = lean_st_ref_set(x_7, x_57, x_31);
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
x_61 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4___closed__1;
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
x_11 = x_62;
goto block_22;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_27, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_27, 1);
lean_inc(x_64);
lean_dec(x_27);
lean_inc(x_7);
lean_inc(x_6);
x_65 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(x_63, x_6, x_7, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_st_ref_take(x_7, x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_24, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_24, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_24, 3);
lean_inc(x_72);
x_73 = lean_ctor_get(x_24, 4);
lean_inc(x_73);
x_74 = lean_ctor_get(x_24, 5);
lean_inc(x_74);
x_75 = lean_ctor_get(x_24, 6);
lean_inc(x_75);
x_76 = lean_ctor_get(x_24, 7);
lean_inc(x_76);
x_77 = lean_ctor_get(x_24, 8);
lean_inc(x_77);
lean_dec(x_24);
x_78 = !lean_is_exclusive(x_68);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_79 = lean_ctor_get(x_68, 8);
lean_dec(x_79);
x_80 = lean_ctor_get(x_68, 7);
lean_dec(x_80);
x_81 = lean_ctor_get(x_68, 6);
lean_dec(x_81);
x_82 = lean_ctor_get(x_68, 5);
lean_dec(x_82);
x_83 = lean_ctor_get(x_68, 4);
lean_dec(x_83);
x_84 = lean_ctor_get(x_68, 3);
lean_dec(x_84);
x_85 = lean_ctor_get(x_68, 2);
lean_dec(x_85);
x_86 = lean_ctor_get(x_68, 0);
lean_dec(x_86);
lean_ctor_set(x_68, 8, x_77);
lean_ctor_set(x_68, 7, x_76);
lean_ctor_set(x_68, 6, x_75);
lean_ctor_set(x_68, 5, x_74);
lean_ctor_set(x_68, 4, x_73);
lean_ctor_set(x_68, 3, x_72);
lean_ctor_set(x_68, 2, x_71);
lean_ctor_set(x_68, 0, x_70);
x_87 = lean_st_ref_set(x_7, x_68, x_69);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_87, 0);
lean_dec(x_89);
x_90 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4___closed__1;
lean_ctor_set(x_87, 0, x_90);
x_11 = x_87;
goto block_22;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
lean_dec(x_87);
x_92 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4___closed__1;
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_11 = x_93;
goto block_22;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_94 = lean_ctor_get(x_68, 1);
lean_inc(x_94);
lean_dec(x_68);
x_95 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_95, 0, x_70);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_95, 2, x_71);
lean_ctor_set(x_95, 3, x_72);
lean_ctor_set(x_95, 4, x_73);
lean_ctor_set(x_95, 5, x_74);
lean_ctor_set(x_95, 6, x_75);
lean_ctor_set(x_95, 7, x_76);
lean_ctor_set(x_95, 8, x_77);
x_96 = lean_st_ref_set(x_7, x_95, x_69);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_98 = x_96;
} else {
 lean_dec_ref(x_96);
 x_98 = lean_box(0);
}
x_99 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4___closed__1;
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_98;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_97);
x_11 = x_100;
goto block_22;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_101 = lean_ctor_get(x_65, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_65, 1);
lean_inc(x_102);
lean_dec(x_65);
x_103 = lean_st_ref_take(x_7, x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_ctor_get(x_24, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_24, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_24, 3);
lean_inc(x_108);
x_109 = lean_ctor_get(x_24, 4);
lean_inc(x_109);
x_110 = lean_ctor_get(x_24, 5);
lean_inc(x_110);
x_111 = lean_ctor_get(x_24, 6);
lean_inc(x_111);
x_112 = lean_ctor_get(x_24, 7);
lean_inc(x_112);
x_113 = lean_ctor_get(x_24, 8);
lean_inc(x_113);
lean_dec(x_24);
x_114 = !lean_is_exclusive(x_104);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_115 = lean_ctor_get(x_104, 8);
lean_dec(x_115);
x_116 = lean_ctor_get(x_104, 7);
lean_dec(x_116);
x_117 = lean_ctor_get(x_104, 6);
lean_dec(x_117);
x_118 = lean_ctor_get(x_104, 5);
lean_dec(x_118);
x_119 = lean_ctor_get(x_104, 4);
lean_dec(x_119);
x_120 = lean_ctor_get(x_104, 3);
lean_dec(x_120);
x_121 = lean_ctor_get(x_104, 2);
lean_dec(x_121);
x_122 = lean_ctor_get(x_104, 0);
lean_dec(x_122);
lean_ctor_set(x_104, 8, x_113);
lean_ctor_set(x_104, 7, x_112);
lean_ctor_set(x_104, 6, x_111);
lean_ctor_set(x_104, 5, x_110);
lean_ctor_set(x_104, 4, x_109);
lean_ctor_set(x_104, 3, x_108);
lean_ctor_set(x_104, 2, x_107);
lean_ctor_set(x_104, 0, x_106);
x_123 = lean_st_ref_set(x_7, x_104, x_105);
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
lean_object* x_125; 
x_125 = lean_ctor_get(x_123, 0);
lean_dec(x_125);
lean_ctor_set_tag(x_123, 1);
lean_ctor_set(x_123, 0, x_101);
x_11 = x_123;
goto block_22;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_101);
lean_ctor_set(x_127, 1, x_126);
x_11 = x_127;
goto block_22;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_128 = lean_ctor_get(x_104, 1);
lean_inc(x_128);
lean_dec(x_104);
x_129 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_129, 0, x_106);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_129, 2, x_107);
lean_ctor_set(x_129, 3, x_108);
lean_ctor_set(x_129, 4, x_109);
lean_ctor_set(x_129, 5, x_110);
lean_ctor_set(x_129, 6, x_111);
lean_ctor_set(x_129, 7, x_112);
lean_ctor_set(x_129, 8, x_113);
x_130 = lean_st_ref_set(x_7, x_129, x_105);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_132 = x_130;
} else {
 lean_dec_ref(x_130);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_132;
 lean_ctor_set_tag(x_133, 1);
}
lean_ctor_set(x_133, 0, x_101);
lean_ctor_set(x_133, 1, x_131);
x_11 = x_133;
goto block_22;
}
}
}
block_22:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_4, x_15);
x_4 = x_16;
x_5 = x_14;
x_8 = x_13;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_runLinters(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_Elab_Command_addLinter___closed__1;
x_6 = lean_st_ref_get(x_5, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Array_isEmpty___rarg(x_8);
if (x_10 == 0)
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
lean_free_object(x_6);
x_11 = lean_array_get_size(x_8);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = lean_box(0);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4(x_1, x_8, x_12, x_13, x_14, x_2, x_3, x_9);
lean_dec(x_8);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
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
lean_object* x_24; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_box(0);
lean_ctor_set(x_6, 0, x_24);
return x_6;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_6, 0);
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_6);
x_27 = l_Array_isEmpty___rarg(x_25);
if (x_27 == 0)
{
lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_array_get_size(x_25);
x_29 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_30 = 0;
x_31 = lean_box(0);
x_32 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4(x_1, x_25, x_29, x_30, x_31, x_2, x_3, x_26);
lean_dec(x_25);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_38 = x_32;
} else {
 lean_dec_ref(x_32);
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
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_26);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Elab_Command_runLinters___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_log___at_Lean_Elab_Command_runLinters___spec__3(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getCurrMacroScope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_getCurrMacroScope(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getMainModule___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getMainModule(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getMainModule___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getMainModule___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_getMainModule___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getMainModule___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_getMainModule(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withFreshMacroScope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_ctor_get(x_2, 3);
x_21 = lean_ctor_get(x_2, 4);
x_22 = lean_ctor_get(x_2, 6);
x_23 = lean_ctor_get(x_2, 7);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_20);
lean_ctor_set(x_24, 4, x_21);
lean_ctor_set(x_24, 5, x_9);
lean_ctor_set(x_24, 6, x_22);
lean_ctor_set(x_24, 7, x_23);
x_25 = lean_apply_3(x_1, x_24, x_3, x_13);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_26 = lean_ctor_get(x_6, 0);
x_27 = lean_ctor_get(x_6, 1);
x_28 = lean_ctor_get(x_6, 2);
x_29 = lean_ctor_get(x_6, 3);
x_30 = lean_ctor_get(x_6, 4);
x_31 = lean_ctor_get(x_6, 5);
x_32 = lean_ctor_get(x_6, 6);
x_33 = lean_ctor_get(x_6, 7);
x_34 = lean_ctor_get(x_6, 8);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_6);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_29, x_35);
x_37 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_37, 0, x_26);
lean_ctor_set(x_37, 1, x_27);
lean_ctor_set(x_37, 2, x_28);
lean_ctor_set(x_37, 3, x_36);
lean_ctor_set(x_37, 4, x_30);
lean_ctor_set(x_37, 5, x_31);
lean_ctor_set(x_37, 6, x_32);
lean_ctor_set(x_37, 7, x_33);
lean_ctor_set(x_37, 8, x_34);
x_38 = lean_st_ref_set(x_3, x_37, x_7);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get(x_2, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_2, 4);
lean_inc(x_44);
x_45 = lean_ctor_get(x_2, 6);
lean_inc(x_45);
x_46 = lean_ctor_get(x_2, 7);
lean_inc(x_46);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 lean_ctor_release(x_2, 7);
 x_47 = x_2;
} else {
 lean_dec_ref(x_2);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 8, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_40);
lean_ctor_set(x_48, 1, x_41);
lean_ctor_set(x_48, 2, x_42);
lean_ctor_set(x_48, 3, x_43);
lean_ctor_set(x_48, 4, x_44);
lean_ctor_set(x_48, 5, x_29);
lean_ctor_set(x_48, 6, x_45);
lean_ctor_set(x_48, 7, x_46);
x_49 = lean_apply_3(x_1, x_48, x_3, x_39);
return x_49;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withFreshMacroScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withFreshMacroScope___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadQuotationCommandElabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_withFreshMacroScope___rarg(x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getCurrMacroScope___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getMainModule___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadQuotationCommandElabM___lambda__1), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_instMonadRefCommandElabM;
x_2 = l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__1;
x_3 = l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__2;
x_4 = l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadQuotationCommandElabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__2;
x_2 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Command", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__4;
x_2 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("commandElabAttribute", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__6;
x_2 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("builtinCommandElab", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("commandElab", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__2;
x_2 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__14;
x_2 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CommandElab", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__6;
x_2 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__16;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("command", 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__8;
x_3 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__10;
x_4 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__12;
x_5 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__15;
x_6 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__17;
x_7 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__18;
x_8 = l_Lean_Elab_mkElabAttribute___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1748_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkInfoTree(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 6);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_Elab_Command_instInhabitedScope;
x_14 = l_List_head_x21___rarg(x_13, x_11);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_14, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_14, 3);
lean_inc(x_21);
lean_dec(x_14);
x_22 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___closed__1;
lean_inc(x_18);
x_23 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 4, x_20);
lean_ctor_set(x_23, 5, x_21);
lean_ctor_set(x_23, 6, x_12);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
lean_ctor_set(x_7, 0, x_24);
return x_7;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_7);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 6);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l_Lean_Elab_Command_instInhabitedScope;
x_31 = l_List_head_x21___rarg(x_30, x_28);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_2);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_3);
x_35 = lean_ctor_get(x_4, 1);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_31, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_31, 3);
lean_inc(x_38);
lean_dec(x_31);
x_39 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___closed__1;
lean_inc(x_35);
x_40 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_40, 0, x_27);
lean_ctor_set(x_40, 1, x_35);
lean_ctor_set(x_40, 2, x_39);
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 4, x_37);
lean_ctor_set(x_40, 5, x_38);
lean_ctor_set(x_40, 6, x_29);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_34);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_26);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkInfoTree___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkInfoTree(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_11, x_8, x_2, x_3, x_12);
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
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 7);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_st_ref_take(x_1, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 7);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_9, 7);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_10, 1);
lean_dec(x_15);
x_16 = l_Lean_Elab_Command_State_messages___default___closed__3;
lean_ctor_set(x_10, 1, x_16);
x_17 = lean_st_ref_set(x_1, x_9, x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_7);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get_uint8(x_10, sizeof(void*)*2);
x_23 = lean_ctor_get(x_10, 0);
lean_inc(x_23);
lean_dec(x_10);
x_24 = l_Lean_Elab_Command_State_messages___default___closed__3;
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_22);
lean_ctor_set(x_9, 7, x_25);
x_26 = lean_st_ref_set(x_1, x_9, x_11);
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
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_30 = lean_ctor_get(x_9, 0);
x_31 = lean_ctor_get(x_9, 1);
x_32 = lean_ctor_get(x_9, 2);
x_33 = lean_ctor_get(x_9, 3);
x_34 = lean_ctor_get(x_9, 4);
x_35 = lean_ctor_get(x_9, 5);
x_36 = lean_ctor_get(x_9, 6);
x_37 = lean_ctor_get(x_9, 8);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_9);
x_38 = lean_ctor_get_uint8(x_10, sizeof(void*)*2);
x_39 = lean_ctor_get(x_10, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_40 = x_10;
} else {
 lean_dec_ref(x_10);
 x_40 = lean_box(0);
}
x_41 = l_Lean_Elab_Command_State_messages___default___closed__3;
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 1);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_38);
x_43 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_43, 0, x_30);
lean_ctor_set(x_43, 1, x_31);
lean_ctor_set(x_43, 2, x_32);
lean_ctor_set(x_43, 3, x_33);
lean_ctor_set(x_43, 4, x_34);
lean_ctor_set(x_43, 5, x_35);
lean_ctor_set(x_43, 6, x_36);
lean_ctor_set(x_43, 7, x_42);
lean_ctor_set(x_43, 8, x_37);
x_44 = lean_st_ref_set(x_1, x_43, x_11);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_7);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__3___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 7);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_apply_3(x_1, x_3, x_4, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = l_Lean_Elab_getResetInfoTrees___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__3___rarg(x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_4);
lean_inc(x_3);
x_16 = lean_apply_3(x_1, x_3, x_4, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_4, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 7);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
lean_inc(x_4);
x_24 = lean_apply_4(x_2, x_23, x_3, x_4, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_st_ref_take(x_4, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 7);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_28, 7);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_29, 1);
lean_dec(x_34);
x_35 = l_Std_PersistentArray_push___rarg(x_14, x_25);
lean_ctor_set(x_29, 1, x_35);
x_36 = lean_st_ref_set(x_4, x_28, x_30);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_17);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_17);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_ctor_get_uint8(x_29, sizeof(void*)*2);
x_42 = lean_ctor_get(x_29, 0);
lean_inc(x_42);
lean_dec(x_29);
x_43 = l_Std_PersistentArray_push___rarg(x_14, x_25);
x_44 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_41);
lean_ctor_set(x_28, 7, x_44);
x_45 = lean_st_ref_set(x_4, x_28, x_30);
lean_dec(x_4);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_17);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_49 = lean_ctor_get(x_28, 0);
x_50 = lean_ctor_get(x_28, 1);
x_51 = lean_ctor_get(x_28, 2);
x_52 = lean_ctor_get(x_28, 3);
x_53 = lean_ctor_get(x_28, 4);
x_54 = lean_ctor_get(x_28, 5);
x_55 = lean_ctor_get(x_28, 6);
x_56 = lean_ctor_get(x_28, 8);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_28);
x_57 = lean_ctor_get_uint8(x_29, sizeof(void*)*2);
x_58 = lean_ctor_get(x_29, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_59 = x_29;
} else {
 lean_dec_ref(x_29);
 x_59 = lean_box(0);
}
x_60 = l_Std_PersistentArray_push___rarg(x_14, x_25);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 1);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*2, x_57);
x_62 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_62, 0, x_49);
lean_ctor_set(x_62, 1, x_50);
lean_ctor_set(x_62, 2, x_51);
lean_ctor_set(x_62, 3, x_52);
lean_ctor_set(x_62, 4, x_53);
lean_ctor_set(x_62, 5, x_54);
lean_ctor_set(x_62, 6, x_55);
lean_ctor_set(x_62, 7, x_61);
lean_ctor_set(x_62, 8, x_56);
x_63 = lean_st_ref_set(x_4, x_62, x_30);
lean_dec(x_4);
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
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_17);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_4);
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
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_16, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_16, 1);
lean_inc(x_72);
lean_dec(x_16);
x_73 = lean_st_ref_get(x_4, x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_ctor_get(x_74, 7);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
lean_inc(x_4);
x_78 = lean_apply_4(x_2, x_77, x_3, x_4, x_75);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_st_ref_take(x_4, x_80);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_82, 7);
lean_inc(x_83);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = !lean_is_exclusive(x_82);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_82, 7);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_83);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_88 = lean_ctor_get(x_83, 1);
lean_dec(x_88);
x_89 = l_Std_PersistentArray_push___rarg(x_14, x_79);
lean_ctor_set(x_83, 1, x_89);
x_90 = lean_st_ref_set(x_4, x_82, x_84);
lean_dec(x_4);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_90, 0);
lean_dec(x_92);
lean_ctor_set_tag(x_90, 1);
lean_ctor_set(x_90, 0, x_71);
return x_90;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_71);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
else
{
uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_95 = lean_ctor_get_uint8(x_83, sizeof(void*)*2);
x_96 = lean_ctor_get(x_83, 0);
lean_inc(x_96);
lean_dec(x_83);
x_97 = l_Std_PersistentArray_push___rarg(x_14, x_79);
x_98 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set_uint8(x_98, sizeof(void*)*2, x_95);
lean_ctor_set(x_82, 7, x_98);
x_99 = lean_st_ref_set(x_4, x_82, x_84);
lean_dec(x_4);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_101 = x_99;
} else {
 lean_dec_ref(x_99);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
 lean_ctor_set_tag(x_102, 1);
}
lean_ctor_set(x_102, 0, x_71);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_103 = lean_ctor_get(x_82, 0);
x_104 = lean_ctor_get(x_82, 1);
x_105 = lean_ctor_get(x_82, 2);
x_106 = lean_ctor_get(x_82, 3);
x_107 = lean_ctor_get(x_82, 4);
x_108 = lean_ctor_get(x_82, 5);
x_109 = lean_ctor_get(x_82, 6);
x_110 = lean_ctor_get(x_82, 8);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_82);
x_111 = lean_ctor_get_uint8(x_83, sizeof(void*)*2);
x_112 = lean_ctor_get(x_83, 0);
lean_inc(x_112);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_113 = x_83;
} else {
 lean_dec_ref(x_83);
 x_113 = lean_box(0);
}
x_114 = l_Std_PersistentArray_push___rarg(x_14, x_79);
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 2, 1);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set_uint8(x_115, sizeof(void*)*2, x_111);
x_116 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_116, 0, x_103);
lean_ctor_set(x_116, 1, x_104);
lean_ctor_set(x_116, 2, x_105);
lean_ctor_set(x_116, 3, x_106);
lean_ctor_set(x_116, 4, x_107);
lean_ctor_set(x_116, 5, x_108);
lean_ctor_set(x_116, 6, x_109);
lean_ctor_set(x_116, 7, x_115);
lean_ctor_set(x_116, 8, x_110);
x_117 = lean_st_ref_set(x_4, x_116, x_84);
lean_dec(x_4);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
 lean_ctor_set_tag(x_120, 1);
}
lean_ctor_set(x_120, 0, x_71);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
uint8_t x_121; 
lean_dec(x_71);
lean_dec(x_14);
lean_dec(x_4);
x_121 = !lean_is_exclusive(x_78);
if (x_121 == 0)
{
return x_78;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_78, 0);
x_123 = lean_ctor_get(x_78, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_78);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected syntax", 17);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("no_elab", 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
lean_inc(x_2);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = l_Lean_indentD(x_7);
x_9 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__2;
x_10 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__3;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1___boxed), 4, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__4;
x_15 = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkInfoTree___boxed), 6, 2);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_2);
x_16 = l_Lean_Elab_withInfoTreeContext___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__2(x_13, x_15, x_4, x_5, x_6);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_inc(x_2);
x_20 = lean_apply_1(x_19, x_2);
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
lean_inc(x_2);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkInfoTree___boxed), 6, 2);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_2);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Elab_withInfoTreeContext___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__2(x_20, x_23, x_4, x_5, x_6);
if (lean_obj_tag(x_24) == 0)
{
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_24;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_24, 1);
x_32 = lean_ctor_get(x_24, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
x_34 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__5;
x_35 = lean_nat_dec_eq(x_34, x_33);
lean_dec(x_33);
if (x_35 == 0)
{
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_24;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_free_object(x_24);
lean_dec(x_25);
lean_inc(x_1);
x_36 = lean_st_ref_set(x_5, x_1, x_31);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_3 = x_18;
x_6 = x_37;
goto _start;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_dec(x_24);
x_40 = lean_ctor_get(x_25, 0);
lean_inc(x_40);
x_41 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__5;
x_42 = lean_nat_dec_eq(x_41, x_40);
lean_dec(x_40);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_25);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_25);
lean_inc(x_1);
x_44 = lean_st_ref_set(x_5, x_1, x_39);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_3 = x_18;
x_6 = x_45;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_getResetInfoTrees___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__3___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_getResetInfoTrees___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__3(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Command_withMacroExpansion___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 7);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_apply_3(x_1, x_3, x_4, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = l_Lean_Elab_getResetInfoTrees___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__3___rarg(x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_4);
lean_inc(x_3);
x_16 = lean_apply_3(x_1, x_3, x_4, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_4, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 7);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
lean_inc(x_4);
x_24 = lean_apply_4(x_2, x_23, x_3, x_4, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_st_ref_take(x_4, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 7);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_28, 7);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_29, 1);
lean_dec(x_34);
x_35 = l_Std_PersistentArray_push___rarg(x_14, x_25);
lean_ctor_set(x_29, 1, x_35);
x_36 = lean_st_ref_set(x_4, x_28, x_30);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_17);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_17);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_ctor_get_uint8(x_29, sizeof(void*)*2);
x_42 = lean_ctor_get(x_29, 0);
lean_inc(x_42);
lean_dec(x_29);
x_43 = l_Std_PersistentArray_push___rarg(x_14, x_25);
x_44 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_41);
lean_ctor_set(x_28, 7, x_44);
x_45 = lean_st_ref_set(x_4, x_28, x_30);
lean_dec(x_4);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_17);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_49 = lean_ctor_get(x_28, 0);
x_50 = lean_ctor_get(x_28, 1);
x_51 = lean_ctor_get(x_28, 2);
x_52 = lean_ctor_get(x_28, 3);
x_53 = lean_ctor_get(x_28, 4);
x_54 = lean_ctor_get(x_28, 5);
x_55 = lean_ctor_get(x_28, 6);
x_56 = lean_ctor_get(x_28, 8);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_28);
x_57 = lean_ctor_get_uint8(x_29, sizeof(void*)*2);
x_58 = lean_ctor_get(x_29, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_59 = x_29;
} else {
 lean_dec_ref(x_29);
 x_59 = lean_box(0);
}
x_60 = l_Std_PersistentArray_push___rarg(x_14, x_25);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 1);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*2, x_57);
x_62 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_62, 0, x_49);
lean_ctor_set(x_62, 1, x_50);
lean_ctor_set(x_62, 2, x_51);
lean_ctor_set(x_62, 3, x_52);
lean_ctor_set(x_62, 4, x_53);
lean_ctor_set(x_62, 5, x_54);
lean_ctor_set(x_62, 6, x_55);
lean_ctor_set(x_62, 7, x_61);
lean_ctor_set(x_62, 8, x_56);
x_63 = lean_st_ref_set(x_4, x_62, x_30);
lean_dec(x_4);
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
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_17);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_4);
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
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_16, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_16, 1);
lean_inc(x_72);
lean_dec(x_16);
x_73 = lean_st_ref_get(x_4, x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_ctor_get(x_74, 7);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
lean_inc(x_4);
x_78 = lean_apply_4(x_2, x_77, x_3, x_4, x_75);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_st_ref_take(x_4, x_80);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_82, 7);
lean_inc(x_83);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = !lean_is_exclusive(x_82);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_82, 7);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_83);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_88 = lean_ctor_get(x_83, 1);
lean_dec(x_88);
x_89 = l_Std_PersistentArray_push___rarg(x_14, x_79);
lean_ctor_set(x_83, 1, x_89);
x_90 = lean_st_ref_set(x_4, x_82, x_84);
lean_dec(x_4);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_90, 0);
lean_dec(x_92);
lean_ctor_set_tag(x_90, 1);
lean_ctor_set(x_90, 0, x_71);
return x_90;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_71);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
else
{
uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_95 = lean_ctor_get_uint8(x_83, sizeof(void*)*2);
x_96 = lean_ctor_get(x_83, 0);
lean_inc(x_96);
lean_dec(x_83);
x_97 = l_Std_PersistentArray_push___rarg(x_14, x_79);
x_98 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set_uint8(x_98, sizeof(void*)*2, x_95);
lean_ctor_set(x_82, 7, x_98);
x_99 = lean_st_ref_set(x_4, x_82, x_84);
lean_dec(x_4);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_101 = x_99;
} else {
 lean_dec_ref(x_99);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
 lean_ctor_set_tag(x_102, 1);
}
lean_ctor_set(x_102, 0, x_71);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_103 = lean_ctor_get(x_82, 0);
x_104 = lean_ctor_get(x_82, 1);
x_105 = lean_ctor_get(x_82, 2);
x_106 = lean_ctor_get(x_82, 3);
x_107 = lean_ctor_get(x_82, 4);
x_108 = lean_ctor_get(x_82, 5);
x_109 = lean_ctor_get(x_82, 6);
x_110 = lean_ctor_get(x_82, 8);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_82);
x_111 = lean_ctor_get_uint8(x_83, sizeof(void*)*2);
x_112 = lean_ctor_get(x_83, 0);
lean_inc(x_112);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_113 = x_83;
} else {
 lean_dec_ref(x_83);
 x_113 = lean_box(0);
}
x_114 = l_Std_PersistentArray_push___rarg(x_14, x_79);
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 2, 1);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set_uint8(x_115, sizeof(void*)*2, x_111);
x_116 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_116, 0, x_103);
lean_ctor_set(x_116, 1, x_104);
lean_ctor_set(x_116, 2, x_105);
lean_ctor_set(x_116, 3, x_106);
lean_ctor_set(x_116, 4, x_107);
lean_ctor_set(x_116, 5, x_108);
lean_ctor_set(x_116, 6, x_109);
lean_ctor_set(x_116, 7, x_115);
lean_ctor_set(x_116, 8, x_110);
x_117 = lean_st_ref_set(x_4, x_116, x_84);
lean_dec(x_4);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
 lean_ctor_set_tag(x_120, 1);
}
lean_ctor_set(x_120, 0, x_71);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
uint8_t x_121; 
lean_dec(x_71);
lean_dec(x_14);
lean_dec(x_4);
x_121 = !lean_is_exclusive(x_78);
if (x_121 == 0)
{
return x_78;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_78, 0);
x_123 = lean_ctor_get(x_78, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_78);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Command_withMacroExpansion___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Command_withMacroExpansion___spec__1___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withMacroExpansion___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_ctor_get(x_4, 2);
x_15 = lean_ctor_get(x_4, 3);
x_16 = lean_ctor_get(x_4, 4);
x_17 = lean_ctor_get(x_4, 5);
x_18 = lean_ctor_get(x_4, 6);
x_19 = lean_ctor_get(x_4, 7);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_2);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
x_22 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_13);
lean_ctor_set(x_22, 2, x_14);
lean_ctor_set(x_22, 3, x_15);
lean_ctor_set(x_22, 4, x_21);
lean_ctor_set(x_22, 5, x_17);
lean_ctor_set(x_22, 6, x_18);
lean_ctor_set(x_22, 7, x_19);
x_23 = lean_apply_3(x_3, x_22, x_5, x_6);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withMacroExpansion___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withMacroExpansion___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withMacroExpansion___rarg___lambda__1), 6, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_3);
x_8 = l_Lean_LocalContext_empty;
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 2, x_2);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withMacroExpansion___rarg___lambda__2___boxed), 5, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Command_withMacroExpansion___spec__1___rarg(x_7, x_11, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withMacroExpansion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withMacroExpansion___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withMacroExpansion___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_withMacroExpansion___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_ctor_get(x_8, 3);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_ctor_get(x_6, 2);
x_20 = lean_ctor_get(x_6, 4);
x_21 = lean_ctor_get(x_6, 5);
x_22 = lean_ctor_get(x_6, 6);
x_23 = lean_ctor_get(x_6, 7);
x_24 = lean_ctor_get(x_6, 8);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_25 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_25, 2, x_19);
lean_ctor_set(x_25, 3, x_1);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_25, 5, x_21);
lean_ctor_set(x_25, 6, x_22);
lean_ctor_set(x_25, 7, x_23);
lean_ctor_set(x_25, 8, x_24);
x_26 = lean_st_ref_set(x_3, x_25, x_7);
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
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__1;
x_2 = l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__1;
x_3 = l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 3);
x_13 = lean_ctor_get(x_4, 4);
x_14 = lean_ctor_get(x_4, 5);
x_15 = lean_ctor_get(x_4, 6);
x_16 = lean_ctor_get(x_4, 7);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_17 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_2);
lean_ctor_set(x_17, 3, x_12);
lean_ctor_set(x_17, 4, x_13);
lean_ctor_set(x_17, 5, x_14);
lean_ctor_set(x_17, 6, x_15);
lean_ctor_set(x_17, 7, x_16);
x_18 = lean_apply_3(x_3, x_17, x_5, x_6);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_ctor_get(x_8, 4);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__1), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__2___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__3___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__1;
x_2 = l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__2;
x_3 = l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadRecDepthCommandElabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("showPartialSyntaxErrors", 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("show elaboration errors from partial syntax trees (i.e. after parser recovery)", 78);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Elab_Command_instInhabitedScope___closed__1;
x_3 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123____closed__2;
x_3 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123____closed__4;
x_4 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_withLogging___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("internal exception ", 19);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withLogging(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(x_6, x_2, x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_5, 1);
x_11 = lean_ctor_get(x_5, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
lean_dec(x_14);
x_15 = l_Lean_Elab_isAbortExceptionId(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_free_object(x_5);
x_16 = l_Lean_InternalExceptionId_getName(x_13, x_10);
lean_dec(x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
lean_free_object(x_6);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_19, 0, x_17);
x_20 = l_Lean_Elab_Command_withLogging___closed__2;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__3;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = 2;
x_25 = l_Lean_log___at_Lean_Elab_Command_runLinters___spec__3(x_23, x_24, x_2, x_3, x_18);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_2, 6);
lean_inc(x_28);
lean_dec(x_2);
x_29 = lean_io_error_to_string(x_27);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_31);
lean_ctor_set(x_6, 0, x_28);
lean_ctor_set(x_16, 0, x_6);
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_34 = lean_ctor_get(x_2, 6);
lean_inc(x_34);
lean_dec(x_2);
x_35 = lean_io_error_to_string(x_32);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_37);
lean_ctor_set(x_6, 0, x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_6);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
}
else
{
lean_object* x_39; 
lean_free_object(x_6);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_box(0);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_39);
return x_5;
}
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_6, 0);
lean_inc(x_40);
lean_dec(x_6);
x_41 = l_Lean_Elab_isAbortExceptionId(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_free_object(x_5);
x_42 = l_Lean_InternalExceptionId_getName(x_40, x_10);
lean_dec(x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_45, 0, x_43);
x_46 = l_Lean_Elab_Command_withLogging___closed__2;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__3;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = 2;
x_51 = l_Lean_log___at_Lean_Elab_Command_runLinters___spec__3(x_49, x_50, x_2, x_3, x_44);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_3);
x_52 = lean_ctor_get(x_42, 0);
lean_inc(x_52);
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
x_55 = lean_ctor_get(x_2, 6);
lean_inc(x_55);
lean_dec(x_2);
x_56 = lean_io_error_to_string(x_52);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_58);
if (lean_is_scalar(x_54)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_54;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_53);
return x_60;
}
}
else
{
lean_object* x_61; 
lean_dec(x_40);
lean_dec(x_3);
lean_dec(x_2);
x_61 = lean_box(0);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_61);
return x_5;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_ctor_get(x_5, 1);
lean_inc(x_62);
lean_dec(x_5);
x_63 = lean_ctor_get(x_6, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_64 = x_6;
} else {
 lean_dec_ref(x_6);
 x_64 = lean_box(0);
}
x_65 = l_Lean_Elab_isAbortExceptionId(x_63);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = l_Lean_InternalExceptionId_getName(x_63, x_62);
lean_dec(x_63);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; 
lean_dec(x_64);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_69, 0, x_67);
x_70 = l_Lean_Elab_Command_withLogging___closed__2;
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__3;
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = 2;
x_75 = l_Lean_log___at_Lean_Elab_Command_runLinters___spec__3(x_73, x_74, x_2, x_3, x_68);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_3);
x_76 = lean_ctor_get(x_66, 0);
lean_inc(x_76);
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
x_79 = lean_ctor_get(x_2, 6);
lean_inc(x_79);
lean_dec(x_2);
x_80 = lean_io_error_to_string(x_76);
x_81 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
if (lean_is_scalar(x_64)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_64;
 lean_ctor_set_tag(x_83, 0);
}
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_82);
if (lean_is_scalar(x_78)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_78;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_77);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_3);
lean_dec(x_2);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_62);
return x_86;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2240____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2240____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2240____closed__1;
x_2 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__18;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2240_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2240____closed__2;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__1___closed__2;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Command_elabCommand___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Elab_Command_instInhabitedScope;
x_10 = l_List_head_x21___rarg(x_9, x_8);
lean_dec(x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_checkTraceOption(x_11, x_1);
lean_dec(x_11);
x_13 = lean_box(x_12);
lean_ctor_set(x_5, 0, x_13);
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_ctor_get(x_14, 2);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Command_instInhabitedScope;
x_18 = l_List_head_x21___rarg(x_17, x_16);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_checkTraceOption(x_19, x_1);
lean_dec(x_19);
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
return x_22;
}
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_traceMsg", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("] ", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_2, x_3, x_4, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Util_Trace_0__Lean_addTraceOptions(x_10);
x_13 = lean_st_ref_take(x_4, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 8);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_14, 8);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__2;
x_22 = l_Lean_Name_append(x_1, x_21);
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_1);
x_24 = l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__4;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__6;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_12);
x_29 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__3;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_7);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Std_PersistentArray_push___rarg(x_20, x_32);
lean_ctor_set(x_15, 0, x_33);
x_34 = lean_st_ref_set(x_4, x_14, x_16);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_41 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
x_42 = lean_ctor_get(x_15, 0);
lean_inc(x_42);
lean_dec(x_15);
x_43 = l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__2;
x_44 = l_Lean_Name_append(x_1, x_43);
x_45 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_45, 0, x_1);
x_46 = l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__4;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__6;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_12);
x_51 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__3;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_7);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Std_PersistentArray_push___rarg(x_42, x_54);
x_56 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_41);
lean_ctor_set(x_14, 8, x_56);
x_57 = lean_st_ref_set(x_4, x_14, x_16);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = lean_box(0);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_62 = lean_ctor_get(x_14, 0);
x_63 = lean_ctor_get(x_14, 1);
x_64 = lean_ctor_get(x_14, 2);
x_65 = lean_ctor_get(x_14, 3);
x_66 = lean_ctor_get(x_14, 4);
x_67 = lean_ctor_get(x_14, 5);
x_68 = lean_ctor_get(x_14, 6);
x_69 = lean_ctor_get(x_14, 7);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_14);
x_70 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
x_71 = lean_ctor_get(x_15, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_72 = x_15;
} else {
 lean_dec_ref(x_15);
 x_72 = lean_box(0);
}
x_73 = l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__2;
x_74 = l_Lean_Name_append(x_1, x_73);
x_75 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_75, 0, x_1);
x_76 = l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__4;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__6;
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_12);
x_81 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__3;
x_82 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_83, 0, x_74);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_7);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Std_PersistentArray_push___rarg(x_71, x_84);
if (lean_is_scalar(x_72)) {
 x_86 = lean_alloc_ctor(0, 1, 1);
} else {
 x_86 = x_72;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_70);
x_87 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_87, 0, x_62);
lean_ctor_set(x_87, 1, x_63);
lean_ctor_set(x_87, 2, x_64);
lean_ctor_set(x_87, 3, x_65);
lean_ctor_set(x_87, 4, x_66);
lean_ctor_set(x_87, 5, x_67);
lean_ctor_set(x_87, 6, x_68);
lean_ctor_set(x_87, 7, x_69);
lean_ctor_set(x_87, 8, x_86);
x_88 = lean_st_ref_set(x_4, x_87, x_16);
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
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Command_elabCommand___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_st_ref_get(x_3, x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 8);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*1);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_1 = x_8;
x_4 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
lean_inc(x_9);
x_18 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Command_elabCommand___spec__3(x_9, x_2, x_3, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_9);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_1 = x_8;
x_4 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_10);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4(x_9, x_25, x_2, x_3, x_23);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_1 = x_8;
x_4 = x_27;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_11, x_8, x_2, x_3, x_12);
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 6);
lean_dec(x_11);
lean_ctor_set(x_3, 6, x_9);
x_12 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7(x_2, x_3, x_4, x_8);
lean_dec(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
x_19 = lean_ctor_get(x_3, 7);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_20 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_16);
lean_ctor_set(x_20, 4, x_17);
lean_ctor_set(x_20, 5, x_18);
lean_ctor_set(x_20, 6, x_9);
lean_ctor_set(x_20, 7, x_19);
x_21 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7(x_2, x_20, x_4, x_8);
lean_dec(x_4);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__1___closed__2;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_expandMacroImpl_x3f(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_free_object(x_6);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_15, x_3, x_16);
lean_dec(x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_20, x_3, x_16);
lean_dec(x_20);
return x_21;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_15, 0, x_6);
x_25 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_15, x_3, x_22);
lean_dec(x_15);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
lean_ctor_set(x_6, 0, x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_6);
x_28 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_27, x_3, x_22);
lean_dec(x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_6, 0);
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_dec(x_5);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
x_35 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_34, x_3, x_31);
lean_dec(x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
lean_dec(x_5);
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(1, 1, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
x_41 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_40, x_3, x_36);
lean_dec(x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Environment_contains(x_1, x_2);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveNamespace(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveGlobalName(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
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
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Command_getScope___rarg(x_3, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 3);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_8);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__1___boxed), 4, 1);
lean_closure_set(x_17, 0, x_8);
lean_inc(x_12);
x_18 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__2___rarg___boxed), 3, 1);
lean_closure_set(x_18, 0, x_12);
lean_inc(x_8);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__2___boxed), 4, 1);
lean_closure_set(x_19, 0, x_8);
lean_inc(x_16);
lean_inc(x_12);
lean_inc(x_8);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__3___boxed), 6, 3);
lean_closure_set(x_20, 0, x_8);
lean_closure_set(x_20, 1, x_12);
lean_closure_set(x_20, 2, x_16);
lean_inc(x_8);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__4___boxed), 6, 3);
lean_closure_set(x_21, 0, x_8);
lean_closure_set(x_21, 1, x_12);
lean_closure_set(x_21, 2, x_16);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_20);
lean_ctor_set(x_22, 4, x_21);
x_23 = l_Lean_Elab_Command_getRef(x_2, x_3, x_15);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_Command_getCurrMacroScope(x_2, x_3, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_2, 2);
lean_inc(x_29);
x_30 = lean_st_ref_get(x_3, x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 4);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_st_ref_get(x_3, x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 3);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_environment_main_module(x_8);
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_27);
lean_ctor_set(x_39, 3, x_29);
lean_ctor_set(x_39, 4, x_33);
lean_ctor_set(x_39, 5, x_24);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_apply_2(x_1, x_39, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_st_ref_take(x_3, x_36);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_50 = lean_ctor_get(x_47, 3);
lean_dec(x_50);
lean_ctor_set(x_47, 3, x_45);
x_51 = lean_st_ref_set(x_3, x_47, x_48);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_ctor_get(x_44, 1);
lean_inc(x_53);
lean_dec(x_44);
x_54 = l_List_reverse___rarg(x_53);
x_55 = l_List_forM___at_Lean_Elab_Command_elabCommand___spec__5(x_54, x_2, x_3, x_52);
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
lean_ctor_set(x_55, 0, x_43);
return x_55;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_43);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_60 = lean_ctor_get(x_47, 0);
x_61 = lean_ctor_get(x_47, 1);
x_62 = lean_ctor_get(x_47, 2);
x_63 = lean_ctor_get(x_47, 4);
x_64 = lean_ctor_get(x_47, 5);
x_65 = lean_ctor_get(x_47, 6);
x_66 = lean_ctor_get(x_47, 7);
x_67 = lean_ctor_get(x_47, 8);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_47);
x_68 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_68, 0, x_60);
lean_ctor_set(x_68, 1, x_61);
lean_ctor_set(x_68, 2, x_62);
lean_ctor_set(x_68, 3, x_45);
lean_ctor_set(x_68, 4, x_63);
lean_ctor_set(x_68, 5, x_64);
lean_ctor_set(x_68, 6, x_65);
lean_ctor_set(x_68, 7, x_66);
lean_ctor_set(x_68, 8, x_67);
x_69 = lean_st_ref_set(x_3, x_68, x_48);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_ctor_get(x_44, 1);
lean_inc(x_71);
lean_dec(x_44);
x_72 = l_List_reverse___rarg(x_71);
x_73 = l_List_forM___at_Lean_Elab_Command_elabCommand___spec__5(x_72, x_2, x_3, x_70);
lean_dec(x_3);
lean_dec(x_2);
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
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_43);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_42, 0);
lean_inc(x_77);
lean_dec(x_42);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_maxRecDepthErrorMessage;
x_81 = lean_string_dec_eq(x_79, x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_82, 0, x_79);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__6(x_78, x_83, x_2, x_3, x_36);
return x_84;
}
else
{
lean_object* x_85; 
lean_dec(x_79);
x_85 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__8(x_78, x_2, x_3, x_36);
lean_dec(x_3);
lean_dec(x_2);
return x_85;
}
}
else
{
lean_object* x_86; 
lean_dec(x_3);
lean_dec(x_2);
x_86 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___rarg(x_36);
return x_86;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_11, x_8, x_2, x_3, x_12);
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 6);
lean_dec(x_11);
lean_ctor_set(x_3, 6, x_9);
x_12 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__12(x_2, x_3, x_4, x_8);
lean_dec(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
x_19 = lean_ctor_get(x_3, 7);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_20 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_16);
lean_ctor_set(x_20, 4, x_17);
lean_ctor_set(x_20, 5, x_18);
lean_ctor_set(x_20, 6, x_9);
lean_ctor_set(x_20, 7, x_19);
x_21 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__12(x_2, x_20, x_4, x_8);
lean_dec(x_4);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__1___closed__2;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
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
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Command_getScope___rarg(x_3, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 3);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_8);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__1___boxed), 4, 1);
lean_closure_set(x_17, 0, x_8);
lean_inc(x_12);
x_18 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__2___rarg___boxed), 3, 1);
lean_closure_set(x_18, 0, x_12);
lean_inc(x_8);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__2___boxed), 4, 1);
lean_closure_set(x_19, 0, x_8);
lean_inc(x_16);
lean_inc(x_12);
lean_inc(x_8);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__3___boxed), 6, 3);
lean_closure_set(x_20, 0, x_8);
lean_closure_set(x_20, 1, x_12);
lean_closure_set(x_20, 2, x_16);
lean_inc(x_8);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__4___boxed), 6, 3);
lean_closure_set(x_21, 0, x_8);
lean_closure_set(x_21, 1, x_12);
lean_closure_set(x_21, 2, x_16);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_20);
lean_ctor_set(x_22, 4, x_21);
x_23 = l_Lean_Elab_Command_getRef(x_2, x_3, x_15);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_Command_getCurrMacroScope(x_2, x_3, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_2, 2);
lean_inc(x_29);
x_30 = lean_st_ref_get(x_3, x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 4);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_st_ref_get(x_3, x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 3);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_environment_main_module(x_8);
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_27);
lean_ctor_set(x_39, 3, x_29);
lean_ctor_set(x_39, 4, x_33);
lean_ctor_set(x_39, 5, x_24);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_apply_2(x_1, x_39, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_st_ref_take(x_3, x_36);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_50 = lean_ctor_get(x_47, 3);
lean_dec(x_50);
lean_ctor_set(x_47, 3, x_45);
x_51 = lean_st_ref_set(x_3, x_47, x_48);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_ctor_get(x_44, 1);
lean_inc(x_53);
lean_dec(x_44);
x_54 = l_List_reverse___rarg(x_53);
x_55 = l_List_forM___at_Lean_Elab_Command_elabCommand___spec__5(x_54, x_2, x_3, x_52);
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
lean_ctor_set(x_55, 0, x_43);
return x_55;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_43);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_60 = lean_ctor_get(x_47, 0);
x_61 = lean_ctor_get(x_47, 1);
x_62 = lean_ctor_get(x_47, 2);
x_63 = lean_ctor_get(x_47, 4);
x_64 = lean_ctor_get(x_47, 5);
x_65 = lean_ctor_get(x_47, 6);
x_66 = lean_ctor_get(x_47, 7);
x_67 = lean_ctor_get(x_47, 8);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_47);
x_68 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_68, 0, x_60);
lean_ctor_set(x_68, 1, x_61);
lean_ctor_set(x_68, 2, x_62);
lean_ctor_set(x_68, 3, x_45);
lean_ctor_set(x_68, 4, x_63);
lean_ctor_set(x_68, 5, x_64);
lean_ctor_set(x_68, 6, x_65);
lean_ctor_set(x_68, 7, x_66);
lean_ctor_set(x_68, 8, x_67);
x_69 = lean_st_ref_set(x_3, x_68, x_48);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_ctor_get(x_44, 1);
lean_inc(x_71);
lean_dec(x_44);
x_72 = l_List_reverse___rarg(x_71);
x_73 = l_List_forM___at_Lean_Elab_Command_elabCommand___spec__5(x_72, x_2, x_3, x_70);
lean_dec(x_3);
lean_dec(x_2);
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
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_43);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_42, 0);
lean_inc(x_77);
lean_dec(x_42);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_maxRecDepthErrorMessage;
x_81 = lean_string_dec_eq(x_79, x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_82, 0, x_79);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__11(x_78, x_83, x_2, x_3, x_36);
return x_84;
}
else
{
lean_object* x_85; 
lean_dec(x_79);
x_85 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__13(x_78, x_2, x_3, x_36);
lean_dec(x_3);
lean_dec(x_2);
return x_85;
}
}
else
{
lean_object* x_86; 
lean_dec(x_3);
lean_dec(x_2);
x_86 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(x_36);
return x_86;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logTrace___at_Lean_Elab_Command_elabCommand___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
lean_inc(x_1);
x_6 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__4;
x_8 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__6;
x_10 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
x_12 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__3;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
x_15 = 0;
x_16 = l_Lean_log___at_Lean_Elab_Command_runLinters___spec__3(x_14, x_15, x_3, x_4, x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__16(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_9 = lean_array_uget(x_1, x_2);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Elab_Command_elabCommand(x_9, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_11;
x_7 = x_12;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_5);
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
else
{
lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCommand___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
x_14 = lean_ctor_get(x_3, 3);
x_15 = lean_ctor_get(x_3, 4);
x_16 = lean_ctor_get(x_3, 5);
x_17 = lean_ctor_get(x_3, 7);
x_18 = lean_ctor_get(x_3, 6);
lean_dec(x_18);
lean_inc(x_17);
lean_inc(x_9);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_ctor_set(x_3, 6, x_9);
x_19 = lean_st_ref_get(x_4, x_8);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 4);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_nat_dec_eq(x_13, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_3);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_13, x_24);
lean_dec(x_13);
x_26 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_12);
lean_ctor_set(x_26, 2, x_25);
lean_ctor_set(x_26, 3, x_14);
lean_ctor_set(x_26, 4, x_15);
lean_ctor_set(x_26, 5, x_16);
lean_ctor_set(x_26, 6, x_9);
lean_ctor_set(x_26, 7, x_17);
x_27 = l_Lean_Elab_Command_withFreshMacroScope___rarg(x_2, x_26, x_4, x_21);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_2);
x_28 = l_Lean_Elab_Command_getRef(x_3, x_4, x_21);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__1(x_29, x_3, x_4, x_30);
lean_dec(x_4);
lean_dec(x_3);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_32 = lean_ctor_get(x_3, 0);
x_33 = lean_ctor_get(x_3, 1);
x_34 = lean_ctor_get(x_3, 2);
x_35 = lean_ctor_get(x_3, 3);
x_36 = lean_ctor_get(x_3, 4);
x_37 = lean_ctor_get(x_3, 5);
x_38 = lean_ctor_get(x_3, 7);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_3);
lean_inc(x_38);
lean_inc(x_9);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
x_39 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_33);
lean_ctor_set(x_39, 2, x_34);
lean_ctor_set(x_39, 3, x_35);
lean_ctor_set(x_39, 4, x_36);
lean_ctor_set(x_39, 5, x_37);
lean_ctor_set(x_39, 6, x_9);
lean_ctor_set(x_39, 7, x_38);
x_40 = lean_st_ref_get(x_4, x_8);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 4);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_nat_dec_eq(x_34, x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_39);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_34, x_45);
lean_dec(x_34);
x_47 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_47, 0, x_32);
lean_ctor_set(x_47, 1, x_33);
lean_ctor_set(x_47, 2, x_46);
lean_ctor_set(x_47, 3, x_35);
lean_ctor_set(x_47, 4, x_36);
lean_ctor_set(x_47, 5, x_37);
lean_ctor_set(x_47, 6, x_9);
lean_ctor_set(x_47, 7, x_38);
x_48 = l_Lean_Elab_Command_withFreshMacroScope___rarg(x_2, x_47, x_4, x_42);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_2);
x_49 = l_Lean_Elab_Command_getRef(x_39, x_4, x_42);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__1(x_50, x_39, x_4, x_51);
lean_dec(x_4);
lean_dec(x_39);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCommand___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
x_6 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__10(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_2, x_7, x_9, x_3, x_4, x_8);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_4);
lean_dec(x_3);
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
}
static lean_object* _init_l_Lean_Elab_Command_elabCommand___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandElabAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCommand___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elaboration function for '", 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCommand___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabCommand___lambda__3___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCommand___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' has not been implemented", 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCommand___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabCommand___lambda__3___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCommand___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_41 = lean_st_ref_get(x_5, x_6);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 2);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Elab_Command_instInhabitedScope;
x_46 = l_List_head_x21___rarg(x_45, x_44);
lean_dec(x_44);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
lean_inc(x_3);
x_48 = l_Lean_checkTraceOption(x_47, x_3);
lean_dec(x_47);
if (x_48 == 0)
{
lean_dec(x_3);
x_7 = x_43;
goto block_40;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_inc(x_1);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_1);
lean_inc(x_5);
lean_inc(x_4);
x_50 = l_Lean_logTrace___at_Lean_Elab_Command_elabCommand___spec__15(x_3, x_49, x_4, x_5, x_43);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_7 = x_51;
goto block_40;
}
block_40:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_st_ref_get(x_5, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_inc(x_1);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_expandMacroImpl_x3f___boxed), 4, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_1);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2(x_12, x_4, x_5, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Command_elabCommand___lambda__3___closed__1;
lean_inc(x_2);
x_17 = l_Lean_KeyedDeclsAttribute_getEntries___rarg(x_16, x_11, x_2);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_9);
x_18 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_18, 0, x_2);
x_19 = l_Lean_Elab_Command_elabCommand___lambda__3___closed__3;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Elab_Command_elabCommand___lambda__3___closed__5;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1___boxed), 4, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__4;
x_25 = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkInfoTree___boxed), 6, 2);
lean_closure_set(x_25, 0, x_24);
lean_closure_set(x_25, 1, x_1);
x_26 = l_Lean_Elab_withInfoTreeContext___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__2(x_23, x_25, x_4, x_5, x_15);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_2);
x_27 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing(x_9, x_1, x_17, x_4, x_5, x_15);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_2);
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_dec(x_13);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_closure((void*)(l_liftExcept___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__8___boxed), 3, 1);
lean_closure_set(x_32, 0, x_31);
lean_inc(x_1);
x_33 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___lambda__2), 5, 2);
lean_closure_set(x_33, 0, x_32);
lean_closure_set(x_33, 1, x_1);
x_34 = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkInfoTree___boxed), 6, 2);
lean_closure_set(x_34, 0, x_30);
lean_closure_set(x_34, 1, x_1);
x_35 = l_Lean_Elab_withInfoTreeContext___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__2(x_33, x_34, x_4, x_5, x_29);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_13);
if (x_36 == 0)
{
return x_13;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_13, 0);
x_38 = lean_ctor_get(x_13, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_13);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCommand___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCommand___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected command", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCommand___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabCommand___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCommand___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabCommand___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCommand___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCommand___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabCommand___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCommand___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___lambda__4___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCommand___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = l_Lean_Elab_Command_elabCommand___closed__5;
x_8 = lean_name_eq(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
x_9 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2240____closed__2;
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___lambda__3), 6, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___lambda__1), 5, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Lean_Elab_Command_withLogging(x_11, x_2, x_3, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_5);
x_13 = lean_array_get_size(x_6);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_6);
x_16 = l_Lean_Elab_Command_elabCommand___closed__6;
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___lambda__1), 5, 2);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_Command_withLogging(x_17, x_2, x_3, x_4);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_13, x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_13);
lean_dec(x_6);
x_20 = l_Lean_Elab_Command_elabCommand___closed__6;
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___lambda__1), 5, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_20);
x_22 = l_Lean_Elab_Command_withLogging(x_21, x_2, x_3, x_4);
return x_22;
}
else
{
size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_24 = lean_box(0);
x_25 = l_Lean_Elab_Command_elabCommand___boxed__const__1;
x_26 = lean_box_usize(x_23);
x_27 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__16___boxed), 7, 4);
lean_closure_set(x_27, 0, x_6);
lean_closure_set(x_27, 1, x_25);
lean_closure_set(x_27, 2, x_26);
lean_closure_set(x_27, 3, x_24);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___lambda__1), 5, 2);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_27);
x_29 = l_Lean_Elab_Command_withLogging(x_28, x_2, x_3, x_4);
return x_29;
}
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Lean_Elab_Command_elabCommand___closed__3;
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___lambda__1), 5, 2);
lean_closure_set(x_31, 0, x_1);
lean_closure_set(x_31, 1, x_30);
x_32 = l_Lean_Elab_Command_withLogging(x_31, x_2, x_3, x_4);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Command_elabCommand___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Command_elabCommand___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Command_elabCommand___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forM___at_Lean_Elab_Command_elabCommand___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabCommand___spec__2___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__12(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__13(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__16(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCommand___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabCommand___lambda__4(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2500____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("input", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2500____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2240____closed__1;
x_2 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2500____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2500_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2500____closed__2;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at_Lean_Elab_Command_elabCommandTopLevel___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 7);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
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
x_10 = lean_ctor_get(x_8, 7);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at_Lean_Elab_Command_elabCommandTopLevel___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_getInfoTrees___at_Lean_Elab_Command_elabCommandTopLevel___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabCommandTopLevel___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_6, x_5);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_4, x_6);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 0);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_15);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Std_PersistentArray_forInAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__3(x_1, x_2, x_13, x_15, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_7, 0, x_21);
lean_ctor_set(x_17, 0, x_7);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_7, 0, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
lean_dec(x_15);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
lean_dec(x_18);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_26);
lean_ctor_set(x_7, 0, x_3);
x_27 = 1;
x_28 = lean_usize_add(x_6, x_27);
x_6 = x_28;
x_10 = x_25;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_free_object(x_7);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_3);
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
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_7, 1);
lean_inc(x_34);
lean_dec(x_7);
lean_inc(x_8);
lean_inc(x_34);
lean_inc(x_2);
lean_inc(x_1);
x_35 = l_Std_PersistentArray_forInAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__3(x_1, x_2, x_13, x_34, x_8, x_9, x_10);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_34);
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_38;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; 
lean_dec(x_34);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_dec(x_35);
x_43 = lean_ctor_get(x_36, 0);
lean_inc(x_43);
lean_dec(x_36);
lean_inc(x_3);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_3);
lean_ctor_set(x_44, 1, x_43);
x_45 = 1;
x_46 = lean_usize_add(x_6, x_45);
x_6 = x_46;
x_7 = x_44;
x_10 = x_42;
goto _start;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_34);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_ctor_get(x_35, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_35, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_50 = x_35;
} else {
 lean_dec_ref(x_35);
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
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabCommandTopLevel___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("info", 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabCommandTopLevel___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_12 = lean_array_uget(x_3, x_5);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_20 = x_6;
} else {
 lean_dec_ref(x_6);
 x_20 = lean_box(0);
}
x_30 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabCommandTopLevel___spec__5___closed__1;
lean_inc(x_1);
x_31 = lean_name_mk_string(x_1, x_30);
x_59 = lean_st_ref_get(x_8, x_9);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_60, 8);
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
x_32 = x_64;
x_33 = x_63;
goto block_58;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
lean_dec(x_59);
lean_inc(x_31);
x_66 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Command_elabCommand___spec__3(x_31, x_7, x_8, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_unbox(x_67);
lean_dec(x_67);
x_32 = x_69;
x_33 = x_68;
goto block_58;
}
block_19:
{
lean_object* x_15; size_t x_16; size_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_5, x_16);
x_5 = x_17;
x_6 = x_15;
x_9 = x_14;
goto _start;
}
block_29:
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_2);
if (lean_is_scalar(x_20)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_20;
}
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_21, 0, x_25);
x_13 = x_21;
x_14 = x_22;
goto block_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
lean_inc(x_2);
if (lean_is_scalar(x_20)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_20;
}
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_13 = x_28;
x_14 = x_22;
goto block_19;
}
}
block_58:
{
if (x_32 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_12);
x_34 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4___closed__1;
x_21 = x_34;
x_22 = x_33;
goto block_29;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_box(0);
x_36 = l_Lean_Elab_InfoTree_format(x_12, x_35, x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_37);
x_40 = l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4(x_31, x_39, x_7, x_8, x_38);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4___closed__1;
x_21 = x_42;
x_22 = x_41;
goto block_29;
}
else
{
uint8_t x_43; 
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_7, 6);
x_46 = lean_io_error_to_string(x_44);
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_inc(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_36, 0, x_49);
return x_36;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_36, 0);
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_36);
x_52 = lean_ctor_get(x_7, 6);
x_53 = lean_io_error_to_string(x_50);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_inc(x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_51);
return x_57;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
x_11 = lean_array_get_size(x_8);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
lean_inc(x_5);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabCommandTopLevel___spec__4(x_1, x_2, x_9, x_8, x_12, x_13, x_10, x_5, x_6, x_7);
lean_dec(x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = l_Std_PersistentArray_forInAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__3___lambda__1(x_18, x_19, x_5, x_6, x_17);
lean_dec(x_5);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_15);
lean_dec(x_5);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_14, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
else
{
uint8_t x_27; 
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
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; 
lean_dec(x_2);
x_31 = lean_ctor_get(x_3, 0);
lean_inc(x_31);
lean_dec(x_3);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_4);
x_34 = lean_array_get_size(x_31);
x_35 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_36 = 0;
x_37 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabCommandTopLevel___spec__5(x_1, x_32, x_31, x_35, x_36, x_33, x_5, x_6, x_7);
lean_dec(x_31);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_box(0);
x_43 = l_Std_PersistentArray_forInAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__3___lambda__1(x_41, x_42, x_5, x_6, x_40);
lean_dec(x_5);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_38);
lean_dec(x_5);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_37, 0);
lean_dec(x_45);
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_46);
return x_37;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_37, 1);
lean_inc(x_47);
lean_dec(x_37);
x_48 = lean_ctor_get(x_39, 0);
lean_inc(x_48);
lean_dec(x_39);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_5);
x_50 = !lean_is_exclusive(x_37);
if (x_50 == 0)
{
return x_37;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_37, 0);
x_52 = lean_ctor_get(x_37, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_37);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabCommandTopLevel___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_12 = lean_array_uget(x_3, x_5);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_20 = x_6;
} else {
 lean_dec_ref(x_6);
 x_20 = lean_box(0);
}
x_30 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabCommandTopLevel___spec__5___closed__1;
lean_inc(x_1);
x_31 = lean_name_mk_string(x_1, x_30);
x_59 = lean_st_ref_get(x_8, x_9);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_60, 8);
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
x_32 = x_64;
x_33 = x_63;
goto block_58;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
lean_dec(x_59);
lean_inc(x_31);
x_66 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Command_elabCommand___spec__3(x_31, x_7, x_8, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_unbox(x_67);
lean_dec(x_67);
x_32 = x_69;
x_33 = x_68;
goto block_58;
}
block_19:
{
lean_object* x_15; size_t x_16; size_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_5, x_16);
x_5 = x_17;
x_6 = x_15;
x_9 = x_14;
goto _start;
}
block_29:
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_2);
if (lean_is_scalar(x_20)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_20;
}
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_21, 0, x_25);
x_13 = x_21;
x_14 = x_22;
goto block_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
lean_inc(x_2);
if (lean_is_scalar(x_20)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_20;
}
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_13 = x_28;
x_14 = x_22;
goto block_19;
}
}
block_58:
{
if (x_32 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_12);
x_34 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4___closed__1;
x_21 = x_34;
x_22 = x_33;
goto block_29;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_box(0);
x_36 = l_Lean_Elab_InfoTree_format(x_12, x_35, x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_37);
x_40 = l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4(x_31, x_39, x_7, x_8, x_38);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4___closed__1;
x_21 = x_42;
x_22 = x_41;
goto block_29;
}
else
{
uint8_t x_43; 
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_7, 6);
x_46 = lean_io_error_to_string(x_44);
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_inc(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_36, 0, x_49);
return x_36;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_36, 0);
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_36);
x_52 = lean_ctor_get(x_7, 6);
x_53 = lean_io_error_to_string(x_50);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_inc(x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_51);
return x_57;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Elab_Command_elabCommandTopLevel___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Elab_Command_elabCommandTopLevel___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Std_PersistentArray_forInAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__3(x_1, x_3, x_7, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
x_21 = lean_array_get_size(x_18);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = 0;
x_24 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabCommandTopLevel___spec__6(x_1, x_19, x_18, x_22, x_23, x_20, x_4, x_5, x_16);
lean_dec(x_4);
lean_dec(x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_24, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
lean_ctor_set(x_24, 0, x_29);
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_25);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_24, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_35);
return x_24;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
lean_dec(x_24);
x_37 = lean_ctor_get(x_26, 0);
lean_inc(x_37);
lean_dec(x_26);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
uint8_t x_39; 
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
}
else
{
uint8_t x_43; 
lean_dec(x_4);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__10(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__9(x_1, x_7, x_5);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("synthPlaceholder", 16);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unsolvedGoals", 13);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__3;
x_2 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__1;
x_4 = lean_name_mk_string(x_1, x_3);
x_5 = lean_name_eq(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__5;
x_7 = lean_name_eq(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__2;
x_9 = l_Lean_Name_isSuffixOf(x_8, x_2);
return x_9;
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
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___boxed), 2, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_ctor_get(x_7, 4);
lean_inc(x_9);
x_10 = l_Lean_MessageData_hasTag(x_8, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (x_10 == 0)
{
lean_dec(x_7);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = l_Std_PersistentArray_push___rarg(x_5, x_7);
x_3 = x_12;
x_5 = x_14;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__10(x_1, x_4, x_9, x_10, x_3);
lean_dec(x_4);
return x_11;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_13, x_13);
if (x_16 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11(x_1, x_12, x_17, x_18, x_3);
lean_dec(x_12);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__12(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__9(x_1, x_7, x_5);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__13(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___boxed), 2, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_ctor_get(x_7, 4);
lean_inc(x_9);
x_10 = l_Lean_MessageData_hasTag(x_8, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (x_10 == 0)
{
lean_dec(x_7);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = l_Std_PersistentArray_push___rarg(x_5, x_7);
x_3 = x_12;
x_5 = x_14;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_usize_shift_right(x_3, x_4);
x_8 = lean_usize_to_nat(x_7);
x_9 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__2___closed__1;
x_10 = lean_array_get(x_9, x_6, x_8);
x_11 = 1;
x_12 = lean_usize_shift_left(x_11, x_4);
x_13 = lean_usize_sub(x_12, x_11);
x_14 = lean_usize_land(x_3, x_13);
x_15 = 5;
x_16 = lean_usize_sub(x_4, x_15);
lean_inc(x_1);
x_17 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__8(x_1, x_10, x_14, x_16, x_5);
lean_dec(x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_8, x_18);
lean_dec(x_8);
x_20 = lean_array_get_size(x_6);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_1);
return x_17;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_20, x_20);
if (x_22 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_1);
return x_17;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
x_23 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_24 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_25 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__12(x_1, x_6, x_23, x_24, x_17);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_usize_to_nat(x_3);
x_28 = lean_array_get_size(x_26);
x_29 = lean_nat_dec_lt(x_27, x_28);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
return x_5;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_28, x_28);
if (x_30 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
return x_5;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; 
x_31 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_32 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_33 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__13(x_1, x_26, x_31, x_32, x_5);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__14(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___boxed), 2, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_ctor_get(x_7, 4);
lean_inc(x_9);
x_10 = l_Lean_MessageData_hasTag(x_8, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (x_10 == 0)
{
lean_dec(x_7);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = l_Std_PersistentArray_push___rarg(x_5, x_7);
x_3 = x_12;
x_5 = x_14;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__15(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___boxed), 2, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_ctor_get(x_7, 4);
lean_inc(x_9);
x_10 = l_Lean_MessageData_hasTag(x_8, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (x_10 == 0)
{
lean_dec(x_7);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = l_Std_PersistentArray_push___rarg(x_5, x_7);
x_3 = x_12;
x_5 = x_14;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__17(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__16(x_1, x_7, x_5);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__18(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___boxed), 2, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_ctor_get(x_7, 4);
lean_inc(x_9);
x_10 = l_Lean_MessageData_hasTag(x_8, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (x_10 == 0)
{
lean_dec(x_7);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = l_Std_PersistentArray_push___rarg(x_5, x_7);
x_3 = x_12;
x_5 = x_14;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__17(x_1, x_4, x_9, x_10, x_3);
lean_dec(x_4);
return x_11;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_13, x_13);
if (x_16 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__18(x_1, x_12, x_17, x_18, x_3);
lean_dec(x_12);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__19(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___boxed), 2, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_ctor_get(x_7, 4);
lean_inc(x_9);
x_10 = l_Lean_MessageData_hasTag(x_8, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (x_10 == 0)
{
lean_dec(x_7);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = l_Std_PersistentArray_push___rarg(x_5, x_7);
x_3 = x_12;
x_5 = x_14;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_foldlM___at_Lean_Elab_Command_elabCommandTopLevel___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
x_8 = lean_nat_dec_le(x_7, x_4);
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_11 = lean_ctor_get_usize(x_2, 4);
lean_inc(x_1);
x_12 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__8(x_1, x_9, x_10, x_11, x_3);
lean_dec(x_9);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_array_get_size(x_13);
x_15 = lean_nat_dec_lt(x_5, x_14);
if (x_15 == 0)
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
return x_12;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_14, x_14);
if (x_16 == 0)
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
return x_12;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__14(x_1, x_13, x_17, x_18, x_12);
lean_dec(x_13);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_nat_sub(x_4, x_7);
lean_dec(x_7);
lean_dec(x_4);
x_22 = lean_array_get_size(x_20);
x_23 = lean_nat_dec_lt(x_21, x_22);
if (x_23 == 0)
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_22, x_22);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; 
x_25 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_26 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_27 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__15(x_1, x_20, x_25, x_26, x_3);
lean_dec(x_20);
return x_27;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_4);
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
lean_inc(x_1);
x_29 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__16(x_1, x_28, x_3);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
lean_dec(x_2);
x_31 = lean_array_get_size(x_30);
x_32 = lean_nat_dec_lt(x_5, x_31);
if (x_32 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_1);
return x_29;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_31, x_31);
if (x_33 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_1);
return x_29;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
x_34 = 0;
x_35 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_36 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__19(x_1, x_30, x_34, x_35, x_29);
lean_dec(x_30);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCommandTopLevel___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_Elab_getInfoTrees___at_Lean_Elab_Command_elabCommandTopLevel___spec__1___rarg(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
lean_inc(x_6);
x_13 = l_Std_PersistentArray_forIn___at_Lean_Elab_Command_elabCommandTopLevel___spec__2(x_1, x_10, x_12, x_6, x_7, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_take(x_7, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_16, 7);
x_20 = lean_ctor_get(x_16, 1);
lean_dec(x_20);
x_21 = l_Std_PersistentArray_append___rarg(x_2, x_4);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_19, 1);
x_24 = l_Std_PersistentArray_append___rarg(x_3, x_23);
lean_ctor_set(x_19, 1, x_24);
lean_ctor_set(x_16, 1, x_21);
x_25 = lean_st_ref_set(x_7, x_16, x_17);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages(x_6, x_7, x_26);
return x_27;
}
else
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get_uint8(x_19, sizeof(void*)*2);
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
x_31 = l_Std_PersistentArray_append___rarg(x_3, x_30);
x_32 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_28);
lean_ctor_set(x_16, 7, x_32);
lean_ctor_set(x_16, 1, x_21);
x_33 = lean_st_ref_set(x_7, x_16, x_17);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages(x_6, x_7, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_36 = lean_ctor_get(x_16, 0);
x_37 = lean_ctor_get(x_16, 2);
x_38 = lean_ctor_get(x_16, 3);
x_39 = lean_ctor_get(x_16, 4);
x_40 = lean_ctor_get(x_16, 5);
x_41 = lean_ctor_get(x_16, 6);
x_42 = lean_ctor_get(x_16, 7);
x_43 = lean_ctor_get(x_16, 8);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_16);
x_44 = l_Std_PersistentArray_append___rarg(x_2, x_4);
x_45 = lean_ctor_get_uint8(x_42, sizeof(void*)*2);
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
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
x_49 = l_Std_PersistentArray_append___rarg(x_3, x_47);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 1);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_45);
x_51 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_51, 0, x_36);
lean_ctor_set(x_51, 1, x_44);
lean_ctor_set(x_51, 2, x_37);
lean_ctor_set(x_51, 3, x_38);
lean_ctor_set(x_51, 4, x_39);
lean_ctor_set(x_51, 5, x_40);
lean_ctor_set(x_51, 6, x_41);
lean_ctor_set(x_51, 7, x_50);
lean_ctor_set(x_51, 8, x_43);
x_52 = lean_st_ref_set(x_7, x_51, x_17);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages(x_6, x_7, x_53);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_13);
if (x_55 == 0)
{
return x_13;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_13, 0);
x_57 = lean_ctor_get(x_13, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_13);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCommandTopLevel___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_showPartialSyntaxErrors;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCommandTopLevel___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec(x_3);
x_7 = lean_st_ref_take(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Lean_Elab_Command_State_messages___default___closed__3;
lean_ctor_set(x_8, 1, x_12);
x_13 = lean_st_ref_set(x_5, x_8, x_9);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Elab_getResetInfoTrees___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__3___rarg(x_5, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_18 = l_Lean_Elab_Command_elabCommand(x_1, x_4, x_5, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Command_runLinters), 4, 1);
lean_closure_set(x_20, 0, x_1);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l_Lean_Elab_Command_withLogging(x_20, x_4, x_5, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_get(x_5, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_st_ref_get(x_5, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 2);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Elab_Command_instInhabitedScope;
x_32 = l_List_head_x21___rarg(x_31, x_30);
lean_dec(x_30);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_Elab_Command_elabCommandTopLevel___lambda__2___closed__1;
x_35 = l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(x_33, x_34);
lean_dec(x_33);
if (x_35 == 0)
{
uint8_t x_36; 
lean_inc(x_11);
x_36 = l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_11);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_37 = lean_box(0);
x_38 = l_Lean_Elab_Command_elabCommandTopLevel___lambda__1(x_2, x_11, x_16, x_26, x_37, x_4, x_5, x_29);
lean_dec(x_5);
return x_38;
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Lean_Syntax_hasMissing(x_1);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_box(0);
x_42 = l_Lean_Elab_Command_elabCommandTopLevel___lambda__1(x_2, x_11, x_16, x_26, x_41, x_4, x_5, x_29);
lean_dec(x_5);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_44 = l_Std_PersistentArray_foldlM___at_Lean_Elab_Command_elabCommandTopLevel___spec__7(x_2, x_26, x_12, x_43);
x_45 = lean_box(0);
x_46 = l_Lean_Elab_Command_elabCommandTopLevel___lambda__1(x_2, x_11, x_16, x_44, x_45, x_4, x_5, x_29);
lean_dec(x_5);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_1);
x_47 = lean_box(0);
x_48 = l_Lean_Elab_Command_elabCommandTopLevel___lambda__1(x_2, x_11, x_16, x_26, x_47, x_4, x_5, x_29);
lean_dec(x_5);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_21);
if (x_49 == 0)
{
return x_21;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_21, 0);
x_51 = lean_ctor_get(x_21, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_21);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_18);
if (x_53 == 0)
{
return x_18;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_18, 0);
x_55 = lean_ctor_get(x_18, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_18);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_57 = lean_ctor_get(x_8, 0);
x_58 = lean_ctor_get(x_8, 1);
x_59 = lean_ctor_get(x_8, 2);
x_60 = lean_ctor_get(x_8, 3);
x_61 = lean_ctor_get(x_8, 4);
x_62 = lean_ctor_get(x_8, 5);
x_63 = lean_ctor_get(x_8, 6);
x_64 = lean_ctor_get(x_8, 7);
x_65 = lean_ctor_get(x_8, 8);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_8);
x_66 = l_Lean_Elab_Command_State_messages___default___closed__3;
x_67 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_67, 0, x_57);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_67, 2, x_59);
lean_ctor_set(x_67, 3, x_60);
lean_ctor_set(x_67, 4, x_61);
lean_ctor_set(x_67, 5, x_62);
lean_ctor_set(x_67, 6, x_63);
lean_ctor_set(x_67, 7, x_64);
lean_ctor_set(x_67, 8, x_65);
x_68 = lean_st_ref_set(x_5, x_67, x_9);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = l_Lean_Elab_getResetInfoTrees___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__3___rarg(x_5, x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_73 = l_Lean_Elab_Command_elabCommand(x_1, x_4, x_5, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
lean_inc(x_1);
x_75 = lean_alloc_closure((void*)(l_Lean_Elab_Command_runLinters), 4, 1);
lean_closure_set(x_75, 0, x_1);
lean_inc(x_5);
lean_inc(x_4);
x_76 = l_Lean_Elab_Command_withLogging(x_75, x_4, x_5, x_74);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_st_ref_get(x_5, x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_st_ref_get(x_5, x_80);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_ctor_get(x_83, 2);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Elab_Command_instInhabitedScope;
x_87 = l_List_head_x21___rarg(x_86, x_85);
lean_dec(x_85);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = l_Lean_Elab_Command_elabCommandTopLevel___lambda__2___closed__1;
x_90 = l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(x_88, x_89);
lean_dec(x_88);
if (x_90 == 0)
{
uint8_t x_91; 
lean_inc(x_58);
x_91 = l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_58);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_1);
x_92 = lean_box(0);
x_93 = l_Lean_Elab_Command_elabCommandTopLevel___lambda__1(x_2, x_58, x_71, x_81, x_92, x_4, x_5, x_84);
lean_dec(x_5);
return x_93;
}
else
{
lean_object* x_94; uint8_t x_95; 
x_94 = l_Lean_Syntax_hasMissing(x_1);
x_95 = lean_unbox(x_94);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_box(0);
x_97 = l_Lean_Elab_Command_elabCommandTopLevel___lambda__1(x_2, x_58, x_71, x_81, x_96, x_4, x_5, x_84);
lean_dec(x_5);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_99 = l_Std_PersistentArray_foldlM___at_Lean_Elab_Command_elabCommandTopLevel___spec__7(x_2, x_81, x_66, x_98);
x_100 = lean_box(0);
x_101 = l_Lean_Elab_Command_elabCommandTopLevel___lambda__1(x_2, x_58, x_71, x_99, x_100, x_4, x_5, x_84);
lean_dec(x_5);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_1);
x_102 = lean_box(0);
x_103 = l_Lean_Elab_Command_elabCommandTopLevel___lambda__1(x_2, x_58, x_71, x_81, x_102, x_4, x_5, x_84);
lean_dec(x_5);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_71);
lean_dec(x_58);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_104 = lean_ctor_get(x_76, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_76, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_106 = x_76;
} else {
 lean_dec_ref(x_76);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_71);
lean_dec(x_58);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_108 = lean_ctor_get(x_73, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_73, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_110 = x_73;
} else {
 lean_dec_ref(x_73);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2500____closed__2;
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
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_11 = lean_ctor_get(x_2, 6);
lean_dec(x_11);
lean_ctor_set(x_2, 6, x_9);
x_24 = lean_st_ref_get(x_3, x_8);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 8);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get_uint8(x_26, sizeof(void*)*1);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = 0;
x_12 = x_29;
x_13 = x_28;
goto block_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Command_elabCommand___spec__3(x_5, x_2, x_3, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_unbox(x_32);
lean_dec(x_32);
x_12 = x_34;
x_13 = x_33;
goto block_23;
}
block_23:
{
if (x_12 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2240____closed__1;
x_15 = lean_box(0);
x_16 = l_Lean_Elab_Command_elabCommandTopLevel___lambda__2(x_1, x_14, x_15, x_2, x_3, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
x_18 = l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4(x_5, x_17, x_2, x_3, x_13);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2240____closed__1;
x_22 = l_Lean_Elab_Command_elabCommandTopLevel___lambda__2(x_1, x_21, x_19, x_2, x_3, x_20);
return x_22;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_35 = lean_ctor_get(x_2, 0);
x_36 = lean_ctor_get(x_2, 1);
x_37 = lean_ctor_get(x_2, 2);
x_38 = lean_ctor_get(x_2, 3);
x_39 = lean_ctor_get(x_2, 4);
x_40 = lean_ctor_get(x_2, 5);
x_41 = lean_ctor_get(x_2, 7);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_2);
x_42 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_36);
lean_ctor_set(x_42, 2, x_37);
lean_ctor_set(x_42, 3, x_38);
lean_ctor_set(x_42, 4, x_39);
lean_ctor_set(x_42, 5, x_40);
lean_ctor_set(x_42, 6, x_9);
lean_ctor_set(x_42, 7, x_41);
x_55 = lean_st_ref_get(x_3, x_8);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 8);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_ctor_get_uint8(x_57, sizeof(void*)*1);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
lean_dec(x_55);
x_60 = 0;
x_43 = x_60;
x_44 = x_59;
goto block_54;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_dec(x_55);
x_62 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Command_elabCommand___spec__3(x_5, x_42, x_3, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_unbox(x_63);
lean_dec(x_63);
x_43 = x_65;
x_44 = x_64;
goto block_54;
}
block_54:
{
if (x_43 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2240____closed__1;
x_46 = lean_box(0);
x_47 = l_Lean_Elab_Command_elabCommandTopLevel___lambda__2(x_1, x_45, x_46, x_42, x_3, x_44);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_inc(x_1);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_1);
x_49 = l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4(x_5, x_48, x_42, x_3, x_44);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2240____closed__1;
x_53 = l_Lean_Elab_Command_elabCommandTopLevel___lambda__2(x_1, x_52, x_50, x_42, x_3, x_51);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at_Lean_Elab_Command_elabCommandTopLevel___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_getInfoTrees___at_Lean_Elab_Command_elabCommandTopLevel___spec__1___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at_Lean_Elab_Command_elabCommandTopLevel___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_getInfoTrees___at_Lean_Elab_Command_elabCommandTopLevel___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabCommandTopLevel___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabCommandTopLevel___spec__4(x_1, x_2, x_3, x_4, x_11, x_12, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabCommandTopLevel___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabCommandTopLevel___spec__5(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentArray_forInAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_PersistentArray_forInAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabCommandTopLevel___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabCommandTopLevel___spec__6(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Elab_Command_elabCommandTopLevel___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentArray_forIn___at_Lean_Elab_Command_elabCommandTopLevel___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Elab_Command_elabCommandTopLevel___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_PersistentArray_forIn___at_Lean_Elab_Command_elabCommandTopLevel___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__10(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__12(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__13(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Elab_Command_elabCommandTopLevel___spec__8(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__14(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__15(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__17(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__18(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__19(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCommandTopLevel___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Command_elabCommandTopLevel___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_adaptExpander(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_6 = lean_apply_4(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_2, x_7, x_9, x_3, x_4, x_8);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_4);
lean_dec(x_3);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = l_Lean_Elab_Command_instInhabitedScope;
x_4 = l_List_head_x21___rarg(x_3, x_2);
x_5 = lean_ctor_get(x_4, 5);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instInhabitedCommandElabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedCommandElabM___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedCommandElabM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_instInhabitedCommandElabM___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instInhabitedCommandElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_instInhabitedCommandElabM___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instInhabitedCommandElabM___lambda__1___boxed), 4, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instInhabitedCommandElabM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_instInhabitedCommandElabM___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 1;
x_2 = 0;
x_3 = 1;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_5, 0, x_1);
lean_ctor_set_uint8(x_5, 1, x_1);
lean_ctor_set_uint8(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, 3, x_2);
lean_ctor_set_uint8(x_5, 4, x_2);
lean_ctor_set_uint8(x_5, 5, x_3);
lean_ctor_set_uint8(x_5, 6, x_1);
lean_ctor_set_uint8(x_5, 7, x_2);
lean_ctor_set_uint8(x_5, 8, x_1);
lean_ctor_set_uint8(x_5, 9, x_1);
lean_ctor_set_uint8(x_5, 10, x_2);
lean_ctor_set_uint8(x_5, 11, x_1);
lean_ctor_set_uint8(x_5, 12, x_1);
lean_ctor_set_uint8(x_5, 13, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__1;
x_3 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___closed__3;
x_4 = l_Lean_Elab_Command_Scope_varDecls___default___closed__1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set(x_6, 4, x_5);
lean_ctor_set(x_6, 5, x_1);
return x_6;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_getBracketedBinderIds___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l_Lean_Syntax_getId(x_5);
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
static lean_object* _init_l_Lean_Elab_Command_getBracketedBinderIds___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_getBracketedBinderIds___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__14;
x_2 = l_Lean_Elab_Command_getBracketedBinderIds___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_getBracketedBinderIds___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("explicitBinder", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_getBracketedBinderIds___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_getBracketedBinderIds___closed__2;
x_2 = l_Lean_Elab_Command_getBracketedBinderIds___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_getBracketedBinderIds___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("implicitBinder", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_getBracketedBinderIds___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_getBracketedBinderIds___closed__2;
x_2 = l_Lean_Elab_Command_getBracketedBinderIds___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_getBracketedBinderIds___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("instBinder", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_getBracketedBinderIds___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_getBracketedBinderIds___closed__2;
x_2 = l_Lean_Elab_Command_getBracketedBinderIds___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_getBracketedBinderIds___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_getBracketedBinderIds___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_getBracketedBinderIds___closed__9;
x_2 = lean_box(0);
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getBracketedBinderIds(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Elab_Command_getBracketedBinderIds___closed__4;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Command_getBracketedBinderIds___closed__6;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Elab_Command_getBracketedBinderIds___closed__8;
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_Elab_Command_Scope_varDecls___default___closed__1;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_dec(x_1);
x_11 = lean_unsigned_to_nat(2u);
lean_inc(x_10);
x_12 = l_Lean_Syntax_matchesNull(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_matchesNull(x_10, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Command_Scope_varDecls___default___closed__1;
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Command_getBracketedBinderIds___closed__10;
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Syntax_getArg(x_10, x_17);
lean_dec(x_10);
x_19 = l_Lean_Syntax_getId(x_18);
lean_dec(x_18);
x_20 = l_Lean_Elab_Command_getBracketedBinderIds___closed__9;
x_21 = lean_array_push(x_20, x_19);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_34; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_Syntax_getArg(x_1, x_22);
x_24 = lean_unsigned_to_nat(2u);
x_25 = l_Lean_Syntax_getArg(x_1, x_24);
lean_dec(x_1);
x_34 = l_Lean_Syntax_isNone(x_25);
if (x_34 == 0)
{
uint8_t x_35; 
lean_inc(x_25);
x_35 = l_Lean_Syntax_matchesNull(x_25, x_24);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_25);
lean_dec(x_23);
x_36 = l_Lean_Elab_Command_Scope_varDecls___default___closed__1;
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = l_Lean_Syntax_getArg(x_25, x_22);
lean_dec(x_25);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_box(0);
x_26 = x_39;
x_27 = x_38;
goto block_33;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_25);
x_40 = lean_box(0);
x_41 = lean_box(0);
x_26 = x_41;
x_27 = x_40;
goto block_33;
}
block_33:
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
lean_dec(x_27);
lean_dec(x_26);
x_28 = l_Lean_Syntax_getArgs(x_23);
lean_dec(x_23);
x_29 = lean_array_get_size(x_28);
x_30 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_31 = 0;
x_32 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_getBracketedBinderIds___spec__1(x_30, x_31, x_28);
return x_32;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_54; 
x_42 = lean_unsigned_to_nat(1u);
x_43 = l_Lean_Syntax_getArg(x_1, x_42);
x_44 = lean_unsigned_to_nat(2u);
x_45 = l_Lean_Syntax_getArg(x_1, x_44);
lean_dec(x_1);
x_54 = l_Lean_Syntax_isNone(x_45);
if (x_54 == 0)
{
uint8_t x_55; 
lean_inc(x_45);
x_55 = l_Lean_Syntax_matchesNull(x_45, x_44);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_45);
lean_dec(x_43);
x_56 = l_Lean_Elab_Command_Scope_varDecls___default___closed__1;
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = l_Lean_Syntax_getArg(x_45, x_42);
lean_dec(x_45);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_box(0);
x_46 = x_59;
x_47 = x_58;
goto block_53;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_45);
x_60 = lean_box(0);
x_61 = lean_box(0);
x_46 = x_61;
x_47 = x_60;
goto block_53;
}
block_53:
{
lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; 
lean_dec(x_47);
lean_dec(x_46);
x_48 = l_Lean_Syntax_getArgs(x_43);
lean_dec(x_43);
x_49 = lean_array_get_size(x_48);
x_50 = lean_usize_of_nat(x_49);
lean_dec(x_49);
x_51 = 0;
x_52 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_getBracketedBinderIds___spec__1(x_50, x_51, x_48);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_getBracketedBinderIds___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_getBracketedBinderIds___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___elambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_1, x_3);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 2);
lean_inc(x_12);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
return x_4;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_15 = lean_ctor_get(x_8, 2);
lean_dec(x_15);
x_16 = lean_ctor_get(x_8, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_8, 0);
lean_dec(x_17);
x_18 = lean_array_fget(x_10, x_11);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_11, x_19);
lean_dec(x_11);
lean_ctor_set(x_8, 1, x_20);
x_21 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_9, x_6, x_18);
lean_ctor_set(x_4, 1, x_21);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_3 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
lean_dec(x_8);
x_25 = lean_array_fget(x_10, x_11);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_11, x_26);
lean_dec(x_11);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_10);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_12);
x_29 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_9, x_6, x_25);
lean_ctor_set(x_4, 1, x_29);
lean_ctor_set(x_4, 0, x_28);
x_30 = 1;
x_31 = lean_usize_add(x_3, x_30);
x_3 = x_31;
goto _start;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_4, 0);
x_34 = lean_ctor_get(x_4, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_4);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_33, 2);
lean_inc(x_37);
x_38 = lean_nat_dec_lt(x_36, x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_6);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_34);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; 
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 lean_ctor_release(x_33, 2);
 x_40 = x_33;
} else {
 lean_dec_ref(x_33);
 x_40 = lean_box(0);
}
x_41 = lean_array_fget(x_35, x_36);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_36, x_42);
lean_dec(x_36);
if (lean_is_scalar(x_40)) {
 x_44 = lean_alloc_ctor(0, 3, 0);
} else {
 x_44 = x_40;
}
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_37);
x_45 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_34, x_6, x_41);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = 1;
x_48 = lean_usize_add(x_3, x_47);
x_3 = x_48;
x_4 = x_46;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Elab_Command_getBracketedBinderIds(x_6);
x_8 = l_Array_append___rarg(x_4, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___elambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; size_t x_16; lean_object* x_17; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Lean_Elab_Command_instInhabitedScope;
x_6 = l_List_head_x21___rarg(x_5, x_4);
x_7 = lean_box(0);
x_8 = lean_ctor_get(x_6, 6);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_toSubarray___rarg(x_8, x_10, x_9);
x_12 = lean_ctor_get(x_6, 5);
lean_inc(x_12);
x_13 = lean_array_get_size(x_12);
x_14 = lean_nat_dec_lt(x_10, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_7);
x_16 = 0;
if (x_14 == 0)
{
lean_object* x_31; 
lean_dec(x_13);
lean_dec(x_12);
x_31 = l_Lean_Elab_Command_Scope_varDecls___default___closed__1;
x_17 = x_31;
goto block_30;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_13, x_13);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_13);
lean_dec(x_12);
x_33 = l_Lean_Elab_Command_Scope_varDecls___default___closed__1;
x_17 = x_33;
goto block_30;
}
else
{
size_t x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_35 = l_Lean_Elab_Command_Scope_varDecls___default___closed__1;
x_36 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___spec__2(x_12, x_16, x_34, x_35);
lean_dec(x_12);
x_17 = x_36;
goto block_30;
}
}
block_30:
{
lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_array_get_size(x_17);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___spec__1(x_17, x_19, x_16, x_15);
lean_dec(x_17);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_1, 4);
x_23 = lean_ctor_get_uint8(x_6, sizeof(void*)*7);
lean_dec(x_6);
x_24 = lean_ctor_get(x_1, 7);
x_25 = 1;
x_26 = 0;
x_27 = l_Lean_Elab_Command_State_messages___default___closed__3;
x_28 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___closed__1;
lean_inc(x_24);
lean_inc(x_22);
x_29 = lean_alloc_ctor(0, 7, 8);
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_22);
lean_ctor_set(x_29, 2, x_27);
lean_ctor_set(x_29, 3, x_28);
lean_ctor_set(x_29, 4, x_21);
lean_ctor_set(x_29, 5, x_7);
lean_ctor_set(x_29, 6, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*7, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*7 + 1, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*7 + 2, x_26);
lean_ctor_set_uint8(x_29, sizeof(void*)*7 + 3, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*7 + 4, x_23);
lean_ctor_set_uint8(x_29, sizeof(void*)*7 + 5, x_26);
lean_ctor_set_uint8(x_29, sizeof(void*)*7 + 6, x_26);
lean_ctor_set_uint8(x_29, sizeof(void*)*7 + 7, x_25);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___elambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___elambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermState(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 4);
x_4 = lean_box(0);
x_5 = lean_box(0);
x_6 = lean_ctor_get(x_2, 7);
lean_inc(x_6);
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_State_infoState___default___closed__3;
x_11 = l_Lean_Elab_Command_State_messages___default___closed__3;
lean_ctor_set(x_6, 1, x_11);
lean_ctor_set(x_6, 0, x_10);
lean_inc(x_3);
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_4);
lean_ctor_set(x_12, 2, x_5);
lean_ctor_set(x_12, 3, x_4);
lean_ctor_set(x_12, 4, x_6);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
lean_dec(x_6);
x_14 = l_Lean_Elab_Command_State_infoState___default___closed__3;
x_15 = l_Lean_Elab_Command_State_messages___default___closed__3;
x_16 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_13);
lean_inc(x_3);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_4);
lean_ctor_set(x_17, 2, x_5);
lean_ctor_set(x_17, 3, x_4);
lean_ctor_set(x_17, 4, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermState___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermState(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
lean_inc(x_1);
x_17 = l_Std_PersistentArray_mapMAux___at_Lean_Elab_Command_liftTermElabM___spec__3(x_1, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = l_Lean_Elab_InfoTree_substitute(x_14, x_17);
x_19 = l_Lean_Elab_ContextInfo_save___at_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___spec__3(x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_18);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_25 = lean_array_uset(x_16, x_3, x_22);
x_3 = x_24;
x_4 = x_25;
x_11 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapMAux___at_Lean_Elab_Command_liftTermElabM___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_array_get_size(x_11);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
x_15 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__4(x_1, x_13, x_14, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_2, 0, x_17);
lean_ctor_set(x_15, 0, x_2);
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
lean_ctor_set(x_2, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_array_get_size(x_21);
x_23 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_24 = 0;
x_25 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__4(x_1, x_23, x_24, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_2);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_2, 0);
x_33 = lean_array_get_size(x_32);
x_34 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_35 = 0;
x_36 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__5(x_1, x_34, x_35, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_ctor_set(x_2, 0, x_38);
lean_ctor_set(x_36, 0, x_2);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_36);
lean_ctor_set(x_2, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_2, 0);
lean_inc(x_42);
lean_dec(x_2);
x_43 = lean_array_get_size(x_42);
x_44 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_45 = 0;
x_46 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__5(x_1, x_44, x_45, x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_47);
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
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = l_Lean_Elab_InfoTree_substitute(x_14, x_17);
x_19 = l_Lean_Elab_ContextInfo_save___at_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___spec__3(x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_18);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_25 = lean_array_uset(x_16, x_3, x_22);
x_3 = x_24;
x_4 = x_25;
x_11 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapM___at_Lean_Elab_Command_liftTermElabM___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_13 = l_Std_PersistentArray_mapMAux___at_Lean_Elab_Command_liftTermElabM___spec__3(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_12);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__6(x_1, x_17, x_18, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_ctor_set(x_2, 1, x_21);
lean_ctor_set(x_2, 0, x_14);
lean_ctor_set(x_19, 0, x_2);
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
lean_ctor_set(x_2, 1, x_22);
lean_ctor_set(x_2, 0, x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
x_28 = lean_ctor_get_usize(x_2, 4);
x_29 = lean_ctor_get(x_2, 3);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
lean_inc(x_1);
x_30 = l_Std_PersistentArray_mapMAux___at_Lean_Elab_Command_liftTermElabM___spec__3(x_1, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_array_get_size(x_26);
x_34 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_35 = 0;
x_36 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__6(x_1, x_34, x_35, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
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
x_40 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_37);
lean_ctor_set(x_40, 2, x_27);
lean_ctor_set(x_40, 3, x_29);
lean_ctor_set_usize(x_40, 4, x_28);
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
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
lean_inc(x_1);
x_17 = l_Std_PersistentArray_mapMAux___at_Lean_Elab_Command_liftTermElabM___spec__8(x_1, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = l_Lean_Elab_InfoTree_substitute(x_14, x_17);
x_19 = l_Lean_Elab_ContextInfo_save___at_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___spec__3(x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_18);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_25 = lean_array_uset(x_16, x_3, x_22);
x_3 = x_24;
x_4 = x_25;
x_11 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapMAux___at_Lean_Elab_Command_liftTermElabM___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_array_get_size(x_11);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
x_15 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__9(x_1, x_13, x_14, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_2, 0, x_17);
lean_ctor_set(x_15, 0, x_2);
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
lean_ctor_set(x_2, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_array_get_size(x_21);
x_23 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_24 = 0;
x_25 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__9(x_1, x_23, x_24, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_2);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_2, 0);
x_33 = lean_array_get_size(x_32);
x_34 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_35 = 0;
x_36 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__10(x_1, x_34, x_35, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_ctor_set(x_2, 0, x_38);
lean_ctor_set(x_36, 0, x_2);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_36);
lean_ctor_set(x_2, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_2, 0);
lean_inc(x_42);
lean_dec(x_2);
x_43 = lean_array_get_size(x_42);
x_44 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_45 = 0;
x_46 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__10(x_1, x_44, x_45, x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_47);
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
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = l_Lean_Elab_InfoTree_substitute(x_14, x_17);
x_19 = l_Lean_Elab_ContextInfo_save___at_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___spec__3(x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_18);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_25 = lean_array_uset(x_16, x_3, x_22);
x_3 = x_24;
x_4 = x_25;
x_11 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapM___at_Lean_Elab_Command_liftTermElabM___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_13 = l_Std_PersistentArray_mapMAux___at_Lean_Elab_Command_liftTermElabM___spec__8(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_12);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__11(x_1, x_17, x_18, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_ctor_set(x_2, 1, x_21);
lean_ctor_set(x_2, 0, x_14);
lean_ctor_set(x_19, 0, x_2);
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
lean_ctor_set(x_2, 1, x_22);
lean_ctor_set(x_2, 0, x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
x_28 = lean_ctor_get_usize(x_2, 4);
x_29 = lean_ctor_get(x_2, 3);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
lean_inc(x_1);
x_30 = l_Std_PersistentArray_mapMAux___at_Lean_Elab_Command_liftTermElabM___spec__8(x_1, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_array_get_size(x_26);
x_34 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_35 = 0;
x_36 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__11(x_1, x_34, x_35, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
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
x_40 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_37);
lean_ctor_set(x_40, 2, x_27);
lean_ctor_set(x_40, 3, x_29);
lean_ctor_set_usize(x_40, 4, x_28);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at_Lean_Elab_Command_liftTermElabM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 4);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___spec__2___rarg(x_3, x_4, x_5, x_6, x_7, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_21 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_st_ref_get(x_7, x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_get(x_3, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 4);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = l_Std_PersistentArray_mapM___at_Lean_Elab_Command_liftTermElabM___spec__2(x_29, x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_28);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_st_ref_get(x_7, x_33);
lean_dec(x_7);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_st_ref_take(x_3, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 4);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_37, 4);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_38, 1);
lean_dec(x_43);
x_44 = l_Std_PersistentArray_append___rarg(x_19, x_32);
lean_ctor_set(x_38, 1, x_44);
x_45 = lean_st_ref_set(x_3, x_37, x_39);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_22);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_22);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get_uint8(x_38, sizeof(void*)*2);
x_51 = lean_ctor_get(x_38, 0);
lean_inc(x_51);
lean_dec(x_38);
x_52 = l_Std_PersistentArray_append___rarg(x_19, x_32);
x_53 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_50);
lean_ctor_set(x_37, 4, x_53);
x_54 = lean_st_ref_set(x_3, x_37, x_39);
lean_dec(x_3);
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
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_22);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_58 = lean_ctor_get(x_37, 0);
x_59 = lean_ctor_get(x_37, 1);
x_60 = lean_ctor_get(x_37, 2);
x_61 = lean_ctor_get(x_37, 3);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_37);
x_62 = lean_ctor_get_uint8(x_38, sizeof(void*)*2);
x_63 = lean_ctor_get(x_38, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_64 = x_38;
} else {
 lean_dec_ref(x_38);
 x_64 = lean_box(0);
}
x_65 = l_Std_PersistentArray_append___rarg(x_19, x_32);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 1);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set_uint8(x_66, sizeof(void*)*2, x_62);
x_67 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_67, 0, x_58);
lean_ctor_set(x_67, 1, x_59);
lean_ctor_set(x_67, 2, x_60);
lean_ctor_set(x_67, 3, x_61);
lean_ctor_set(x_67, 4, x_66);
x_68 = lean_st_ref_set(x_3, x_67, x_39);
lean_dec(x_3);
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
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_22);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_72 = lean_ctor_get(x_21, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_21, 1);
lean_inc(x_73);
lean_dec(x_21);
x_74 = lean_st_ref_get(x_7, x_73);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_st_ref_get(x_3, x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 4);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
x_81 = l_Std_PersistentArray_mapM___at_Lean_Elab_Command_liftTermElabM___spec__7(x_79, x_80, x_2, x_3, x_4, x_5, x_6, x_7, x_78);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_st_ref_get(x_7, x_83);
lean_dec(x_7);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = lean_st_ref_take(x_3, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_87, 4);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = !lean_is_exclusive(x_87);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_87, 4);
lean_dec(x_91);
x_92 = !lean_is_exclusive(x_88);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = lean_ctor_get(x_88, 1);
lean_dec(x_93);
x_94 = l_Std_PersistentArray_append___rarg(x_19, x_82);
lean_ctor_set(x_88, 1, x_94);
x_95 = lean_st_ref_set(x_3, x_87, x_89);
lean_dec(x_3);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_95, 0);
lean_dec(x_97);
lean_ctor_set_tag(x_95, 1);
lean_ctor_set(x_95, 0, x_72);
return x_95;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_72);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
else
{
uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_100 = lean_ctor_get_uint8(x_88, sizeof(void*)*2);
x_101 = lean_ctor_get(x_88, 0);
lean_inc(x_101);
lean_dec(x_88);
x_102 = l_Std_PersistentArray_append___rarg(x_19, x_82);
x_103 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set_uint8(x_103, sizeof(void*)*2, x_100);
lean_ctor_set(x_87, 4, x_103);
x_104 = lean_st_ref_set(x_3, x_87, x_89);
lean_dec(x_3);
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
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
 lean_ctor_set_tag(x_107, 1);
}
lean_ctor_set(x_107, 0, x_72);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_108 = lean_ctor_get(x_87, 0);
x_109 = lean_ctor_get(x_87, 1);
x_110 = lean_ctor_get(x_87, 2);
x_111 = lean_ctor_get(x_87, 3);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_87);
x_112 = lean_ctor_get_uint8(x_88, sizeof(void*)*2);
x_113 = lean_ctor_get(x_88, 0);
lean_inc(x_113);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_114 = x_88;
} else {
 lean_dec_ref(x_88);
 x_114 = lean_box(0);
}
x_115 = l_Std_PersistentArray_append___rarg(x_19, x_82);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(0, 2, 1);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_115);
lean_ctor_set_uint8(x_116, sizeof(void*)*2, x_112);
x_117 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_117, 0, x_108);
lean_ctor_set(x_117, 1, x_109);
lean_ctor_set(x_117, 2, x_110);
lean_ctor_set(x_117, 3, x_111);
lean_ctor_set(x_117, 4, x_116);
x_118 = lean_st_ref_set(x_3, x_117, x_89);
lean_dec(x_3);
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
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
 lean_ctor_set_tag(x_121, 1);
}
lean_ctor_set(x_121, 0, x_72);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at_Lean_Elab_Command_liftTermElabM___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at_Lean_Elab_Command_liftTermElabM___spec__1___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_withSaveInfoContext___at_Lean_Elab_Command_liftTermElabM___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
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
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
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
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_State_infoState___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_State_infoState___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_State_infoState___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instBEqExpr;
x_2 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instHashableExpr;
x_2 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_State_infoState___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
x_2 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__3;
x_3 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__4;
x_4 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__7;
x_5 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_4);
lean_ctor_set(x_5, 6, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___closed__1;
x_3 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__8;
x_4 = l_Lean_Elab_Command_State_messages___default___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_io_get_num_heartbeats(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 6);
lean_inc(x_15);
x_16 = l_Lean_Elab_Command_instInhabitedScope;
x_17 = l_List_head_x21___rarg(x_16, x_13);
lean_dec(x_13);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftTermElabM___rarg___lambda__1), 8, 1);
lean_closure_set(x_18, 0, x_2);
x_19 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext(x_3, x_7, x_1);
lean_inc(x_7);
x_20 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermState(x_17, x_7);
lean_dec(x_17);
x_21 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkCoreContext(x_3, x_7, x_10);
lean_dec(x_7);
x_22 = l_Lean_Elab_Command_State_traceState___default___closed__1;
x_23 = l_Lean_Elab_Command_liftCoreM___rarg___closed__1;
x_24 = l_Lean_Elab_Command_State_messages___default___closed__3;
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_14);
lean_ctor_set(x_25, 2, x_15);
lean_ctor_set(x_25, 3, x_22);
lean_ctor_set(x_25, 4, x_23);
lean_ctor_set(x_25, 5, x_24);
x_26 = lean_st_mk_ref(x_25, x_11);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_27, x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__9;
x_32 = lean_st_mk_ref(x_31, x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext;
lean_inc(x_27);
lean_inc(x_33);
x_36 = l_Lean_Elab_Term_TermElabM_run___rarg(x_18, x_19, x_20, x_35, x_33, x_21, x_27, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_st_ref_get(x_27, x_38);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_st_ref_get(x_33, x_40);
lean_dec(x_33);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_st_ref_get(x_27, x_42);
lean_dec(x_27);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_37, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_37, 1);
lean_inc(x_47);
lean_dec(x_37);
x_48 = lean_st_ref_take(x_4, x_45);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_44, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_44, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_44, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_44, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_44, 5);
lean_inc(x_55);
lean_dec(x_44);
x_56 = !lean_is_exclusive(x_49);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_57 = lean_ctor_get(x_49, 1);
x_58 = lean_ctor_get(x_49, 7);
x_59 = lean_ctor_get(x_49, 6);
lean_dec(x_59);
x_60 = lean_ctor_get(x_49, 3);
lean_dec(x_60);
x_61 = lean_ctor_get(x_49, 0);
lean_dec(x_61);
x_62 = l_Std_PersistentArray_append___rarg(x_57, x_55);
x_63 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore(x_3, x_62, x_54);
x_64 = !lean_is_exclusive(x_58);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_58, 1);
x_66 = lean_ctor_get(x_47, 4);
lean_inc(x_66);
lean_dec(x_47);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Std_PersistentArray_append___rarg(x_65, x_67);
lean_ctor_set(x_58, 1, x_68);
lean_ctor_set(x_49, 6, x_53);
lean_ctor_set(x_49, 3, x_52);
lean_ctor_set(x_49, 1, x_63);
lean_ctor_set(x_49, 0, x_51);
x_69 = lean_st_ref_set(x_4, x_49, x_50);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
lean_dec(x_71);
x_72 = lean_ctor_get(x_46, 0);
lean_inc(x_72);
lean_dec(x_46);
lean_ctor_set_tag(x_69, 1);
lean_ctor_set(x_69, 0, x_72);
return x_69;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
lean_dec(x_69);
x_74 = lean_ctor_get(x_46, 0);
lean_inc(x_74);
lean_dec(x_46);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_69);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_69, 0);
lean_dec(x_77);
x_78 = lean_ctor_get(x_46, 0);
lean_inc(x_78);
lean_dec(x_46);
lean_ctor_set(x_69, 0, x_78);
return x_69;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_69, 1);
lean_inc(x_79);
lean_dec(x_69);
x_80 = lean_ctor_get(x_46, 0);
lean_inc(x_80);
lean_dec(x_46);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
else
{
uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_82 = lean_ctor_get_uint8(x_58, sizeof(void*)*2);
x_83 = lean_ctor_get(x_58, 0);
x_84 = lean_ctor_get(x_58, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_58);
x_85 = lean_ctor_get(x_47, 4);
lean_inc(x_85);
lean_dec(x_47);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = l_Std_PersistentArray_append___rarg(x_84, x_86);
x_88 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set_uint8(x_88, sizeof(void*)*2, x_82);
lean_ctor_set(x_49, 7, x_88);
lean_ctor_set(x_49, 6, x_53);
lean_ctor_set(x_49, 3, x_52);
lean_ctor_set(x_49, 1, x_63);
lean_ctor_set(x_49, 0, x_51);
x_89 = lean_st_ref_set(x_4, x_49, x_50);
if (lean_obj_tag(x_46) == 0)
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
x_92 = lean_ctor_get(x_46, 0);
lean_inc(x_92);
lean_dec(x_46);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_91;
 lean_ctor_set_tag(x_93, 1);
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_95 = x_89;
} else {
 lean_dec_ref(x_89);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_46, 0);
lean_inc(x_96);
lean_dec(x_46);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_98 = lean_ctor_get(x_49, 1);
x_99 = lean_ctor_get(x_49, 2);
x_100 = lean_ctor_get(x_49, 4);
x_101 = lean_ctor_get(x_49, 5);
x_102 = lean_ctor_get(x_49, 7);
x_103 = lean_ctor_get(x_49, 8);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_49);
x_104 = l_Std_PersistentArray_append___rarg(x_98, x_55);
x_105 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore(x_3, x_104, x_54);
x_106 = lean_ctor_get_uint8(x_102, sizeof(void*)*2);
x_107 = lean_ctor_get(x_102, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_102, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_109 = x_102;
} else {
 lean_dec_ref(x_102);
 x_109 = lean_box(0);
}
x_110 = lean_ctor_get(x_47, 4);
lean_inc(x_110);
lean_dec(x_47);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_112 = l_Std_PersistentArray_append___rarg(x_108, x_111);
if (lean_is_scalar(x_109)) {
 x_113 = lean_alloc_ctor(0, 2, 1);
} else {
 x_113 = x_109;
}
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set_uint8(x_113, sizeof(void*)*2, x_106);
x_114 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_114, 0, x_51);
lean_ctor_set(x_114, 1, x_105);
lean_ctor_set(x_114, 2, x_99);
lean_ctor_set(x_114, 3, x_52);
lean_ctor_set(x_114, 4, x_100);
lean_ctor_set(x_114, 5, x_101);
lean_ctor_set(x_114, 6, x_53);
lean_ctor_set(x_114, 7, x_113);
lean_ctor_set(x_114, 8, x_103);
x_115 = lean_st_ref_set(x_4, x_114, x_50);
if (lean_obj_tag(x_46) == 0)
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
x_118 = lean_ctor_get(x_46, 0);
lean_inc(x_118);
lean_dec(x_46);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_117;
 lean_ctor_set_tag(x_119, 1);
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_115, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_121 = x_115;
} else {
 lean_dec_ref(x_115);
 x_121 = lean_box(0);
}
x_122 = lean_ctor_get(x_46, 0);
lean_inc(x_122);
lean_dec(x_46);
if (lean_is_scalar(x_121)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_121;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_120);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_3);
x_124 = !lean_is_exclusive(x_36);
if (x_124 == 0)
{
return x_36;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_36, 0);
x_126 = lean_ctor_get(x_36, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_36);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_liftTermElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftTermElabM___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__4(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__5(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapMAux___at_Lean_Elab_Command_liftTermElabM___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_PersistentArray_mapMAux___at_Lean_Elab_Command_liftTermElabM___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__6(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapM___at_Lean_Elab_Command_liftTermElabM___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_PersistentArray_mapM___at_Lean_Elab_Command_liftTermElabM___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__9(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__10(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapMAux___at_Lean_Elab_Command_liftTermElabM___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_PersistentArray_mapMAux___at_Lean_Elab_Command_liftTermElabM___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__11(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapM___at_Lean_Elab_Command_liftTermElabM___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_PersistentArray_mapM___at_Lean_Elab_Command_liftTermElabM___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_liftTermElabM___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runTermElabM___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_uget(x_1, x_3);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 2);
lean_inc(x_20);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_11);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_24 = lean_ctor_get(x_16, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_16, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_16, 0);
lean_dec(x_26);
x_27 = lean_array_fget(x_18, x_19);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_19, x_28);
lean_dec(x_19);
lean_ctor_set(x_16, 1, x_29);
x_30 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_17, x_14, x_27);
lean_ctor_set(x_4, 1, x_30);
x_31 = 1;
x_32 = lean_usize_add(x_3, x_31);
x_3 = x_32;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; 
lean_dec(x_16);
x_34 = lean_array_fget(x_18, x_19);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_19, x_35);
lean_dec(x_19);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_18);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_20);
x_38 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_17, x_14, x_34);
lean_ctor_set(x_4, 1, x_38);
lean_ctor_set(x_4, 0, x_37);
x_39 = 1;
x_40 = lean_usize_add(x_3, x_39);
x_3 = x_40;
goto _start;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_42 = lean_ctor_get(x_4, 0);
x_43 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_4);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 2);
lean_inc(x_46);
x_47 = lean_nat_dec_lt(x_45, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_14);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_43);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_11);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; 
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 x_50 = x_42;
} else {
 lean_dec_ref(x_42);
 x_50 = lean_box(0);
}
x_51 = lean_array_fget(x_44, x_45);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_45, x_52);
lean_dec(x_45);
if (lean_is_scalar(x_50)) {
 x_54 = lean_alloc_ctor(0, 3, 0);
} else {
 x_54 = x_50;
}
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_46);
x_55 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_43, x_14, x_51);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = 1;
x_58 = lean_usize_add(x_3, x_57);
x_3 = x_58;
x_4 = x_56;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_runTermElabM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_apply_1(x_1, x_2);
x_12 = l_Lean_Elab_Term_withoutAutoBoundImplicit___rarg(x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Command_runTermElabM___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_runTermElabM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_11, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_array_get_size(x_3);
x_16 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_17 = l_Array_toSubarray___rarg(x_3, x_16, x_15);
x_18 = lean_ctor_get(x_1, 6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_14);
x_20 = lean_array_get_size(x_18);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = 0;
x_23 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runTermElabM___spec__1(x_18, x_21, x_22, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_4);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_4, 5);
lean_dec(x_28);
lean_ctor_set(x_4, 5, x_26);
x_29 = l_Lean_Core_resetMessageLog(x_8, x_9, x_25);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_Command_runTermElabM___rarg___lambda__1___boxed), 10, 1);
lean_closure_set(x_31, 0, x_2);
x_32 = l_Lean_Elab_Command_runTermElabM___rarg___lambda__2___closed__1;
x_33 = l_Lean_Elab_Term_addAutoBoundImplicits_x27___rarg(x_3, x_32, x_31, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_34 = lean_ctor_get(x_4, 0);
x_35 = lean_ctor_get(x_4, 1);
x_36 = lean_ctor_get_uint8(x_4, sizeof(void*)*7);
x_37 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 1);
x_38 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 2);
x_39 = lean_ctor_get(x_4, 2);
x_40 = lean_ctor_get(x_4, 3);
x_41 = lean_ctor_get(x_4, 4);
x_42 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 3);
x_43 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 4);
x_44 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 5);
x_45 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 6);
x_46 = lean_ctor_get(x_4, 6);
x_47 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 7);
lean_inc(x_46);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_4);
x_48 = lean_alloc_ctor(0, 7, 8);
lean_ctor_set(x_48, 0, x_34);
lean_ctor_set(x_48, 1, x_35);
lean_ctor_set(x_48, 2, x_39);
lean_ctor_set(x_48, 3, x_40);
lean_ctor_set(x_48, 4, x_41);
lean_ctor_set(x_48, 5, x_26);
lean_ctor_set(x_48, 6, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*7, x_36);
lean_ctor_set_uint8(x_48, sizeof(void*)*7 + 1, x_37);
lean_ctor_set_uint8(x_48, sizeof(void*)*7 + 2, x_38);
lean_ctor_set_uint8(x_48, sizeof(void*)*7 + 3, x_42);
lean_ctor_set_uint8(x_48, sizeof(void*)*7 + 4, x_43);
lean_ctor_set_uint8(x_48, sizeof(void*)*7 + 5, x_44);
lean_ctor_set_uint8(x_48, sizeof(void*)*7 + 6, x_45);
lean_ctor_set_uint8(x_48, sizeof(void*)*7 + 7, x_47);
x_49 = l_Lean_Core_resetMessageLog(x_8, x_9, x_25);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_alloc_closure((void*)(l_Lean_Elab_Command_runTermElabM___rarg___lambda__1___boxed), 10, 1);
lean_closure_set(x_51, 0, x_2);
x_52 = l_Lean_Elab_Command_runTermElabM___rarg___lambda__2___closed__1;
x_53 = l_Lean_Elab_Term_addAutoBoundImplicits_x27___rarg(x_3, x_52, x_51, x_48, x_5, x_6, x_7, x_8, x_9, x_50);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_12);
if (x_54 == 0)
{
return x_12;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_12, 0);
x_56 = lean_ctor_get(x_12, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_12);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_runTermElabM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l_Lean_Elab_Command_getScope___rarg(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 5);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Command_runTermElabM___rarg___lambda__2___boxed), 10, 2);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_2);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg), 9, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withAutoBoundImplicit___rarg), 8, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = l_Lean_Elab_Command_liftTermElabM___rarg(x_1, x_12, x_3, x_4, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_runTermElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_runTermElabM___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runTermElabM___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runTermElabM___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_runTermElabM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_runTermElabM___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_runTermElabM___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_runTermElabM___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_runTermElabM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_runTermElabM___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_catchExceptions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_withLogging(x_1, x_2, x_3, x_4);
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
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_5, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_liftAttrM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_liftCoreM___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_liftAttrM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_0__Lean_Elab_Command_liftAttrM___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_liftAttrM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_liftAttrM___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getScopes___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getScopes(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getScopes___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getScopes___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_getScopes___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getScopes___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_getScopes(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Command_modifyScope___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_modifyScope___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Elab.Command", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_modifyScope___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Elab.Command.modifyScope", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_modifyScope___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_modifyScope___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Command_modifyScope___closed__1;
x_2 = l_Lean_Elab_Command_modifyScope___closed__2;
x_3 = lean_unsigned_to_nat(428u);
x_4 = lean_unsigned_to_nat(16u);
x_5 = l_Lean_Elab_Command_modifyScope___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_modifyScope(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_6, 2);
lean_dec(x_10);
x_11 = l_Lean_Elab_Command_modifyScope___closed__4;
x_12 = l_panic___at_Lean_Elab_Command_modifyScope___spec__1(x_11);
lean_ctor_set(x_6, 2, x_12);
x_13 = lean_st_ref_set(x_3, x_6, x_8);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
x_22 = lean_ctor_get(x_6, 3);
x_23 = lean_ctor_get(x_6, 4);
x_24 = lean_ctor_get(x_6, 5);
x_25 = lean_ctor_get(x_6, 6);
x_26 = lean_ctor_get(x_6, 7);
x_27 = lean_ctor_get(x_6, 8);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_28 = l_Lean_Elab_Command_modifyScope___closed__4;
x_29 = l_panic___at_Lean_Elab_Command_modifyScope___spec__1(x_28);
x_30 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_21);
lean_ctor_set(x_30, 2, x_29);
lean_ctor_set(x_30, 3, x_22);
lean_ctor_set(x_30, 4, x_23);
lean_ctor_set(x_30, 5, x_24);
lean_ctor_set(x_30, 6, x_25);
lean_ctor_set(x_30, 7, x_26);
lean_ctor_set(x_30, 8, x_27);
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
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_58 = lean_ctor_get(x_6, 0);
x_59 = lean_ctor_get(x_6, 1);
x_60 = lean_ctor_get(x_6, 3);
x_61 = lean_ctor_get(x_6, 4);
x_62 = lean_ctor_get(x_6, 5);
x_63 = lean_ctor_get(x_6, 6);
x_64 = lean_ctor_get(x_6, 7);
x_65 = lean_ctor_get(x_6, 8);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_6);
x_66 = lean_ctor_get(x_7, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_7, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_68 = x_7;
} else {
 lean_dec_ref(x_7);
 x_68 = lean_box(0);
}
x_69 = lean_apply_1(x_1, x_66);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
x_71 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_71, 0, x_58);
lean_ctor_set(x_71, 1, x_59);
lean_ctor_set(x_71, 2, x_70);
lean_ctor_set(x_71, 3, x_60);
lean_ctor_set(x_71, 4, x_61);
lean_ctor_set(x_71, 5, x_62);
lean_ctor_set(x_71, 6, x_63);
lean_ctor_set(x_71, 7, x_64);
lean_ctor_set(x_71, 8, x_65);
x_72 = lean_st_ref_set(x_3, x_71, x_36);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_modifyScope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_modifyScope(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withScope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_apply_3(x_2, x_3, x_4, x_9);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
x_15 = lean_st_ref_take(x_4, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_16, 2);
lean_dec(x_19);
lean_inc(x_13);
x_20 = lean_apply_1(x_1, x_13);
lean_inc(x_14);
lean_ctor_set(x_8, 0, x_20);
lean_ctor_set(x_16, 2, x_8);
x_21 = lean_st_ref_set(x_4, x_16, x_17);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
lean_inc(x_4);
x_23 = lean_apply_3(x_2, x_3, x_4, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_take(x_4, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_27, 2);
lean_dec(x_30);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_13);
lean_ctor_set(x_31, 1, x_14);
lean_ctor_set(x_27, 2, x_31);
x_32 = lean_st_ref_set(x_4, x_27, x_28);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_24);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_37 = lean_ctor_get(x_27, 0);
x_38 = lean_ctor_get(x_27, 1);
x_39 = lean_ctor_get(x_27, 3);
x_40 = lean_ctor_get(x_27, 4);
x_41 = lean_ctor_get(x_27, 5);
x_42 = lean_ctor_get(x_27, 6);
x_43 = lean_ctor_get(x_27, 7);
x_44 = lean_ctor_get(x_27, 8);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_27);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_13);
lean_ctor_set(x_45, 1, x_14);
x_46 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_38);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_46, 3, x_39);
lean_ctor_set(x_46, 4, x_40);
lean_ctor_set(x_46, 5, x_41);
lean_ctor_set(x_46, 6, x_42);
lean_ctor_set(x_46, 7, x_43);
lean_ctor_set(x_46, 8, x_44);
x_47 = lean_st_ref_set(x_4, x_46, x_28);
lean_dec(x_4);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_24);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_51 = lean_ctor_get(x_23, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_23, 1);
lean_inc(x_52);
lean_dec(x_23);
x_53 = lean_st_ref_take(x_4, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = !lean_is_exclusive(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_54, 2);
lean_dec(x_57);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_13);
lean_ctor_set(x_58, 1, x_14);
lean_ctor_set(x_54, 2, x_58);
x_59 = lean_st_ref_set(x_4, x_54, x_55);
lean_dec(x_4);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
lean_ctor_set_tag(x_59, 1);
lean_ctor_set(x_59, 0, x_51);
return x_59;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_51);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_64 = lean_ctor_get(x_54, 0);
x_65 = lean_ctor_get(x_54, 1);
x_66 = lean_ctor_get(x_54, 3);
x_67 = lean_ctor_get(x_54, 4);
x_68 = lean_ctor_get(x_54, 5);
x_69 = lean_ctor_get(x_54, 6);
x_70 = lean_ctor_get(x_54, 7);
x_71 = lean_ctor_get(x_54, 8);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_54);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_13);
lean_ctor_set(x_72, 1, x_14);
x_73 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_65);
lean_ctor_set(x_73, 2, x_72);
lean_ctor_set(x_73, 3, x_66);
lean_ctor_set(x_73, 4, x_67);
lean_ctor_set(x_73, 5, x_68);
lean_ctor_set(x_73, 6, x_69);
lean_ctor_set(x_73, 7, x_70);
lean_ctor_set(x_73, 8, x_71);
x_74 = lean_st_ref_set(x_4, x_73, x_55);
lean_dec(x_4);
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
lean_ctor_set(x_77, 0, x_51);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_78 = lean_ctor_get(x_16, 0);
x_79 = lean_ctor_get(x_16, 1);
x_80 = lean_ctor_get(x_16, 3);
x_81 = lean_ctor_get(x_16, 4);
x_82 = lean_ctor_get(x_16, 5);
x_83 = lean_ctor_get(x_16, 6);
x_84 = lean_ctor_get(x_16, 7);
x_85 = lean_ctor_get(x_16, 8);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_16);
lean_inc(x_13);
x_86 = lean_apply_1(x_1, x_13);
lean_inc(x_14);
lean_ctor_set(x_8, 0, x_86);
x_87 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_87, 0, x_78);
lean_ctor_set(x_87, 1, x_79);
lean_ctor_set(x_87, 2, x_8);
lean_ctor_set(x_87, 3, x_80);
lean_ctor_set(x_87, 4, x_81);
lean_ctor_set(x_87, 5, x_82);
lean_ctor_set(x_87, 6, x_83);
lean_ctor_set(x_87, 7, x_84);
lean_ctor_set(x_87, 8, x_85);
x_88 = lean_st_ref_set(x_4, x_87, x_17);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
lean_inc(x_4);
x_90 = lean_apply_3(x_2, x_3, x_4, x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_st_ref_take(x_4, x_92);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_94, 3);
lean_inc(x_98);
x_99 = lean_ctor_get(x_94, 4);
lean_inc(x_99);
x_100 = lean_ctor_get(x_94, 5);
lean_inc(x_100);
x_101 = lean_ctor_get(x_94, 6);
lean_inc(x_101);
x_102 = lean_ctor_get(x_94, 7);
lean_inc(x_102);
x_103 = lean_ctor_get(x_94, 8);
lean_inc(x_103);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 lean_ctor_release(x_94, 2);
 lean_ctor_release(x_94, 3);
 lean_ctor_release(x_94, 4);
 lean_ctor_release(x_94, 5);
 lean_ctor_release(x_94, 6);
 lean_ctor_release(x_94, 7);
 lean_ctor_release(x_94, 8);
 x_104 = x_94;
} else {
 lean_dec_ref(x_94);
 x_104 = lean_box(0);
}
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_13);
lean_ctor_set(x_105, 1, x_14);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 9, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_96);
lean_ctor_set(x_106, 1, x_97);
lean_ctor_set(x_106, 2, x_105);
lean_ctor_set(x_106, 3, x_98);
lean_ctor_set(x_106, 4, x_99);
lean_ctor_set(x_106, 5, x_100);
lean_ctor_set(x_106, 6, x_101);
lean_ctor_set(x_106, 7, x_102);
lean_ctor_set(x_106, 8, x_103);
x_107 = lean_st_ref_set(x_4, x_106, x_95);
lean_dec(x_4);
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
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_91);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_111 = lean_ctor_get(x_90, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_90, 1);
lean_inc(x_112);
lean_dec(x_90);
x_113 = lean_st_ref_take(x_4, x_112);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 3);
lean_inc(x_118);
x_119 = lean_ctor_get(x_114, 4);
lean_inc(x_119);
x_120 = lean_ctor_get(x_114, 5);
lean_inc(x_120);
x_121 = lean_ctor_get(x_114, 6);
lean_inc(x_121);
x_122 = lean_ctor_get(x_114, 7);
lean_inc(x_122);
x_123 = lean_ctor_get(x_114, 8);
lean_inc(x_123);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 lean_ctor_release(x_114, 2);
 lean_ctor_release(x_114, 3);
 lean_ctor_release(x_114, 4);
 lean_ctor_release(x_114, 5);
 lean_ctor_release(x_114, 6);
 lean_ctor_release(x_114, 7);
 lean_ctor_release(x_114, 8);
 x_124 = x_114;
} else {
 lean_dec_ref(x_114);
 x_124 = lean_box(0);
}
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_13);
lean_ctor_set(x_125, 1, x_14);
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(0, 9, 0);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_116);
lean_ctor_set(x_126, 1, x_117);
lean_ctor_set(x_126, 2, x_125);
lean_ctor_set(x_126, 3, x_118);
lean_ctor_set(x_126, 4, x_119);
lean_ctor_set(x_126, 5, x_120);
lean_ctor_set(x_126, 6, x_121);
lean_ctor_set(x_126, 7, x_122);
lean_ctor_set(x_126, 8, x_123);
x_127 = lean_st_ref_set(x_4, x_126, x_115);
lean_dec(x_4);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_129 = x_127;
} else {
 lean_dec_ref(x_127);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
 lean_ctor_set_tag(x_130, 1);
}
lean_ctor_set(x_130, 0, x_111);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_131 = lean_ctor_get(x_8, 0);
x_132 = lean_ctor_get(x_8, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_8);
x_133 = lean_st_ref_take(x_4, x_11);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_134, 3);
lean_inc(x_138);
x_139 = lean_ctor_get(x_134, 4);
lean_inc(x_139);
x_140 = lean_ctor_get(x_134, 5);
lean_inc(x_140);
x_141 = lean_ctor_get(x_134, 6);
lean_inc(x_141);
x_142 = lean_ctor_get(x_134, 7);
lean_inc(x_142);
x_143 = lean_ctor_get(x_134, 8);
lean_inc(x_143);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 lean_ctor_release(x_134, 2);
 lean_ctor_release(x_134, 3);
 lean_ctor_release(x_134, 4);
 lean_ctor_release(x_134, 5);
 lean_ctor_release(x_134, 6);
 lean_ctor_release(x_134, 7);
 lean_ctor_release(x_134, 8);
 x_144 = x_134;
} else {
 lean_dec_ref(x_134);
 x_144 = lean_box(0);
}
lean_inc(x_131);
x_145 = lean_apply_1(x_1, x_131);
lean_inc(x_132);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_132);
if (lean_is_scalar(x_144)) {
 x_147 = lean_alloc_ctor(0, 9, 0);
} else {
 x_147 = x_144;
}
lean_ctor_set(x_147, 0, x_136);
lean_ctor_set(x_147, 1, x_137);
lean_ctor_set(x_147, 2, x_146);
lean_ctor_set(x_147, 3, x_138);
lean_ctor_set(x_147, 4, x_139);
lean_ctor_set(x_147, 5, x_140);
lean_ctor_set(x_147, 6, x_141);
lean_ctor_set(x_147, 7, x_142);
lean_ctor_set(x_147, 8, x_143);
x_148 = lean_st_ref_set(x_4, x_147, x_135);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec(x_148);
lean_inc(x_4);
x_150 = lean_apply_3(x_2, x_3, x_4, x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_st_ref_take(x_4, x_152);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_ctor_get(x_154, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_154, 3);
lean_inc(x_158);
x_159 = lean_ctor_get(x_154, 4);
lean_inc(x_159);
x_160 = lean_ctor_get(x_154, 5);
lean_inc(x_160);
x_161 = lean_ctor_get(x_154, 6);
lean_inc(x_161);
x_162 = lean_ctor_get(x_154, 7);
lean_inc(x_162);
x_163 = lean_ctor_get(x_154, 8);
lean_inc(x_163);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 lean_ctor_release(x_154, 2);
 lean_ctor_release(x_154, 3);
 lean_ctor_release(x_154, 4);
 lean_ctor_release(x_154, 5);
 lean_ctor_release(x_154, 6);
 lean_ctor_release(x_154, 7);
 lean_ctor_release(x_154, 8);
 x_164 = x_154;
} else {
 lean_dec_ref(x_154);
 x_164 = lean_box(0);
}
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_131);
lean_ctor_set(x_165, 1, x_132);
if (lean_is_scalar(x_164)) {
 x_166 = lean_alloc_ctor(0, 9, 0);
} else {
 x_166 = x_164;
}
lean_ctor_set(x_166, 0, x_156);
lean_ctor_set(x_166, 1, x_157);
lean_ctor_set(x_166, 2, x_165);
lean_ctor_set(x_166, 3, x_158);
lean_ctor_set(x_166, 4, x_159);
lean_ctor_set(x_166, 5, x_160);
lean_ctor_set(x_166, 6, x_161);
lean_ctor_set(x_166, 7, x_162);
lean_ctor_set(x_166, 8, x_163);
x_167 = lean_st_ref_set(x_4, x_166, x_155);
lean_dec(x_4);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_169 = x_167;
} else {
 lean_dec_ref(x_167);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_151);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_171 = lean_ctor_get(x_150, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_150, 1);
lean_inc(x_172);
lean_dec(x_150);
x_173 = lean_st_ref_take(x_4, x_172);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_ctor_get(x_174, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_174, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_174, 3);
lean_inc(x_178);
x_179 = lean_ctor_get(x_174, 4);
lean_inc(x_179);
x_180 = lean_ctor_get(x_174, 5);
lean_inc(x_180);
x_181 = lean_ctor_get(x_174, 6);
lean_inc(x_181);
x_182 = lean_ctor_get(x_174, 7);
lean_inc(x_182);
x_183 = lean_ctor_get(x_174, 8);
lean_inc(x_183);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 lean_ctor_release(x_174, 2);
 lean_ctor_release(x_174, 3);
 lean_ctor_release(x_174, 4);
 lean_ctor_release(x_174, 5);
 lean_ctor_release(x_174, 6);
 lean_ctor_release(x_174, 7);
 lean_ctor_release(x_174, 8);
 x_184 = x_174;
} else {
 lean_dec_ref(x_174);
 x_184 = lean_box(0);
}
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_131);
lean_ctor_set(x_185, 1, x_132);
if (lean_is_scalar(x_184)) {
 x_186 = lean_alloc_ctor(0, 9, 0);
} else {
 x_186 = x_184;
}
lean_ctor_set(x_186, 0, x_176);
lean_ctor_set(x_186, 1, x_177);
lean_ctor_set(x_186, 2, x_185);
lean_ctor_set(x_186, 3, x_178);
lean_ctor_set(x_186, 4, x_179);
lean_ctor_set(x_186, 5, x_180);
lean_ctor_set(x_186, 6, x_181);
lean_ctor_set(x_186, 7, x_182);
lean_ctor_set(x_186, 8, x_183);
x_187 = lean_st_ref_set(x_4, x_186, x_175);
lean_dec(x_4);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_189 = x_187;
} else {
 lean_dec_ref(x_187);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 2, 0);
} else {
 x_190 = x_189;
 lean_ctor_set_tag(x_190, 1);
}
lean_ctor_set(x_190, 0, x_171);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withScope___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getLevelNames___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Elab_Command_getScope___rarg(x_1, x_2);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getLevelNames(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getLevelNames___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getLevelNames___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_getLevelNames___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_getLevelNames___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_getLevelNames(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("a universe level named '", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' has already been declared", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__2;
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__4;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_9, x_2, x_3, x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addUnivLevel___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 4);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_2, 4, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get(x_2, 4);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_10);
x_15 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_7);
lean_ctor_set(x_15, 2, x_8);
lean_ctor_set(x_15, 3, x_9);
lean_ctor_set(x_15, 4, x_14);
lean_ctor_set(x_15, 5, x_11);
lean_ctor_set(x_15, 6, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*7, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addUnivLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_dec(x_1);
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
x_15 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_5, x_13);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Command_addUnivLevel___lambda__1), 2, 1);
lean_closure_set(x_16, 0, x_5);
x_17 = l_Lean_Elab_Command_modifyScope(x_16, x_2, x_3, x_14);
lean_dec(x_2);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1(x_5, x_2, x_3, x_14);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_2, 2);
x_22 = lean_ctor_get(x_2, 3);
x_23 = lean_ctor_get(x_2, 4);
x_24 = lean_ctor_get(x_2, 5);
x_25 = lean_ctor_get(x_2, 7);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_2);
x_26 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set(x_26, 4, x_23);
lean_ctor_set(x_26, 5, x_24);
lean_ctor_set(x_26, 6, x_9);
lean_ctor_set(x_26, 7, x_25);
x_27 = l_Lean_Elab_Command_getLevelNames___rarg(x_3, x_8);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_5, x_28);
lean_dec(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_Command_addUnivLevel___lambda__1), 2, 1);
lean_closure_set(x_31, 0, x_5);
x_32 = l_Lean_Elab_Command_modifyScope(x_31, x_26, x_3, x_29);
lean_dec(x_26);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1(x_5, x_26, x_3, x_29);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addUnivLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_addUnivLevel(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_11, x_8, x_2, x_3, x_12);
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
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid declaration name '", 26);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("', structure '", 14);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' has field '", 13);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_6);
x_12 = lean_array_uget(x_3, x_5);
lean_inc(x_12);
x_13 = l_Lean_Name_append(x_2, x_12);
x_14 = lean_name_eq(x_13, x_1);
lean_dec(x_13);
if (x_14 == 0)
{
size_t x_15; size_t x_16; lean_object* x_17; 
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_5, x_15);
x_17 = lean_box(0);
x_5 = x_16;
x_6 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_19 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_19, 0, x_1);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__2;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__4;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_24, 0, x_2);
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__6;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_28, 0, x_12);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__8;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_31, x_7, x_8, x_9);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___at_Lean_Elab_Command_expandDeclId___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_st_ref_get(x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_5);
x_11 = l_Lean_isStructure(x_10, x_5);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_6);
x_13 = lean_st_ref_get(x_3, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
lean_inc(x_5);
x_18 = l_Lean_getStructureFieldsFlattened(x_16, x_5, x_17);
x_19 = lean_array_get_size(x_18);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = 0;
x_22 = lean_box(0);
x_23 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5(x_1, x_5, x_18, x_20, x_21, x_22, x_2, x_3, x_15);
lean_dec(x_18);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_6, 0);
x_33 = lean_ctor_get(x_6, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_6);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_5);
x_35 = l_Lean_isStructure(x_34, x_5);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; 
x_38 = lean_st_ref_get(x_3, x_33);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = 1;
lean_inc(x_5);
x_43 = l_Lean_getStructureFieldsFlattened(x_41, x_5, x_42);
x_44 = lean_array_get_size(x_43);
x_45 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_46 = 0;
x_47 = lean_box(0);
x_48 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5(x_1, x_5, x_43, x_45, x_46, x_47, x_2, x_3, x_40);
lean_dec(x_43);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_48, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_54 = x_48;
} else {
 lean_dec_ref(x_48);
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
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_2);
lean_dec(x_1);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_4);
return x_57;
}
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("a non-private declaration '", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_inc(x_10);
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
x_15 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__1___closed__2;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__4;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_18, x_4, x_5, x_6);
return x_19;
}
}
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("a private declaration '", 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_7 = l_Lean_mkPrivateName(x_2, x_1);
lean_inc(x_2);
x_8 = l_Lean_Environment_contains(x_2, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__1(x_1, x_2, x_9, x_4, x_5, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_2);
x_11 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__2___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__4;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_15, x_4, x_5, x_6);
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
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("private declaration '", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_inc(x_1);
lean_inc(x_8);
x_9 = l_Lean_Environment_contains(x_8, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__2(x_1, x_8, x_10, x_2, x_3, x_7);
lean_dec(x_3);
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
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__8;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__4;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_17, x_2, x_3, x_7);
lean_dec(x_3);
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
x_25 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___closed__2;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__4;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_28, x_2, x_3, x_7);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_Elab_Command_expandDeclId___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_17 = lean_ctor_get(x_6, 1);
x_18 = lean_ctor_get(x_6, 2);
x_19 = lean_ctor_get(x_6, 3);
x_20 = lean_ctor_get(x_6, 4);
x_21 = lean_ctor_get(x_6, 5);
x_22 = lean_ctor_get(x_6, 6);
x_23 = lean_ctor_get(x_6, 7);
x_24 = lean_ctor_get(x_6, 8);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_25 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_17);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_19);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_25, 5, x_21);
lean_ctor_set(x_25, 6, x_22);
lean_ctor_set(x_25, 7, x_23);
lean_ctor_set(x_25, 8, x_24);
x_26 = lean_st_ref_set(x_3, x_25, x_7);
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
}
}
static lean_object* _init_l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_protectedExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__6(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_6; 
lean_inc(x_2);
x_6 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7(x_2, x_3, x_4, x_5);
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
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7(x_2, x_3, x_4, x_5);
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
x_21 = l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__6___closed__1;
lean_inc(x_2);
x_22 = l_Lean_TagDeclarationExtension_tag(x_21, x_20, x_2);
x_23 = l_Lean_setEnv___at_Lean_Elab_Command_expandDeclId___spec__8(x_22, x_3, x_4, x_19);
lean_dec(x_4);
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
lean_dec(x_4);
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
x_37 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7(x_36, x_3, x_4, x_34);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_11, x_8, x_2, x_3, x_12);
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
static lean_object* _init_l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("protected declarations must be in a namespace", 45);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_6);
lean_inc(x_1);
x_9 = l_Lean_Elab_checkIfShadowingStructureField___at_Lean_Elab_Command_expandDeclId___spec__3(x_1, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_dec(x_2);
lean_inc(x_7);
lean_inc(x_6);
x_12 = l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__6(x_11, x_1, x_6, x_7, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_box(x_11);
if (lean_obj_tag(x_13) == 1)
{
if (lean_obj_tag(x_3) == 1)
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_6);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_box(0);
x_18 = lean_name_mk_string(x_17, x_16);
x_19 = l_Lean_Name_append(x_18, x_4);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_12, 0, x_20);
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_box(0);
x_25 = lean_name_mk_string(x_24, x_23);
x_26 = l_Lean_Name_append(x_25, x_4);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_22);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
lean_dec(x_3);
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_dec(x_12);
x_30 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1___closed__2;
x_31 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__9(x_30, x_6, x_7, x_29);
lean_dec(x_7);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_12);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_12, 0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_4);
lean_ctor_set(x_12, 0, x_34);
return x_12;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_12, 0);
x_36 = lean_ctor_get(x_12, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_12);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_4);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_12);
if (x_39 == 0)
{
return x_12;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_12, 0);
x_41 = lean_ctor_get(x_12, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_12);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_9);
if (x_43 == 0)
{
return x_9;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_9, 0);
x_45 = lean_ctor_get(x_9, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_9);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
lean_dec(x_8);
if (x_5 == 0)
{
uint8_t x_43; 
x_43 = 0;
x_12 = x_43;
goto block_42;
}
else
{
uint8_t x_44; 
x_44 = 1;
x_12 = x_44;
goto block_42;
}
block_42:
{
lean_object* x_13; 
if (x_12 == 0)
{
lean_object* x_34; 
lean_dec(x_4);
lean_inc(x_7);
x_34 = l_Lean_Name_append(x_6, x_7);
x_13 = x_34;
goto block_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_box(0);
lean_inc(x_2);
x_36 = l_Lean_Name_replacePrefix(x_2, x_3, x_35);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_4, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 3);
lean_inc(x_39);
lean_dec(x_4);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_37);
lean_ctor_set(x_40, 2, x_38);
lean_ctor_set(x_40, 3, x_39);
x_41 = l_Lean_MacroScopesView_review(x_40);
x_13 = x_41;
goto block_33;
}
block_33:
{
if (x_12 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1(x_13, x_1, x_6, x_7, x_14, x_9, x_10, x_11);
return x_15;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_box(0);
x_19 = lean_name_mk_string(x_18, x_17);
x_20 = l_Lean_Name_replacePrefix(x_16, x_3, x_18);
lean_dec(x_3);
x_21 = lean_box(0);
x_22 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1(x_13, x_1, x_20, x_19, x_21, x_9, x_10, x_11);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_1);
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_2);
x_24 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__2;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__8;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_27, x_9, x_10, x_11);
lean_dec(x_10);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("atomic identifier expected '", 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
lean_dec(x_8);
x_12 = l_Lean_Name_isAtomic(x_2);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Elab_isFreshInstanceName(x_2);
if (x_13 == 0)
{
if (x_5 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_14, 0, x_7);
x_15 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__3___closed__2;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__8;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_18, x_9, x_10, x_11);
lean_dec(x_10);
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
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_24, x_9, x_10, x_11);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_26, x_9, x_10, x_11);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_28, x_9, x_10, x_11);
return x_29;
}
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_root_", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid declaration name `_root_`, `_root_` is a prefix used to refer to the 'root' namespace", 93);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
lean_inc(x_3);
x_7 = l_Lean_extractMacroScopes(x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___closed__2;
x_10 = l_Lean_Name_isPrefixOf(x_9, x_8);
x_11 = lean_name_eq(x_8, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__3(x_2, x_8, x_9, x_7, x_10, x_1, x_3, x_12, x_4, x_5, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___closed__4;
x_15 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_14, x_4, x_5, x_6);
lean_dec(x_5);
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
}
}
static lean_object* _init_l_Lean_addDocString___at_Lean_Elab_Command_expandDeclId___spec__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_DocString_0__Lean_docStringExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___at_Lean_Elab_Command_expandDeclId___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_st_ref_take(x_4, x_5);
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
x_11 = l_Lean_addDocString___at_Lean_Elab_Command_expandDeclId___spec__11___closed__1;
x_12 = l_Lean_MapDeclarationExtension_insert___rarg(x_11, x_10, x_1, x_2);
lean_ctor_set(x_7, 0, x_12);
x_13 = lean_st_ref_set(x_4, x_7, x_8);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
x_22 = lean_ctor_get(x_7, 2);
x_23 = lean_ctor_get(x_7, 3);
x_24 = lean_ctor_get(x_7, 4);
x_25 = lean_ctor_get(x_7, 5);
x_26 = lean_ctor_get(x_7, 6);
x_27 = lean_ctor_get(x_7, 7);
x_28 = lean_ctor_get(x_7, 8);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
x_29 = l_Lean_addDocString___at_Lean_Elab_Command_expandDeclId___spec__11___closed__1;
x_30 = l_Lean_MapDeclarationExtension_insert___rarg(x_29, x_20, x_1, x_2);
x_31 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_21);
lean_ctor_set(x_31, 2, x_22);
lean_ctor_set(x_31, 3, x_23);
lean_ctor_set(x_31, 4, x_24);
lean_ctor_set(x_31, 5, x_25);
lean_ctor_set(x_31, 6, x_26);
lean_ctor_set(x_31, 7, x_27);
lean_ctor_set(x_31, 8, x_28);
x_32 = lean_st_ref_set(x_4, x_31, x_8);
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
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___at_Lean_Elab_Command_expandDeclId___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_addDocString___at_Lean_Elab_Command_expandDeclId___spec__11(x_1, x_8, x_3, x_4, x_5);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_11, x_8, x_2, x_3, x_12);
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_expandDeclId___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__2;
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__4;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__13(x_9, x_2, x_3, x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_expandDeclId___spec__14(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_uget(x_1, x_2);
x_10 = l_Lean_Syntax_getId(x_9);
x_11 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_10, x_4);
if (x_11 == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; 
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_4);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_4);
x_16 = l_Lean_Elab_Command_getRef(x_5, x_6, x_7);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_replaceRef(x_9, x_17);
lean_dec(x_17);
lean_dec(x_9);
x_20 = !lean_is_exclusive(x_5);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_5, 6);
lean_dec(x_21);
lean_ctor_set(x_5, 6, x_19);
x_22 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_expandDeclId___spec__12(x_10, x_5, x_6, x_18);
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get(x_5, 0);
x_28 = lean_ctor_get(x_5, 1);
x_29 = lean_ctor_get(x_5, 2);
x_30 = lean_ctor_get(x_5, 3);
x_31 = lean_ctor_get(x_5, 4);
x_32 = lean_ctor_get(x_5, 5);
x_33 = lean_ctor_get(x_5, 7);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_5);
x_34 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_28);
lean_ctor_set(x_34, 2, x_29);
lean_ctor_set(x_34, 3, x_30);
lean_ctor_set(x_34, 4, x_31);
lean_ctor_set(x_34, 5, x_32);
lean_ctor_set(x_34, 6, x_19);
lean_ctor_set(x_34, 7, x_33);
x_35 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_expandDeclId___spec__12(x_10, x_34, x_6, x_18);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
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
lean_object* x_40; 
lean_dec(x_5);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_7);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = l_Lean_Elab_Command_getRef(x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_replaceRef(x_1, x_10);
lean_dec(x_10);
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get(x_6, 2);
x_16 = lean_ctor_get(x_6, 3);
x_17 = lean_ctor_get(x_6, 4);
x_18 = lean_ctor_get(x_6, 5);
x_19 = lean_ctor_get(x_6, 7);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_20 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_16);
lean_ctor_set(x_20, 4, x_17);
lean_ctor_set(x_20, 5, x_18);
lean_ctor_set(x_20, 6, x_12);
lean_ctor_set(x_20, 7, x_19);
lean_inc(x_7);
lean_inc(x_3);
x_21 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2(x_2, x_3, x_4, x_20, x_7, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
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
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
lean_dec(x_3);
lean_inc(x_24);
x_27 = l_Lean_addDocString_x27___at_Lean_Elab_Command_expandDeclId___spec__10(x_24, x_26, x_6, x_7, x_23);
lean_dec(x_7);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_5);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_32, 2, x_5);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_7);
lean_dec(x_5);
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
}
static lean_object* _init_l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Elab_Command_Scope_varDecls___default___closed__1;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_10, x_12);
lean_dec(x_10);
x_14 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
lean_object* x_35; 
lean_dec(x_15);
lean_dec(x_14);
x_35 = l_Lean_Elab_Command_Scope_varDecls___default___closed__1;
x_18 = x_35;
goto block_34;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_15, x_15);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_15);
lean_dec(x_14);
x_37 = l_Lean_Elab_Command_Scope_varDecls___default___closed__1;
x_18 = x_37;
goto block_34;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_40 = l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___closed__1;
x_41 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(x_14, x_38, x_39, x_40);
lean_dec(x_14);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_18 = x_42;
goto block_34;
}
}
block_34:
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_array_get_size(x_18);
x_20 = lean_nat_dec_lt(x_16, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_18);
x_21 = l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___lambda__1(x_3, x_1, x_4, x_9, x_2, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_3);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_19, x_19);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_18);
x_23 = l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___lambda__1(x_3, x_1, x_4, x_9, x_2, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_3);
return x_23;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_19);
lean_dec(x_19);
lean_inc(x_5);
x_26 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_expandDeclId___spec__14(x_18, x_24, x_25, x_2, x_5, x_6, x_7);
lean_dec(x_18);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___lambda__1(x_3, x_1, x_4, x_9, x_27, x_5, x_6, x_28);
lean_dec(x_5);
lean_dec(x_3);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
}
}
else
{
lean_object* x_43; 
lean_dec(x_10);
x_43 = l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___lambda__1(x_3, x_1, x_4, x_9, x_2, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_3);
return x_43;
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__15___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("', there is a section variable with the same name", 49);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__15___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__15___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__15(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_5);
x_11 = lean_array_uget(x_2, x_4);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_name_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_usize_add(x_4, x_14);
x_16 = lean_box(0);
x_4 = x_15;
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_inc(x_12);
x_18 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_18, 0, x_12);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__15___closed__2;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_22, x_6, x_7, x_8);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__16(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_5);
x_11 = lean_array_uget(x_2, x_4);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_name_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_usize_add(x_4, x_14);
x_16 = lean_box(0);
x_4 = x_15;
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_inc(x_12);
x_18 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_18, 0, x_12);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__15___closed__2;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_22, x_6, x_7, x_8);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__17(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_5);
x_11 = lean_array_uget(x_2, x_4);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_name_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_usize_add(x_4, x_14);
x_16 = lean_box(0);
x_4 = x_15;
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_inc(x_12);
x_18 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_18, 0, x_12);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__15___closed__2;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_22, x_6, x_7, x_8);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_expandDeclId___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_Scope_varDecls___default___closed__1;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static size_t _init_l_Lean_Elab_Command_expandDeclId___closed__2() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lean_Elab_Command_expandDeclId___closed__1;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandDeclId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l_Lean_Elab_Command_getScope___rarg(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_Command_getLevelNames___rarg(x_4, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1(x_9, x_11, x_1, x_2, x_3, x_4, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; size_t x_23; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Command_getScope___rarg(x_4, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 5);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_get_size(x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_lt(x_21, x_20);
x_23 = 0;
if (x_22 == 0)
{
lean_object* x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_20);
lean_dec(x_19);
x_24 = l_Lean_Elab_Command_Scope_varDecls___default___closed__1;
x_25 = l_Lean_Elab_Command_expandDeclId___closed__2;
x_26 = lean_box(0);
x_27 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__15(x_14, x_24, x_25, x_23, x_26, x_3, x_4, x_18);
lean_dec(x_4);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_14);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_14);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_14);
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
x_36 = lean_nat_dec_le(x_20, x_20);
if (x_36 == 0)
{
lean_object* x_37; size_t x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_20);
lean_dec(x_19);
x_37 = l_Lean_Elab_Command_Scope_varDecls___default___closed__1;
x_38 = l_Lean_Elab_Command_expandDeclId___closed__2;
x_39 = lean_box(0);
x_40 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__16(x_14, x_37, x_38, x_23, x_39, x_3, x_4, x_18);
lean_dec(x_4);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_14);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_14);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_14);
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_40, 0);
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_40);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
size_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_50 = l_Lean_Elab_Command_Scope_varDecls___default___closed__1;
x_51 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___spec__2(x_19, x_23, x_49, x_50);
lean_dec(x_19);
x_52 = lean_array_get_size(x_51);
x_53 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_54 = lean_box(0);
x_55 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__17(x_14, x_51, x_53, x_23, x_54, x_3, x_4, x_18);
lean_dec(x_4);
lean_dec(x_51);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
lean_ctor_set(x_55, 0, x_14);
return x_55;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_14);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_14);
x_60 = !lean_is_exclusive(x_55);
if (x_60 == 0)
{
return x_55;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_55, 0);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_55);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_4);
lean_dec(x_3);
x_64 = !lean_is_exclusive(x_13);
if (x_64 == 0)
{
return x_13;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_13, 0);
x_66 = lean_ctor_get(x_13, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_13);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkIfShadowingStructureField___at_Lean_Elab_Command_expandDeclId___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_checkIfShadowingStructureField___at_Lean_Elab_Command_expandDeclId___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_Elab_Command_expandDeclId___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_setEnv___at_Lean_Elab_Command_expandDeclId___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__6(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__9(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__3(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___at_Lean_Elab_Command_expandDeclId___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addDocString___at_Lean_Elab_Command_expandDeclId___spec__11(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___at_Lean_Elab_Command_expandDeclId___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addDocString_x27___at_Lean_Elab_Command_expandDeclId___spec__10(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__13(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_expandDeclId___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_expandDeclId___spec__12(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_expandDeclId___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_expandDeclId___spec__14(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__15(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__16(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__17(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ResolveName(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Reduce(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Term(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Cache(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Binders(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_DeclModifiers(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_InfoTree(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_SetOption(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ResolveName(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Reduce(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Cache(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclModifiers(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_InfoTree(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SetOption(builtin, lean_io_mk_world());
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
l_Lean_Elab_Command_Scope_varDecls___default___closed__1 = _init_l_Lean_Elab_Command_Scope_varDecls___default___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_Scope_varDecls___default___closed__1);
l_Lean_Elab_Command_Scope_varDecls___default = _init_l_Lean_Elab_Command_Scope_varDecls___default();
lean_mark_persistent(l_Lean_Elab_Command_Scope_varDecls___default);
l_Lean_Elab_Command_Scope_varUIds___default = _init_l_Lean_Elab_Command_Scope_varUIds___default();
lean_mark_persistent(l_Lean_Elab_Command_Scope_varUIds___default);
l_Lean_Elab_Command_Scope_isNoncomputable___default = _init_l_Lean_Elab_Command_Scope_isNoncomputable___default();
l_Lean_Elab_Command_instInhabitedScope___closed__1 = _init_l_Lean_Elab_Command_instInhabitedScope___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedScope___closed__1);
l_Lean_Elab_Command_instInhabitedScope___closed__2 = _init_l_Lean_Elab_Command_instInhabitedScope___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedScope___closed__2);
l_Lean_Elab_Command_instInhabitedScope = _init_l_Lean_Elab_Command_instInhabitedScope();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedScope);
l_Lean_Elab_Command_State_messages___default___closed__1 = _init_l_Lean_Elab_Command_State_messages___default___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_State_messages___default___closed__1);
l_Lean_Elab_Command_State_messages___default___closed__2 = _init_l_Lean_Elab_Command_State_messages___default___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_State_messages___default___closed__2);
l_Lean_Elab_Command_State_messages___default___closed__3 = _init_l_Lean_Elab_Command_State_messages___default___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_State_messages___default___closed__3);
l_Lean_Elab_Command_State_messages___default = _init_l_Lean_Elab_Command_State_messages___default();
lean_mark_persistent(l_Lean_Elab_Command_State_messages___default);
l_Lean_Elab_Command_State_scopes___default___closed__1 = _init_l_Lean_Elab_Command_State_scopes___default___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_State_scopes___default___closed__1);
l_Lean_Elab_Command_State_scopes___default = _init_l_Lean_Elab_Command_State_scopes___default();
lean_mark_persistent(l_Lean_Elab_Command_State_scopes___default);
l_Lean_Elab_Command_State_nextMacroScope___default___closed__1 = _init_l_Lean_Elab_Command_State_nextMacroScope___default___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_State_nextMacroScope___default___closed__1);
l_Lean_Elab_Command_State_nextMacroScope___default = _init_l_Lean_Elab_Command_State_nextMacroScope___default();
lean_mark_persistent(l_Lean_Elab_Command_State_nextMacroScope___default);
l_Lean_Elab_Command_State_nextInstIdx___default = _init_l_Lean_Elab_Command_State_nextInstIdx___default();
lean_mark_persistent(l_Lean_Elab_Command_State_nextInstIdx___default);
l_Lean_Elab_Command_State_ngen___default___closed__1 = _init_l_Lean_Elab_Command_State_ngen___default___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_State_ngen___default___closed__1);
l_Lean_Elab_Command_State_ngen___default___closed__2 = _init_l_Lean_Elab_Command_State_ngen___default___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_State_ngen___default___closed__2);
l_Lean_Elab_Command_State_ngen___default___closed__3 = _init_l_Lean_Elab_Command_State_ngen___default___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_State_ngen___default___closed__3);
l_Lean_Elab_Command_State_ngen___default = _init_l_Lean_Elab_Command_State_ngen___default();
lean_mark_persistent(l_Lean_Elab_Command_State_ngen___default);
l_Lean_Elab_Command_State_infoState___default___closed__1 = _init_l_Lean_Elab_Command_State_infoState___default___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_State_infoState___default___closed__1);
l_Lean_Elab_Command_State_infoState___default___closed__2 = _init_l_Lean_Elab_Command_State_infoState___default___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_State_infoState___default___closed__2);
l_Lean_Elab_Command_State_infoState___default___closed__3 = _init_l_Lean_Elab_Command_State_infoState___default___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_State_infoState___default___closed__3);
l_Lean_Elab_Command_State_infoState___default___closed__4 = _init_l_Lean_Elab_Command_State_infoState___default___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_State_infoState___default___closed__4);
l_Lean_Elab_Command_State_infoState___default = _init_l_Lean_Elab_Command_State_infoState___default();
lean_mark_persistent(l_Lean_Elab_Command_State_infoState___default);
l_Lean_Elab_Command_State_traceState___default___closed__1 = _init_l_Lean_Elab_Command_State_traceState___default___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_State_traceState___default___closed__1);
l_Lean_Elab_Command_State_traceState___default = _init_l_Lean_Elab_Command_State_traceState___default();
lean_mark_persistent(l_Lean_Elab_Command_State_traceState___default);
l_Lean_Elab_Command_instInhabitedState___closed__1 = _init_l_Lean_Elab_Command_instInhabitedState___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedState___closed__1);
l_Lean_Elab_Command_instInhabitedState___closed__2 = _init_l_Lean_Elab_Command_instInhabitedState___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedState___closed__2);
l_Lean_Elab_Command_instInhabitedState___closed__3 = _init_l_Lean_Elab_Command_instInhabitedState___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedState___closed__3);
l_Lean_Elab_Command_instInhabitedState___closed__4 = _init_l_Lean_Elab_Command_instInhabitedState___closed__4();
l_Lean_Elab_Command_instInhabitedState___closed__5 = _init_l_Lean_Elab_Command_instInhabitedState___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedState___closed__5);
l_Lean_Elab_Command_instInhabitedState___closed__6 = _init_l_Lean_Elab_Command_instInhabitedState___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedState___closed__6);
l_Lean_Elab_Command_instInhabitedState___closed__7 = _init_l_Lean_Elab_Command_instInhabitedState___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedState___closed__7);
l_Lean_Elab_Command_instInhabitedState___closed__8 = _init_l_Lean_Elab_Command_instInhabitedState___closed__8();
l_Lean_Elab_Command_instInhabitedState___closed__9 = _init_l_Lean_Elab_Command_instInhabitedState___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedState___closed__9);
l_Lean_Elab_Command_instInhabitedState___closed__10 = _init_l_Lean_Elab_Command_instInhabitedState___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedState___closed__10);
l_Lean_Elab_Command_instInhabitedState___closed__11 = _init_l_Lean_Elab_Command_instInhabitedState___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedState___closed__11);
l_Lean_Elab_Command_instInhabitedState___closed__12 = _init_l_Lean_Elab_Command_instInhabitedState___closed__12();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedState___closed__12);
l_Lean_Elab_Command_instInhabitedState___closed__13 = _init_l_Lean_Elab_Command_instInhabitedState___closed__13();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedState___closed__13);
l_Lean_Elab_Command_instInhabitedState = _init_l_Lean_Elab_Command_instInhabitedState();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedState);
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
l_Lean_Elab_Command_instMonadCommandElabM___closed__1 = _init_l_Lean_Elab_Command_instMonadCommandElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instMonadCommandElabM___closed__1);
l_Lean_Elab_Command_instMonadCommandElabM___closed__2 = _init_l_Lean_Elab_Command_instMonadCommandElabM___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_instMonadCommandElabM___closed__2);
l_Lean_Elab_Command_instMonadCommandElabM___closed__3 = _init_l_Lean_Elab_Command_instMonadCommandElabM___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_instMonadCommandElabM___closed__3);
l_Lean_Elab_Command_instMonadCommandElabM___closed__4 = _init_l_Lean_Elab_Command_instMonadCommandElabM___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_instMonadCommandElabM___closed__4);
l_Lean_Elab_Command_instMonadCommandElabM___closed__5 = _init_l_Lean_Elab_Command_instMonadCommandElabM___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_instMonadCommandElabM___closed__5);
l_Lean_Elab_Command_instMonadCommandElabM___closed__6 = _init_l_Lean_Elab_Command_instMonadCommandElabM___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_instMonadCommandElabM___closed__6);
l_Lean_Elab_Command_instMonadCommandElabM = _init_l_Lean_Elab_Command_instMonadCommandElabM();
lean_mark_persistent(l_Lean_Elab_Command_instMonadCommandElabM);
l_Lean_Elab_Command_mkState___closed__1 = _init_l_Lean_Elab_Command_mkState___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_mkState___closed__1);
if (builtin) {res = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_417_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Command_lintersRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Command_lintersRef);
lean_dec_ref(res);
}l_Lean_Elab_Command_addLinter___closed__1 = _init_l_Lean_Elab_Command_addLinter___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_addLinter___closed__1);
l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__1 = _init_l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__1);
l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__2 = _init_l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__2);
l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__3 = _init_l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__3);
l_Lean_Elab_Command_instMonadInfoTreeCommandElabM = _init_l_Lean_Elab_Command_instMonadInfoTreeCommandElabM();
lean_mark_persistent(l_Lean_Elab_Command_instMonadInfoTreeCommandElabM);
l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__1 = _init_l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__1);
l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__2 = _init_l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__2);
l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__3 = _init_l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__3);
l_Lean_Elab_Command_instMonadEnvCommandElabM = _init_l_Lean_Elab_Command_instMonadEnvCommandElabM();
lean_mark_persistent(l_Lean_Elab_Command_instMonadEnvCommandElabM);
l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___closed__1 = _init_l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___closed__1();
lean_mark_persistent(l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___closed__1);
l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___closed__2 = _init_l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___closed__2();
lean_mark_persistent(l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___closed__2);
l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___closed__3 = _init_l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___closed__3();
lean_mark_persistent(l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___closed__3);
l_Lean_Elab_Command_instAddMessageContextCommandElabM___closed__1 = _init_l_Lean_Elab_Command_instAddMessageContextCommandElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instAddMessageContextCommandElabM___closed__1);
l_Lean_Elab_Command_instAddMessageContextCommandElabM = _init_l_Lean_Elab_Command_instAddMessageContextCommandElabM();
lean_mark_persistent(l_Lean_Elab_Command_instAddMessageContextCommandElabM);
l_Lean_Elab_Command_instMonadRefCommandElabM___closed__1 = _init_l_Lean_Elab_Command_instMonadRefCommandElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instMonadRefCommandElabM___closed__1);
l_Lean_Elab_Command_instMonadRefCommandElabM___closed__2 = _init_l_Lean_Elab_Command_instMonadRefCommandElabM___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_instMonadRefCommandElabM___closed__2);
l_Lean_Elab_Command_instMonadRefCommandElabM___closed__3 = _init_l_Lean_Elab_Command_instMonadRefCommandElabM___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_instMonadRefCommandElabM___closed__3);
l_Lean_Elab_Command_instMonadRefCommandElabM = _init_l_Lean_Elab_Command_instMonadRefCommandElabM();
lean_mark_persistent(l_Lean_Elab_Command_instMonadRefCommandElabM);
l_Lean_Elab_Command_instMonadTraceCommandElabM___closed__1 = _init_l_Lean_Elab_Command_instMonadTraceCommandElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instMonadTraceCommandElabM___closed__1);
l_Lean_Elab_Command_instMonadTraceCommandElabM___closed__2 = _init_l_Lean_Elab_Command_instMonadTraceCommandElabM___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_instMonadTraceCommandElabM___closed__2);
l_Lean_Elab_Command_instMonadTraceCommandElabM___closed__3 = _init_l_Lean_Elab_Command_instMonadTraceCommandElabM___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_instMonadTraceCommandElabM___closed__3);
l_Lean_Elab_Command_instMonadTraceCommandElabM = _init_l_Lean_Elab_Command_instMonadTraceCommandElabM();
lean_mark_persistent(l_Lean_Elab_Command_instMonadTraceCommandElabM);
l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__1 = _init_l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__1();
lean_mark_persistent(l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__1);
l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__2 = _init_l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__2();
lean_mark_persistent(l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__2);
l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__3 = _init_l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__3();
lean_mark_persistent(l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__3);
l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__4 = _init_l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__4();
lean_mark_persistent(l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__4);
l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__5 = _init_l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__5();
lean_mark_persistent(l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___closed__5);
l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__2___closed__1 = _init_l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__2___closed__1();
lean_mark_persistent(l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessagesCore___spec__2___closed__1);
l_Lean_Elab_Command_liftCoreM___rarg___closed__1 = _init_l_Lean_Elab_Command_liftCoreM___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_liftCoreM___rarg___closed__1);
l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__1 = _init_l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__1);
l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__2 = _init_l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__2);
l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__3 = _init_l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__3);
l_Lean_Elab_Command_instMonadResolveNameCommandElabM = _init_l_Lean_Elab_Command_instMonadResolveNameCommandElabM();
lean_mark_persistent(l_Lean_Elab_Command_instMonadResolveNameCommandElabM);
l_Lean_Elab_Command_instMonadLogCommandElabM___closed__1 = _init_l_Lean_Elab_Command_instMonadLogCommandElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instMonadLogCommandElabM___closed__1);
l_Lean_Elab_Command_instMonadLogCommandElabM___closed__2 = _init_l_Lean_Elab_Command_instMonadLogCommandElabM___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_instMonadLogCommandElabM___closed__2);
l_Lean_Elab_Command_instMonadLogCommandElabM___closed__3 = _init_l_Lean_Elab_Command_instMonadLogCommandElabM___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_instMonadLogCommandElabM___closed__3);
l_Lean_Elab_Command_instMonadLogCommandElabM___closed__4 = _init_l_Lean_Elab_Command_instMonadLogCommandElabM___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_instMonadLogCommandElabM___closed__4);
l_Lean_Elab_Command_instMonadLogCommandElabM___closed__5 = _init_l_Lean_Elab_Command_instMonadLogCommandElabM___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_instMonadLogCommandElabM___closed__5);
l_Lean_Elab_Command_instMonadLogCommandElabM = _init_l_Lean_Elab_Command_instMonadLogCommandElabM();
lean_mark_persistent(l_Lean_Elab_Command_instMonadLogCommandElabM);
l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__1 = _init_l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__1();
lean_mark_persistent(l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__1);
l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__2 = _init_l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__2();
lean_mark_persistent(l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__2);
l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__3 = _init_l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__3();
lean_mark_persistent(l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4___closed__1);
l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__1 = _init_l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__1);
l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__2 = _init_l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__2);
l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__3 = _init_l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__3);
l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__4 = _init_l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__4);
l_Lean_Elab_Command_instMonadQuotationCommandElabM = _init_l_Lean_Elab_Command_instMonadQuotationCommandElabM();
lean_mark_persistent(l_Lean_Elab_Command_instMonadQuotationCommandElabM);
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
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__10 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__10);
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__11 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__11);
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__12 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__12();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__12);
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__13 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__13();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__13);
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__14 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__14();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__14);
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__15 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__15();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__15);
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__16 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__16();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__16);
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__17 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__17();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__17);
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__18 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__18();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__18);
if (builtin) {res = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1748_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Command_commandElabAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Command_commandElabAttribute);
lean_dec_ref(res);
}l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__1 = _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__1);
l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__2 = _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__2);
l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__3 = _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__3);
l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__4 = _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__4);
l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__5 = _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___closed__5);
l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__1 = _init_l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__1);
l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__2 = _init_l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__2);
l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__3 = _init_l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__3);
l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM = _init_l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM();
lean_mark_persistent(l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM);
l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__1 = _init_l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__1);
l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__2 = _init_l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__2);
l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__3 = _init_l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__3);
l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__4 = _init_l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__4);
l_Lean_Elab_Command_instMonadRecDepthCommandElabM = _init_l_Lean_Elab_Command_instMonadRecDepthCommandElabM();
lean_mark_persistent(l_Lean_Elab_Command_instMonadRecDepthCommandElabM);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123____closed__1 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123____closed__1();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123____closed__1);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123____closed__2 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123____closed__2();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123____closed__2);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123____closed__3 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123____closed__3();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123____closed__3);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123____closed__4 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123____closed__4();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123____closed__4);
if (builtin) {res = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2123_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Command_showPartialSyntaxErrors = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Command_showPartialSyntaxErrors);
lean_dec_ref(res);
}l_Lean_Elab_Command_withLogging___closed__1 = _init_l_Lean_Elab_Command_withLogging___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_withLogging___closed__1);
l_Lean_Elab_Command_withLogging___closed__2 = _init_l_Lean_Elab_Command_withLogging___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_withLogging___closed__2);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2240____closed__1 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2240____closed__1();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2240____closed__1);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2240____closed__2 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2240____closed__2();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2240____closed__2);
res = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2240_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__1___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__1___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__1___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__1___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__1___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Command_elabCommand___spec__1___closed__2);
l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__1 = _init_l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__1();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__1);
l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__2 = _init_l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__2);
l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__3 = _init_l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__3();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__3);
l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__4 = _init_l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__4();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__4);
l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__5 = _init_l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__5();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__5);
l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__6 = _init_l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__6();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__4___closed__6);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___rarg___closed__1);
l_Lean_Elab_Command_elabCommand___lambda__3___closed__1 = _init_l_Lean_Elab_Command_elabCommand___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabCommand___lambda__3___closed__1);
l_Lean_Elab_Command_elabCommand___lambda__3___closed__2 = _init_l_Lean_Elab_Command_elabCommand___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabCommand___lambda__3___closed__2);
l_Lean_Elab_Command_elabCommand___lambda__3___closed__3 = _init_l_Lean_Elab_Command_elabCommand___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabCommand___lambda__3___closed__3);
l_Lean_Elab_Command_elabCommand___lambda__3___closed__4 = _init_l_Lean_Elab_Command_elabCommand___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabCommand___lambda__3___closed__4);
l_Lean_Elab_Command_elabCommand___lambda__3___closed__5 = _init_l_Lean_Elab_Command_elabCommand___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabCommand___lambda__3___closed__5);
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
l_Lean_Elab_Command_elabCommand___boxed__const__1 = _init_l_Lean_Elab_Command_elabCommand___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_Command_elabCommand___boxed__const__1);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2500____closed__1 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2500____closed__1();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2500____closed__1);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2500____closed__2 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2500____closed__2();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2500____closed__2);
res = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_2500_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabCommandTopLevel___spec__5___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabCommandTopLevel___spec__5___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabCommandTopLevel___spec__5___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__2);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__3 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__3);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__4 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__4();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__4);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__5 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__5();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommandTopLevel___spec__11___lambda__1___closed__5);
l_Lean_Elab_Command_elabCommandTopLevel___lambda__2___closed__1 = _init_l_Lean_Elab_Command_elabCommandTopLevel___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabCommandTopLevel___lambda__2___closed__1);
l_Lean_Elab_Command_instInhabitedCommandElabM___closed__1 = _init_l_Lean_Elab_Command_instInhabitedCommandElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedCommandElabM___closed__1);
l_Lean_Elab_Command_instInhabitedCommandElabM___closed__2 = _init_l_Lean_Elab_Command_instInhabitedCommandElabM___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedCommandElabM___closed__2);
l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__1 = _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__1);
l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__2 = _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__2);
l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext = _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext();
lean_mark_persistent(l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext);
l_Lean_Elab_Command_getBracketedBinderIds___closed__1 = _init_l_Lean_Elab_Command_getBracketedBinderIds___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_getBracketedBinderIds___closed__1);
l_Lean_Elab_Command_getBracketedBinderIds___closed__2 = _init_l_Lean_Elab_Command_getBracketedBinderIds___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_getBracketedBinderIds___closed__2);
l_Lean_Elab_Command_getBracketedBinderIds___closed__3 = _init_l_Lean_Elab_Command_getBracketedBinderIds___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_getBracketedBinderIds___closed__3);
l_Lean_Elab_Command_getBracketedBinderIds___closed__4 = _init_l_Lean_Elab_Command_getBracketedBinderIds___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_getBracketedBinderIds___closed__4);
l_Lean_Elab_Command_getBracketedBinderIds___closed__5 = _init_l_Lean_Elab_Command_getBracketedBinderIds___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_getBracketedBinderIds___closed__5);
l_Lean_Elab_Command_getBracketedBinderIds___closed__6 = _init_l_Lean_Elab_Command_getBracketedBinderIds___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_getBracketedBinderIds___closed__6);
l_Lean_Elab_Command_getBracketedBinderIds___closed__7 = _init_l_Lean_Elab_Command_getBracketedBinderIds___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_getBracketedBinderIds___closed__7);
l_Lean_Elab_Command_getBracketedBinderIds___closed__8 = _init_l_Lean_Elab_Command_getBracketedBinderIds___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_getBracketedBinderIds___closed__8);
l_Lean_Elab_Command_getBracketedBinderIds___closed__9 = _init_l_Lean_Elab_Command_getBracketedBinderIds___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_getBracketedBinderIds___closed__9);
l_Lean_Elab_Command_getBracketedBinderIds___closed__10 = _init_l_Lean_Elab_Command_getBracketedBinderIds___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_getBracketedBinderIds___closed__10);
l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___closed__1 = _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___closed__1);
l_Lean_Elab_Command_liftTermElabM___rarg___closed__1 = _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_liftTermElabM___rarg___closed__1);
l_Lean_Elab_Command_liftTermElabM___rarg___closed__2 = _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_liftTermElabM___rarg___closed__2);
l_Lean_Elab_Command_liftTermElabM___rarg___closed__3 = _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_liftTermElabM___rarg___closed__3);
l_Lean_Elab_Command_liftTermElabM___rarg___closed__4 = _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_liftTermElabM___rarg___closed__4);
l_Lean_Elab_Command_liftTermElabM___rarg___closed__5 = _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_liftTermElabM___rarg___closed__5);
l_Lean_Elab_Command_liftTermElabM___rarg___closed__6 = _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_liftTermElabM___rarg___closed__6);
l_Lean_Elab_Command_liftTermElabM___rarg___closed__7 = _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_liftTermElabM___rarg___closed__7);
l_Lean_Elab_Command_liftTermElabM___rarg___closed__8 = _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_liftTermElabM___rarg___closed__8);
l_Lean_Elab_Command_liftTermElabM___rarg___closed__9 = _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_liftTermElabM___rarg___closed__9);
l_Lean_Elab_Command_runTermElabM___rarg___lambda__2___closed__1 = _init_l_Lean_Elab_Command_runTermElabM___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_runTermElabM___rarg___lambda__2___closed__1);
l_Lean_Elab_Command_modifyScope___closed__1 = _init_l_Lean_Elab_Command_modifyScope___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_modifyScope___closed__1);
l_Lean_Elab_Command_modifyScope___closed__2 = _init_l_Lean_Elab_Command_modifyScope___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_modifyScope___closed__2);
l_Lean_Elab_Command_modifyScope___closed__3 = _init_l_Lean_Elab_Command_modifyScope___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_modifyScope___closed__3);
l_Lean_Elab_Command_modifyScope___closed__4 = _init_l_Lean_Elab_Command_modifyScope___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_modifyScope___closed__4);
l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__1 = _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__1();
lean_mark_persistent(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__1);
l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__2 = _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__2();
lean_mark_persistent(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__2);
l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__3 = _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__3();
lean_mark_persistent(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__3);
l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__4 = _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__4();
lean_mark_persistent(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__1___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__6);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__7 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__7);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__8 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__5___closed__8);
l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__1___closed__1 = _init_l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__1___closed__1);
l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__1___closed__2 = _init_l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__1___closed__2);
l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__2___closed__1 = _init_l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__2___closed__1);
l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__2___closed__2 = _init_l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___lambda__2___closed__2);
l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___closed__1 = _init_l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___closed__1();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___closed__1);
l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___closed__2 = _init_l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___closed__2();
lean_mark_persistent(l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__7___closed__2);
l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__6___closed__1 = _init_l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__6___closed__1();
lean_mark_persistent(l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__6___closed__1);
l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1___closed__1 = _init_l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1___closed__1);
l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1___closed__2 = _init_l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1___closed__2);
l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__3___closed__1 = _init_l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__3___closed__1);
l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__3___closed__2 = _init_l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__3___closed__2);
l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___closed__1 = _init_l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___closed__1();
lean_mark_persistent(l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___closed__1);
l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___closed__2 = _init_l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___closed__2();
lean_mark_persistent(l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___closed__2);
l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___closed__3 = _init_l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___closed__3();
lean_mark_persistent(l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___closed__3);
l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___closed__4 = _init_l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___closed__4();
lean_mark_persistent(l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___closed__4);
l_Lean_addDocString___at_Lean_Elab_Command_expandDeclId___spec__11___closed__1 = _init_l_Lean_addDocString___at_Lean_Elab_Command_expandDeclId___spec__11___closed__1();
lean_mark_persistent(l_Lean_addDocString___at_Lean_Elab_Command_expandDeclId___spec__11___closed__1);
l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___closed__1 = _init_l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___closed__1();
lean_mark_persistent(l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__15___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__15___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__15___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__15___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__15___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_expandDeclId___spec__15___closed__2);
l_Lean_Elab_Command_expandDeclId___closed__1 = _init_l_Lean_Elab_Command_expandDeclId___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_expandDeclId___closed__1);
l_Lean_Elab_Command_expandDeclId___closed__2 = _init_l_Lean_Elab_Command_expandDeclId___closed__2();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
