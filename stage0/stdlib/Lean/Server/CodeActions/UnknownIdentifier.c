// Lean compiler output
// Module: Lean.Server.CodeActions.UnknownIdentifier
// Imports: Lean.Server.FileWorker.Utils Lean.Data.Lsp.Internal Lean.Server.Requests Lean.Server.Completion.CompletionInfoSelection Lean.Server.CodeActions.Basic Lean.Server.Completion.CompletionUtils
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
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0___boxed(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitAllUnknownIdentifierRanges_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitAllUnknownIdentifierRanges_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_utf8RangeToLspRange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_computeQueries_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___closed__0;
static lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__8;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(size_t, size_t, lean_object*);
lean_object* l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Server_FileWorker_collectOpenNamespaces_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__2;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__1;
uint8_t l_Array_isEmpty___redArg(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
static lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__2___closed__0;
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___lam__0(uint8_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__2;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_computeQueries_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectOpenNamespaces(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
static lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__3;
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitAllUnknownIdentifierRanges_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0(lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__6;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__6;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object*);
lean_object* l_Lean_Server_RequestM_findCmdParsedSnap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_computeQueries_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_checkCancelled(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_computeQueries_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_computeQueries_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_ofPosition(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__7;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__4;
lean_object* l_Lean_Server_RequestCancellationToken_requestCancellationTask(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_String_Range_overlaps(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
static lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__4;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__5;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(size_t, size_t, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg___closed__0;
lean_object* l_Lean_Server_RequestM_findCmdDataAtPos(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__2;
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0;
lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_collectOpenNamespaces___closed__0;
static lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1;
static lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__5;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_toJsonCodeActionResolveData____x40_Lean_Server_CodeActions_Basic___hyg_70_(lean_object*);
static lean_object* l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitAllUnknownIdentifierRanges_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg___lam__0(uint8_t, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__0;
lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_runLintersAsync_spec__2(size_t, size_t, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitAllUnknownIdentifierRanges_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__1(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__7;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3700_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeQueries(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1;
lean_object* l_Lean_Server_ServerTask_waitAny___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__0;
lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_runLintersAsync_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitAllUnknownIdentifierRanges_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_collectOpenNamespaces_spec__0(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(lean_object*);
static lean_object* l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg___lam__0___closed__1;
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_Name_getString_x21(lean_object*);
static lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__1;
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_4019_(lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Server_Completion_getDotCompletionTypeNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__0;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_computeQueries_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0___boxed(lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__1;
static lean_object* l_Lean_Server_FileWorker_computeQueries___closed__0;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitAllUnknownIdentifierRanges_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Server_Completion_minimizeGlobalIdentifierInContext(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeQueries___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__9;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Server_RequestError_ofIoError(lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_collectOpenNamespaces_spec__0___closed__0;
static lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_8, x_7);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_9, 1);
x_15 = lean_ctor_get(x_9, 0);
lean_dec(x_15);
x_16 = lean_array_uget(x_6, x_8);
lean_inc(x_14);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(x_1, x_2, x_3, x_4, x_16, x_14, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_5);
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
lean_ctor_set(x_9, 0, x_21);
lean_ctor_set(x_17, 0, x_9);
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
lean_ctor_set(x_9, 0, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_9);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
lean_dec(x_14);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
lean_dec(x_18);
lean_inc(x_5);
lean_ctor_set(x_9, 1, x_26);
lean_ctor_set(x_9, 0, x_5);
x_27 = 1;
x_28 = lean_usize_add(x_8, x_27);
x_8 = x_28;
x_10 = x_25;
goto _start;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_dec(x_9);
x_31 = lean_array_uget(x_6, x_8);
lean_inc(x_30);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_32 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(x_1, x_2, x_3, x_4, x_31, x_30, x_10);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_30);
if (lean_is_scalar(x_35)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_35;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; 
lean_dec(x_30);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_dec(x_32);
x_40 = lean_ctor_get(x_33, 0);
lean_inc(x_40);
lean_dec(x_33);
lean_inc(x_5);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_5);
lean_ctor_set(x_41, 1, x_40);
x_42 = 1;
x_43 = lean_usize_add(x_8, x_42);
x_8 = x_43;
x_9 = x_41;
x_10 = x_39;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_5, x_4);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_6, 1);
x_12 = lean_ctor_get(x_6, 0);
lean_dec(x_12);
x_13 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_11);
x_14 = lean_apply_3(x_1, x_13, x_11, x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_6, 0, x_18);
lean_ctor_set(x_14, 0, x_6);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_6, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
lean_dec(x_11);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_23);
lean_ctor_set(x_6, 0, x_2);
x_24 = 1;
x_25 = lean_usize_add(x_5, x_24);
x_5 = x_25;
x_7 = x_22;
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
lean_dec(x_6);
x_28 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_27);
x_29 = lean_apply_3(x_1, x_28, x_27, x_7);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_27);
if (lean_is_scalar(x_32)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_32;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; 
lean_dec(x_27);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_dec(x_29);
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
lean_dec(x_30);
lean_inc(x_2);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_37);
x_39 = 1;
x_40 = lean_usize_add(x_5, x_39);
x_5 = x_40;
x_6 = x_38;
x_7 = x_36;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 4);
lean_inc(x_9);
lean_dec(x_4);
x_10 = l_Lean_MessageData_hasTag(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_inc(x_7);
lean_inc(x_2);
x_13 = l_Lean_FileMap_ofPosition(x_2, x_7);
if (lean_obj_tag(x_8) == 0)
{
x_14 = x_7;
goto block_23;
}
else
{
lean_object* x_24; 
lean_dec(x_7);
x_24 = lean_ctor_get(x_8, 0);
lean_inc(x_24);
lean_dec(x_8);
x_14 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = l_Lean_FileMap_ofPosition(x_2, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_String_Range_overlaps(x_16, x_3, x_10, x_10);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_5);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_6);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_array_push(x_5, x_16);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_6);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
x_12 = lean_array_size(x_9);
x_13 = 0;
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_10, x_9, x_12, x_13, x_11, x_7);
lean_dec(x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_19);
lean_ctor_set(x_14, 0, x_5);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_21);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_15);
lean_free_object(x_5);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_14, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
lean_dec(x_16);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_5, 0);
lean_inc(x_29);
lean_dec(x_5);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_6);
x_32 = lean_array_size(x_29);
x_33 = 0;
x_34 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_30, x_29, x_32, x_33, x_31, x_7);
lean_dec(x_29);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_38 = x_34;
} else {
 lean_dec_ref(x_34);
 x_38 = lean_box(0);
}
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_35);
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_43 = x_34;
} else {
 lean_dec_ref(x_34);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_36, 0);
lean_inc(x_44);
lean_dec(x_36);
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
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_5);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_5, 0);
x_48 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0___lam__0___boxed), 6, 3);
lean_closure_set(x_48, 0, x_1);
lean_closure_set(x_48, 1, x_2);
lean_closure_set(x_48, 2, x_3);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_6);
x_51 = lean_array_size(x_47);
x_52 = 0;
x_53 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(x_48, x_49, x_47, x_51, x_52, x_50, x_7);
lean_dec(x_47);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_53, 0);
lean_dec(x_57);
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
lean_ctor_set(x_5, 0, x_58);
lean_ctor_set(x_53, 0, x_5);
return x_53;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
lean_dec(x_53);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_dec(x_54);
lean_ctor_set(x_5, 0, x_60);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_5);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_54);
lean_free_object(x_5);
x_62 = !lean_is_exclusive(x_53);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_53, 0);
lean_dec(x_63);
x_64 = lean_ctor_get(x_55, 0);
lean_inc(x_64);
lean_dec(x_55);
lean_ctor_set(x_53, 0, x_64);
return x_53;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_53, 1);
lean_inc(x_65);
lean_dec(x_53);
x_66 = lean_ctor_get(x_55, 0);
lean_inc(x_66);
lean_dec(x_55);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; size_t x_72; size_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_68 = lean_ctor_get(x_5, 0);
lean_inc(x_68);
lean_dec(x_5);
x_69 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0___lam__0___boxed), 6, 3);
lean_closure_set(x_69, 0, x_1);
lean_closure_set(x_69, 1, x_2);
lean_closure_set(x_69, 2, x_3);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_6);
x_72 = lean_array_size(x_68);
x_73 = 0;
x_74 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(x_69, x_70, x_68, x_72, x_73, x_71, x_7);
lean_dec(x_68);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_78 = x_74;
} else {
 lean_dec_ref(x_74);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_dec(x_75);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
if (lean_is_scalar(x_78)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_78;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_77);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_75);
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
x_84 = lean_ctor_get(x_76, 0);
lean_inc(x_84);
lean_dec(x_76);
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
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_5, x_4);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_6, 1);
x_12 = lean_ctor_get(x_6, 0);
lean_dec(x_12);
x_13 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_11);
x_14 = lean_apply_3(x_1, x_13, x_11, x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_6, 0, x_15);
lean_ctor_set(x_14, 0, x_6);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_6, 0, x_20);
lean_ctor_set(x_14, 0, x_6);
return x_14;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_23 = x_15;
} else {
 lean_dec_ref(x_15);
 x_23 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(1, 1, 0);
} else {
 x_24 = x_23;
 lean_ctor_set_tag(x_24, 1);
}
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_6, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
lean_dec(x_11);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_ctor_get(x_15, 0);
lean_inc(x_27);
lean_dec(x_15);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_27);
lean_ctor_set(x_6, 0, x_2);
x_28 = 1;
x_29 = lean_usize_add(x_5, x_28);
x_5 = x_29;
x_7 = x_26;
goto _start;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_6, 1);
lean_inc(x_31);
lean_dec(x_6);
x_32 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_31);
x_33 = lean_apply_3(x_1, x_32, x_31, x_7);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_2);
lean_dec(x_1);
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
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_38 = x_34;
} else {
 lean_dec_ref(x_34);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 1, 0);
} else {
 x_39 = x_38;
 lean_ctor_set_tag(x_39, 1);
}
lean_ctor_set(x_39, 0, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_31);
if (lean_is_scalar(x_36)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_36;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_35);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; 
lean_dec(x_31);
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_dec(x_33);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
lean_dec(x_34);
lean_inc(x_2);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_2);
lean_ctor_set(x_44, 1, x_43);
x_45 = 1;
x_46 = lean_usize_add(x_5, x_45);
x_5 = x_46;
x_6 = x_44;
x_7 = x_42;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 4);
lean_inc(x_9);
lean_dec(x_4);
x_10 = l_Lean_MessageData_hasTag(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_inc(x_7);
lean_inc(x_2);
x_13 = l_Lean_FileMap_ofPosition(x_2, x_7);
if (lean_obj_tag(x_8) == 0)
{
x_14 = x_7;
goto block_23;
}
else
{
lean_object* x_24; 
lean_dec(x_7);
x_24 = lean_ctor_get(x_8, 0);
lean_inc(x_24);
lean_dec(x_8);
x_14 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = l_Lean_FileMap_ofPosition(x_2, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_String_Range_overlaps(x_16, x_3, x_10, x_10);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_5);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_6);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_array_push(x_5, x_16);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_6);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(x_1, x_2, x_3, x_5, x_7, x_5, x_6);
lean_dec(x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0___lam__0___boxed), 6, 3);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_3);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_array_size(x_8);
x_23 = 0;
x_24 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__3(x_19, x_20, x_8, x_22, x_23, x_21, x_17);
lean_dec(x_8);
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
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_unknownIdentifierMessageTag;
x_3 = lean_name_eq(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_inc(x_1);
x_5 = l_Lean_Server_RequestM_findCmdParsedSnap(x_1, x_4);
x_6 = lean_task_get_own(x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_dec(x_9);
x_10 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0;
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_10);
return x_2;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_11 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_ctor_get(x_14, 3);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 3);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go(x_17);
lean_inc(x_2);
x_19 = l_Lean_Language_SnapshotTree_collectMessagesInRange(x_18, x_2);
x_20 = lean_task_get_own(x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0___boxed), 1, 0);
x_23 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0;
x_24 = l_Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0(x_22, x_16, x_2, x_21, x_23, x_3);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_12 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_12, x_9, x_10);
lean_dec(x_6);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__3(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitAllUnknownIdentifierRanges_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_7, x_6);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_8, 1);
x_14 = lean_ctor_get(x_8, 0);
lean_dec(x_14);
x_15 = lean_array_uget(x_5, x_7);
lean_inc(x_13);
lean_inc(x_2);
lean_inc(x_1);
x_16 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitAllUnknownIdentifierRanges_spec__0_spec__0(x_1, x_2, x_3, x_15, x_13, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_8, 0, x_20);
lean_ctor_set(x_16, 0, x_8);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_8, 0, x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
lean_dec(x_13);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_25);
lean_ctor_set(x_8, 0, x_4);
x_26 = 1;
x_27 = lean_usize_add(x_7, x_26);
x_7 = x_27;
x_9 = x_24;
goto _start;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_dec(x_8);
x_30 = lean_array_uget(x_5, x_7);
lean_inc(x_29);
lean_inc(x_2);
lean_inc(x_1);
x_31 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitAllUnknownIdentifierRanges_spec__0_spec__0(x_1, x_2, x_3, x_30, x_29, x_9);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_29);
if (lean_is_scalar(x_34)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_34;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; 
lean_dec(x_29);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_dec(x_31);
x_39 = lean_ctor_get(x_32, 0);
lean_inc(x_39);
lean_dec(x_32);
lean_inc(x_4);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_39);
x_41 = 1;
x_42 = lean_usize_add(x_7, x_41);
x_7 = x_42;
x_8 = x_40;
x_9 = x_38;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitAllUnknownIdentifierRanges_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 4);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l_Lean_MessageData_hasTag(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_6);
lean_inc(x_2);
x_12 = l_Lean_FileMap_ofPosition(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
x_13 = x_6;
goto block_19;
}
else
{
lean_object* x_20; 
lean_dec(x_6);
x_20 = lean_ctor_get(x_7, 0);
lean_inc(x_20);
lean_dec(x_7);
x_13 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Lean_FileMap_ofPosition(x_2, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_array_push(x_4, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitAllUnknownIdentifierRanges_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_array_size(x_8);
x_12 = 0;
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitAllUnknownIdentifierRanges_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_9, x_8, x_11, x_12, x_10, x_6);
lean_dec(x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_18);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_14);
lean_free_object(x_4);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_13, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_24);
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_4, 0);
lean_inc(x_28);
lean_dec(x_4);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_5);
x_31 = lean_array_size(x_28);
x_32 = 0;
x_33 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitAllUnknownIdentifierRanges_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_29, x_28, x_31, x_32, x_30, x_6);
lean_dec(x_28);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_37 = x_33;
} else {
 lean_dec_ref(x_33);
 x_37 = lean_box(0);
}
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
if (lean_is_scalar(x_37)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_37;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_34);
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_42 = x_33;
} else {
 lean_dec_ref(x_33);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_35, 0);
lean_inc(x_43);
lean_dec(x_35);
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
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_4);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_46 = lean_ctor_get(x_4, 0);
x_47 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitAllUnknownIdentifierRanges_spec__0_spec__0___lam__0), 5, 2);
lean_closure_set(x_47, 0, x_1);
lean_closure_set(x_47, 1, x_2);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_5);
x_50 = lean_array_size(x_46);
x_51 = 0;
x_52 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(x_47, x_48, x_46, x_50, x_51, x_49, x_6);
lean_dec(x_46);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_52, 0);
lean_dec(x_56);
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_dec(x_53);
lean_ctor_set(x_4, 0, x_57);
lean_ctor_set(x_52, 0, x_4);
return x_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_dec(x_52);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
lean_dec(x_53);
lean_ctor_set(x_4, 0, x_59);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_4);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec(x_53);
lean_free_object(x_4);
x_61 = !lean_is_exclusive(x_52);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_52, 0);
lean_dec(x_62);
x_63 = lean_ctor_get(x_54, 0);
lean_inc(x_63);
lean_dec(x_54);
lean_ctor_set(x_52, 0, x_63);
return x_52;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_52, 1);
lean_inc(x_64);
lean_dec(x_52);
x_65 = lean_ctor_get(x_54, 0);
lean_inc(x_65);
lean_dec(x_54);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; size_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_67 = lean_ctor_get(x_4, 0);
lean_inc(x_67);
lean_dec(x_4);
x_68 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitAllUnknownIdentifierRanges_spec__0_spec__0___lam__0), 5, 2);
lean_closure_set(x_68, 0, x_1);
lean_closure_set(x_68, 1, x_2);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_5);
x_71 = lean_array_size(x_67);
x_72 = 0;
x_73 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(x_68, x_69, x_67, x_71, x_72, x_70, x_6);
lean_dec(x_67);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
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
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
if (lean_is_scalar(x_77)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_77;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_76);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_74);
x_81 = lean_ctor_get(x_73, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_82 = x_73;
} else {
 lean_dec_ref(x_73);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_75, 0);
lean_inc(x_83);
lean_dec(x_75);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitAllUnknownIdentifierRanges_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 4);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l_Lean_MessageData_hasTag(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_6);
lean_inc(x_2);
x_12 = l_Lean_FileMap_ofPosition(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
x_13 = x_6;
goto block_19;
}
else
{
lean_object* x_20; 
lean_dec(x_6);
x_20 = lean_ctor_get(x_7, 0);
lean_inc(x_20);
lean_dec(x_7);
x_13 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Lean_FileMap_ofPosition(x_2, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_array_push(x_4, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitAllUnknownIdentifierRanges_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitAllUnknownIdentifierRanges_spec__0_spec__0(x_1, x_2, x_4, x_6, x_4, x_5);
lean_dec(x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_7);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitAllUnknownIdentifierRanges_spec__0___lam__0), 5, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_2);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
x_21 = lean_array_size(x_7);
x_22 = 0;
x_23 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__3(x_18, x_19, x_7, x_21, x_22, x_20, x_16);
lean_dec(x_7);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_24);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_23, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_34);
return x_23;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_dec(x_23);
x_36 = lean_ctor_get(x_25, 0);
lean_inc(x_36);
lean_dec(x_25);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__1___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_17; 
x_17 = lean_box(0);
x_6 = x_17;
goto block_16;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
x_23 = l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__2___closed__1;
x_24 = lean_box(1);
x_25 = lean_unbox(x_24);
x_26 = l_Lean_Language_SnapshotTask_map___redArg(x_20, x_23, x_21, x_22, x_25);
lean_ctor_set(x_5, 0, x_26);
x_6 = x_5;
goto block_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_5, 0);
lean_inc(x_27);
lean_dec(x_5);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
x_31 = l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__2___closed__1;
x_32 = lean_box(1);
x_33 = lean_unbox(x_32);
x_34 = l_Lean_Language_SnapshotTask_map___redArg(x_28, x_31, x_29, x_30, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_6 = x_35;
goto block_16;
}
}
block_16:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Language_SnapshotTask_map___redArg(x_4, x_1, x_7, x_8, x_10);
x_12 = l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__2___closed__0;
x_13 = lean_array_push(x_12, x_11);
x_14 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___redArg(x_6, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__1;
x_4 = l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__2;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__3;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_4 = x_1;
} else {
 lean_dec_ref(x_1);
 x_4 = lean_box(0);
}
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_5, 3);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 4);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__0;
x_16 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__1), 1, 0);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__3;
x_19 = l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__4;
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_41; 
x_41 = lean_box(0);
x_20 = x_41;
goto block_40;
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_10);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_10, 0);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_inc(x_16);
x_47 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__2), 2, 1);
lean_closure_set(x_47, 0, x_16);
x_48 = lean_box(1);
x_49 = lean_unbox(x_48);
x_50 = l_Lean_Language_SnapshotTask_map___redArg(x_44, x_47, x_45, x_46, x_49);
lean_ctor_set(x_10, 0, x_50);
x_20 = x_10;
goto block_40;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_51 = lean_ctor_get(x_10, 0);
lean_inc(x_51);
lean_dec(x_10);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_inc(x_16);
x_55 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__2), 2, 1);
lean_closure_set(x_55, 0, x_16);
x_56 = lean_box(1);
x_57 = lean_unbox(x_56);
x_58 = l_Lean_Language_SnapshotTask_map___redArg(x_52, x_55, x_53, x_54, x_57);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_20 = x_59;
goto block_40;
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0;
x_14 = l_Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitAllUnknownIdentifierRanges_spec__0(x_11, x_7, x_12, x_13, x_2);
return x_14;
}
block_40:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_21 = lean_ctor_get(x_9, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
x_23 = lean_box(1);
x_24 = lean_unbox(x_23);
x_25 = l_Lean_Language_SnapshotTask_map___redArg(x_9, x_16, x_21, x_22, x_24);
x_26 = l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__2___closed__0;
x_27 = lean_array_push(x_26, x_25);
x_28 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___redArg(x_20, x_27);
if (lean_is_scalar(x_4)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_4;
}
lean_ctor_set(x_29, 0, x_8);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Language_SnapshotTree_getAll(x_29);
x_31 = lean_array_size(x_30);
x_32 = 0;
x_33 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_runLintersAsync_spec__2(x_31, x_32, x_30);
x_34 = lean_array_get_size(x_33);
x_35 = lean_nat_dec_lt(x_17, x_34);
if (x_35 == 0)
{
lean_dec(x_34);
lean_dec(x_33);
x_12 = x_18;
goto block_15;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_34, x_34);
if (x_36 == 0)
{
lean_dec(x_34);
lean_dec(x_33);
x_12 = x_18;
goto block_15;
}
else
{
size_t x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_38 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_runLintersAsync_spec__3(x_33, x_32, x_37, x_19);
lean_dec(x_33);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_12 = x_39;
goto block_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitAllUnknownIdentifierRanges_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_11 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitAllUnknownIdentifierRanges_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_10, x_11, x_8, x_9);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitAllUnknownIdentifierRanges_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitAllUnknownIdentifierRanges_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_collectOpenNamespaces_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_collectOpenNamespaces_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_4 = x_1;
} else {
 lean_dec_ref(x_1);
 x_4 = lean_box(0);
}
x_5 = l_Lean_Name_isAnonymous(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_collectOpenNamespaces_spec__0___closed__0;
lean_inc(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_array_push(x_3, x_7);
if (lean_obj_tag(x_2) == 0)
{
x_9 = x_2;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_9 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_10; 
if (lean_is_scalar(x_4)) {
 x_10 = lean_alloc_ctor(0, 2, 0);
} else {
 x_10 = x_4;
}
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_1 = x_10;
goto _start;
}
}
else
{
lean_object* x_14; 
if (lean_is_scalar(x_4)) {
 x_14 = lean_alloc_ctor(0, 2, 0);
} else {
 x_14 = x_4;
}
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Server_FileWorker_collectOpenNamespaces_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_6 = x_1;
} else {
 lean_dec_ref(x_1);
 x_6 = lean_box(0);
}
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_array_mk(x_12);
lean_ctor_set(x_4, 1, x_13);
x_7 = x_4;
goto block_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_16 = lean_array_mk(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_7 = x_17;
goto block_10;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
lean_ctor_set(x_4, 1, x_19);
lean_ctor_set(x_4, 0, x_20);
x_7 = x_4;
goto block_10;
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
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_7 = x_23;
goto block_10;
}
}
block_10:
{
lean_object* x_8; 
if (lean_is_scalar(x_6)) {
 x_8 = lean_alloc_ctor(1, 2, 0);
} else {
 x_8 = x_6;
}
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_1 = x_5;
x_2 = x_8;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_collectOpenNamespaces___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectOpenNamespaces(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = l_Lean_Server_FileWorker_collectOpenNamespaces___closed__0;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_collectOpenNamespaces_spec__0(x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = l_List_mapTR_loop___at___Lean_Server_FileWorker_collectOpenNamespaces_spec__1(x_2, x_7);
x_9 = lean_array_mk(x_8);
x_10 = l_Array_append___redArg(x_6, x_9);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 3);
lean_dec(x_14);
x_15 = lean_ctor_get(x_10, 2);
lean_dec(x_15);
x_16 = lean_ctor_get(x_10, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_13, 3);
lean_inc(x_17);
lean_dec(x_13);
x_18 = l_Lean_Server_Completion_minimizeGlobalIdentifierInContext(x_2, x_3, x_8);
lean_ctor_set(x_1, 1, x_5);
lean_ctor_set(x_1, 0, x_4);
x_19 = l_Lean_FileMap_utf8RangeToLspRange(x_17, x_1);
lean_inc(x_18);
x_20 = l_Lean_Name_toString(x_18, x_6, x_7);
x_21 = lean_box(0);
lean_ctor_set(x_10, 3, x_21);
lean_ctor_set(x_10, 2, x_21);
lean_ctor_set(x_10, 1, x_20);
lean_ctor_set(x_10, 0, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_10);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_10, 0);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_ctor_get(x_23, 3);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Server_Completion_minimizeGlobalIdentifierInContext(x_2, x_3, x_8);
lean_ctor_set(x_1, 1, x_5);
lean_ctor_set(x_1, 0, x_4);
x_26 = l_Lean_FileMap_utf8RangeToLspRange(x_24, x_1);
lean_inc(x_25);
x_27 = l_Lean_Name_toString(x_25, x_6, x_7);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 lean_ctor_release(x_31, 3);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get(x_32, 3);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Server_Completion_minimizeGlobalIdentifierInContext(x_2, x_3, x_8);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_4);
lean_ctor_set(x_36, 1, x_5);
x_37 = l_Lean_FileMap_utf8RangeToLspRange(x_34, x_36);
lean_inc(x_35);
x_38 = l_Lean_Name_toString(x_35, x_6, x_7);
x_39 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_40 = lean_alloc_ctor(0, 4, 0);
} else {
 x_40 = x_33;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_39);
lean_ctor_set(x_40, 3, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
x_7 = l_Lean_Syntax_getPos_x3f(x_3, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unbox(x_5);
x_11 = l_Lean_Syntax_getTailPos_x3f(x_3, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 4);
lean_inc(x_19);
x_20 = lean_ctor_get(x_14, 5);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0___boxed), 1, 0);
x_22 = lean_unbox(x_5);
lean_inc(x_21);
x_23 = l_Lean_Name_toString(x_4, x_22, x_21);
lean_inc(x_20);
lean_inc(x_19);
x_24 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__1___boxed), 8, 7);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_19);
lean_closure_set(x_24, 2, x_20);
lean_closure_set(x_24, 3, x_9);
lean_closure_set(x_24, 4, x_17);
lean_closure_set(x_24, 5, x_5);
lean_closure_set(x_24, 6, x_21);
x_25 = l_Lean_Server_FileWorker_collectOpenNamespaces(x_19, x_20);
lean_ctor_set(x_2, 1, x_25);
lean_ctor_set(x_2, 0, x_23);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_18);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set(x_11, 0, x_26);
return x_11;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_11, 0);
lean_inc(x_27);
lean_dec(x_11);
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_14, 4);
lean_inc(x_29);
x_30 = lean_ctor_get(x_14, 5);
lean_inc(x_30);
lean_dec(x_14);
x_31 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0___boxed), 1, 0);
x_32 = lean_unbox(x_5);
lean_inc(x_31);
x_33 = l_Lean_Name_toString(x_4, x_32, x_31);
lean_inc(x_30);
lean_inc(x_29);
x_34 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__1___boxed), 8, 7);
lean_closure_set(x_34, 0, x_1);
lean_closure_set(x_34, 1, x_29);
lean_closure_set(x_34, 2, x_30);
lean_closure_set(x_34, 3, x_9);
lean_closure_set(x_34, 4, x_27);
lean_closure_set(x_34, 5, x_5);
lean_closure_set(x_34, 6, x_31);
x_35 = l_Lean_Server_FileWorker_collectOpenNamespaces(x_29, x_30);
lean_ctor_set(x_2, 1, x_35);
lean_ctor_set(x_2, 0, x_33);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_2);
lean_ctor_set(x_36, 1, x_28);
lean_ctor_set(x_36, 2, x_34);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
lean_dec(x_2);
x_39 = lean_ctor_get(x_11, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_40 = x_11;
} else {
 lean_dec_ref(x_11);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 4);
lean_inc(x_42);
x_43 = lean_ctor_get(x_38, 5);
lean_inc(x_43);
lean_dec(x_38);
x_44 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0___boxed), 1, 0);
x_45 = lean_unbox(x_5);
lean_inc(x_44);
x_46 = l_Lean_Name_toString(x_4, x_45, x_44);
lean_inc(x_43);
lean_inc(x_42);
x_47 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__1___boxed), 8, 7);
lean_closure_set(x_47, 0, x_1);
lean_closure_set(x_47, 1, x_42);
lean_closure_set(x_47, 2, x_43);
lean_closure_set(x_47, 3, x_9);
lean_closure_set(x_47, 4, x_39);
lean_closure_set(x_47, 5, x_5);
lean_closure_set(x_47, 6, x_44);
x_48 = l_Lean_Server_FileWorker_collectOpenNamespaces(x_42, x_43);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_41);
lean_ctor_set(x_50, 2, x_47);
if (lean_is_scalar(x_40)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_40;
}
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_6);
lean_dec(x_6);
x_10 = l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__1(x_1, x_2, x_3, x_4, x_5, x_9, x_7, x_8);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_computeIdQuery_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_collectOpenNamespaces_spec__0___closed__0;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_19; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_20, x_3, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Server_Completion_getDotCompletionTypeNames(x_23, x_2, x_3, x_4, x_5, x_24);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_25);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_25, 0);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_inc(x_34);
x_13 = x_25;
x_14 = x_34;
x_15 = x_35;
goto block_18;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
lean_inc(x_37);
lean_inc(x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_13 = x_38;
x_14 = x_36;
x_15 = x_37;
goto block_18;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_19);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_19, 0);
x_41 = lean_ctor_get(x_19, 1);
lean_inc(x_41);
lean_inc(x_40);
x_13 = x_19;
x_14 = x_40;
x_15 = x_41;
goto block_18;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_19, 0);
x_43 = lean_ctor_get(x_19, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_19);
lean_inc(x_43);
lean_inc(x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_13 = x_44;
x_14 = x_42;
x_15 = x_43;
goto block_18;
}
}
block_12:
{
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_dec(x_7);
return x_8;
}
}
block_18:
{
uint8_t x_16; 
x_16 = l_Lean_Exception_isInterrupt(x_14);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_Lean_Exception_isRuntime(x_14);
lean_dec(x_14);
x_7 = x_15;
x_8 = x_13;
x_9 = x_17;
goto block_12;
}
else
{
lean_dec(x_14);
x_7 = x_15;
x_8 = x_13;
x_9 = x_16;
goto block_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = l_Lean_FileMap_utf8RangeToLspRange(x_3, x_5);
x_7 = l_Lean_Name_getString_x21(x_4);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_5, 0);
lean_dec(x_10);
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_Syntax_getPos_x3f(x_9, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 0, x_14);
return x_5;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unbox(x_11);
x_17 = l_Lean_Syntax_getTailPos_x3f(x_9, x_16);
lean_dec(x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 0, x_18);
return x_5;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_5);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0), 6, 1);
lean_closure_set(x_20, 0, x_7);
lean_inc(x_2);
x_21 = l_Lean_Elab_ContextInfo_runMetaM___redArg(x_2, x_6, x_20, x_4);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = l_Array_isEmpty___redArg(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
lean_dec(x_1);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_35, 3);
lean_inc(x_36);
lean_dec(x_35);
x_37 = !lean_is_exclusive(x_2);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_2, 0);
x_39 = lean_ctor_get(x_2, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
lean_inc(x_19);
lean_inc(x_15);
x_42 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__1), 4, 3);
lean_closure_set(x_42, 0, x_15);
lean_closure_set(x_42, 1, x_19);
lean_closure_set(x_42, 2, x_36);
x_43 = lean_string_utf8_extract(x_40, x_15, x_19);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_40);
x_44 = lean_array_size(x_32);
x_45 = 0;
x_46 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(x_44, x_45, x_32);
lean_ctor_set(x_2, 1, x_46);
lean_ctor_set(x_2, 0, x_43);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set(x_47, 1, x_41);
lean_ctor_set(x_47, 2, x_42);
lean_ctor_set(x_22, 0, x_47);
return x_21;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
lean_dec(x_2);
x_49 = lean_ctor_get(x_36, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_19);
lean_inc(x_15);
x_51 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__1), 4, 3);
lean_closure_set(x_51, 0, x_15);
lean_closure_set(x_51, 1, x_19);
lean_closure_set(x_51, 2, x_36);
x_52 = lean_string_utf8_extract(x_49, x_15, x_19);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_49);
x_53 = lean_array_size(x_32);
x_54 = 0;
x_55 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(x_53, x_54, x_32);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_50);
lean_ctor_set(x_57, 2, x_51);
lean_ctor_set(x_22, 0, x_57);
return x_21;
}
}
else
{
lean_object* x_58; 
lean_free_object(x_22);
lean_dec(x_32);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_box(0);
lean_ctor_set(x_21, 0, x_58);
return x_21;
}
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_22, 0);
lean_inc(x_59);
lean_dec(x_22);
x_60 = l_Array_isEmpty___redArg(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; size_t x_70; size_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
lean_dec(x_1);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_ctor_get(x_62, 3);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get(x_2, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_65 = x_2;
} else {
 lean_dec_ref(x_2);
 x_65 = lean_box(0);
}
x_66 = lean_ctor_get(x_63, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 0);
lean_inc(x_67);
lean_dec(x_64);
lean_inc(x_19);
lean_inc(x_15);
x_68 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__1), 4, 3);
lean_closure_set(x_68, 0, x_15);
lean_closure_set(x_68, 1, x_19);
lean_closure_set(x_68, 2, x_63);
x_69 = lean_string_utf8_extract(x_66, x_15, x_19);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_66);
x_70 = lean_array_size(x_59);
x_71 = 0;
x_72 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(x_70, x_71, x_59);
if (lean_is_scalar(x_65)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_65;
}
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_67);
lean_ctor_set(x_74, 2, x_68);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_21, 0, x_75);
return x_21;
}
else
{
lean_object* x_76; 
lean_dec(x_59);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_76 = lean_box(0);
lean_ctor_set(x_21, 0, x_76);
return x_21;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_21, 1);
lean_inc(x_77);
lean_dec(x_21);
x_78 = lean_ctor_get(x_22, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_79 = x_22;
} else {
 lean_dec_ref(x_22);
 x_79 = lean_box(0);
}
x_80 = l_Array_isEmpty___redArg(x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; size_t x_90; size_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_81 = lean_ctor_get(x_1, 0);
lean_inc(x_81);
lean_dec(x_1);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_ctor_get(x_82, 3);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_ctor_get(x_2, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_85 = x_2;
} else {
 lean_dec_ref(x_2);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_83, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
lean_dec(x_84);
lean_inc(x_19);
lean_inc(x_15);
x_88 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__1), 4, 3);
lean_closure_set(x_88, 0, x_15);
lean_closure_set(x_88, 1, x_19);
lean_closure_set(x_88, 2, x_83);
x_89 = lean_string_utf8_extract(x_86, x_15, x_19);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_86);
x_90 = lean_array_size(x_78);
x_91 = 0;
x_92 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(x_90, x_91, x_78);
if (lean_is_scalar(x_85)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_85;
}
lean_ctor_set(x_93, 0, x_89);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_87);
lean_ctor_set(x_94, 2, x_88);
if (lean_is_scalar(x_79)) {
 x_95 = lean_alloc_ctor(1, 1, 0);
} else {
 x_95 = x_79;
}
lean_ctor_set(x_95, 0, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_77);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_77);
return x_98;
}
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_21);
if (x_99 == 0)
{
return x_21;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_21, 0);
x_101 = lean_ctor_get(x_21, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_21);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_5, 1);
lean_inc(x_103);
lean_dec(x_5);
x_104 = lean_box(1);
x_105 = lean_unbox(x_104);
x_106 = l_Lean_Syntax_getPos_x3f(x_103, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_103);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_4);
return x_108;
}
else
{
lean_object* x_109; uint8_t x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_106, 0);
lean_inc(x_109);
lean_dec(x_106);
x_110 = lean_unbox(x_104);
x_111 = l_Lean_Syntax_getTailPos_x3f(x_103, x_110);
lean_dec(x_103);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_109);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_4);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_111, 0);
lean_inc(x_114);
lean_dec(x_111);
x_115 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0), 6, 1);
lean_closure_set(x_115, 0, x_7);
lean_inc(x_2);
x_116 = l_Lean_Elab_ContextInfo_runMetaM___redArg(x_2, x_6, x_115, x_4);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_114);
lean_dec(x_109);
lean_dec(x_2);
lean_dec(x_1);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
x_120 = lean_box(0);
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_119;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_118);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_122 = lean_ctor_get(x_116, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_123 = x_116;
} else {
 lean_dec_ref(x_116);
 x_123 = lean_box(0);
}
x_124 = lean_ctor_get(x_117, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_125 = x_117;
} else {
 lean_dec_ref(x_117);
 x_125 = lean_box(0);
}
x_126 = l_Array_isEmpty___redArg(x_124);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; size_t x_136; size_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_127 = lean_ctor_get(x_1, 0);
lean_inc(x_127);
lean_dec(x_1);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
lean_dec(x_127);
x_129 = lean_ctor_get(x_128, 3);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_ctor_get(x_2, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_131 = x_2;
} else {
 lean_dec_ref(x_2);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get(x_129, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 0);
lean_inc(x_133);
lean_dec(x_130);
lean_inc(x_114);
lean_inc(x_109);
x_134 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__1), 4, 3);
lean_closure_set(x_134, 0, x_109);
lean_closure_set(x_134, 1, x_114);
lean_closure_set(x_134, 2, x_129);
x_135 = lean_string_utf8_extract(x_132, x_109, x_114);
lean_dec(x_114);
lean_dec(x_109);
lean_dec(x_132);
x_136 = lean_array_size(x_124);
x_137 = 0;
x_138 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(x_136, x_137, x_124);
if (lean_is_scalar(x_131)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_131;
}
lean_ctor_set(x_139, 0, x_135);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_133);
lean_ctor_set(x_140, 2, x_134);
if (lean_is_scalar(x_125)) {
 x_141 = lean_alloc_ctor(1, 1, 0);
} else {
 x_141 = x_125;
}
lean_ctor_set(x_141, 0, x_140);
if (lean_is_scalar(x_123)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_123;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_122);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_114);
lean_dec(x_109);
lean_dec(x_2);
lean_dec(x_1);
x_143 = lean_box(0);
if (lean_is_scalar(x_123)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_123;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_122);
return x_144;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_114);
lean_dec(x_109);
lean_dec(x_2);
lean_dec(x_1);
x_145 = lean_ctor_get(x_116, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_116, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_147 = x_116;
} else {
 lean_dec_ref(x_116);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1, x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_11 = l_Lean_Expr_cleanupAnnotations(x_8);
x_12 = l_Lean_Expr_getAppFn(x_11);
lean_dec(x_11);
x_13 = l_Lean_Expr_cleanupAnnotations(x_12);
if (lean_obj_tag(x_13) == 4)
{
lean_object* x_14; 
x_14 = l_Lean_Server_Completion_getDotCompletionTypeNames(x_13, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_29; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
x_29 = l_Lean_Exception_isInterrupt(x_23);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Exception_isRuntime(x_23);
lean_dec(x_23);
x_25 = x_30;
goto block_28;
}
else
{
lean_dec(x_23);
x_25 = x_29;
goto block_28;
}
block_28:
{
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_14);
x_26 = lean_box(0);
if (lean_is_scalar(x_10)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_10;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
else
{
lean_dec(x_24);
lean_dec(x_10);
return x_14;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_38; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
lean_inc(x_32);
lean_inc(x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_38 = l_Lean_Exception_isInterrupt(x_31);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = l_Lean_Exception_isRuntime(x_31);
lean_dec(x_31);
x_34 = x_39;
goto block_37;
}
else
{
lean_dec(x_31);
x_34 = x_38;
goto block_37;
}
block_37:
{
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_33);
x_35 = lean_box(0);
if (lean_is_scalar(x_10)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_10;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
return x_36;
}
else
{
lean_dec(x_32);
lean_dec(x_10);
return x_33;
}
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_box(0);
if (lean_is_scalar(x_10)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_10;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_9);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 3);
lean_dec(x_10);
x_11 = lean_ctor_get(x_6, 2);
lean_dec(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_9, 3);
lean_inc(x_13);
lean_dec(x_9);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_2);
x_14 = l_Lean_FileMap_utf8RangeToLspRange(x_13, x_1);
x_15 = l_Lean_Name_getString_x21(x_4);
x_16 = lean_box(0);
lean_ctor_set(x_6, 3, x_16);
lean_ctor_set(x_6, 2, x_16);
lean_ctor_set(x_6, 1, x_15);
lean_ctor_set(x_6, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
lean_dec(x_18);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_2);
x_20 = l_Lean_FileMap_utf8RangeToLspRange(x_19, x_1);
x_21 = l_Lean_Name_getString_x21(x_4);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set(x_23, 3, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 lean_ctor_release(x_25, 3);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get(x_26, 3);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
x_30 = l_Lean_FileMap_utf8RangeToLspRange(x_28, x_29);
x_31 = l_Lean_Name_getString_x21(x_4);
x_32 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_33 = lean_alloc_ctor(0, 4, 0);
} else {
 x_33 = x_27;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_computeDotIdQuery_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_Syntax_getPos_x3f(x_3, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_unbox(x_8);
x_15 = l_Lean_Syntax_getTailPos_x3f(x_3, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_ctor_get(x_6, 0);
lean_inc(x_21);
lean_dec(x_6);
x_22 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__0), 6, 1);
lean_closure_set(x_22, 0, x_21);
lean_inc(x_2);
x_23 = l_Lean_Elab_ContextInfo_runMetaM___redArg(x_2, x_5, x_22, x_7);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
x_31 = !lean_is_exclusive(x_2);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_2, 0);
x_33 = lean_ctor_get(x_2, 1);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_23);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_23, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_24);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_24, 0);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
lean_dec(x_32);
x_39 = l_Lean_Server_FileWorker_computeDotIdQuery_x3f___closed__0;
x_40 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__2), 4, 3);
lean_closure_set(x_40, 0, x_1);
lean_closure_set(x_40, 1, x_13);
lean_closure_set(x_40, 2, x_20);
x_41 = lean_unbox(x_8);
x_42 = l_Lean_Name_toString(x_4, x_41, x_39);
x_43 = lean_array_size(x_37);
x_44 = 0;
x_45 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(x_43, x_44, x_37);
lean_ctor_set(x_2, 1, x_45);
lean_ctor_set(x_2, 0, x_42);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set(x_46, 1, x_38);
lean_ctor_set(x_46, 2, x_40);
lean_ctor_set(x_24, 0, x_46);
return x_23;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; size_t x_53; size_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_47 = lean_ctor_get(x_24, 0);
lean_inc(x_47);
lean_dec(x_24);
x_48 = lean_ctor_get(x_32, 0);
lean_inc(x_48);
lean_dec(x_32);
x_49 = l_Lean_Server_FileWorker_computeDotIdQuery_x3f___closed__0;
x_50 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__2), 4, 3);
lean_closure_set(x_50, 0, x_1);
lean_closure_set(x_50, 1, x_13);
lean_closure_set(x_50, 2, x_20);
x_51 = lean_unbox(x_8);
x_52 = l_Lean_Name_toString(x_4, x_51, x_49);
x_53 = lean_array_size(x_47);
x_54 = 0;
x_55 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(x_53, x_54, x_47);
lean_ctor_set(x_2, 1, x_55);
lean_ctor_set(x_2, 0, x_52);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_48);
lean_ctor_set(x_56, 2, x_50);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_23, 0, x_57);
return x_23;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; size_t x_66; size_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_58 = lean_ctor_get(x_23, 1);
lean_inc(x_58);
lean_dec(x_23);
x_59 = lean_ctor_get(x_24, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_60 = x_24;
} else {
 lean_dec_ref(x_24);
 x_60 = lean_box(0);
}
x_61 = lean_ctor_get(x_32, 0);
lean_inc(x_61);
lean_dec(x_32);
x_62 = l_Lean_Server_FileWorker_computeDotIdQuery_x3f___closed__0;
x_63 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__2), 4, 3);
lean_closure_set(x_63, 0, x_1);
lean_closure_set(x_63, 1, x_13);
lean_closure_set(x_63, 2, x_20);
x_64 = lean_unbox(x_8);
x_65 = l_Lean_Name_toString(x_4, x_64, x_62);
x_66 = lean_array_size(x_59);
x_67 = 0;
x_68 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(x_66, x_67, x_59);
lean_ctor_set(x_2, 1, x_68);
lean_ctor_set(x_2, 0, x_65);
x_69 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_69, 0, x_2);
lean_ctor_set(x_69, 1, x_61);
lean_ctor_set(x_69, 2, x_63);
if (lean_is_scalar(x_60)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_60;
}
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_58);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; size_t x_82; size_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_72 = lean_ctor_get(x_2, 0);
lean_inc(x_72);
lean_dec(x_2);
x_73 = lean_ctor_get(x_23, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_74 = x_23;
} else {
 lean_dec_ref(x_23);
 x_74 = lean_box(0);
}
x_75 = lean_ctor_get(x_24, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_76 = x_24;
} else {
 lean_dec_ref(x_24);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_72, 0);
lean_inc(x_77);
lean_dec(x_72);
x_78 = l_Lean_Server_FileWorker_computeDotIdQuery_x3f___closed__0;
x_79 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__2), 4, 3);
lean_closure_set(x_79, 0, x_1);
lean_closure_set(x_79, 1, x_13);
lean_closure_set(x_79, 2, x_20);
x_80 = lean_unbox(x_8);
x_81 = l_Lean_Name_toString(x_4, x_80, x_78);
x_82 = lean_array_size(x_75);
x_83 = 0;
x_84 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(x_82, x_83, x_75);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_77);
lean_ctor_set(x_86, 2, x_79);
if (lean_is_scalar(x_76)) {
 x_87 = lean_alloc_ctor(1, 1, 0);
} else {
 x_87 = x_76;
}
lean_ctor_set(x_87, 0, x_86);
if (lean_is_scalar(x_74)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_74;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_73);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_23);
if (x_89 == 0)
{
return x_23;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_23, 0);
x_91 = lean_ctor_get(x_23, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_23);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_FileWorker_computeDotIdQuery_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_computeQueries_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_4, x_3);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_array_uget(x_2, x_4);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 2);
lean_inc(x_23);
switch (lean_obj_tag(x_23)) {
case 0:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_1);
x_26 = l_Lean_Server_FileWorker_computeDotQuery_x3f(x_1, x_24, x_25, x_6);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_13 = x_5;
x_14 = x_27;
x_15 = x_28;
goto block_18;
}
else
{
uint8_t x_29; 
lean_dec(x_5);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = l_Lean_Server_RequestError_ofIoError(x_30);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = l_Lean_Server_RequestError_ofIoError(x_32);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
case 1:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
lean_dec(x_22);
x_37 = lean_ctor_get(x_23, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_dec(x_23);
lean_inc(x_1);
x_39 = l_Lean_Server_FileWorker_computeIdQuery_x3f(x_1, x_36, x_37, x_38);
lean_dec(x_37);
x_13 = x_5;
x_14 = x_39;
x_15 = x_6;
goto block_18;
}
case 2:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_dec(x_22);
x_41 = lean_ctor_get(x_23, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_23, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_23, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_23, 3);
lean_inc(x_44);
lean_dec(x_23);
lean_inc(x_1);
x_45 = l_Lean_Server_FileWorker_computeDotIdQuery_x3f(x_1, x_40, x_41, x_42, x_43, x_44, x_6);
lean_dec(x_41);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_13 = x_5;
x_14 = x_46;
x_15 = x_47;
goto block_18;
}
else
{
uint8_t x_48; 
lean_dec(x_5);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_45);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_45, 0);
x_50 = l_Lean_Server_RequestError_ofIoError(x_49);
lean_ctor_set(x_45, 0, x_50);
return x_45;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_45, 0);
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_45);
x_53 = l_Lean_Server_RequestError_ofIoError(x_51);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
default: 
{
lean_dec(x_23);
lean_dec(x_22);
x_7 = x_5;
x_8 = x_6;
goto block_12;
}
}
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
x_5 = x_7;
x_6 = x_8;
goto _start;
}
block_18:
{
if (lean_obj_tag(x_14) == 0)
{
x_7 = x_13;
x_8 = x_15;
goto block_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_push(x_13, x_16);
x_7 = x_17;
x_8 = x_15;
goto block_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_computeQueries_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_computeQueries_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_computeQueries_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_array_uget(x_2, x_4);
x_11 = lean_array_size(x_10);
x_12 = 0;
lean_inc(x_1);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_computeQueries_spec__0___redArg(x_1, x_10, x_11, x_12, x_5, x_7);
lean_dec(x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_16 = l_Array_isEmpty___redArg(x_14);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
return x_13;
}
else
{
size_t x_17; size_t x_18; 
lean_dec(x_13);
x_17 = 1;
x_18 = lean_usize_add(x_4, x_17);
x_4 = x_18;
x_5 = x_14;
x_7 = x_15;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_13;
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_computeQueries___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeQueries(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Server_RequestM_findCmdDataAtPos(x_1, x_2, x_6);
x_8 = lean_task_get_own(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = l_Lean_Server_FileWorker_computeQueries___closed__0;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_ctor_get(x_13, 3);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(x_16, x_2, x_14, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Server_FileWorker_computeQueries___closed__0;
x_20 = lean_array_size(x_18);
x_21 = 0;
x_22 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_computeQueries_spec__1(x_1, x_18, x_20, x_21, x_19, x_3, x_4);
lean_dec(x_18);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_computeQueries_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_computeQueries_spec__0___redArg(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_computeQueries_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_computeQueries_spec__0(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_computeQueries_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_computeQueries_spec__1(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeQueries___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_computeQueries(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknownIdentifiers", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Import all unambiguous unknown identifiers", 42, 42);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = lean_box(0);
x_4 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__0;
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = lean_box(0);
x_10 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider;
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
x_13 = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_toJsonCodeActionResolveData____x40_Lean_Server_CodeActions_Basic___hyg_70_(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_4);
lean_ctor_set(x_15, 3, x_5);
lean_ctor_set(x_15, 4, x_6);
lean_ctor_set(x_15, 5, x_7);
lean_ctor_set(x_15, 6, x_3);
lean_ctor_set(x_15, 7, x_8);
lean_ctor_set(x_15, 8, x_9);
lean_ctor_set(x_15, 9, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cannot parse server request response: ", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_4019_(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_free_object(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg___lam__0___closed__0;
x_8 = l_Lean_Json_compress(x_3);
x_9 = lean_string_append(x_7, x_8);
lean_dec(x_8);
x_10 = l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg___lam__0___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_5);
lean_dec(x_5);
x_13 = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_unbox(x_6);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_14);
return x_13;
}
else
{
lean_object* x_15; 
lean_dec(x_3);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
lean_inc(x_16);
x_17 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_4019_(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg___lam__0___closed__0;
x_21 = l_Lean_Json_compress(x_16);
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
x_23 = l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg___lam__0___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_24, x_18);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_unbox(x_19);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_16);
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
lean_dec(x_17);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_1);
if (x_30 == 0)
{
return x_1;
}
else
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
lean_dec(x_1);
x_33 = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_31);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 5);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3700_(x_2);
x_7 = lean_apply_3(x_5, x_1, x_6, x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg___lam__0), 1, 0);
x_11 = l_Lean_Server_ServerTask_mapCheap___redArg(x_10, x_9);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg___lam__0), 1, 0);
x_15 = l_Lean_Server_ServerTask_mapCheap___redArg(x_14, x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Import ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" from ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("quickfix", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("import ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Change to ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_7, x_6);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; 
x_18 = lean_array_uget(x_5, x_7);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_18, sizeof(void*)*2);
lean_dec(x_18);
x_22 = lean_ctor_get(x_8, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_24 = x_8;
} else {
 lean_dec_ref(x_8);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 2);
lean_inc(x_26);
lean_inc(x_20);
lean_inc(x_25);
x_27 = l_Lean_Environment_contains(x_25, x_20, x_16);
if (x_27 == 0)
{
goto block_146;
}
else
{
if (x_4 == 0)
{
lean_dec(x_25);
x_28 = x_4;
goto block_142;
}
else
{
goto block_146;
}
}
block_142:
{
lean_object* x_29; 
x_29 = lean_apply_1(x_26, x_20);
if (x_27 == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = lean_box(x_28);
x_34 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_34, 0, x_33);
x_35 = lean_box(0);
x_36 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__0;
lean_inc(x_34);
x_37 = l_Lean_Name_toString(x_31, x_16, x_34);
x_38 = lean_string_append(x_36, x_37);
lean_dec(x_37);
x_39 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__1;
x_40 = lean_string_append(x_38, x_39);
x_41 = l_Lean_Name_toString(x_19, x_16, x_34);
x_42 = lean_string_append(x_40, x_41);
x_43 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__3;
x_44 = lean_box(0);
x_45 = lean_box(0);
lean_inc(x_2);
x_46 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_2);
x_47 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__4;
x_48 = lean_string_append(x_47, x_41);
lean_dec(x_41);
x_49 = l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg___lam__0___closed__1;
x_50 = lean_string_append(x_48, x_49);
lean_inc(x_3);
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_3);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_35);
lean_ctor_set(x_51, 3, x_35);
x_52 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__5;
x_53 = lean_array_push(x_52, x_51);
x_54 = lean_array_push(x_53, x_32);
lean_ctor_set(x_29, 1, x_54);
lean_ctor_set(x_29, 0, x_46);
x_55 = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(x_29);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_box(0);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_59, 0, x_35);
lean_ctor_set(x_59, 1, x_35);
lean_ctor_set(x_59, 2, x_42);
lean_ctor_set(x_59, 3, x_43);
lean_ctor_set(x_59, 4, x_44);
lean_ctor_set(x_59, 5, x_45);
lean_ctor_set(x_59, 6, x_35);
lean_ctor_set(x_59, 7, x_56);
lean_ctor_set(x_59, 8, x_57);
lean_ctor_set(x_59, 9, x_58);
x_60 = lean_array_push(x_23, x_59);
if (x_21 == 0)
{
lean_object* x_61; 
if (lean_is_scalar(x_24)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_24;
}
lean_ctor_set(x_61, 0, x_22);
lean_ctor_set(x_61, 1, x_60);
x_10 = x_61;
x_11 = x_9;
goto block_15;
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_22);
x_62 = lean_box(x_16);
if (lean_is_scalar(x_24)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_24;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
x_10 = x_63;
x_11 = x_9;
goto block_15;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_64 = lean_ctor_get(x_29, 0);
x_65 = lean_ctor_get(x_29, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_29);
x_66 = lean_box(x_28);
x_67 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_67, 0, x_66);
x_68 = lean_box(0);
x_69 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__0;
lean_inc(x_67);
x_70 = l_Lean_Name_toString(x_64, x_16, x_67);
x_71 = lean_string_append(x_69, x_70);
lean_dec(x_70);
x_72 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__1;
x_73 = lean_string_append(x_71, x_72);
x_74 = l_Lean_Name_toString(x_19, x_16, x_67);
x_75 = lean_string_append(x_73, x_74);
x_76 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__3;
x_77 = lean_box(0);
x_78 = lean_box(0);
lean_inc(x_2);
x_79 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_2);
x_80 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__4;
x_81 = lean_string_append(x_80, x_74);
lean_dec(x_74);
x_82 = l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg___lam__0___closed__1;
x_83 = lean_string_append(x_81, x_82);
lean_inc(x_3);
x_84 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_84, 0, x_3);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_68);
lean_ctor_set(x_84, 3, x_68);
x_85 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__5;
x_86 = lean_array_push(x_85, x_84);
x_87 = lean_array_push(x_86, x_65);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_79);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(x_88);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_box(0);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_93, 0, x_68);
lean_ctor_set(x_93, 1, x_68);
lean_ctor_set(x_93, 2, x_75);
lean_ctor_set(x_93, 3, x_76);
lean_ctor_set(x_93, 4, x_77);
lean_ctor_set(x_93, 5, x_78);
lean_ctor_set(x_93, 6, x_68);
lean_ctor_set(x_93, 7, x_90);
lean_ctor_set(x_93, 8, x_91);
lean_ctor_set(x_93, 9, x_92);
x_94 = lean_array_push(x_23, x_93);
if (x_21 == 0)
{
lean_object* x_95; 
if (lean_is_scalar(x_24)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_24;
}
lean_ctor_set(x_95, 0, x_22);
lean_ctor_set(x_95, 1, x_94);
x_10 = x_95;
x_11 = x_9;
goto block_15;
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_22);
x_96 = lean_box(x_16);
if (lean_is_scalar(x_24)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_24;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
x_10 = x_97;
x_11 = x_9;
goto block_15;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_19);
x_98 = !lean_is_exclusive(x_29);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_99 = lean_ctor_get(x_29, 0);
x_100 = lean_ctor_get(x_29, 1);
x_101 = lean_box(x_28);
x_102 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_102, 0, x_101);
x_103 = lean_box(0);
x_104 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__6;
x_105 = l_Lean_Name_toString(x_99, x_27, x_102);
x_106 = lean_string_append(x_104, x_105);
lean_dec(x_105);
x_107 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__3;
x_108 = lean_box(0);
x_109 = lean_box(0);
lean_inc(x_2);
x_110 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_2);
x_111 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__7;
x_112 = lean_array_push(x_111, x_100);
lean_ctor_set(x_29, 1, x_112);
lean_ctor_set(x_29, 0, x_110);
x_113 = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(x_29);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = lean_box(0);
x_116 = lean_box(0);
x_117 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_117, 0, x_103);
lean_ctor_set(x_117, 1, x_103);
lean_ctor_set(x_117, 2, x_106);
lean_ctor_set(x_117, 3, x_107);
lean_ctor_set(x_117, 4, x_108);
lean_ctor_set(x_117, 5, x_109);
lean_ctor_set(x_117, 6, x_103);
lean_ctor_set(x_117, 7, x_114);
lean_ctor_set(x_117, 8, x_115);
lean_ctor_set(x_117, 9, x_116);
x_118 = lean_array_push(x_23, x_117);
if (lean_is_scalar(x_24)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_24;
}
lean_ctor_set(x_119, 0, x_22);
lean_ctor_set(x_119, 1, x_118);
x_10 = x_119;
x_11 = x_9;
goto block_15;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_120 = lean_ctor_get(x_29, 0);
x_121 = lean_ctor_get(x_29, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_29);
x_122 = lean_box(x_28);
x_123 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_123, 0, x_122);
x_124 = lean_box(0);
x_125 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__6;
x_126 = l_Lean_Name_toString(x_120, x_27, x_123);
x_127 = lean_string_append(x_125, x_126);
lean_dec(x_126);
x_128 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__3;
x_129 = lean_box(0);
x_130 = lean_box(0);
lean_inc(x_2);
x_131 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_2);
x_132 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__7;
x_133 = lean_array_push(x_132, x_121);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(x_134);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_135);
x_137 = lean_box(0);
x_138 = lean_box(0);
x_139 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_139, 0, x_124);
lean_ctor_set(x_139, 1, x_124);
lean_ctor_set(x_139, 2, x_127);
lean_ctor_set(x_139, 3, x_128);
lean_ctor_set(x_139, 4, x_129);
lean_ctor_set(x_139, 5, x_130);
lean_ctor_set(x_139, 6, x_124);
lean_ctor_set(x_139, 7, x_136);
lean_ctor_set(x_139, 8, x_137);
lean_ctor_set(x_139, 9, x_138);
x_140 = lean_array_push(x_23, x_139);
if (lean_is_scalar(x_24)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_24;
}
lean_ctor_set(x_141, 0, x_22);
lean_ctor_set(x_141, 1, x_140);
x_10 = x_141;
x_11 = x_9;
goto block_15;
}
}
}
block_146:
{
lean_object* x_143; uint8_t x_144; 
x_143 = l_Lean_Environment_mainModule(x_25);
lean_dec(x_25);
x_144 = lean_name_eq(x_19, x_143);
lean_dec(x_143);
if (x_144 == 0)
{
x_28 = x_144;
goto block_142;
}
else
{
lean_object* x_145; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_19);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_22);
lean_ctor_set(x_145, 1, x_23);
x_10 = x_145;
x_11 = x_9;
goto block_15;
}
}
}
block_15:
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_7, x_12);
x_7 = x_13;
x_8 = x_10;
x_9 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3_spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_6, x_5);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_7, 1);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
x_22 = lean_ctor_get(x_15, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_15, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_15, 0);
lean_dec(x_24);
x_25 = lean_array_uget(x_4, x_6);
x_26 = lean_array_fget(x_16, x_17);
x_27 = lean_array_size(x_26);
x_28 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_29 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(x_25, x_1, x_2, x_3, x_26, x_27, x_28, x_13, x_9);
lean_dec(x_26);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_17, x_32);
lean_dec(x_17);
lean_ctor_set(x_15, 1, x_33);
lean_ctor_set(x_7, 1, x_30);
x_34 = 1;
x_35 = lean_usize_add(x_6, x_34);
x_6 = x_35;
x_9 = x_31;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; 
lean_dec(x_15);
x_37 = lean_array_uget(x_4, x_6);
x_38 = lean_array_fget(x_16, x_17);
x_39 = lean_array_size(x_38);
x_40 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_41 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(x_37, x_1, x_2, x_3, x_38, x_39, x_40, x_13, x_9);
lean_dec(x_38);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_17, x_44);
lean_dec(x_17);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_16);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_18);
lean_ctor_set(x_7, 1, x_42);
lean_ctor_set(x_7, 0, x_46);
x_47 = 1;
x_48 = lean_usize_add(x_6, x_47);
x_6 = x_48;
x_9 = x_43;
goto _start;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_50 = lean_ctor_get(x_7, 0);
x_51 = lean_ctor_get(x_13, 0);
x_52 = lean_ctor_get(x_13, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_13);
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_50, 2);
lean_inc(x_55);
x_56 = lean_nat_dec_lt(x_54, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_52);
lean_ctor_set(x_7, 1, x_57);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_7);
lean_ctor_set(x_58, 1, x_9);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; size_t x_63; size_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; size_t x_72; 
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 lean_ctor_release(x_50, 2);
 x_59 = x_50;
} else {
 lean_dec_ref(x_50);
 x_59 = lean_box(0);
}
x_60 = lean_array_uget(x_4, x_6);
x_61 = lean_array_fget(x_53, x_54);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_51);
lean_ctor_set(x_62, 1, x_52);
x_63 = lean_array_size(x_61);
x_64 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_65 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(x_60, x_1, x_2, x_3, x_61, x_63, x_64, x_62, x_9);
lean_dec(x_61);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_nat_add(x_54, x_68);
lean_dec(x_54);
if (lean_is_scalar(x_59)) {
 x_70 = lean_alloc_ctor(0, 3, 0);
} else {
 x_70 = x_59;
}
lean_ctor_set(x_70, 0, x_53);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_70, 2, x_55);
lean_ctor_set(x_7, 1, x_66);
lean_ctor_set(x_7, 0, x_70);
x_71 = 1;
x_72 = lean_usize_add(x_6, x_71);
x_6 = x_72;
x_9 = x_67;
goto _start;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_74 = lean_ctor_get(x_7, 1);
x_75 = lean_ctor_get(x_7, 0);
lean_inc(x_74);
lean_inc(x_75);
lean_dec(x_7);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_78 = x_74;
} else {
 lean_dec_ref(x_74);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_75, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_75, 2);
lean_inc(x_81);
x_82 = lean_nat_dec_lt(x_80, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_78)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_78;
}
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_77);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_75);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_9);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; size_t x_90; size_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; size_t x_100; 
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 x_86 = x_75;
} else {
 lean_dec_ref(x_75);
 x_86 = lean_box(0);
}
x_87 = lean_array_uget(x_4, x_6);
x_88 = lean_array_fget(x_79, x_80);
if (lean_is_scalar(x_78)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_78;
}
lean_ctor_set(x_89, 0, x_76);
lean_ctor_set(x_89, 1, x_77);
x_90 = lean_array_size(x_88);
x_91 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_92 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(x_87, x_1, x_2, x_3, x_88, x_90, x_91, x_89, x_9);
lean_dec(x_88);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_add(x_80, x_95);
lean_dec(x_80);
if (lean_is_scalar(x_86)) {
 x_97 = lean_alloc_ctor(0, 3, 0);
} else {
 x_97 = x_86;
}
lean_ctor_set(x_97, 0, x_79);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_81);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_93);
x_99 = 1;
x_100 = lean_usize_add(x_6, x_99);
x_6 = x_100;
x_7 = x_98;
x_9 = x_94;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_6, x_5);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_7, 1);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; 
x_22 = lean_ctor_get(x_15, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_15, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_15, 0);
lean_dec(x_24);
x_25 = lean_array_uget(x_4, x_6);
x_26 = lean_array_fget(x_16, x_17);
x_27 = lean_array_size(x_26);
x_28 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_29 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(x_25, x_1, x_2, x_3, x_26, x_27, x_28, x_13, x_9);
lean_dec(x_26);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_17, x_32);
lean_dec(x_17);
lean_ctor_set(x_15, 1, x_33);
lean_ctor_set(x_7, 1, x_30);
x_34 = 1;
x_35 = lean_usize_add(x_6, x_34);
x_36 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_35, x_7, x_8, x_31);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; lean_object* x_49; 
lean_dec(x_15);
x_37 = lean_array_uget(x_4, x_6);
x_38 = lean_array_fget(x_16, x_17);
x_39 = lean_array_size(x_38);
x_40 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_41 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(x_37, x_1, x_2, x_3, x_38, x_39, x_40, x_13, x_9);
lean_dec(x_38);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_17, x_44);
lean_dec(x_17);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_16);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_18);
lean_ctor_set(x_7, 1, x_42);
lean_ctor_set(x_7, 0, x_46);
x_47 = 1;
x_48 = lean_usize_add(x_6, x_47);
x_49 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_48, x_7, x_8, x_43);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_50 = lean_ctor_get(x_7, 0);
x_51 = lean_ctor_get(x_13, 0);
x_52 = lean_ctor_get(x_13, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_13);
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_50, 2);
lean_inc(x_55);
x_56 = lean_nat_dec_lt(x_54, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_52);
lean_ctor_set(x_7, 1, x_57);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_7);
lean_ctor_set(x_58, 1, x_9);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; size_t x_63; size_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; size_t x_72; lean_object* x_73; 
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 lean_ctor_release(x_50, 2);
 x_59 = x_50;
} else {
 lean_dec_ref(x_50);
 x_59 = lean_box(0);
}
x_60 = lean_array_uget(x_4, x_6);
x_61 = lean_array_fget(x_53, x_54);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_51);
lean_ctor_set(x_62, 1, x_52);
x_63 = lean_array_size(x_61);
x_64 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_65 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(x_60, x_1, x_2, x_3, x_61, x_63, x_64, x_62, x_9);
lean_dec(x_61);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_nat_add(x_54, x_68);
lean_dec(x_54);
if (lean_is_scalar(x_59)) {
 x_70 = lean_alloc_ctor(0, 3, 0);
} else {
 x_70 = x_59;
}
lean_ctor_set(x_70, 0, x_53);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_70, 2, x_55);
lean_ctor_set(x_7, 1, x_66);
lean_ctor_set(x_7, 0, x_70);
x_71 = 1;
x_72 = lean_usize_add(x_6, x_71);
x_73 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_72, x_7, x_8, x_67);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_74 = lean_ctor_get(x_7, 1);
x_75 = lean_ctor_get(x_7, 0);
lean_inc(x_74);
lean_inc(x_75);
lean_dec(x_7);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_78 = x_74;
} else {
 lean_dec_ref(x_74);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_75, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_75, 2);
lean_inc(x_81);
x_82 = lean_nat_dec_lt(x_80, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_78)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_78;
}
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_77);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_75);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_9);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; size_t x_90; size_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; size_t x_100; lean_object* x_101; 
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 x_86 = x_75;
} else {
 lean_dec_ref(x_75);
 x_86 = lean_box(0);
}
x_87 = lean_array_uget(x_4, x_6);
x_88 = lean_array_fget(x_79, x_80);
if (lean_is_scalar(x_78)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_78;
}
lean_ctor_set(x_89, 0, x_76);
lean_ctor_set(x_89, 1, x_77);
x_90 = lean_array_size(x_88);
x_91 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_92 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(x_87, x_1, x_2, x_3, x_88, x_90, x_91, x_89, x_9);
lean_dec(x_88);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_add(x_80, x_95);
lean_dec(x_80);
if (lean_is_scalar(x_86)) {
 x_97 = lean_alloc_ctor(0, 3, 0);
} else {
 x_97 = x_86;
}
lean_ctor_set(x_97, 0, x_79);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_81);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_93);
x_99 = 1;
x_100 = lean_usize_add(x_6, x_99);
x_101 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_100, x_98, x_8, x_94);
return x_101;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("$/lean/queryModule", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 4);
lean_inc(x_7);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 0);
lean_dec(x_10);
lean_inc(x_6);
x_11 = l_Lean_Server_FileWorker_computeQueries(x_6, x_9, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Array_isEmpty___redArg(x_13);
if (x_15 == 0)
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_free_object(x_11);
x_16 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0;
x_17 = lean_array_size(x_13);
x_18 = 0;
lean_inc(x_13);
x_19 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(x_17, x_18, x_13);
lean_ctor_set(x_3, 1, x_19);
lean_ctor_set(x_3, 0, x_1);
lean_inc(x_4);
x_20 = l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg(x_16, x_3, x_4, x_14);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__0), 1, 0);
x_25 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__1), 1, 0);
x_26 = l_Lean_Server_ServerTask_mapCheap___redArg(x_24, x_22);
x_27 = l_Lean_Server_RequestCancellationToken_requestCancellationTask(x_7);
lean_dec(x_7);
x_28 = l_Lean_Server_ServerTask_mapCheap___redArg(x_25, x_27);
x_29 = lean_box(0);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 1, x_29);
lean_ctor_set(x_20, 0, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_20);
x_31 = l_Lean_Server_ServerTask_waitAny___redArg(x_30, x_23);
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
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_32, 0);
lean_inc(x_48);
lean_dec(x_32);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_85 = lean_ctor_get(x_6, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_ctor_get(x_86, 3);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_Syntax_getTailPos_x3f(x_88, x_15);
lean_dec(x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
lean_dec(x_87);
x_90 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__2;
x_50 = x_90;
goto block_84;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_87, 3);
lean_inc(x_92);
lean_dec(x_87);
x_93 = l_Lean_FileMap_utf8PosToLspPos(x_92, x_91);
lean_dec(x_91);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_93, 0);
x_96 = lean_ctor_get(x_93, 1);
lean_dec(x_96);
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_nat_add(x_95, x_97);
lean_dec(x_95);
x_99 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_93, 1, x_99);
lean_ctor_set(x_93, 0, x_98);
x_50 = x_93;
goto block_84;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_93, 0);
lean_inc(x_100);
lean_dec(x_93);
x_101 = lean_unsigned_to_nat(1u);
x_102 = lean_nat_add(x_100, x_101);
lean_dec(x_100);
x_103 = lean_unsigned_to_nat(0u);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_50 = x_104;
goto block_84;
}
}
block_84:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1;
x_53 = lean_array_get_size(x_49);
x_54 = lean_nat_dec_lt(x_51, x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_34)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_34;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_33);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_34);
lean_inc(x_50);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_50);
x_57 = l_Array_toSubarray___redArg(x_49, x_51, x_53);
x_58 = lean_box(x_15);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_52);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(x_6, x_56, x_15, x_13, x_17, x_18, x_60, x_4, x_33);
lean_dec(x_4);
lean_dec(x_13);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
uint8_t x_66; 
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_61);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_61, 0);
lean_dec(x_67);
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_dec(x_63);
lean_ctor_set(x_61, 0, x_68);
return x_61;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_61, 1);
lean_inc(x_69);
lean_dec(x_61);
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
lean_dec(x_63);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_61);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_61, 0);
lean_dec(x_73);
x_74 = lean_ctor_get(x_63, 1);
lean_inc(x_74);
lean_dec(x_63);
x_75 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2;
x_76 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(x_2, x_75);
x_77 = lean_array_push(x_74, x_76);
lean_ctor_set(x_61, 0, x_77);
return x_61;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_61, 1);
lean_inc(x_78);
lean_dec(x_61);
x_79 = lean_ctor_get(x_63, 1);
lean_inc(x_79);
lean_dec(x_63);
x_80 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2;
x_81 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(x_2, x_80);
x_82 = lean_array_push(x_79, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_78);
return x_83;
}
}
}
}
}
else
{
lean_dec(x_48);
lean_dec(x_34);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
x_35 = x_4;
goto block_47;
}
}
else
{
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
x_35 = x_4;
goto block_47;
}
block_47:
{
lean_object* x_36; 
x_36 = l_Lean_Server_RequestM_checkCancelled(x_35, x_33);
lean_dec(x_35);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
x_39 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1;
lean_ctor_set(x_36, 0, x_39);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1;
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
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
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_105 = lean_ctor_get(x_20, 0);
x_106 = lean_ctor_get(x_20, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_20);
x_107 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__0), 1, 0);
x_108 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__1), 1, 0);
x_109 = l_Lean_Server_ServerTask_mapCheap___redArg(x_107, x_105);
x_110 = l_Lean_Server_RequestCancellationToken_requestCancellationTask(x_7);
lean_dec(x_7);
x_111 = l_Lean_Server_ServerTask_mapCheap___redArg(x_108, x_110);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_109);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Lean_Server_ServerTask_waitAny___redArg(x_114, x_106);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_118 = x_115;
} else {
 lean_dec_ref(x_115);
 x_118 = lean_box(0);
}
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_116, 0);
lean_inc(x_130);
lean_dec(x_116);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec(x_130);
x_160 = lean_ctor_get(x_6, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 0);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_ctor_get(x_161, 3);
lean_inc(x_163);
lean_dec(x_161);
x_164 = l_Lean_Syntax_getTailPos_x3f(x_163, x_15);
lean_dec(x_163);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; 
lean_dec(x_162);
x_165 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__2;
x_132 = x_165;
goto block_159;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_166 = lean_ctor_get(x_164, 0);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_ctor_get(x_162, 3);
lean_inc(x_167);
lean_dec(x_162);
x_168 = l_Lean_FileMap_utf8PosToLspPos(x_167, x_166);
lean_dec(x_166);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_170 = x_168;
} else {
 lean_dec_ref(x_168);
 x_170 = lean_box(0);
}
x_171 = lean_unsigned_to_nat(1u);
x_172 = lean_nat_add(x_169, x_171);
lean_dec(x_169);
x_173 = lean_unsigned_to_nat(0u);
if (lean_is_scalar(x_170)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_170;
}
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
x_132 = x_174;
goto block_159;
}
block_159:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_133 = lean_unsigned_to_nat(0u);
x_134 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1;
x_135 = lean_array_get_size(x_131);
x_136 = lean_nat_dec_lt(x_133, x_135);
if (x_136 == 0)
{
lean_object* x_137; 
lean_dec(x_135);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_118)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_118;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_117);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
lean_dec(x_118);
lean_inc(x_132);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_132);
lean_ctor_set(x_138, 1, x_132);
x_139 = l_Array_toSubarray___redArg(x_131, x_133, x_135);
x_140 = lean_box(x_15);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_134);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_141);
x_143 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(x_6, x_138, x_15, x_13, x_17, x_18, x_142, x_4, x_117);
lean_dec(x_4);
lean_dec(x_13);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_unbox(x_146);
lean_dec(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_2);
x_148 = lean_ctor_get(x_143, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_149 = x_143;
} else {
 lean_dec_ref(x_143);
 x_149 = lean_box(0);
}
x_150 = lean_ctor_get(x_145, 1);
lean_inc(x_150);
lean_dec(x_145);
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_149;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_148);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_152 = lean_ctor_get(x_143, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_153 = x_143;
} else {
 lean_dec_ref(x_143);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_145, 1);
lean_inc(x_154);
lean_dec(x_145);
x_155 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2;
x_156 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(x_2, x_155);
x_157 = lean_array_push(x_154, x_156);
if (lean_is_scalar(x_153)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_153;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_152);
return x_158;
}
}
}
}
else
{
lean_dec(x_130);
lean_dec(x_118);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
x_119 = x_4;
goto block_129;
}
}
else
{
lean_dec(x_118);
lean_dec(x_116);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
x_119 = x_4;
goto block_129;
}
block_129:
{
lean_object* x_120; 
x_120 = l_Lean_Server_RequestM_checkCancelled(x_119, x_117);
lean_dec(x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
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
x_123 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1;
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_121);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_120, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_120, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_127 = x_120;
} else {
 lean_dec_ref(x_120);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
}
}
else
{
lean_object* x_175; 
lean_dec(x_13);
lean_free_object(x_3);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_175 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1;
lean_ctor_set(x_11, 0, x_175);
return x_11;
}
}
else
{
lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_176 = lean_ctor_get(x_11, 0);
x_177 = lean_ctor_get(x_11, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_11);
x_178 = l_Array_isEmpty___redArg(x_176);
if (x_178 == 0)
{
lean_object* x_179; size_t x_180; size_t x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_179 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0;
x_180 = lean_array_size(x_176);
x_181 = 0;
lean_inc(x_176);
x_182 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(x_180, x_181, x_176);
lean_ctor_set(x_3, 1, x_182);
lean_ctor_set(x_3, 0, x_1);
lean_inc(x_4);
x_183 = l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg(x_179, x_3, x_4, x_177);
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
x_187 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__0), 1, 0);
x_188 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__1), 1, 0);
x_189 = l_Lean_Server_ServerTask_mapCheap___redArg(x_187, x_184);
x_190 = l_Lean_Server_RequestCancellationToken_requestCancellationTask(x_7);
lean_dec(x_7);
x_191 = l_Lean_Server_ServerTask_mapCheap___redArg(x_188, x_190);
x_192 = lean_box(0);
if (lean_is_scalar(x_186)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_186;
 lean_ctor_set_tag(x_193, 1);
}
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_189);
lean_ctor_set(x_194, 1, x_193);
x_195 = l_Lean_Server_ServerTask_waitAny___redArg(x_194, x_185);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_198 = x_195;
} else {
 lean_dec_ref(x_195);
 x_198 = lean_box(0);
}
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_196, 0);
lean_inc(x_210);
lean_dec(x_196);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
lean_dec(x_210);
x_240 = lean_ctor_get(x_6, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 0);
lean_inc(x_242);
lean_dec(x_240);
x_243 = lean_ctor_get(x_241, 3);
lean_inc(x_243);
lean_dec(x_241);
x_244 = l_Lean_Syntax_getTailPos_x3f(x_243, x_178);
lean_dec(x_243);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; 
lean_dec(x_242);
x_245 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__2;
x_212 = x_245;
goto block_239;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_246 = lean_ctor_get(x_244, 0);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_ctor_get(x_242, 3);
lean_inc(x_247);
lean_dec(x_242);
x_248 = l_Lean_FileMap_utf8PosToLspPos(x_247, x_246);
lean_dec(x_246);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_250 = x_248;
} else {
 lean_dec_ref(x_248);
 x_250 = lean_box(0);
}
x_251 = lean_unsigned_to_nat(1u);
x_252 = lean_nat_add(x_249, x_251);
lean_dec(x_249);
x_253 = lean_unsigned_to_nat(0u);
if (lean_is_scalar(x_250)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_250;
}
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
x_212 = x_254;
goto block_239;
}
block_239:
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_213 = lean_unsigned_to_nat(0u);
x_214 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1;
x_215 = lean_array_get_size(x_211);
x_216 = lean_nat_dec_lt(x_213, x_215);
if (x_216 == 0)
{
lean_object* x_217; 
lean_dec(x_215);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_176);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_198)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_198;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_197);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
lean_dec(x_198);
lean_inc(x_212);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_212);
lean_ctor_set(x_218, 1, x_212);
x_219 = l_Array_toSubarray___redArg(x_211, x_213, x_215);
x_220 = lean_box(x_178);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_214);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_219);
lean_ctor_set(x_222, 1, x_221);
x_223 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(x_6, x_218, x_178, x_176, x_180, x_181, x_222, x_4, x_197);
lean_dec(x_4);
lean_dec(x_176);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
lean_dec(x_224);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_unbox(x_226);
lean_dec(x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_2);
x_228 = lean_ctor_get(x_223, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_229 = x_223;
} else {
 lean_dec_ref(x_223);
 x_229 = lean_box(0);
}
x_230 = lean_ctor_get(x_225, 1);
lean_inc(x_230);
lean_dec(x_225);
if (lean_is_scalar(x_229)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_229;
}
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_228);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_232 = lean_ctor_get(x_223, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_233 = x_223;
} else {
 lean_dec_ref(x_223);
 x_233 = lean_box(0);
}
x_234 = lean_ctor_get(x_225, 1);
lean_inc(x_234);
lean_dec(x_225);
x_235 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2;
x_236 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(x_2, x_235);
x_237 = lean_array_push(x_234, x_236);
if (lean_is_scalar(x_233)) {
 x_238 = lean_alloc_ctor(0, 2, 0);
} else {
 x_238 = x_233;
}
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_232);
return x_238;
}
}
}
}
else
{
lean_dec(x_210);
lean_dec(x_198);
lean_dec(x_176);
lean_dec(x_6);
lean_dec(x_2);
x_199 = x_4;
goto block_209;
}
}
else
{
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_176);
lean_dec(x_6);
lean_dec(x_2);
x_199 = x_4;
goto block_209;
}
block_209:
{
lean_object* x_200; 
x_200 = l_Lean_Server_RequestM_checkCancelled(x_199, x_197);
lean_dec(x_199);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_202 = x_200;
} else {
 lean_dec_ref(x_200);
 x_202 = lean_box(0);
}
x_203 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1;
if (lean_is_scalar(x_202)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_202;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_201);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_205 = lean_ctor_get(x_200, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_200, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_207 = x_200;
} else {
 lean_dec_ref(x_200);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
}
else
{
lean_object* x_255; lean_object* x_256; 
lean_dec(x_176);
lean_free_object(x_3);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_255 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1;
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_177);
return x_256;
}
}
}
else
{
uint8_t x_257; 
lean_free_object(x_3);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_257 = !lean_is_exclusive(x_11);
if (x_257 == 0)
{
return x_11;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_11, 0);
x_259 = lean_ctor_get(x_11, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_11);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
}
}
else
{
lean_object* x_261; lean_object* x_262; 
x_261 = lean_ctor_get(x_3, 1);
lean_inc(x_261);
lean_dec(x_3);
lean_inc(x_6);
x_262 = l_Lean_Server_FileWorker_computeQueries(x_6, x_261, x_4, x_5);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_265 = x_262;
} else {
 lean_dec_ref(x_262);
 x_265 = lean_box(0);
}
x_266 = l_Array_isEmpty___redArg(x_263);
if (x_266 == 0)
{
lean_object* x_267; size_t x_268; size_t x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_265);
x_267 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0;
x_268 = lean_array_size(x_263);
x_269 = 0;
lean_inc(x_263);
x_270 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(x_268, x_269, x_263);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_1);
lean_ctor_set(x_271, 1, x_270);
lean_inc(x_4);
x_272 = l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg(x_267, x_271, x_4, x_264);
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_275 = x_272;
} else {
 lean_dec_ref(x_272);
 x_275 = lean_box(0);
}
x_276 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__0), 1, 0);
x_277 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__1), 1, 0);
x_278 = l_Lean_Server_ServerTask_mapCheap___redArg(x_276, x_273);
x_279 = l_Lean_Server_RequestCancellationToken_requestCancellationTask(x_7);
lean_dec(x_7);
x_280 = l_Lean_Server_ServerTask_mapCheap___redArg(x_277, x_279);
x_281 = lean_box(0);
if (lean_is_scalar(x_275)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_275;
 lean_ctor_set_tag(x_282, 1);
}
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_278);
lean_ctor_set(x_283, 1, x_282);
x_284 = l_Lean_Server_ServerTask_waitAny___redArg(x_283, x_274);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_287 = x_284;
} else {
 lean_dec_ref(x_284);
 x_287 = lean_box(0);
}
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_299; 
x_299 = lean_ctor_get(x_285, 0);
lean_inc(x_299);
lean_dec(x_285);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
lean_dec(x_299);
x_329 = lean_ctor_get(x_6, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_329, 1);
lean_inc(x_330);
x_331 = lean_ctor_get(x_329, 0);
lean_inc(x_331);
lean_dec(x_329);
x_332 = lean_ctor_get(x_330, 3);
lean_inc(x_332);
lean_dec(x_330);
x_333 = l_Lean_Syntax_getTailPos_x3f(x_332, x_266);
lean_dec(x_332);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; 
lean_dec(x_331);
x_334 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__2;
x_301 = x_334;
goto block_328;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_335 = lean_ctor_get(x_333, 0);
lean_inc(x_335);
lean_dec(x_333);
x_336 = lean_ctor_get(x_331, 3);
lean_inc(x_336);
lean_dec(x_331);
x_337 = l_Lean_FileMap_utf8PosToLspPos(x_336, x_335);
lean_dec(x_335);
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_339 = x_337;
} else {
 lean_dec_ref(x_337);
 x_339 = lean_box(0);
}
x_340 = lean_unsigned_to_nat(1u);
x_341 = lean_nat_add(x_338, x_340);
lean_dec(x_338);
x_342 = lean_unsigned_to_nat(0u);
if (lean_is_scalar(x_339)) {
 x_343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_343 = x_339;
}
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
x_301 = x_343;
goto block_328;
}
block_328:
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_302 = lean_unsigned_to_nat(0u);
x_303 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1;
x_304 = lean_array_get_size(x_300);
x_305 = lean_nat_dec_lt(x_302, x_304);
if (x_305 == 0)
{
lean_object* x_306; 
lean_dec(x_304);
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_263);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_287)) {
 x_306 = lean_alloc_ctor(0, 2, 0);
} else {
 x_306 = x_287;
}
lean_ctor_set(x_306, 0, x_303);
lean_ctor_set(x_306, 1, x_286);
return x_306;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
lean_dec(x_287);
lean_inc(x_301);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_301);
lean_ctor_set(x_307, 1, x_301);
x_308 = l_Array_toSubarray___redArg(x_300, x_302, x_304);
x_309 = lean_box(x_266);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_303);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_308);
lean_ctor_set(x_311, 1, x_310);
x_312 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(x_6, x_307, x_266, x_263, x_268, x_269, x_311, x_4, x_286);
lean_dec(x_4);
lean_dec(x_263);
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_313, 1);
lean_inc(x_314);
lean_dec(x_313);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_unbox(x_315);
lean_dec(x_315);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_2);
x_317 = lean_ctor_get(x_312, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_318 = x_312;
} else {
 lean_dec_ref(x_312);
 x_318 = lean_box(0);
}
x_319 = lean_ctor_get(x_314, 1);
lean_inc(x_319);
lean_dec(x_314);
if (lean_is_scalar(x_318)) {
 x_320 = lean_alloc_ctor(0, 2, 0);
} else {
 x_320 = x_318;
}
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_317);
return x_320;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_321 = lean_ctor_get(x_312, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_322 = x_312;
} else {
 lean_dec_ref(x_312);
 x_322 = lean_box(0);
}
x_323 = lean_ctor_get(x_314, 1);
lean_inc(x_323);
lean_dec(x_314);
x_324 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2;
x_325 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(x_2, x_324);
x_326 = lean_array_push(x_323, x_325);
if (lean_is_scalar(x_322)) {
 x_327 = lean_alloc_ctor(0, 2, 0);
} else {
 x_327 = x_322;
}
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_321);
return x_327;
}
}
}
}
else
{
lean_dec(x_299);
lean_dec(x_287);
lean_dec(x_263);
lean_dec(x_6);
lean_dec(x_2);
x_288 = x_4;
goto block_298;
}
}
else
{
lean_dec(x_287);
lean_dec(x_285);
lean_dec(x_263);
lean_dec(x_6);
lean_dec(x_2);
x_288 = x_4;
goto block_298;
}
block_298:
{
lean_object* x_289; 
x_289 = l_Lean_Server_RequestM_checkCancelled(x_288, x_286);
lean_dec(x_288);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_290 = lean_ctor_get(x_289, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_291 = x_289;
} else {
 lean_dec_ref(x_289);
 x_291 = lean_box(0);
}
x_292 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1;
if (lean_is_scalar(x_291)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_291;
}
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_290);
return x_293;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_294 = lean_ctor_get(x_289, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_289, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_296 = x_289;
} else {
 lean_dec_ref(x_289);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_296)) {
 x_297 = lean_alloc_ctor(1, 2, 0);
} else {
 x_297 = x_296;
}
lean_ctor_set(x_297, 0, x_294);
lean_ctor_set(x_297, 1, x_295);
return x_297;
}
}
}
else
{
lean_object* x_344; lean_object* x_345; 
lean_dec(x_263);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_344 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1;
if (lean_is_scalar(x_265)) {
 x_345 = lean_alloc_ctor(0, 2, 0);
} else {
 x_345 = x_265;
}
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_264);
return x_345;
}
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_346 = lean_ctor_get(x_262, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_262, 1);
lean_inc(x_347);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_348 = x_262;
} else {
 lean_dec_ref(x_262);
 x_348 = lean_box(0);
}
if (lean_is_scalar(x_348)) {
 x_349 = lean_alloc_ctor(1, 2, 0);
} else {
 x_349 = x_348;
}
lean_ctor_set(x_349, 0, x_346);
lean_ctor_set(x_349, 1, x_347);
return x_349;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(x_1, x_2, x_3, x_10, x_5, x_11, x_12, x_8, x_9);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2(x_1, x_2, x_3, x_11, x_5, x_12, x_13, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3_spec__3(x_1, x_2, x_10, x_4, x_11, x_12, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(x_1, x_2, x_10, x_4, x_11, x_12, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_7);
return x_7;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_uget(x_4, x_6);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*2);
if (x_15 == 0)
{
lean_dec(x_14);
x_8 = x_1;
goto block_12;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
x_18 = l_Lean_Environment_contains(x_17, x_16, x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
else
{
lean_dec(x_14);
x_8 = x_1;
goto block_12;
}
}
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_6, x_9);
x_6 = x_10;
x_7 = x_8;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_17 = x_5;
} else {
 lean_dec_ref(x_5);
 x_17 = lean_box(0);
}
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_20 = x_15;
} else {
 lean_dec_ref(x_15);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_16, 2);
lean_inc(x_23);
x_24 = lean_nat_dec_lt(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_1);
if (lean_is_scalar(x_20)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_20;
}
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_19);
if (lean_is_scalar(x_17)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_17;
}
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_6);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_29 = lean_ctor_get(x_16, 2);
lean_dec(x_29);
x_30 = lean_ctor_get(x_16, 1);
lean_dec(x_30);
x_31 = lean_ctor_get(x_16, 0);
lean_dec(x_31);
x_32 = lean_array_uget(x_2, x_4);
x_33 = lean_array_fget(x_21, x_22);
x_34 = lean_box(0);
x_35 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg___closed__0;
x_36 = lean_array_size(x_33);
x_37 = 0;
lean_inc(x_32);
x_38 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(x_35, x_32, x_34, x_33, x_36, x_37, x_35);
lean_dec(x_33);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_22, x_41);
lean_dec(x_22);
lean_ctor_set(x_16, 1, x_42);
if (lean_obj_tag(x_39) == 0)
{
lean_dec(x_40);
lean_dec(x_32);
lean_dec(x_20);
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_39, 0);
lean_inc(x_52);
lean_dec(x_39);
if (lean_obj_tag(x_52) == 0)
{
lean_dec(x_40);
lean_dec(x_32);
lean_dec(x_20);
goto block_51;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_17);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_32, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_32, 2);
lean_inc(x_57);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 x_58 = x_32;
} else {
 lean_dec_ref(x_32);
 x_58 = lean_box(0);
}
x_59 = l_Lean_Environment_mainModule(x_56);
lean_dec(x_56);
x_60 = lean_name_eq(x_54, x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_130; lean_object* x_140; uint64_t x_141; uint64_t x_142; uint64_t x_143; uint64_t x_144; uint64_t x_145; uint64_t x_146; uint64_t x_147; size_t x_148; size_t x_149; size_t x_150; size_t x_151; size_t x_152; lean_object* x_153; uint8_t x_154; 
x_61 = lean_ctor_get(x_19, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_19, 1);
lean_inc(x_62);
x_63 = lean_box(x_60);
x_64 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_64, 0, x_63);
x_65 = lean_apply_1(x_57, x_55);
x_140 = lean_array_get_size(x_62);
x_141 = l_Lean_Name_hash___override(x_54);
x_142 = 32;
x_143 = lean_uint64_shift_right(x_141, x_142);
x_144 = lean_uint64_xor(x_141, x_143);
x_145 = 16;
x_146 = lean_uint64_shift_right(x_144, x_145);
x_147 = lean_uint64_xor(x_144, x_146);
x_148 = lean_uint64_to_usize(x_147);
x_149 = lean_usize_of_nat(x_140);
lean_dec(x_140);
x_150 = 1;
x_151 = lean_usize_sub(x_149, x_150);
x_152 = lean_usize_land(x_148, x_151);
x_153 = lean_array_uget(x_62, x_152);
x_154 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__0___redArg(x_54, x_153);
lean_dec(x_153);
if (x_154 == 0)
{
x_130 = x_24;
goto block_139;
}
else
{
if (x_60 == 0)
{
lean_dec(x_64);
x_66 = x_18;
x_67 = x_19;
x_68 = x_61;
x_69 = x_62;
x_70 = x_6;
goto block_129;
}
else
{
x_130 = x_60;
goto block_139;
}
}
block_129:
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_65);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; size_t x_83; size_t x_84; size_t x_85; size_t x_86; size_t x_87; lean_object* x_88; uint8_t x_89; 
x_72 = lean_ctor_get(x_65, 1);
x_73 = lean_ctor_get(x_65, 0);
lean_dec(x_73);
x_74 = lean_array_push(x_66, x_72);
x_75 = lean_array_get_size(x_69);
x_76 = l_Lean_Name_hash___override(x_54);
x_77 = 32;
x_78 = lean_uint64_shift_right(x_76, x_77);
x_79 = lean_uint64_xor(x_76, x_78);
x_80 = 16;
x_81 = lean_uint64_shift_right(x_79, x_80);
x_82 = lean_uint64_xor(x_79, x_81);
x_83 = lean_uint64_to_usize(x_82);
x_84 = lean_usize_of_nat(x_75);
lean_dec(x_75);
x_85 = 1;
x_86 = lean_usize_sub(x_84, x_85);
x_87 = lean_usize_land(x_83, x_86);
x_88 = lean_array_uget(x_69, x_87);
x_89 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__0___redArg(x_54, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
lean_dec(x_67);
x_90 = lean_nat_add(x_68, x_41);
lean_dec(x_68);
if (lean_is_scalar(x_58)) {
 x_91 = lean_alloc_ctor(1, 3, 0);
} else {
 x_91 = x_58;
 lean_ctor_set_tag(x_91, 1);
}
lean_ctor_set(x_91, 0, x_54);
lean_ctor_set(x_91, 1, x_34);
lean_ctor_set(x_91, 2, x_88);
x_92 = lean_array_uset(x_69, x_87, x_91);
x_93 = lean_unsigned_to_nat(4u);
x_94 = lean_nat_mul(x_90, x_93);
x_95 = lean_unsigned_to_nat(3u);
x_96 = lean_nat_div(x_94, x_95);
lean_dec(x_94);
x_97 = lean_array_get_size(x_92);
x_98 = lean_nat_dec_le(x_96, x_97);
lean_dec(x_97);
lean_dec(x_96);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__1___redArg(x_92);
lean_ctor_set(x_65, 1, x_99);
lean_ctor_set(x_65, 0, x_90);
x_43 = x_74;
x_44 = x_70;
x_45 = x_65;
goto block_48;
}
else
{
lean_ctor_set(x_65, 1, x_92);
lean_ctor_set(x_65, 0, x_90);
x_43 = x_74;
x_44 = x_70;
x_45 = x_65;
goto block_48;
}
}
else
{
lean_dec(x_88);
lean_free_object(x_65);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_58);
lean_dec(x_54);
x_43 = x_74;
x_44 = x_70;
x_45 = x_67;
goto block_48;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint64_t x_103; uint64_t x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; uint64_t x_108; uint64_t x_109; size_t x_110; size_t x_111; size_t x_112; size_t x_113; size_t x_114; lean_object* x_115; uint8_t x_116; 
x_100 = lean_ctor_get(x_65, 1);
lean_inc(x_100);
lean_dec(x_65);
x_101 = lean_array_push(x_66, x_100);
x_102 = lean_array_get_size(x_69);
x_103 = l_Lean_Name_hash___override(x_54);
x_104 = 32;
x_105 = lean_uint64_shift_right(x_103, x_104);
x_106 = lean_uint64_xor(x_103, x_105);
x_107 = 16;
x_108 = lean_uint64_shift_right(x_106, x_107);
x_109 = lean_uint64_xor(x_106, x_108);
x_110 = lean_uint64_to_usize(x_109);
x_111 = lean_usize_of_nat(x_102);
lean_dec(x_102);
x_112 = 1;
x_113 = lean_usize_sub(x_111, x_112);
x_114 = lean_usize_land(x_110, x_113);
x_115 = lean_array_uget(x_69, x_114);
x_116 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__0___redArg(x_54, x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
lean_dec(x_67);
x_117 = lean_nat_add(x_68, x_41);
lean_dec(x_68);
if (lean_is_scalar(x_58)) {
 x_118 = lean_alloc_ctor(1, 3, 0);
} else {
 x_118 = x_58;
 lean_ctor_set_tag(x_118, 1);
}
lean_ctor_set(x_118, 0, x_54);
lean_ctor_set(x_118, 1, x_34);
lean_ctor_set(x_118, 2, x_115);
x_119 = lean_array_uset(x_69, x_114, x_118);
x_120 = lean_unsigned_to_nat(4u);
x_121 = lean_nat_mul(x_117, x_120);
x_122 = lean_unsigned_to_nat(3u);
x_123 = lean_nat_div(x_121, x_122);
lean_dec(x_121);
x_124 = lean_array_get_size(x_119);
x_125 = lean_nat_dec_le(x_123, x_124);
lean_dec(x_124);
lean_dec(x_123);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__1___redArg(x_119);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_117);
lean_ctor_set(x_127, 1, x_126);
x_43 = x_101;
x_44 = x_70;
x_45 = x_127;
goto block_48;
}
else
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_117);
lean_ctor_set(x_128, 1, x_119);
x_43 = x_101;
x_44 = x_70;
x_45 = x_128;
goto block_48;
}
}
else
{
lean_dec(x_115);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_58);
lean_dec(x_54);
x_43 = x_101;
x_44 = x_70;
x_45 = x_67;
goto block_48;
}
}
}
block_139:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_131 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__4;
lean_inc(x_54);
x_132 = l_Lean_Name_toString(x_54, x_130, x_64);
x_133 = lean_string_append(x_131, x_132);
lean_dec(x_132);
x_134 = l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg___lam__0___closed__1;
x_135 = lean_string_append(x_133, x_134);
x_136 = lean_box(0);
lean_inc(x_1);
x_137 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_137, 0, x_1);
lean_ctor_set(x_137, 1, x_135);
lean_ctor_set(x_137, 2, x_136);
lean_ctor_set(x_137, 3, x_136);
x_138 = lean_array_push(x_18, x_137);
x_66 = x_138;
x_67 = x_19;
x_68 = x_61;
x_69 = x_62;
x_70 = x_6;
goto block_129;
}
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_40);
lean_dec(x_20);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_18);
lean_ctor_set(x_155, 1, x_19);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_16);
lean_ctor_set(x_156, 1, x_155);
x_7 = x_156;
x_8 = x_6;
goto block_12;
}
}
}
block_48:
{
lean_object* x_46; lean_object* x_47; 
if (lean_is_scalar(x_40)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_40;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
if (lean_is_scalar(x_20)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_20;
}
lean_ctor_set(x_47, 0, x_16);
lean_ctor_set(x_47, 1, x_46);
x_7 = x_47;
x_8 = x_44;
goto block_12;
}
block_51:
{
lean_object* x_49; lean_object* x_50; 
if (lean_is_scalar(x_17)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_17;
}
lean_ctor_set(x_49, 0, x_18);
lean_ctor_set(x_49, 1, x_19);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_16);
lean_ctor_set(x_50, 1, x_49);
x_7 = x_50;
x_8 = x_6;
goto block_12;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; size_t x_161; size_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_16);
x_157 = lean_array_uget(x_2, x_4);
x_158 = lean_array_fget(x_21, x_22);
x_159 = lean_box(0);
x_160 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg___closed__0;
x_161 = lean_array_size(x_158);
x_162 = 0;
lean_inc(x_157);
x_163 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(x_160, x_157, x_159, x_158, x_161, x_162, x_160);
lean_dec(x_158);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_165 = x_163;
} else {
 lean_dec_ref(x_163);
 x_165 = lean_box(0);
}
x_166 = lean_unsigned_to_nat(1u);
x_167 = lean_nat_add(x_22, x_166);
lean_dec(x_22);
x_168 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_168, 0, x_21);
lean_ctor_set(x_168, 1, x_167);
lean_ctor_set(x_168, 2, x_23);
if (lean_obj_tag(x_164) == 0)
{
lean_dec(x_165);
lean_dec(x_157);
lean_dec(x_20);
goto block_177;
}
else
{
lean_object* x_178; 
x_178 = lean_ctor_get(x_164, 0);
lean_inc(x_178);
lean_dec(x_164);
if (lean_obj_tag(x_178) == 0)
{
lean_dec(x_165);
lean_dec(x_157);
lean_dec(x_20);
goto block_177;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
lean_dec(x_17);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
lean_dec(x_178);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_ctor_get(x_157, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_157, 2);
lean_inc(x_183);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 lean_ctor_release(x_157, 2);
 x_184 = x_157;
} else {
 lean_dec_ref(x_157);
 x_184 = lean_box(0);
}
x_185 = l_Lean_Environment_mainModule(x_182);
lean_dec(x_182);
x_186 = lean_name_eq(x_180, x_185);
lean_dec(x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_228; lean_object* x_238; uint64_t x_239; uint64_t x_240; uint64_t x_241; uint64_t x_242; uint64_t x_243; uint64_t x_244; uint64_t x_245; size_t x_246; size_t x_247; size_t x_248; size_t x_249; size_t x_250; lean_object* x_251; uint8_t x_252; 
x_187 = lean_ctor_get(x_19, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_19, 1);
lean_inc(x_188);
x_189 = lean_box(x_186);
x_190 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_190, 0, x_189);
x_191 = lean_apply_1(x_183, x_181);
x_238 = lean_array_get_size(x_188);
x_239 = l_Lean_Name_hash___override(x_180);
x_240 = 32;
x_241 = lean_uint64_shift_right(x_239, x_240);
x_242 = lean_uint64_xor(x_239, x_241);
x_243 = 16;
x_244 = lean_uint64_shift_right(x_242, x_243);
x_245 = lean_uint64_xor(x_242, x_244);
x_246 = lean_uint64_to_usize(x_245);
x_247 = lean_usize_of_nat(x_238);
lean_dec(x_238);
x_248 = 1;
x_249 = lean_usize_sub(x_247, x_248);
x_250 = lean_usize_land(x_246, x_249);
x_251 = lean_array_uget(x_188, x_250);
x_252 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__0___redArg(x_180, x_251);
lean_dec(x_251);
if (x_252 == 0)
{
x_228 = x_24;
goto block_237;
}
else
{
if (x_186 == 0)
{
lean_dec(x_190);
x_192 = x_18;
x_193 = x_19;
x_194 = x_187;
x_195 = x_188;
x_196 = x_6;
goto block_227;
}
else
{
x_228 = x_186;
goto block_237;
}
}
block_227:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint64_t x_201; uint64_t x_202; uint64_t x_203; uint64_t x_204; uint64_t x_205; uint64_t x_206; uint64_t x_207; size_t x_208; size_t x_209; size_t x_210; size_t x_211; size_t x_212; lean_object* x_213; uint8_t x_214; 
x_197 = lean_ctor_get(x_191, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_198 = x_191;
} else {
 lean_dec_ref(x_191);
 x_198 = lean_box(0);
}
x_199 = lean_array_push(x_192, x_197);
x_200 = lean_array_get_size(x_195);
x_201 = l_Lean_Name_hash___override(x_180);
x_202 = 32;
x_203 = lean_uint64_shift_right(x_201, x_202);
x_204 = lean_uint64_xor(x_201, x_203);
x_205 = 16;
x_206 = lean_uint64_shift_right(x_204, x_205);
x_207 = lean_uint64_xor(x_204, x_206);
x_208 = lean_uint64_to_usize(x_207);
x_209 = lean_usize_of_nat(x_200);
lean_dec(x_200);
x_210 = 1;
x_211 = lean_usize_sub(x_209, x_210);
x_212 = lean_usize_land(x_208, x_211);
x_213 = lean_array_uget(x_195, x_212);
x_214 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__0___redArg(x_180, x_213);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
lean_dec(x_193);
x_215 = lean_nat_add(x_194, x_166);
lean_dec(x_194);
if (lean_is_scalar(x_184)) {
 x_216 = lean_alloc_ctor(1, 3, 0);
} else {
 x_216 = x_184;
 lean_ctor_set_tag(x_216, 1);
}
lean_ctor_set(x_216, 0, x_180);
lean_ctor_set(x_216, 1, x_159);
lean_ctor_set(x_216, 2, x_213);
x_217 = lean_array_uset(x_195, x_212, x_216);
x_218 = lean_unsigned_to_nat(4u);
x_219 = lean_nat_mul(x_215, x_218);
x_220 = lean_unsigned_to_nat(3u);
x_221 = lean_nat_div(x_219, x_220);
lean_dec(x_219);
x_222 = lean_array_get_size(x_217);
x_223 = lean_nat_dec_le(x_221, x_222);
lean_dec(x_222);
lean_dec(x_221);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; 
x_224 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__1___redArg(x_217);
if (lean_is_scalar(x_198)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_198;
}
lean_ctor_set(x_225, 0, x_215);
lean_ctor_set(x_225, 1, x_224);
x_169 = x_199;
x_170 = x_196;
x_171 = x_225;
goto block_174;
}
else
{
lean_object* x_226; 
if (lean_is_scalar(x_198)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_198;
}
lean_ctor_set(x_226, 0, x_215);
lean_ctor_set(x_226, 1, x_217);
x_169 = x_199;
x_170 = x_196;
x_171 = x_226;
goto block_174;
}
}
else
{
lean_dec(x_213);
lean_dec(x_198);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_184);
lean_dec(x_180);
x_169 = x_199;
x_170 = x_196;
x_171 = x_193;
goto block_174;
}
}
block_237:
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_229 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__4;
lean_inc(x_180);
x_230 = l_Lean_Name_toString(x_180, x_228, x_190);
x_231 = lean_string_append(x_229, x_230);
lean_dec(x_230);
x_232 = l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg___lam__0___closed__1;
x_233 = lean_string_append(x_231, x_232);
x_234 = lean_box(0);
lean_inc(x_1);
x_235 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_235, 0, x_1);
lean_ctor_set(x_235, 1, x_233);
lean_ctor_set(x_235, 2, x_234);
lean_ctor_set(x_235, 3, x_234);
x_236 = lean_array_push(x_18, x_235);
x_192 = x_236;
x_193 = x_19;
x_194 = x_187;
x_195 = x_188;
x_196 = x_6;
goto block_227;
}
}
else
{
lean_object* x_253; lean_object* x_254; 
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_165);
lean_dec(x_20);
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_18);
lean_ctor_set(x_253, 1, x_19);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_168);
lean_ctor_set(x_254, 1, x_253);
x_7 = x_254;
x_8 = x_6;
goto block_12;
}
}
}
block_174:
{
lean_object* x_172; lean_object* x_173; 
if (lean_is_scalar(x_165)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_165;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_171);
if (lean_is_scalar(x_20)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_20;
}
lean_ctor_set(x_173, 0, x_168);
lean_ctor_set(x_173, 1, x_172);
x_7 = x_173;
x_8 = x_170;
goto block_12;
}
block_177:
{
lean_object* x_175; lean_object* x_176; 
if (lean_is_scalar(x_17)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_17;
}
lean_ctor_set(x_175, 0, x_18);
lean_ctor_set(x_175, 1, x_19);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_168);
lean_ctor_set(x_176, 1, x_175);
x_7 = x_176;
x_8 = x_6;
goto block_12;
}
}
}
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
x_5 = x_7;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(x_3, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_6, x_5);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_3);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_20 = x_7;
} else {
 lean_dec_ref(x_7);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_23 = x_18;
} else {
 lean_dec_ref(x_18);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_19, 2);
lean_inc(x_26);
x_27 = lean_nat_dec_lt(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
if (lean_is_scalar(x_23)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_23;
}
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_22);
if (lean_is_scalar(x_20)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_20;
}
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_9);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_32 = lean_ctor_get(x_19, 2);
lean_dec(x_32);
x_33 = lean_ctor_get(x_19, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_19, 0);
lean_dec(x_34);
x_35 = lean_array_uget(x_4, x_6);
x_36 = lean_array_fget(x_24, x_25);
x_37 = lean_box(0);
x_38 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg___closed__0;
x_39 = lean_array_size(x_36);
x_40 = 0;
lean_inc(x_35);
x_41 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(x_38, x_35, x_37, x_36, x_39, x_40, x_38);
lean_dec(x_36);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_25, x_44);
lean_dec(x_25);
lean_ctor_set(x_19, 1, x_45);
if (lean_obj_tag(x_42) == 0)
{
lean_dec(x_43);
lean_dec(x_35);
lean_dec(x_23);
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_42, 0);
lean_inc(x_55);
lean_dec(x_42);
if (lean_obj_tag(x_55) == 0)
{
lean_dec(x_43);
lean_dec(x_35);
lean_dec(x_23);
goto block_54;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_dec(x_20);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_35, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_35, 2);
lean_inc(x_60);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 lean_ctor_release(x_35, 2);
 x_61 = x_35;
} else {
 lean_dec_ref(x_35);
 x_61 = lean_box(0);
}
x_62 = l_Lean_Environment_mainModule(x_59);
lean_dec(x_59);
x_63 = lean_name_eq(x_57, x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_133; lean_object* x_143; uint64_t x_144; uint64_t x_145; uint64_t x_146; uint64_t x_147; uint64_t x_148; uint64_t x_149; uint64_t x_150; size_t x_151; size_t x_152; size_t x_153; size_t x_154; size_t x_155; lean_object* x_156; uint8_t x_157; 
x_64 = lean_ctor_get(x_22, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_22, 1);
lean_inc(x_65);
x_66 = lean_box(x_63);
x_67 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_67, 0, x_66);
x_68 = lean_apply_1(x_60, x_58);
x_143 = lean_array_get_size(x_65);
x_144 = l_Lean_Name_hash___override(x_57);
x_145 = 32;
x_146 = lean_uint64_shift_right(x_144, x_145);
x_147 = lean_uint64_xor(x_144, x_146);
x_148 = 16;
x_149 = lean_uint64_shift_right(x_147, x_148);
x_150 = lean_uint64_xor(x_147, x_149);
x_151 = lean_uint64_to_usize(x_150);
x_152 = lean_usize_of_nat(x_143);
lean_dec(x_143);
x_153 = 1;
x_154 = lean_usize_sub(x_152, x_153);
x_155 = lean_usize_land(x_151, x_154);
x_156 = lean_array_uget(x_65, x_155);
x_157 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__0___redArg(x_57, x_156);
lean_dec(x_156);
if (x_157 == 0)
{
x_133 = x_27;
goto block_142;
}
else
{
if (x_63 == 0)
{
lean_dec(x_67);
x_69 = x_21;
x_70 = x_22;
x_71 = x_64;
x_72 = x_65;
x_73 = x_9;
goto block_132;
}
else
{
x_133 = x_63;
goto block_142;
}
}
block_132:
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_68);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; uint64_t x_85; size_t x_86; size_t x_87; size_t x_88; size_t x_89; size_t x_90; lean_object* x_91; uint8_t x_92; 
x_75 = lean_ctor_get(x_68, 1);
x_76 = lean_ctor_get(x_68, 0);
lean_dec(x_76);
x_77 = lean_array_push(x_69, x_75);
x_78 = lean_array_get_size(x_72);
x_79 = l_Lean_Name_hash___override(x_57);
x_80 = 32;
x_81 = lean_uint64_shift_right(x_79, x_80);
x_82 = lean_uint64_xor(x_79, x_81);
x_83 = 16;
x_84 = lean_uint64_shift_right(x_82, x_83);
x_85 = lean_uint64_xor(x_82, x_84);
x_86 = lean_uint64_to_usize(x_85);
x_87 = lean_usize_of_nat(x_78);
lean_dec(x_78);
x_88 = 1;
x_89 = lean_usize_sub(x_87, x_88);
x_90 = lean_usize_land(x_86, x_89);
x_91 = lean_array_uget(x_72, x_90);
x_92 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__0___redArg(x_57, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
lean_dec(x_70);
x_93 = lean_nat_add(x_71, x_44);
lean_dec(x_71);
if (lean_is_scalar(x_61)) {
 x_94 = lean_alloc_ctor(1, 3, 0);
} else {
 x_94 = x_61;
 lean_ctor_set_tag(x_94, 1);
}
lean_ctor_set(x_94, 0, x_57);
lean_ctor_set(x_94, 1, x_37);
lean_ctor_set(x_94, 2, x_91);
x_95 = lean_array_uset(x_72, x_90, x_94);
x_96 = lean_unsigned_to_nat(4u);
x_97 = lean_nat_mul(x_93, x_96);
x_98 = lean_unsigned_to_nat(3u);
x_99 = lean_nat_div(x_97, x_98);
lean_dec(x_97);
x_100 = lean_array_get_size(x_95);
x_101 = lean_nat_dec_le(x_99, x_100);
lean_dec(x_100);
lean_dec(x_99);
if (x_101 == 0)
{
lean_object* x_102; 
x_102 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__1___redArg(x_95);
lean_ctor_set(x_68, 1, x_102);
lean_ctor_set(x_68, 0, x_93);
x_46 = x_77;
x_47 = x_73;
x_48 = x_68;
goto block_51;
}
else
{
lean_ctor_set(x_68, 1, x_95);
lean_ctor_set(x_68, 0, x_93);
x_46 = x_77;
x_47 = x_73;
x_48 = x_68;
goto block_51;
}
}
else
{
lean_dec(x_91);
lean_free_object(x_68);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_61);
lean_dec(x_57);
x_46 = x_77;
x_47 = x_73;
x_48 = x_70;
goto block_51;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint64_t x_106; uint64_t x_107; uint64_t x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; size_t x_113; size_t x_114; size_t x_115; size_t x_116; size_t x_117; lean_object* x_118; uint8_t x_119; 
x_103 = lean_ctor_get(x_68, 1);
lean_inc(x_103);
lean_dec(x_68);
x_104 = lean_array_push(x_69, x_103);
x_105 = lean_array_get_size(x_72);
x_106 = l_Lean_Name_hash___override(x_57);
x_107 = 32;
x_108 = lean_uint64_shift_right(x_106, x_107);
x_109 = lean_uint64_xor(x_106, x_108);
x_110 = 16;
x_111 = lean_uint64_shift_right(x_109, x_110);
x_112 = lean_uint64_xor(x_109, x_111);
x_113 = lean_uint64_to_usize(x_112);
x_114 = lean_usize_of_nat(x_105);
lean_dec(x_105);
x_115 = 1;
x_116 = lean_usize_sub(x_114, x_115);
x_117 = lean_usize_land(x_113, x_116);
x_118 = lean_array_uget(x_72, x_117);
x_119 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__0___redArg(x_57, x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
lean_dec(x_70);
x_120 = lean_nat_add(x_71, x_44);
lean_dec(x_71);
if (lean_is_scalar(x_61)) {
 x_121 = lean_alloc_ctor(1, 3, 0);
} else {
 x_121 = x_61;
 lean_ctor_set_tag(x_121, 1);
}
lean_ctor_set(x_121, 0, x_57);
lean_ctor_set(x_121, 1, x_37);
lean_ctor_set(x_121, 2, x_118);
x_122 = lean_array_uset(x_72, x_117, x_121);
x_123 = lean_unsigned_to_nat(4u);
x_124 = lean_nat_mul(x_120, x_123);
x_125 = lean_unsigned_to_nat(3u);
x_126 = lean_nat_div(x_124, x_125);
lean_dec(x_124);
x_127 = lean_array_get_size(x_122);
x_128 = lean_nat_dec_le(x_126, x_127);
lean_dec(x_127);
lean_dec(x_126);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__1___redArg(x_122);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_120);
lean_ctor_set(x_130, 1, x_129);
x_46 = x_104;
x_47 = x_73;
x_48 = x_130;
goto block_51;
}
else
{
lean_object* x_131; 
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_120);
lean_ctor_set(x_131, 1, x_122);
x_46 = x_104;
x_47 = x_73;
x_48 = x_131;
goto block_51;
}
}
else
{
lean_dec(x_118);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_61);
lean_dec(x_57);
x_46 = x_104;
x_47 = x_73;
x_48 = x_70;
goto block_51;
}
}
}
block_142:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_134 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__4;
lean_inc(x_57);
x_135 = l_Lean_Name_toString(x_57, x_133, x_67);
x_136 = lean_string_append(x_134, x_135);
lean_dec(x_135);
x_137 = l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg___lam__0___closed__1;
x_138 = lean_string_append(x_136, x_137);
x_139 = lean_box(0);
lean_inc(x_3);
x_140 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_140, 0, x_3);
lean_ctor_set(x_140, 1, x_138);
lean_ctor_set(x_140, 2, x_139);
lean_ctor_set(x_140, 3, x_139);
x_141 = lean_array_push(x_21, x_140);
x_69 = x_141;
x_70 = x_22;
x_71 = x_64;
x_72 = x_65;
x_73 = x_9;
goto block_132;
}
}
else
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_43);
lean_dec(x_23);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_21);
lean_ctor_set(x_158, 1, x_22);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_19);
lean_ctor_set(x_159, 1, x_158);
x_10 = x_159;
x_11 = x_9;
goto block_15;
}
}
}
block_51:
{
lean_object* x_49; lean_object* x_50; 
if (lean_is_scalar(x_43)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_43;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
if (lean_is_scalar(x_23)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_23;
}
lean_ctor_set(x_50, 0, x_19);
lean_ctor_set(x_50, 1, x_49);
x_10 = x_50;
x_11 = x_47;
goto block_15;
}
block_54:
{
lean_object* x_52; lean_object* x_53; 
if (lean_is_scalar(x_20)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_20;
}
lean_ctor_set(x_52, 0, x_21);
lean_ctor_set(x_52, 1, x_22);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_19);
lean_ctor_set(x_53, 1, x_52);
x_10 = x_53;
x_11 = x_9;
goto block_15;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; size_t x_164; size_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_19);
x_160 = lean_array_uget(x_4, x_6);
x_161 = lean_array_fget(x_24, x_25);
x_162 = lean_box(0);
x_163 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg___closed__0;
x_164 = lean_array_size(x_161);
x_165 = 0;
lean_inc(x_160);
x_166 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(x_163, x_160, x_162, x_161, x_164, x_165, x_163);
lean_dec(x_161);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_168 = x_166;
} else {
 lean_dec_ref(x_166);
 x_168 = lean_box(0);
}
x_169 = lean_unsigned_to_nat(1u);
x_170 = lean_nat_add(x_25, x_169);
lean_dec(x_25);
x_171 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_171, 0, x_24);
lean_ctor_set(x_171, 1, x_170);
lean_ctor_set(x_171, 2, x_26);
if (lean_obj_tag(x_167) == 0)
{
lean_dec(x_168);
lean_dec(x_160);
lean_dec(x_23);
goto block_180;
}
else
{
lean_object* x_181; 
x_181 = lean_ctor_get(x_167, 0);
lean_inc(x_181);
lean_dec(x_167);
if (lean_obj_tag(x_181) == 0)
{
lean_dec(x_168);
lean_dec(x_160);
lean_dec(x_23);
goto block_180;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
lean_dec(x_20);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
lean_dec(x_181);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_ctor_get(x_160, 1);
lean_inc(x_185);
x_186 = lean_ctor_get(x_160, 2);
lean_inc(x_186);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 x_187 = x_160;
} else {
 lean_dec_ref(x_160);
 x_187 = lean_box(0);
}
x_188 = l_Lean_Environment_mainModule(x_185);
lean_dec(x_185);
x_189 = lean_name_eq(x_183, x_188);
lean_dec(x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_231; lean_object* x_241; uint64_t x_242; uint64_t x_243; uint64_t x_244; uint64_t x_245; uint64_t x_246; uint64_t x_247; uint64_t x_248; size_t x_249; size_t x_250; size_t x_251; size_t x_252; size_t x_253; lean_object* x_254; uint8_t x_255; 
x_190 = lean_ctor_get(x_22, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_22, 1);
lean_inc(x_191);
x_192 = lean_box(x_189);
x_193 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_193, 0, x_192);
x_194 = lean_apply_1(x_186, x_184);
x_241 = lean_array_get_size(x_191);
x_242 = l_Lean_Name_hash___override(x_183);
x_243 = 32;
x_244 = lean_uint64_shift_right(x_242, x_243);
x_245 = lean_uint64_xor(x_242, x_244);
x_246 = 16;
x_247 = lean_uint64_shift_right(x_245, x_246);
x_248 = lean_uint64_xor(x_245, x_247);
x_249 = lean_uint64_to_usize(x_248);
x_250 = lean_usize_of_nat(x_241);
lean_dec(x_241);
x_251 = 1;
x_252 = lean_usize_sub(x_250, x_251);
x_253 = lean_usize_land(x_249, x_252);
x_254 = lean_array_uget(x_191, x_253);
x_255 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__0___redArg(x_183, x_254);
lean_dec(x_254);
if (x_255 == 0)
{
x_231 = x_27;
goto block_240;
}
else
{
if (x_189 == 0)
{
lean_dec(x_193);
x_195 = x_21;
x_196 = x_22;
x_197 = x_190;
x_198 = x_191;
x_199 = x_9;
goto block_230;
}
else
{
x_231 = x_189;
goto block_240;
}
}
block_230:
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint64_t x_204; uint64_t x_205; uint64_t x_206; uint64_t x_207; uint64_t x_208; uint64_t x_209; uint64_t x_210; size_t x_211; size_t x_212; size_t x_213; size_t x_214; size_t x_215; lean_object* x_216; uint8_t x_217; 
x_200 = lean_ctor_get(x_194, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_201 = x_194;
} else {
 lean_dec_ref(x_194);
 x_201 = lean_box(0);
}
x_202 = lean_array_push(x_195, x_200);
x_203 = lean_array_get_size(x_198);
x_204 = l_Lean_Name_hash___override(x_183);
x_205 = 32;
x_206 = lean_uint64_shift_right(x_204, x_205);
x_207 = lean_uint64_xor(x_204, x_206);
x_208 = 16;
x_209 = lean_uint64_shift_right(x_207, x_208);
x_210 = lean_uint64_xor(x_207, x_209);
x_211 = lean_uint64_to_usize(x_210);
x_212 = lean_usize_of_nat(x_203);
lean_dec(x_203);
x_213 = 1;
x_214 = lean_usize_sub(x_212, x_213);
x_215 = lean_usize_land(x_211, x_214);
x_216 = lean_array_uget(x_198, x_215);
x_217 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__0___redArg(x_183, x_216);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
lean_dec(x_196);
x_218 = lean_nat_add(x_197, x_169);
lean_dec(x_197);
if (lean_is_scalar(x_187)) {
 x_219 = lean_alloc_ctor(1, 3, 0);
} else {
 x_219 = x_187;
 lean_ctor_set_tag(x_219, 1);
}
lean_ctor_set(x_219, 0, x_183);
lean_ctor_set(x_219, 1, x_162);
lean_ctor_set(x_219, 2, x_216);
x_220 = lean_array_uset(x_198, x_215, x_219);
x_221 = lean_unsigned_to_nat(4u);
x_222 = lean_nat_mul(x_218, x_221);
x_223 = lean_unsigned_to_nat(3u);
x_224 = lean_nat_div(x_222, x_223);
lean_dec(x_222);
x_225 = lean_array_get_size(x_220);
x_226 = lean_nat_dec_le(x_224, x_225);
lean_dec(x_225);
lean_dec(x_224);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; 
x_227 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__1___redArg(x_220);
if (lean_is_scalar(x_201)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_201;
}
lean_ctor_set(x_228, 0, x_218);
lean_ctor_set(x_228, 1, x_227);
x_172 = x_202;
x_173 = x_199;
x_174 = x_228;
goto block_177;
}
else
{
lean_object* x_229; 
if (lean_is_scalar(x_201)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_201;
}
lean_ctor_set(x_229, 0, x_218);
lean_ctor_set(x_229, 1, x_220);
x_172 = x_202;
x_173 = x_199;
x_174 = x_229;
goto block_177;
}
}
else
{
lean_dec(x_216);
lean_dec(x_201);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_187);
lean_dec(x_183);
x_172 = x_202;
x_173 = x_199;
x_174 = x_196;
goto block_177;
}
}
block_240:
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_232 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__4;
lean_inc(x_183);
x_233 = l_Lean_Name_toString(x_183, x_231, x_193);
x_234 = lean_string_append(x_232, x_233);
lean_dec(x_233);
x_235 = l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg___lam__0___closed__1;
x_236 = lean_string_append(x_234, x_235);
x_237 = lean_box(0);
lean_inc(x_3);
x_238 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_238, 0, x_3);
lean_ctor_set(x_238, 1, x_236);
lean_ctor_set(x_238, 2, x_237);
lean_ctor_set(x_238, 3, x_237);
x_239 = lean_array_push(x_21, x_238);
x_195 = x_239;
x_196 = x_22;
x_197 = x_190;
x_198 = x_191;
x_199 = x_9;
goto block_230;
}
}
else
{
lean_object* x_256; lean_object* x_257; 
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_168);
lean_dec(x_23);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_21);
lean_ctor_set(x_256, 1, x_22);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_171);
lean_ctor_set(x_257, 1, x_256);
x_10 = x_257;
x_11 = x_9;
goto block_15;
}
}
}
block_177:
{
lean_object* x_175; lean_object* x_176; 
if (lean_is_scalar(x_168)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_168;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_174);
if (lean_is_scalar(x_23)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_23;
}
lean_ctor_set(x_176, 0, x_171);
lean_ctor_set(x_176, 1, x_175);
x_10 = x_176;
x_11 = x_173;
goto block_15;
}
block_180:
{
lean_object* x_178; lean_object* x_179; 
if (lean_is_scalar(x_20)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_20;
}
lean_ctor_set(x_178, 0, x_21);
lean_ctor_set(x_178, 1, x_22);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_171);
lean_ctor_set(x_179, 1, x_178);
x_10 = x_179;
x_11 = x_9;
goto block_15;
}
}
}
}
block_15:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = 1;
x_13 = lean_usize_add(x_6, x_12);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(x_3, x_4, x_5, x_13, x_10, x_11);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_3, x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_uget(x_2, x_3);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_1);
x_17 = l_Lean_Server_FileWorker_computeQueries(x_1, x_16, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Array_append___redArg(x_5, x_18);
lean_dec(x_18);
x_8 = x_20;
x_9 = x_19;
goto block_13;
}
else
{
lean_dec(x_5);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_8 = x_21;
x_9 = x_22;
goto block_13;
}
else
{
lean_dec(x_1);
return x_17;
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
block_13:
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_5 = x_8;
x_7 = x_9;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_hash___override___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__3;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__4;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__5;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__6;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__7;
x_2 = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_91; lean_object* x_92; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 3);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0;
x_12 = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__1;
x_146 = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__9;
x_147 = lean_unsigned_to_nat(0u);
x_148 = lean_array_get_size(x_3);
x_149 = lean_nat_dec_lt(x_147, x_148);
if (x_149 == 0)
{
lean_dec(x_148);
x_91 = x_146;
x_92 = x_5;
goto block_145;
}
else
{
uint8_t x_150; 
x_150 = lean_nat_dec_le(x_148, x_148);
if (x_150 == 0)
{
lean_dec(x_148);
x_91 = x_146;
x_92 = x_5;
goto block_145;
}
else
{
size_t x_151; size_t x_152; lean_object* x_153; 
x_151 = 0;
x_152 = lean_usize_of_nat(x_148);
lean_dec(x_148);
lean_inc(x_6);
x_153 = l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3(x_6, x_3, x_151, x_152, x_146, x_4, x_5);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_91 = x_154;
x_92 = x_155;
goto block_145;
}
else
{
uint8_t x_156; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_156 = !lean_is_exclusive(x_153);
if (x_156 == 0)
{
return x_153;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_153, 0);
x_158 = lean_ctor_get(x_153, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_153);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
}
block_90:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_inc(x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_get_size(x_13);
x_22 = l_Array_toSubarray___redArg(x_13, x_20, x_21);
x_23 = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__8;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1(x_11, x_12, x_19, x_16, x_14, x_15, x_24, x_4, x_17);
lean_dec(x_4);
lean_dec(x_16);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_2);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_2, 7);
lean_dec(x_34);
x_35 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_6);
lean_ctor_set(x_27, 1, x_31);
lean_ctor_set(x_27, 0, x_35);
x_36 = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(x_27);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_2, 7, x_37);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_25, 0, x_38);
return x_25;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
x_41 = lean_ctor_get(x_2, 2);
x_42 = lean_ctor_get(x_2, 3);
x_43 = lean_ctor_get(x_2, 4);
x_44 = lean_ctor_get(x_2, 5);
x_45 = lean_ctor_get(x_2, 6);
x_46 = lean_ctor_get(x_2, 8);
x_47 = lean_ctor_get(x_2, 9);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_2);
x_48 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_6);
lean_ctor_set(x_27, 1, x_31);
lean_ctor_set(x_27, 0, x_48);
x_49 = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(x_27);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_40);
lean_ctor_set(x_51, 2, x_41);
lean_ctor_set(x_51, 3, x_42);
lean_ctor_set(x_51, 4, x_43);
lean_ctor_set(x_51, 5, x_44);
lean_ctor_set(x_51, 6, x_45);
lean_ctor_set(x_51, 7, x_50);
lean_ctor_set(x_51, 8, x_46);
lean_ctor_set(x_51, 9, x_47);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_25, 0, x_52);
return x_25;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_53 = lean_ctor_get(x_27, 0);
lean_inc(x_53);
lean_dec(x_27);
x_54 = lean_ctor_get(x_2, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_2, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_2, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_2, 4);
lean_inc(x_58);
x_59 = lean_ctor_get(x_2, 5);
lean_inc(x_59);
x_60 = lean_ctor_get(x_2, 6);
lean_inc(x_60);
x_61 = lean_ctor_get(x_2, 8);
lean_inc(x_61);
x_62 = lean_ctor_get(x_2, 9);
lean_inc(x_62);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 lean_ctor_release(x_2, 7);
 lean_ctor_release(x_2, 8);
 lean_ctor_release(x_2, 9);
 x_63 = x_2;
} else {
 lean_dec_ref(x_2);
 x_63 = lean_box(0);
}
x_64 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_6);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_53);
x_66 = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(x_65);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
if (lean_is_scalar(x_63)) {
 x_68 = lean_alloc_ctor(0, 10, 0);
} else {
 x_68 = x_63;
}
lean_ctor_set(x_68, 0, x_54);
lean_ctor_set(x_68, 1, x_55);
lean_ctor_set(x_68, 2, x_56);
lean_ctor_set(x_68, 3, x_57);
lean_ctor_set(x_68, 4, x_58);
lean_ctor_set(x_68, 5, x_59);
lean_ctor_set(x_68, 6, x_60);
lean_ctor_set(x_68, 7, x_67);
lean_ctor_set(x_68, 8, x_61);
lean_ctor_set(x_68, 9, x_62);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_25, 0, x_69);
return x_25;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_70 = lean_ctor_get(x_25, 1);
lean_inc(x_70);
lean_dec(x_25);
x_71 = lean_ctor_get(x_27, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_72 = x_27;
} else {
 lean_dec_ref(x_27);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_2, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_2, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_2, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_2, 3);
lean_inc(x_76);
x_77 = lean_ctor_get(x_2, 4);
lean_inc(x_77);
x_78 = lean_ctor_get(x_2, 5);
lean_inc(x_78);
x_79 = lean_ctor_get(x_2, 6);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 8);
lean_inc(x_80);
x_81 = lean_ctor_get(x_2, 9);
lean_inc(x_81);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 lean_ctor_release(x_2, 7);
 lean_ctor_release(x_2, 8);
 lean_ctor_release(x_2, 9);
 x_82 = x_2;
} else {
 lean_dec_ref(x_2);
 x_82 = lean_box(0);
}
x_83 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_6);
if (lean_is_scalar(x_72)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_72;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_71);
x_85 = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(x_84);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
if (lean_is_scalar(x_82)) {
 x_87 = lean_alloc_ctor(0, 10, 0);
} else {
 x_87 = x_82;
}
lean_ctor_set(x_87, 0, x_73);
lean_ctor_set(x_87, 1, x_74);
lean_ctor_set(x_87, 2, x_75);
lean_ctor_set(x_87, 3, x_76);
lean_ctor_set(x_87, 4, x_77);
lean_ctor_set(x_87, 5, x_78);
lean_ctor_set(x_87, 6, x_79);
lean_ctor_set(x_87, 7, x_86);
lean_ctor_set(x_87, 8, x_80);
lean_ctor_set(x_87, 9, x_81);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_70);
return x_89;
}
}
block_145:
{
uint8_t x_93; 
x_93 = l_Array_isEmpty___redArg(x_91);
if (x_93 == 0)
{
lean_object* x_94; size_t x_95; size_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_94 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0;
x_95 = lean_array_size(x_91);
x_96 = 0;
lean_inc(x_91);
x_97 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(x_95, x_96, x_91);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_1);
lean_ctor_set(x_98, 1, x_97);
lean_inc(x_4);
x_99 = l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg(x_94, x_98, x_4, x_92);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = lean_ctor_get(x_99, 1);
x_103 = lean_task_get_own(x_101);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_free_object(x_99);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_ctor_get(x_9, 3);
lean_inc(x_105);
lean_dec(x_9);
x_106 = l_Lean_Syntax_getTailPos_x3f(x_105, x_93);
lean_dec(x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
lean_dec(x_10);
x_107 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__2;
x_13 = x_104;
x_14 = x_95;
x_15 = x_96;
x_16 = x_91;
x_17 = x_102;
x_18 = x_107;
goto block_90;
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
lean_dec(x_106);
x_109 = l_Lean_FileMap_utf8PosToLspPos(x_10, x_108);
lean_dec(x_108);
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_111 = lean_ctor_get(x_109, 0);
x_112 = lean_ctor_get(x_109, 1);
lean_dec(x_112);
x_113 = lean_unsigned_to_nat(1u);
x_114 = lean_nat_add(x_111, x_113);
lean_dec(x_111);
x_115 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_109, 1, x_115);
lean_ctor_set(x_109, 0, x_114);
x_13 = x_104;
x_14 = x_95;
x_15 = x_96;
x_16 = x_91;
x_17 = x_102;
x_18 = x_109;
goto block_90;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_116 = lean_ctor_get(x_109, 0);
lean_inc(x_116);
lean_dec(x_109);
x_117 = lean_unsigned_to_nat(1u);
x_118 = lean_nat_add(x_116, x_117);
lean_dec(x_116);
x_119 = lean_unsigned_to_nat(0u);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_13 = x_104;
x_14 = x_95;
x_15 = x_96;
x_16 = x_91;
x_17 = x_102;
x_18 = x_120;
goto block_90;
}
}
}
else
{
lean_object* x_121; 
lean_dec(x_103);
lean_dec(x_91);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_121 = lean_box(0);
lean_ctor_set(x_99, 0, x_121);
return x_99;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_99, 0);
x_123 = lean_ctor_get(x_99, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_99);
x_124 = lean_task_get_own(x_122);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
lean_dec(x_124);
x_126 = lean_ctor_get(x_9, 3);
lean_inc(x_126);
lean_dec(x_9);
x_127 = l_Lean_Syntax_getTailPos_x3f(x_126, x_93);
lean_dec(x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
lean_dec(x_10);
x_128 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__2;
x_13 = x_125;
x_14 = x_95;
x_15 = x_96;
x_16 = x_91;
x_17 = x_123;
x_18 = x_128;
goto block_90;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
lean_dec(x_127);
x_130 = l_Lean_FileMap_utf8PosToLspPos(x_10, x_129);
lean_dec(x_129);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_132 = x_130;
} else {
 lean_dec_ref(x_130);
 x_132 = lean_box(0);
}
x_133 = lean_unsigned_to_nat(1u);
x_134 = lean_nat_add(x_131, x_133);
lean_dec(x_131);
x_135 = lean_unsigned_to_nat(0u);
if (lean_is_scalar(x_132)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_132;
}
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_13 = x_125;
x_14 = x_95;
x_15 = x_96;
x_16 = x_91;
x_17 = x_123;
x_18 = x_136;
goto block_90;
}
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_124);
lean_dec(x_91);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_137 = lean_box(0);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_123);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_91);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_6);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_6, 1);
lean_dec(x_140);
x_141 = lean_ctor_get(x_6, 0);
lean_dec(x_141);
x_142 = lean_box(0);
lean_ctor_set(x_6, 1, x_92);
lean_ctor_set(x_6, 0, x_142);
return x_6;
}
else
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_6);
x_143 = lean_box(0);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_92);
return x_144;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1(x_1, x_2, x_3, x_4, x_10, x_11, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1(x_1, x_2, x_3, x_4, x_10, x_11, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* initialize_Lean_Server_FileWorker_Utils(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Internal(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Requests(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Completion_CompletionInfoSelection(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_CodeActions_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Completion_CompletionUtils(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_CodeActions_UnknownIdentifier(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_FileWorker_Utils(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Internal(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Requests(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Completion_CompletionInfoSelection(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_CodeActions_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Completion_CompletionUtils(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0 = _init_l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0();
lean_mark_persistent(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0);
l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__1___closed__0 = _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__1___closed__0();
lean_mark_persistent(l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__1___closed__0);
l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__2___closed__0 = _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__2___closed__0();
lean_mark_persistent(l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__2___closed__0);
l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__2___closed__1 = _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__2___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___lam__2___closed__1);
l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__0 = _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__0();
lean_mark_persistent(l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__0);
l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__1 = _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__1);
l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__2 = _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__2);
l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__3 = _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__3);
l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__4 = _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_waitAllUnknownIdentifierRanges___closed__4);
l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_collectOpenNamespaces_spec__0___closed__0 = _init_l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_collectOpenNamespaces_spec__0___closed__0();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_collectOpenNamespaces_spec__0___closed__0);
l_Lean_Server_FileWorker_collectOpenNamespaces___closed__0 = _init_l_Lean_Server_FileWorker_collectOpenNamespaces___closed__0();
lean_mark_persistent(l_Lean_Server_FileWorker_collectOpenNamespaces___closed__0);
l_Lean_Server_FileWorker_computeDotIdQuery_x3f___closed__0 = _init_l_Lean_Server_FileWorker_computeDotIdQuery_x3f___closed__0();
lean_mark_persistent(l_Lean_Server_FileWorker_computeDotIdQuery_x3f___closed__0);
l_Lean_Server_FileWorker_computeQueries___closed__0 = _init_l_Lean_Server_FileWorker_computeQueries___closed__0();
lean_mark_persistent(l_Lean_Server_FileWorker_computeQueries___closed__0);
l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__0 = _init_l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__0();
lean_mark_persistent(l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__0);
l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1 = _init_l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1);
l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider = _init_l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider();
lean_mark_persistent(l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider);
l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__0 = _init_l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__0();
lean_mark_persistent(l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__0);
l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg___lam__0___closed__0 = _init_l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg___lam__0___closed__0);
l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg___lam__0___closed__1 = _init_l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___redArg___lam__0___closed__1);
l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__0);
l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__1);
l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2);
l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__3);
l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__4);
l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__5 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__5();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__5);
l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__6 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__6();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__6);
l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__7 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__7();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__7);
l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0 = _init_l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0();
lean_mark_persistent(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0);
l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1 = _init_l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1);
l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__2 = _init_l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__2);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg___closed__0);
l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0 = _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0();
lean_mark_persistent(l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0);
l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__1 = _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__1);
l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__2 = _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__2);
l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__3 = _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__3);
l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__4 = _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__4);
l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__5 = _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__5();
lean_mark_persistent(l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__5);
l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__6 = _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__6();
lean_mark_persistent(l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__6);
l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__7 = _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__7();
lean_mark_persistent(l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__7);
l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__8 = _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__8();
lean_mark_persistent(l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__8);
l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__9 = _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__9();
lean_mark_persistent(l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__9);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
