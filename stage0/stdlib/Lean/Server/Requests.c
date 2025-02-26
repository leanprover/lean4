// Lean compiler output
// Module: Lean.Server.Requests
// Imports: Lean.DeclarationRange Lean.Data.Json Lean.Data.Lsp Lean.Elab.Command Lean.Server.RequestCancellation Lean.Server.ServerTask Lean.Server.FileSource Lean.Server.FileWorker.Utils Lean.Server.Rpc.Basic Std.Sync.Mutex
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
static lean_object* l_Lean_Server_registerLspRequestHandler___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Server_lookupLspRequestHandler___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Server_parseRequestParams___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_RequestError_methodNotFound___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_liftExcept___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_isStatefulLspRequestMethod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__9(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at_Lean_Server_RequestM_withWaitFindSnapAtPos___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Server_chainLspRequestHandler___lambda__1___closed__1;
LEAN_EXPORT uint8_t l_Lean_FileMap_rangeContainsHoverPos(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_registerLspRequestHandler___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_ofException(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_chainLspRequestHandler___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Server_partialLspRequestHandlerMethods___spec__2___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_ReaderT_bind___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_partialLspRequestHandlerMethods___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at_Lean_Server_partialLspRequestHandlerMethods___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Server_handleOnDidChange___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at_Lean_Server_isStatefulLspRequestMethod___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___rarg___lambda__1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_get___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__2(lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
static lean_object* l_Lean_Server_chainLspRequestHandler___lambda__1___closed__2;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask(lean_object*);
lean_object* l_Std_Mutex_new___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Server_lookupLspRequestHandler___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdParsedSnap_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at_Lean_Server_partialLspRequestHandlerMethods___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask(lean_object*);
static lean_object* l_Lean_Server_chainStatefulLspRequestHandler___lambda__1___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestTask_pure___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_checkCancelled___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at_Lean_Server_isStatefulLspRequestMethod___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Server_partialLspRequestHandlerMethods___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_traverseChildren___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_AsyncList_waitFind_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_requestHandlers;
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__10___closed__2;
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdParsedSnap(lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerLspRequestHandler___lambda__4___closed__1;
static lean_object* l_Lean_Server_registerLspRequestHandler___lambda__4___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_checkCancelled(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_handleOnDidChange___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_traverseChildren___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_RequestError_requestCancelled___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findInfoTreeAtPos___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initializing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestContext_srcSearchPath(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_partialLspRequestHandlerMethods(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_chainStatefulLspRequestHandler___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Server_lookupLspRequestHandler___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_toLspResponseError___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftEIOExceptionRequestM___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___closed__1;
LEAN_EXPORT lean_object* l_panic___at_Lean_Server_RequestM_findCmdDataAtPos___spec__1(lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedInfoTree;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedRequestError;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_handleOnDidChange___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_2474_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at_Lean_Server_isStatefulLspRequestMethod___spec__2(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Server_lookupStatefulLspRequestHandler___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at_Lean_Server_isStatefulLspRequestMethod___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerLspRequestHandler___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_routeLspRequest___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdParsedSnap_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdParsedSnap_go___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_handleLspRequest___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_3332_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at_Lean_Server_handleOnDidChange___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_isStatefulLspRequestMethod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at_Lean_Server_handleOnDidChange___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_traverseChildren(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Server_registerLspRequestHandler___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Server_registerLspRequestHandler___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_internalError(lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_map___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at_Lean_Server_isStatefulLspRequestMethod___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_EIO_asTask___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_lookupStatefulLspRequestHandler___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_fileChanged;
lean_object* l_outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Server_lookupStatefulLspRequestHandler___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_handleOnDidChange___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_RequestM_findCmdParsedSnap_containsHoverPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findInfoTreeAtPos___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_rangeContainsHoverPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_registerLspRequestHandler___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_routeLspRequest(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_methodNotFound___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_traverseChildren___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftEIOExceptionRequestM___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_chainLspRequestHandler___lambda__3___closed__2;
static lean_object* l_Lean_Server_parseRequestParams___rarg___closed__2;
static lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdParsedSnap_containsHoverPos___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_chainStatefulLspRequestHandler___lambda__1___closed__2;
static lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Server_registerLspRequestHandler___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at_Lean_Server_registerLspRequestHandler___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_basemutex_lock(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_handleOnDidChange___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___closed__3;
extern lean_object* l_Task_Priority_default;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdParsedSnap_isAfterHoverPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdParsedSnap_go___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_statefulRequestHandlers;
LEAN_EXPORT uint8_t l_Lean_Server_RequestM_findCmdParsedSnap_isAfterHoverPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_traverseChildren___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_chainStatefulLspRequestHandler___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_toLspResponseError(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_registerCompleteStatefulLspRequestHandler___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__3___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_methodNotFound(lean_object*);
static lean_object* l_Lean_Server_RequestError_methodNotFound___closed__1;
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_2474____closed__2;
lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_traverseTree___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_RequestM_findCmdParsedSnap_go___lambda__1___closed__1;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO(lean_object*);
lean_object* lean_usize_to_nat(size_t);
static lean_object* l_Lean_Server_RequestM_findInfoTreeAtPos___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Server_lookupLspRequestHandler___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Server_partialLspRequestHandlerMethods___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_handleLspRequest___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at_Lean_Server_isStatefulLspRequestMethod___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at_Lean_Server_RequestM_withWaitFindSnapAtPos___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_handleOnDidChange___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_chainLspRequestHandler___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Server_lookupStatefulLspRequestHandler___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at_Lean_Server_partialLspRequestHandlerMethods___spec__1___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_instInhabitedRequestError___closed__2;
uint8_t l_String_Range_contains(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__4;
static lean_object* l_Lean_Server_chainLspRequestHandler___lambda__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__10___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_chainStatefulLspRequestHandler___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Server_lookupLspRequestHandler___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findInfoTreeAtPos(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestTask_pure(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc(lean_object*);
lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(lean_object*);
static lean_object* l_Lean_Server_chainStatefulLspRequestHandler___lambda__3___closed__1;
static lean_object* l_Lean_Server_handleLspRequest___closed__2;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftCancellableMRequestM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_traverseTree(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at_Lean_Server_handleOnDidChange___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Server_lookupStatefulLspRequestHandler___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_partialLspRequestHandlerMethods___spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_get___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_liftExcept___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Server_lookupLspRequestHandler___spec__2(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at_Lean_Server_registerLspRequestHandler___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Server_lookupStatefulLspRequestHandler___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_handleOnDidChange___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at_Lean_Server_registerLspRequestHandler___spec__7(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Server_RequestError_fileChanged___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at_Lean_Server_handleOnDidChange___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_lookupLspRequestHandler___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_toArray___at_Lean_Server_partialLspRequestHandlerMethods___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_handleOnDidChange___spec__4___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Server_lookupLspRequestHandler(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_registerCompleteStatefulLspRequestHandler___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Language_SnapshotTree_foldSnaps___rarg___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap(lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_toArray___at_Lean_Server_partialLspRequestHandlerMethods___spec__1___closed__2;
static lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__3;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_RequestError_fileChanged___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Server_lookupStatefulLspRequestHandler___spec__2(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Server_instInhabitedRequestError___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_registerLspRequestHandler___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdParsedSnap_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_traverseChildren___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_2474____closed__1;
LEAN_EXPORT lean_object* l_liftExcept___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___rarg___lambda__1___boxed(lean_object*);
static lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_chainStatefulLspRequestHandler___spec__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdParsedSnap___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_chainStatefulLspRequestHandler___spec__3___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_requestCancelled;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Server_registerLspRequestHandler___spec__4(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_handleOnDidChange___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_chainLspRequestHandler___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_chainStatefulLspRequestHandler___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at_Lean_Server_registerLspRequestHandler___spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_traverseChildren___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_ofIoError(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_lookupStatefulLspRequestHandler(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Server_partialLspRequestHandlerMethods___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCostly___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_traverseChildren___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_handleOnDidChange___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftEIOExceptionRequestM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Server_handleOnDidChange___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftCancellableMRequestM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_invalidParams(lean_object*);
lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCostly___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_FileMap_rangeContainsHoverPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_string_utf8_byte_size(x_6);
x_8 = lean_nat_dec_eq(x_5, x_7);
lean_dec(x_7);
x_9 = l_String_Range_contains(x_2, x_3, x_8);
return x_9;
}
else
{
uint8_t x_10; uint8_t x_11; 
x_10 = 1;
x_11 = l_String_Range_contains(x_2, x_3, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_rangeContainsHoverPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_FileMap_rangeContainsHoverPos(x_1, x_2, x_3, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_traverseTree___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_to_list(x_4);
x_6 = l_Lean_Language_SnapshotTree_foldSnaps_traverseChildren___rarg(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_traverseTree(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldSnaps_traverseTree___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_traverseChildren___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Language_SnapshotTree_foldSnaps_traverseChildren___rarg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_traverseChildren___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Lean_Language_SnapshotTree_foldSnaps_traverseChildren___rarg(x_1, x_6, x_2);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_3, 1);
lean_dec(x_9);
x_10 = lean_task_pure(x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
x_13 = lean_task_pure(x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_traverseChildren___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
lean_inc(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldSnaps_traverseTree___rarg), 3, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_3);
x_8 = l_Task_Priority_default;
x_9 = 1;
x_10 = lean_task_bind(x_6, x_7, x_8, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldSnaps_traverseChildren___rarg___lambda__2), 3, 2);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_4);
x_12 = lean_task_bind(x_10, x_11, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_traverseChildren___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 1);
lean_dec(x_7);
x_8 = 1;
x_9 = lean_box(x_8);
lean_ctor_set(x_4, 1, x_9);
x_10 = lean_task_pure(x_4);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = 1;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_task_pure(x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = lean_ctor_get_uint8(x_5, 0);
lean_dec(x_5);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
lean_dec(x_4);
x_18 = l_Lean_Language_SnapshotTree_foldSnaps_traverseChildren___rarg(x_1, x_17, x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_box(0);
x_21 = l_Lean_Language_SnapshotTree_foldSnaps_traverseChildren___rarg___lambda__3(x_3, x_1, x_19, x_2, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_traverseChildren___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_4 = 0;
x_5 = lean_box(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_task_pure(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_8);
x_10 = lean_apply_2(x_1, x_8, x_2);
x_11 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldSnaps_traverseChildren___rarg___lambda__4), 4, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_8);
x_12 = l_Task_Priority_default;
x_13 = 1;
x_14 = lean_task_bind(x_10, x_11, x_12, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_traverseChildren(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldSnaps_traverseChildren___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_traverseChildren___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Language_SnapshotTree_foldSnaps_traverseChildren___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_traverseChildren___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Language_SnapshotTree_foldSnaps_traverseChildren___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_SnapshotTree_foldSnaps___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldSnaps___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_4 = l_Lean_Language_SnapshotTree_foldSnaps_traverseTree___rarg(x_3, x_2, x_1);
x_5 = l_Lean_Language_SnapshotTree_foldSnaps___rarg___closed__1;
x_6 = l_Task_Priority_default;
x_7 = 1;
x_8 = lean_task_map(x_5, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldSnaps___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_SnapshotTree_foldSnaps___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__1___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__1___closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_4 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__1), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Task_Priority_default;
x_7 = 1;
x_8 = lean_task_map(x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__3___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__3___closed__1;
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_task_pure(x_8);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = 1;
x_13 = l_Lean_Syntax_getRangeWithTrailing_x3f(x_11, x_12);
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_FileMap_rangeContainsHoverPos(x_2, x_14, x_3, x_4);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
x_16 = lean_box(0);
x_17 = l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__2(x_1, x_5, x_16);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(0);
x_6 = lean_box(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__3___boxed), 6, 4);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_3);
lean_closure_set(x_7, 3, x_6);
x_8 = l_Lean_Language_SnapshotTree_foldSnaps___rarg(x_2, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__2(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__3(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Language_SnapshotTree_findInfoTreeAtPos(x_1, x_2, x_3, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedRequestError___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedRequestError___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lean_Server_instInhabitedRequestError___closed__1;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedRequestError() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_instInhabitedRequestError___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Server_RequestError_fileChanged___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("File changed.", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_RequestError_fileChanged___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 7;
x_2 = l_Lean_Server_RequestError_fileChanged___closed__1;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_RequestError_fileChanged() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_RequestError_fileChanged___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Server_RequestError_methodNotFound___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("No request handler found for '", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_RequestError_methodNotFound___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_methodNotFound(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_2 = l_Lean_Server_RequestError_methodNotFound___closed__1;
x_3 = lean_string_append(x_2, x_1);
x_4 = l_Lean_Server_RequestError_methodNotFound___closed__2;
x_5 = lean_string_append(x_3, x_4);
x_6 = 2;
x_7 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_methodNotFound___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_RequestError_methodNotFound(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_invalidParams(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = 3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_internalError(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = 4;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_RequestError_requestCancelled___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 8;
x_2 = l_Lean_Server_instInhabitedRequestError___closed__1;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_RequestError_requestCancelled() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_RequestError_requestCancelled___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_ofException(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Exception_toMessageData(x_1);
x_4 = l_Lean_MessageData_toString(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = 4;
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = 4;
x_12 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_ofIoError(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_io_error_to_string(x_1);
x_3 = 4;
x_4 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_toLspResponseError(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_box(0);
lean_inc(x_4);
x_6 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_toLspResponseError___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_RequestError_toLspResponseError(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_parseRequestParams___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cannot parse request params: ", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_parseRequestParams___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_Json_compress(x_2);
x_7 = l_Lean_Server_parseRequestParams___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_Server_parseRequestParams___rarg___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_5);
lean_dec(x_5);
x_12 = l_Lean_Server_instInhabitedRequestError___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = 0;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
lean_ctor_set(x_3, 0, x_15);
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = l_Lean_Json_compress(x_2);
x_18 = l_Lean_Server_parseRequestParams___rarg___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = l_Lean_Server_parseRequestParams___rarg___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_string_append(x_21, x_16);
lean_dec(x_16);
x_23 = l_Lean_Server_instInhabitedRequestError___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = 0;
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_3);
if (x_28 == 0)
{
return x_3;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
lean_dec(x_3);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_parseRequestParams___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestContext_srcSearchPath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_task_get_own(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestTask_pure___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = lean_task_pure(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestTask_pure(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_RequestTask_pure___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
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
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = l_Lean_Server_RequestError_ofIoError(x_10);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = l_Lean_Server_RequestError_ofIoError(x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_instMonadLiftIORequestM___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_instMonadLiftIORequestM___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftEIOExceptionRequestM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = l_Lean_Server_RequestError_ofException(x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_ctor_set_tag(x_11, 1);
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftEIOExceptionRequestM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_instMonadLiftEIOExceptionRequestM___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftEIOExceptionRequestM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_instMonadLiftEIOExceptionRequestM___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftCancellableMRequestM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 5);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_2(x_1, x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_6);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = l_Lean_Server_RequestError_requestCancelled;
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = l_Lean_Server_RequestError_requestCancelled;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_5, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
lean_ctor_set(x_5, 0, x_15);
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = l_Lean_Server_RequestError_ofIoError(x_20);
lean_ctor_set(x_5, 0, x_21);
return x_5;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_5);
x_24 = l_Lean_Server_RequestError_ofIoError(x_22);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftCancellableMRequestM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_instMonadLiftCancellableMRequestM___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
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
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_12, 0, x_11);
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
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_runInIO___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_readDoc___rarg___lambda__1), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_readDoc___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_apply_1(x_1, x_2);
x_5 = l_Lean_Server_ServerTask_EIO_asTask___rarg(x_4, x_3);
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
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_asTask___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_task_pure(x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_task_pure(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_pureTask___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, x_3, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapTaskCheap___rarg___lambda__1), 4, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
x_6 = l_Lean_Server_ServerTask_EIO_mapTaskCheap___rarg(x_5, x_1, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
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
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapTaskCheap___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapTaskCheap___rarg___lambda__1), 4, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
x_6 = l_Lean_Server_ServerTask_EIO_mapTaskCostly___rarg(x_5, x_1, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
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
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapTaskCostly___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapTaskCheap___rarg___lambda__1), 4, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
x_6 = l_Lean_Server_ServerTask_EIO_bindTaskCheap___rarg(x_1, x_5, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
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
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindTaskCheap___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapTaskCheap___rarg___lambda__1), 4, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
x_6 = l_Lean_Server_ServerTask_EIO_bindTaskCostly___rarg(x_1, x_5, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
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
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindTaskCostly___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_checkCancelled(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 5);
x_4 = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
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
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_4, 0);
lean_dec(x_14);
x_15 = l_Lean_Server_RequestError_requestCancelled;
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_15);
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
x_17 = l_Lean_Server_RequestError_requestCancelled;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_checkCancelled___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_RequestM_checkCancelled(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Lean_Server_RequestError_ofIoError(x_6);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_2(x_1, x_4, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_apply_3(x_2, x_11, x_4, x_5);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_waitFindSnapAux___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_IO_AsyncList_waitFind_x3f___rarg(x_2, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_waitFindSnapAux___rarg), 5, 2);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_4);
x_11 = l_Lean_Server_RequestM_mapTaskCostly___rarg(x_9, x_10, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_withWaitFindSnap___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_IO_AsyncList_waitFind_x3f___rarg(x_2, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_waitFindSnapAux___rarg), 5, 2);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_4);
x_11 = l_Lean_Server_RequestM_bindTaskCostly___rarg(x_9, x_10, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindWaitFindSnap___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at_Lean_Server_RequestM_withWaitFindSnapAtPos___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Server_Snapshots_Snapshot_endPos(x_2);
x_4 = lean_nat_dec_le(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no snapshot found at ", 21, 21);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_5 = l_Lean_Server_RequestM_readDoc___at_Lean_Server_RequestM_withWaitFindSnapAtPos___spec__1(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_1);
x_11 = l_Lean_FileMap_lspPosToUtf8Pos(x_10, x_1);
lean_dec(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = l___private_Init_Data_Repr_0__Nat_reprFast(x_13);
x_15 = l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec(x_1);
x_20 = l___private_Init_Data_Repr_0__Nat_reprFast(x_19);
x_21 = lean_string_append(x_18, x_20);
lean_dec(x_20);
x_22 = l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___closed__3;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___closed__4;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Lean_Server_instInhabitedRequestError___closed__1;
x_27 = lean_string_append(x_25, x_26);
x_28 = 3;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___lambda__2___boxed), 3, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = l_Lean_Server_RequestM_withWaitFindSnap___rarg(x_6, x_12, x_30, x_2, x_3, x_7);
return x_31;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at_Lean_Server_RequestM_withWaitFindSnapAtPos___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_RequestM_readDoc___at_Lean_Server_RequestM_withWaitFindSnapAtPos___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_RequestM_findCmdParsedSnap_containsHoverPos(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
x_5 = 1;
x_6 = l_Lean_Syntax_getRangeWithTrailing_x3f(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_10, 2);
x_12 = 0;
x_13 = l_Lean_FileMap_rangeContainsHoverPos(x_11, x_8, x_2, x_12);
lean_dec(x_8);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdParsedSnap_containsHoverPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Server_RequestM_findCmdParsedSnap_containsHoverPos(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_RequestM_findCmdParsedSnap_isAfterHoverPos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = 1;
x_5 = l_Lean_Syntax_getPos_x3f(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_nat_dec_lt(x_1, x_7);
lean_dec(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdParsedSnap_isAfterHoverPos___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Server_RequestM_findCmdParsedSnap_isAfterHoverPos(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_RequestM_findCmdParsedSnap_go___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_task_pure(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdParsedSnap_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 6);
lean_inc(x_5);
lean_dec(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Lean_Server_RequestM_findCmdParsedSnap_go___lambda__1___closed__1;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_findCmdParsedSnap_go), 3, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_3);
x_10 = l_Task_Priority_default;
x_11 = 1;
x_12 = lean_task_bind(x_8, x_9, x_10, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdParsedSnap_go___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Server_RequestM_findCmdParsedSnap_isAfterHoverPos(x_3, x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_Server_RequestM_findCmdParsedSnap_go___lambda__1(x_1, x_2, x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = l_Lean_Server_RequestM_findCmdParsedSnap_go___lambda__1___closed__1;
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdParsedSnap_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Server_RequestM_findCmdParsedSnap_containsHoverPos(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Lean_Server_RequestM_findCmdParsedSnap_go___lambda__2(x_3, x_1, x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_3);
x_8 = lean_task_pure(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdParsedSnap_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_RequestM_findCmdParsedSnap_go___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdParsedSnap_go___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_RequestM_findCmdParsedSnap_go___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdParsedSnap___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = l_Lean_Server_RequestM_findCmdParsedSnap_go___lambda__1___closed__1;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_findCmdParsedSnap_go), 3, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = l_Task_Priority_default;
x_11 = 1;
x_12 = lean_task_bind(x_8, x_9, x_10, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdParsedSnap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Lean_Server_RequestM_findCmdParsedSnap_go___lambda__1___closed__1;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_findCmdParsedSnap___lambda__1), 3, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
x_11 = l_Task_Priority_default;
x_12 = 1;
x_13 = lean_task_bind(x_9, x_10, x_11, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Server_RequestM_findCmdDataAtPos___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: ", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("s.cmdState.infoState.trees.size == 1\n        ", 45, 45);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__1;
x_2 = l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Server.Requests", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Server.RequestM.findCmdDataAtPos", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__4;
x_2 = l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__5;
x_3 = lean_unsigned_to_nat(309u);
x_4 = lean_unsigned_to_nat(8u);
x_5 = l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 6);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__6;
x_10 = l_panic___at_Lean_Server_RequestM_findCmdDataAtPos___spec__1(x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_6);
lean_dec(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_14 = l_Lean_Elab_instInhabitedInfoTree;
x_15 = l_outOfBounds___rarg(x_14);
lean_inc(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = l_Lean_Elab_instInhabitedInfoTree;
x_19 = l_Lean_PersistentArray_get_x21___rarg(x_18, x_5, x_12);
lean_inc(x_11);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Task_Priority_default;
x_7 = 1;
x_8 = lean_task_map(x_3, x_5, x_6, x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_2, 0, x_12);
x_13 = lean_task_pure(x_2);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_task_pure(x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = l_Lean_Server_RequestM_findCmdParsedSnap_go___lambda__1___closed__1;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_6);
x_10 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(x_6);
x_11 = l_Lean_Language_SnapshotTree_findInfoTreeAtPos(x_9, x_10, x_2, x_3);
x_12 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_findCmdDataAtPos___lambda__2), 2, 1);
lean_closure_set(x_12, 0, x_6);
x_13 = l_Task_Priority_default;
x_14 = 1;
x_15 = lean_task_bind(x_11, x_12, x_13, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_Lean_Server_RequestM_findCmdParsedSnap(x_1, x_2);
x_5 = lean_box(x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_findCmdDataAtPos___lambda__3___boxed), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_5);
x_7 = l_Task_Priority_default;
x_8 = 1;
x_9 = lean_task_bind(x_4, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_Server_RequestM_findCmdDataAtPos___lambda__3(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Server_RequestM_findCmdDataAtPos(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findInfoTreeAtPos___lambda__1(lean_object* x_1) {
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
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
static lean_object* _init_l_Lean_Server_RequestM_findInfoTreeAtPos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_findInfoTreeAtPos___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findInfoTreeAtPos(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_4 = l_Lean_Server_RequestM_findCmdDataAtPos(x_1, x_2, x_3);
x_5 = l_Lean_Server_RequestM_findInfoTreeAtPos___closed__1;
x_6 = l_Task_Priority_default;
x_7 = 1;
x_8 = lean_task_map(x_5, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findInfoTreeAtPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Server_RequestM_findInfoTreeAtPos(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_1(x_2, x_3);
x_9 = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___rarg(x_1, x_7, x_8, x_4);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set_tag(x_9, 1);
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
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_9, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_9, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_dec(x_9);
x_25 = l_Lean_Server_RequestError_ofException(x_23, x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_ctor_set_tag(x_25, 1);
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_runCommandElabM___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_1(x_2, x_3);
x_9 = l_Lean_Server_Snapshots_Snapshot_runCoreM___rarg(x_1, x_7, x_8, x_4);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set_tag(x_9, 1);
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
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_9, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_9, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_dec(x_9);
x_25 = l_Lean_Server_RequestError_ofException(x_23, x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_ctor_set_tag(x_25, 1);
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_runCoreM___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_1(x_2, x_3);
x_9 = l_Lean_Server_Snapshots_Snapshot_runTermElabM___rarg(x_1, x_7, x_8, x_4);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set_tag(x_9, 1);
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
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_9, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_9, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_dec(x_9);
x_25 = l_Lean_Server_RequestError_ofException(x_23, x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_ctor_set_tag(x_25, 1);
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_runTermElabM___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_2474____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_2474____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_2474____closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_2474_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_2474____closed__2;
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
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_registerLspRequestHandler___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_registerLspRequestHandler___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_liftExcept___at_Lean_Server_registerLspRequestHandler___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Server_registerLspRequestHandler___spec__4(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_9; lean_object* x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = lean_string_hash(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Server_registerLspRequestHandler___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_18 = lean_string_dec_eq(x_3, x_17);
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__2;
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
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_string_dec_eq(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
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
x_28 = lean_string_dec_eq(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
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
x_36 = lean_usize_shift_right(x_2, x_9);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3(x_35, x_36, x_37, x_4, x_5);
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
x_41 = lean_usize_shift_right(x_2, x_9);
x_42 = lean_usize_add(x_3, x_8);
x_43 = l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3(x_40, x_41, x_42, x_4, x_5);
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
x_51 = l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__2;
x_52 = lean_usize_land(x_2, x_51);
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
x_58 = lean_box(0);
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
x_63 = lean_string_dec_eq(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
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
x_73 = lean_usize_shift_right(x_2, x_50);
x_74 = lean_usize_add(x_3, x_49);
x_75 = l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3(x_71, x_73, x_74, x_4, x_5);
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
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; size_t x_85; uint8_t x_86; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Server_registerLspRequestHandler___spec__5(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__3;
x_93 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Server_registerLspRequestHandler___spec__4(x_3, x_90, x_91, lean_box(0), x_83, x_92);
lean_dec(x_91);
lean_dec(x_90);
return x_93;
}
else
{
return x_84;
}
}
else
{
return x_84;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Server_registerLspRequestHandler___spec__5(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__3;
x_107 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Server_registerLspRequestHandler___spec__4(x_3, x_104, x_105, lean_box(0), x_97, x_106);
lean_dec(x_105);
lean_dec(x_104);
return x_107;
}
else
{
return x_98;
}
}
else
{
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Server_registerLspRequestHandler___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_string_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at_Lean_Server_registerLspRequestHandler___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_string_dec_eq(x_5, x_9);
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
uint8_t x_14; 
lean_dec(x_4);
x_14 = 1;
return x_14;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at_Lean_Server_registerLspRequestHandler___spec__7(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__2;
x_7 = lean_usize_land(x_2, x_6);
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
x_12 = lean_string_dec_eq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_usize_shift_right(x_2, x_5);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_PersistentHashMap_containsAtAux___at_Lean_Server_registerLspRequestHandler___spec__8(x_17, x_18, lean_box(0), x_19, x_3);
lean_dec(x_18);
lean_dec(x_17);
return x_20;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_string_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at_Lean_Server_registerLspRequestHandler___spec__7(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_parseRequestParams___rarg(x_1, x_3);
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
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_apply_1(x_2, x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_apply_1(x_2, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Server_parseRequestParams___rarg(x_1, x_4);
x_8 = l_liftExcept___at_Lean_Server_registerLspRequestHandler___spec__1___rarg(x_7, x_5, x_6);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_apply_3(x_2, x_9, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_closure((void*)(l_Except_map___rarg), 2, 1);
lean_closure_set(x_14, 0, x_3);
x_15 = l_Task_Priority_default;
x_16 = 1;
x_17 = lean_task_map(x_14, x_13, x_15, x_16);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_closure((void*)(l_Except_map___rarg), 2, 1);
lean_closure_set(x_20, 0, x_3);
x_21 = l_Task_Priority_default;
x_22 = 1;
x_23 = lean_task_map(x_20, x_18, x_21, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_11);
if (x_25 == 0)
{
return x_11;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
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
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_8);
if (x_29 == 0)
{
return x_8;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_8, 0);
x_31 = lean_ctor_get(x_8, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_8);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_requestHandlers;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___lambda__1), 3, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___lambda__2), 6, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_4);
x_10 = l_Lean_Server_registerLspRequestHandler___lambda__3___closed__1;
x_11 = lean_st_ref_take(x_10, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 0, x_8);
x_15 = l_Lean_PersistentHashMap_insert___at_Lean_Server_registerLspRequestHandler___spec__2(x_13, x_5, x_11);
x_16 = lean_st_ref_set(x_10, x_15, x_14);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_9);
x_24 = l_Lean_PersistentHashMap_insert___at_Lean_Server_registerLspRequestHandler___spec__2(x_21, x_5, x_23);
x_25 = lean_st_ref_set(x_10, x_24, x_22);
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
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to register LSP request handler for '", 44, 44);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("': already registered", 21, 21);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Server_registerLspRequestHandler___lambda__3___closed__1;
x_9 = lean_st_ref_get(x_8, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lean_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__6(x_11, x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_9);
x_14 = lean_box(0);
x_15 = l_Lean_Server_registerLspRequestHandler___lambda__3(x_1, x_2, x_3, x_4, x_5, x_14, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Lean_Server_registerLspRequestHandler___lambda__4___closed__1;
x_17 = lean_string_append(x_16, x_5);
lean_dec(x_5);
x_18 = l_Lean_Server_registerLspRequestHandler___lambda__4___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_23 = l_Lean_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__6(x_21, x_5);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Lean_Server_registerLspRequestHandler___lambda__3(x_1, x_2, x_3, x_4, x_5, x_24, x_22);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = l_Lean_Server_registerLspRequestHandler___lambda__4___closed__1;
x_27 = lean_string_append(x_26, x_5);
lean_dec(x_5);
x_28 = l_Lean_Server_registerLspRequestHandler___lambda__4___closed__2;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_22);
return x_31;
}
}
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("': only possible during initialization", 38, 38);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_initializing(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = l_Lean_Server_registerLspRequestHandler___lambda__4___closed__1;
x_15 = lean_string_append(x_14, x_1);
lean_dec(x_1);
x_16 = l_Lean_Server_registerLspRequestHandler___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = l_Lean_Server_registerLspRequestHandler___lambda__4___closed__1;
x_21 = lean_string_append(x_20, x_1);
lean_dec(x_1);
x_22 = l_Lean_Server_registerLspRequestHandler___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
lean_dec(x_9);
x_27 = lean_box(0);
x_28 = l_Lean_Server_registerLspRequestHandler___lambda__4(x_3, x_4, x_7, x_6, x_1, x_27, x_26);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_registerLspRequestHandler___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_liftExcept___at_Lean_Server_registerLspRequestHandler___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Server_registerLspRequestHandler___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Server_registerLspRequestHandler___spec__4(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at_Lean_Server_registerLspRequestHandler___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Lean_PersistentHashMap_containsAtAux___at_Lean_Server_registerLspRequestHandler___spec__8(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at_Lean_Server_registerLspRequestHandler___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at_Lean_Server_registerLspRequestHandler___spec__7(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__6(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_registerLspRequestHandler___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_registerLspRequestHandler___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Server_lookupLspRequestHandler___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = lean_string_dec_eq(x_5, x_9);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Server_lookupLspRequestHandler___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__2;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_string_dec_eq(x_3, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_free_object(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_usize_shift_right(x_2, x_6);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = 5;
x_22 = l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__2;
x_23 = lean_usize_land(x_2, x_22);
x_24 = lean_usize_to_nat(x_23);
x_25 = lean_box(2);
x_26 = lean_array_get(x_25, x_20, x_24);
lean_dec(x_24);
lean_dec(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_string_dec_eq(x_3, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_usize_shift_right(x_2, x_21);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Server_lookupLspRequestHandler___spec__3(x_36, x_37, lean_box(0), x_38, x_3);
lean_dec(x_37);
lean_dec(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Server_lookupLspRequestHandler___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_string_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Server_lookupLspRequestHandler___spec__2(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupLspRequestHandler(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Server_registerLspRequestHandler___lambda__3___closed__1;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Server_lookupLspRequestHandler___spec__1(x_6, x_1);
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
x_10 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Server_lookupLspRequestHandler___spec__1(x_8, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Server_lookupLspRequestHandler___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Server_lookupLspRequestHandler___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Server_lookupLspRequestHandler___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Server_lookupLspRequestHandler___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Server_lookupLspRequestHandler___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Server_lookupLspRequestHandler___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupLspRequestHandler___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_lookupLspRequestHandler(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_chainLspRequestHandler___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_chainLspRequestHandler___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_liftExcept___at_Lean_Server_chainLspRequestHandler___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_chainLspRequestHandler___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to parse original LSP response for `", 43, 43);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_chainLspRequestHandler___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` when chaining: ", 17, 17);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_apply_1(x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Server_chainLspRequestHandler___lambda__1___closed__1;
x_12 = lean_string_append(x_11, x_2);
x_13 = l_Lean_Server_chainLspRequestHandler___lambda__1___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_string_append(x_14, x_10);
lean_dec(x_10);
x_16 = l_Lean_Server_instInhabitedRequestError___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = 4;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
lean_ctor_set(x_8, 0, x_19);
return x_8;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_dec(x_8);
x_21 = l_Lean_Server_chainLspRequestHandler___lambda__1___closed__1;
x_22 = lean_string_append(x_21, x_2);
x_23 = l_Lean_Server_chainLspRequestHandler___lambda__1___closed__2;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_24, x_20);
lean_dec(x_20);
x_26 = l_Lean_Server_instInhabitedRequestError___closed__1;
x_27 = lean_string_append(x_25, x_26);
x_28 = 4;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_8);
if (x_31 == 0)
{
return x_8;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_8, 0);
lean_inc(x_32);
lean_dec(x_8);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
x_11 = lean_apply_3(x_10, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___lambda__1___boxed), 3, 2);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_3);
x_15 = l_Task_Priority_default;
x_16 = 1;
x_17 = lean_task_map(x_14, x_12, x_15, x_16);
x_18 = l_Lean_Server_parseRequestParams___rarg(x_4, x_7);
x_19 = l_liftExcept___at_Lean_Server_chainLspRequestHandler___spec__1___rarg(x_18, x_8, x_13);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_apply_4(x_5, x_20, x_17, x_8, x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_alloc_closure((void*)(l_Except_map___rarg), 2, 1);
lean_closure_set(x_25, 0, x_6);
x_26 = lean_task_map(x_25, x_24, x_15, x_16);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_22);
x_29 = lean_alloc_closure((void*)(l_Except_map___rarg), 2, 1);
lean_closure_set(x_29, 0, x_6);
x_30 = lean_task_map(x_29, x_27, x_15, x_16);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_6);
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
return x_22;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_22);
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
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_36 = !lean_is_exclusive(x_19);
if (x_36 == 0)
{
return x_19;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_19, 0);
x_38 = lean_ctor_get(x_19, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_19);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_11);
if (x_40 == 0)
{
return x_11;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_11, 0);
x_42 = lean_ctor_get(x_11, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_11);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
static lean_object* _init_l_Lean_Server_chainLspRequestHandler___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to chain LSP request handler for '", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_chainLspRequestHandler___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("': no initial handler registered", 32, 32);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Server_lookupLspRequestHandler(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = l_Lean_Server_chainLspRequestHandler___lambda__3___closed__1;
x_13 = lean_string_append(x_12, x_1);
lean_dec(x_1);
x_14 = l_Lean_Server_chainLspRequestHandler___lambda__3___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = l_Lean_Server_chainLspRequestHandler___lambda__3___closed__1;
x_19 = lean_string_append(x_18, x_1);
lean_dec(x_1);
x_20 = l_Lean_Server_chainLspRequestHandler___lambda__3___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_dec(x_8);
x_25 = lean_ctor_get(x_9, 0);
lean_inc(x_25);
lean_dec(x_9);
lean_inc(x_1);
lean_inc(x_25);
x_26 = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___lambda__2), 9, 6);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_2);
lean_closure_set(x_26, 2, x_1);
lean_closure_set(x_26, 3, x_3);
lean_closure_set(x_26, 4, x_4);
lean_closure_set(x_26, 5, x_5);
x_27 = l_Lean_Server_registerLspRequestHandler___lambda__3___closed__1;
x_28 = lean_st_ref_take(x_27, x_24);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_25, 1);
lean_dec(x_32);
lean_ctor_set(x_25, 1, x_26);
x_33 = l_Lean_PersistentHashMap_insert___at_Lean_Server_registerLspRequestHandler___spec__2(x_29, x_1, x_25);
x_34 = lean_st_ref_set(x_27, x_33, x_30);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_25, 0);
lean_inc(x_39);
lean_dec(x_25);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_26);
x_41 = l_Lean_PersistentHashMap_insert___at_Lean_Server_registerLspRequestHandler___spec__2(x_29, x_1, x_40);
x_42 = lean_st_ref_set(x_27, x_41, x_30);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_initializing(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = l_Lean_Server_chainLspRequestHandler___lambda__3___closed__1;
x_15 = lean_string_append(x_14, x_1);
lean_dec(x_1);
x_16 = l_Lean_Server_registerLspRequestHandler___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = l_Lean_Server_chainLspRequestHandler___lambda__3___closed__1;
x_21 = lean_string_append(x_20, x_1);
lean_dec(x_1);
x_22 = l_Lean_Server_registerLspRequestHandler___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
lean_dec(x_9);
x_27 = lean_box(0);
x_28 = l_Lean_Server_chainLspRequestHandler___lambda__3(x_1, x_5, x_3, x_7, x_6, x_27, x_26);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_chainLspRequestHandler___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_liftExcept___at_Lean_Server_chainLspRequestHandler___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_chainLspRequestHandler___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_chainLspRequestHandler___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_3332_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_2474____closed__2;
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
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Got invalid state type in stateful LSP request handler for ", 59, 59);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___rarg(x_2, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___closed__1;
x_9 = lean_string_append(x_8, x_1);
x_10 = l_Lean_Server_instInhabitedRequestError___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = 4;
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___rarg(x_2, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___closed__1;
x_8 = lean_string_append(x_7, x_1);
x_9 = l_Lean_Server_instInhabitedRequestError___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_liftExcept___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_get___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_1, x_3);
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
}
LEAN_EXPORT lean_object* l_liftExcept___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_liftExcept___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__3___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_ReaderT_bind___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__4___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_io_basemutex_lock(x_5, x_4);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_3(x_2, x_8, x_3, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_io_basemutex_unlock(x_5, x_11);
lean_dec(x_5);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_io_basemutex_unlock(x_5, x_18);
lean_dec(x_5);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_io_basemutex_lock(x_5, x_4);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_3(x_2, x_8, x_3, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_io_basemutex_unlock(x_5, x_11);
lean_dec(x_5);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_io_basemutex_unlock(x_5, x_18);
lean_dec(x_5);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__9(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_9; lean_object* x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = lean_string_hash(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__8(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_18 = lean_string_dec_eq(x_3, x_17);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__2;
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
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_string_dec_eq(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
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
x_28 = lean_string_dec_eq(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
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
x_36 = lean_usize_shift_right(x_2, x_9);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__8(x_35, x_36, x_37, x_4, x_5);
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
x_41 = lean_usize_shift_right(x_2, x_9);
x_42 = lean_usize_add(x_3, x_8);
x_43 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__8(x_40, x_41, x_42, x_4, x_5);
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
x_51 = l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__2;
x_52 = lean_usize_land(x_2, x_51);
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
x_58 = lean_box(0);
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
x_63 = lean_string_dec_eq(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
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
x_73 = lean_usize_shift_right(x_2, x_50);
x_74 = lean_usize_add(x_3, x_49);
x_75 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__8(x_71, x_73, x_74, x_4, x_5);
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
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; size_t x_85; uint8_t x_86; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__10(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__3;
x_93 = l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__9(x_3, x_90, x_91, lean_box(0), x_83, x_92);
lean_dec(x_91);
lean_dec(x_90);
return x_93;
}
else
{
return x_84;
}
}
else
{
return x_84;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__10(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__3;
x_107 = l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__9(x_3, x_104, x_105, lean_box(0), x_97, x_106);
lean_dec(x_105);
lean_dec(x_104);
return x_107;
}
else
{
return x_98;
}
}
else
{
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_string_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__8(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Server_parseRequestParams___rarg(x_1, x_6);
x_11 = l_liftExcept___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__1___rarg(x_10, x_8, x_9);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(x_2, x_7, lean_box(0), x_3, x_8, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_apply_4(x_4, x_12, x_15, x_8, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_apply_1(x_5, x_25);
lean_ctor_set(x_19, 0, x_26);
lean_ctor_set(x_18, 0, x_3);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_18);
lean_ctor_set(x_17, 0, x_27);
return x_17;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_apply_1(x_5, x_28);
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_29);
lean_ctor_set(x_18, 0, x_3);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_18);
lean_ctor_set(x_17, 0, x_32);
return x_17;
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_dec(x_18);
x_34 = lean_ctor_get(x_19, 0);
lean_inc(x_34);
x_35 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_36 = x_19;
} else {
 lean_dec_ref(x_19);
 x_36 = lean_box(0);
}
x_37 = lean_apply_1(x_5, x_34);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 1, 1);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_3);
lean_ctor_set(x_39, 1, x_33);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_17, 0, x_40);
return x_17;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_41 = lean_ctor_get(x_17, 1);
lean_inc(x_41);
lean_dec(x_17);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_43 = x_18;
} else {
 lean_dec_ref(x_18);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_19, 0);
lean_inc(x_44);
x_45 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_46 = x_19;
} else {
 lean_dec_ref(x_19);
 x_46 = lean_box(0);
}
x_47 = lean_apply_1(x_5, x_44);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 1, 1);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_45);
if (lean_is_scalar(x_43)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_43;
}
lean_ctor_set(x_49, 0, x_3);
lean_ctor_set(x_49, 1, x_42);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_41);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_5);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_17);
if (x_52 == 0)
{
return x_17;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_17, 0);
x_54 = lean_ctor_get(x_17, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_17);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_14);
if (x_56 == 0)
{
return x_14;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_14, 0);
x_58 = lean_ctor_get(x_14, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_14);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_st_ref_get(x_1, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Server_parseRequestParams___rarg(x_2, x_3);
x_15 = l_liftExcept___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__3___rarg(x_14, x_9, x_13);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(x_4, x_12, lean_box(0), x_5, x_9, x_17);
lean_dec(x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_apply_4(x_6, x_16, x_19, x_9, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_apply_1(x_7, x_28);
lean_ctor_set(x_23, 0, x_29);
lean_ctor_set(x_22, 0, x_5);
x_30 = lean_st_ref_set(x_1, x_22, x_24);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_23);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
lean_inc(x_35);
lean_dec(x_23);
x_37 = lean_apply_1(x_7, x_35);
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_36);
lean_ctor_set(x_22, 0, x_5);
x_39 = lean_st_ref_set(x_1, x_22, x_24);
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
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_43 = lean_ctor_get(x_22, 1);
lean_inc(x_43);
lean_dec(x_22);
x_44 = lean_ctor_get(x_23, 0);
lean_inc(x_44);
x_45 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_46 = x_23;
} else {
 lean_dec_ref(x_23);
 x_46 = lean_box(0);
}
x_47 = lean_apply_1(x_7, x_44);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 1, 1);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_5);
lean_ctor_set(x_49, 1, x_43);
x_50 = lean_st_ref_set(x_1, x_49, x_24);
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
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_7);
lean_dec(x_5);
x_54 = !lean_is_exclusive(x_21);
if (x_54 == 0)
{
return x_21;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_21, 0);
x_56 = lean_ctor_get(x_21, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_21);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_58 = !lean_is_exclusive(x_18);
if (x_58 == 0)
{
return x_18;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_18, 0);
x_60 = lean_ctor_get(x_18, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_18);
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
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_62 = !lean_is_exclusive(x_15);
if (x_62 == 0)
{
return x_15;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_15, 0);
x_64 = lean_ctor_get(x_15, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_15);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__3___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_12 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__2___boxed), 10, 7);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_5);
lean_closure_set(x_12, 5, x_6);
lean_closure_set(x_12, 6, x_7);
x_13 = l_Lean_Server_RequestM_mapTaskCostly___rarg(x_8, x_12, x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__4___closed__1;
x_17 = l_Task_Priority_default;
x_18 = 1;
lean_inc(x_14);
x_19 = lean_task_map(x_16, x_14, x_17, x_18);
x_20 = lean_st_ref_set(x_9, x_19, x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_14);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_get___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__2___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__4___boxed), 11, 7);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_8);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_4);
lean_closure_set(x_11, 5, x_5);
lean_closure_set(x_11, 6, x_6);
x_12 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__5___closed__1;
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__4___rarg), 5, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_11);
x_14 = l_Std_Mutex_atomically___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__5(x_7, x_13, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(x_1, x_5, lean_box(0), x_2, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_apply_4(x_3, x_4, x_9, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_2);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_11, 0, x_21);
return x_11;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
if (lean_is_scalar(x_25)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_25;
}
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_23);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
return x_11;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_11, 0);
x_32 = lean_ctor_get(x_11, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_11);
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
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_8);
if (x_34 == 0)
{
return x_8;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_8, 0);
x_36 = lean_ctor_get(x_8, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_8);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(x_2, x_10, lean_box(0), x_3, x_7, x_11);
lean_dec(x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_apply_4(x_4, x_5, x_13, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
lean_ctor_set(x_16, 0, x_3);
x_20 = lean_st_ref_set(x_1, x_16, x_17);
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
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_st_ref_set(x_1, x_26, x_17);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_15);
if (x_32 == 0)
{
return x_15;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_15, 0);
x_34 = lean_ctor_get(x_15, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_15);
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
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_12);
if (x_36 == 0)
{
return x_12;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_12, 0);
x_38 = lean_ctor_get(x_12, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_12);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_10 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__7___boxed), 8, 5);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_5);
x_11 = l_Lean_Server_RequestM_mapTaskCostly___rarg(x_6, x_10, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__4___closed__1;
x_15 = l_Task_Priority_default;
x_16 = 1;
x_17 = lean_task_map(x_14, x_12, x_15, x_16);
x_18 = lean_st_ref_set(x_7, x_17, x_13);
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
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__8___boxed), 9, 5);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_4);
lean_closure_set(x_9, 4, x_6);
x_10 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__5___closed__1;
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__4___rarg), 5, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_9);
x_12 = l_Std_Mutex_atomically___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__6(x_5, x_11, x_7, x_8);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__10___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_task_pure(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__10___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_statefulRequestHandlers;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___lambda__1), 3, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
x_13 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__10___closed__1;
x_14 = l_Std_Mutex_new___rarg(x_13, x_11);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_3);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 0, x_3);
lean_inc(x_14);
x_18 = lean_st_mk_ref(x_14, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_5);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__1___boxed), 9, 5);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_5);
lean_closure_set(x_21, 2, x_3);
lean_closure_set(x_21, 3, x_6);
lean_closure_set(x_21, 4, x_7);
lean_inc(x_16);
lean_inc(x_3);
lean_inc(x_5);
lean_inc(x_19);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__5), 10, 7);
lean_closure_set(x_22, 0, x_19);
lean_closure_set(x_22, 1, x_1);
lean_closure_set(x_22, 2, x_5);
lean_closure_set(x_22, 3, x_3);
lean_closure_set(x_22, 4, x_6);
lean_closure_set(x_22, 5, x_7);
lean_closure_set(x_22, 6, x_16);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_5);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__6___boxed), 7, 3);
lean_closure_set(x_23, 0, x_5);
lean_closure_set(x_23, 1, x_3);
lean_closure_set(x_23, 2, x_8);
lean_inc(x_16);
lean_inc(x_5);
lean_inc(x_19);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__9), 8, 5);
lean_closure_set(x_24, 0, x_19);
lean_closure_set(x_24, 1, x_5);
lean_closure_set(x_24, 2, x_3);
lean_closure_set(x_24, 3, x_8);
lean_closure_set(x_24, 4, x_16);
x_25 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__10___closed__2;
x_26 = lean_st_ref_take(x_25, x_20);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_22);
lean_ctor_set(x_29, 3, x_23);
lean_ctor_set(x_29, 4, x_24);
lean_ctor_set(x_29, 5, x_16);
lean_ctor_set(x_29, 6, x_14);
lean_ctor_set(x_29, 7, x_19);
lean_ctor_set(x_29, 8, x_9);
x_30 = l_Lean_PersistentHashMap_insert___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__7(x_27, x_5, x_29);
x_31 = lean_st_ref_set(x_25, x_30, x_28);
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
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_36 = lean_ctor_get(x_14, 0);
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_14);
lean_inc(x_3);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_3);
lean_ctor_set(x_38, 1, x_4);
lean_inc(x_38);
x_39 = lean_st_mk_ref(x_38, x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_5);
lean_inc(x_1);
x_42 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__1___boxed), 9, 5);
lean_closure_set(x_42, 0, x_1);
lean_closure_set(x_42, 1, x_5);
lean_closure_set(x_42, 2, x_3);
lean_closure_set(x_42, 3, x_6);
lean_closure_set(x_42, 4, x_7);
lean_inc(x_36);
lean_inc(x_3);
lean_inc(x_5);
lean_inc(x_40);
x_43 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__5), 10, 7);
lean_closure_set(x_43, 0, x_40);
lean_closure_set(x_43, 1, x_1);
lean_closure_set(x_43, 2, x_5);
lean_closure_set(x_43, 3, x_3);
lean_closure_set(x_43, 4, x_6);
lean_closure_set(x_43, 5, x_7);
lean_closure_set(x_43, 6, x_36);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_5);
x_44 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__6___boxed), 7, 3);
lean_closure_set(x_44, 0, x_5);
lean_closure_set(x_44, 1, x_3);
lean_closure_set(x_44, 2, x_8);
lean_inc(x_36);
lean_inc(x_5);
lean_inc(x_40);
x_45 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__9), 8, 5);
lean_closure_set(x_45, 0, x_40);
lean_closure_set(x_45, 1, x_5);
lean_closure_set(x_45, 2, x_3);
lean_closure_set(x_45, 3, x_8);
lean_closure_set(x_45, 4, x_36);
x_46 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__10___closed__2;
x_47 = lean_st_ref_take(x_46, x_41);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_50, 0, x_12);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set(x_50, 2, x_43);
lean_ctor_set(x_50, 3, x_44);
lean_ctor_set(x_50, 4, x_45);
lean_ctor_set(x_50, 5, x_36);
lean_ctor_set(x_50, 6, x_38);
lean_ctor_set(x_50, 7, x_40);
lean_ctor_set(x_50, 8, x_9);
x_51 = l_Lean_PersistentHashMap_insert___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__7(x_48, x_5, x_50);
x_52 = lean_st_ref_set(x_46, x_51, x_49);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to register stateful LSP request handler for '", 53, 53);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_initializing(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___closed__1;
x_20 = lean_string_append(x_19, x_1);
lean_dec(x_1);
x_21 = l_Lean_Server_registerLspRequestHandler___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_dec(x_14);
x_25 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___closed__1;
x_26 = lean_string_append(x_25, x_1);
lean_dec(x_1);
x_27 = l_Lean_Server_registerLspRequestHandler___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_box(0);
x_33 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__10(x_4, x_5, x_9, x_10, x_1, x_11, x_7, x_12, x_2, x_32, x_31);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_liftExcept___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_get___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_StateRefT_x27_get___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_liftExcept___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__3___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__9(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__8(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__3(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(x_1, x_2, lean_box(0), x_3, x_4, lean_box(0), x_5, lean_box(0), x_6, x_7, x_8, x_9, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_Server_registerLspRequestHandler___lambda__3___closed__1;
x_15 = lean_st_ref_get(x_14, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = l_Lean_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__6(x_17, x_1);
if (x_19 == 0)
{
lean_object* x_20; 
lean_free_object(x_15);
x_20 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(x_1, x_2, lean_box(0), x_4, x_5, lean_box(0), x_7, lean_box(0), x_9, x_10, x_11, x_12, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_21 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___closed__1;
x_22 = lean_string_append(x_21, x_1);
lean_dec(x_1);
x_23 = l_Lean_Server_registerLspRequestHandler___lambda__4___closed__2;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_25);
return x_15;
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
x_28 = l_Lean_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__6(x_26, x_1);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(x_1, x_2, lean_box(0), x_4, x_5, lean_box(0), x_7, lean_box(0), x_9, x_10, x_11, x_12, x_27);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_30 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___closed__1;
x_31 = lean_string_append(x_30, x_1);
lean_dec(x_1);
x_32 = l_Lean_Server_registerLspRequestHandler___lambda__4___closed__2;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_27);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_registerCompleteStatefulLspRequestHandler___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_Lean_Server_registerLspRequestHandler___lambda__3___closed__1;
x_14 = lean_st_ref_get(x_13, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Lean_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__6(x_16, x_5);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_14);
x_19 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(x_5, x_6, lean_box(0), x_1, x_2, lean_box(0), x_4, lean_box(0), x_8, x_9, x_10, x_11, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_20 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___closed__1;
x_21 = lean_string_append(x_20, x_5);
lean_dec(x_5);
x_22 = l_Lean_Server_registerLspRequestHandler___lambda__4___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = l_Lean_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__6(x_25, x_5);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(x_5, x_6, lean_box(0), x_1, x_2, lean_box(0), x_4, lean_box(0), x_8, x_9, x_10, x_11, x_26);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_29 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___closed__1;
x_30 = lean_string_append(x_29, x_5);
lean_dec(x_5);
x_31 = l_Lean_Server_registerLspRequestHandler___lambda__4___closed__2;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_26);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_registerCompleteStatefulLspRequestHandler___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_registerCompleteStatefulLspRequestHandler___spec__1___rarg), 12, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_4(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = 1;
x_12 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
lean_ctor_set(x_8, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = 1;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_6, 0, x_17);
return x_6;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_22 = x_18;
} else {
 lean_dec_ref(x_18);
 x_22 = lean_box(0);
}
x_23 = 1;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
if (lean_is_scalar(x_22)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_22;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_19);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_6);
if (x_27 == 0)
{
return x_6;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_6, 0);
x_29 = lean_ctor_get(x_6, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_6);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_alloc_closure((void*)(l_Lean_Server_registerCompleteStatefulLspRequestHandler___lambda__1), 5, 1);
lean_closure_set(x_13, 0, x_10);
x_14 = lean_box(0);
x_15 = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_registerCompleteStatefulLspRequestHandler___spec__1___rarg(x_3, x_4, lean_box(0), x_6, x_1, x_14, lean_box(0), x_8, x_9, x_13, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
x_16 = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler(x_1, x_15, lean_box(0), x_5, x_6, lean_box(0), x_8, lean_box(0), x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at_Lean_Server_isStatefulLspRequestMethod___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_string_dec_eq(x_5, x_9);
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
uint8_t x_14; 
lean_dec(x_4);
x_14 = 1;
return x_14;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at_Lean_Server_isStatefulLspRequestMethod___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__2;
x_7 = lean_usize_land(x_2, x_6);
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
x_12 = lean_string_dec_eq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_usize_shift_right(x_2, x_5);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_PersistentHashMap_containsAtAux___at_Lean_Server_isStatefulLspRequestMethod___spec__3(x_17, x_18, lean_box(0), x_19, x_3);
lean_dec(x_18);
lean_dec(x_17);
return x_20;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at_Lean_Server_isStatefulLspRequestMethod___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_string_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at_Lean_Server_isStatefulLspRequestMethod___spec__2(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_isStatefulLspRequestMethod(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__10___closed__2;
x_4 = lean_st_ref_get(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_PersistentHashMap_contains___at_Lean_Server_isStatefulLspRequestMethod___spec__1(x_6, x_1);
x_8 = lean_box(x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = l_Lean_PersistentHashMap_contains___at_Lean_Server_isStatefulLspRequestMethod___spec__1(x_9, x_1);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at_Lean_Server_isStatefulLspRequestMethod___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Lean_PersistentHashMap_containsAtAux___at_Lean_Server_isStatefulLspRequestMethod___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at_Lean_Server_isStatefulLspRequestMethod___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at_Lean_Server_isStatefulLspRequestMethod___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at_Lean_Server_isStatefulLspRequestMethod___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at_Lean_Server_isStatefulLspRequestMethod___spec__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_isStatefulLspRequestMethod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_isStatefulLspRequestMethod(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Server_lookupStatefulLspRequestHandler___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = lean_string_dec_eq(x_5, x_9);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Server_lookupStatefulLspRequestHandler___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__2;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_string_dec_eq(x_3, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_free_object(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_usize_shift_right(x_2, x_6);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = 5;
x_22 = l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__2;
x_23 = lean_usize_land(x_2, x_22);
x_24 = lean_usize_to_nat(x_23);
x_25 = lean_box(2);
x_26 = lean_array_get(x_25, x_20, x_24);
lean_dec(x_24);
lean_dec(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_string_dec_eq(x_3, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_usize_shift_right(x_2, x_21);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Server_lookupStatefulLspRequestHandler___spec__3(x_36, x_37, lean_box(0), x_38, x_3);
lean_dec(x_37);
lean_dec(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Server_lookupStatefulLspRequestHandler___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_string_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Server_lookupStatefulLspRequestHandler___spec__2(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupStatefulLspRequestHandler(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__10___closed__2;
x_4 = lean_st_ref_get(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Server_lookupStatefulLspRequestHandler___spec__1(x_6, x_1);
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
x_10 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Server_lookupStatefulLspRequestHandler___spec__1(x_8, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Server_lookupStatefulLspRequestHandler___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Server_lookupStatefulLspRequestHandler___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Server_lookupStatefulLspRequestHandler___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Server_lookupStatefulLspRequestHandler___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Server_lookupStatefulLspRequestHandler___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Server_lookupStatefulLspRequestHandler___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupStatefulLspRequestHandler___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_lookupStatefulLspRequestHandler(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Server_partialLspRequestHandlerMethods___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at_Lean_Server_partialLspRequestHandlerMethods___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_array_push(x_1, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_toArray___at_Lean_Server_partialLspRequestHandlerMethods___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_toArray___at_Lean_Server_partialLspRequestHandlerMethods___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_toArray___at_Lean_Server_partialLspRequestHandlerMethods___spec__1___lambda__1), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at_Lean_Server_partialLspRequestHandlerMethods___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_PersistentHashMap_toArray___at_Lean_Server_partialLspRequestHandlerMethods___spec__1___closed__2;
x_3 = l_Lean_PersistentHashMap_toArray___at_Lean_Server_partialLspRequestHandlerMethods___spec__1___closed__1;
x_4 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_partialLspRequestHandlerMethods___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 8);
lean_inc(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_6);
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_ctor_set(x_6, 1, x_17);
lean_ctor_set(x_6, 0, x_16);
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 0, x_13);
x_18 = lean_array_push(x_4, x_10);
x_2 = x_8;
x_4 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
lean_ctor_set(x_6, 1, x_21);
lean_ctor_set(x_6, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_6);
x_23 = lean_array_push(x_4, x_22);
x_2 = x_8;
x_4 = x_23;
goto _start;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_6, 0);
lean_inc(x_25);
lean_dec(x_6);
x_26 = lean_ctor_get(x_10, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_28 = x_10;
} else {
 lean_dec_ref(x_10);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
 lean_ctor_set_tag(x_30, 0);
}
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_array_push(x_4, x_30);
x_2 = x_8;
x_4 = x_31;
goto _start;
}
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Server_partialLspRequestHandlerMethods___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_toArray___at_Lean_Server_partialLspRequestHandlerMethods___spec__1___closed__1;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_le(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Lean_PersistentHashMap_toArray___at_Lean_Server_partialLspRequestHandlerMethods___spec__1___closed__1;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_usize_of_nat(x_2);
x_10 = lean_usize_of_nat(x_3);
x_11 = l_Lean_PersistentHashMap_toArray___at_Lean_Server_partialLspRequestHandlerMethods___spec__1___closed__1;
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Server_partialLspRequestHandlerMethods___spec__4(x_1, x_9, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_partialLspRequestHandlerMethods(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__10___closed__2;
x_3 = lean_st_ref_get(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_PersistentHashMap_toArray___at_Lean_Server_partialLspRequestHandlerMethods___spec__1(x_5);
lean_dec(x_5);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_filterMapM___at_Lean_Server_partialLspRequestHandlerMethods___spec__3(x_6, x_8, x_7);
lean_dec(x_7);
lean_dec(x_6);
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
x_12 = l_Lean_PersistentHashMap_toArray___at_Lean_Server_partialLspRequestHandlerMethods___spec__1(x_10);
lean_dec(x_10);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Array_filterMapM___at_Lean_Server_partialLspRequestHandlerMethods___spec__3(x_12, x_14, x_13);
lean_dec(x_13);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Server_partialLspRequestHandlerMethods___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlM___at_Lean_Server_partialLspRequestHandlerMethods___spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at_Lean_Server_partialLspRequestHandlerMethods___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentHashMap_toArray___at_Lean_Server_partialLspRequestHandlerMethods___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_partialLspRequestHandlerMethods___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Server_partialLspRequestHandlerMethods___spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Server_partialLspRequestHandlerMethods___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterMapM___at_Lean_Server_partialLspRequestHandlerMethods___spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_chainStatefulLspRequestHandler___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_chainStatefulLspRequestHandler___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_liftExcept___at_Lean_Server_chainStatefulLspRequestHandler___spec__2___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_chainStatefulLspRequestHandler___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_chainStatefulLspRequestHandler___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_liftExcept___at_Lean_Server_chainStatefulLspRequestHandler___spec__3___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Server_parseRequestParams___rarg(x_1, x_6);
x_11 = l_liftExcept___at_Lean_Server_chainStatefulLspRequestHandler___spec__2___rarg(x_10, x_8, x_9);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(x_2, x_7, lean_box(0), x_3, x_8, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_apply_4(x_4, x_12, x_15, x_8, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_apply_1(x_5, x_25);
lean_ctor_set(x_19, 0, x_26);
lean_ctor_set(x_18, 0, x_3);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_18);
lean_ctor_set(x_17, 0, x_27);
return x_17;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_apply_1(x_5, x_28);
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_29);
lean_ctor_set(x_18, 0, x_3);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_18);
lean_ctor_set(x_17, 0, x_32);
return x_17;
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_dec(x_18);
x_34 = lean_ctor_get(x_19, 0);
lean_inc(x_34);
x_35 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_36 = x_19;
} else {
 lean_dec_ref(x_19);
 x_36 = lean_box(0);
}
x_37 = lean_apply_1(x_5, x_34);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 1, 1);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_3);
lean_ctor_set(x_39, 1, x_33);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_17, 0, x_40);
return x_17;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_41 = lean_ctor_get(x_17, 1);
lean_inc(x_41);
lean_dec(x_17);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_43 = x_18;
} else {
 lean_dec_ref(x_18);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_19, 0);
lean_inc(x_44);
x_45 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_46 = x_19;
} else {
 lean_dec_ref(x_19);
 x_46 = lean_box(0);
}
x_47 = lean_apply_1(x_5, x_44);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 1, 1);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_45);
if (lean_is_scalar(x_43)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_43;
}
lean_ctor_set(x_49, 0, x_3);
lean_ctor_set(x_49, 1, x_42);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_41);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_5);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_17);
if (x_52 == 0)
{
return x_17;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_17, 0);
x_54 = lean_ctor_get(x_17, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_17);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_14);
if (x_56 == 0)
{
return x_14;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_14, 0);
x_58 = lean_ctor_get(x_14, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_14);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_st_ref_get(x_1, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Server_parseRequestParams___rarg(x_2, x_3);
x_15 = l_liftExcept___at_Lean_Server_chainStatefulLspRequestHandler___spec__3___rarg(x_14, x_9, x_13);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(x_4, x_12, lean_box(0), x_5, x_9, x_17);
lean_dec(x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_apply_4(x_6, x_16, x_19, x_9, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_apply_1(x_7, x_28);
lean_ctor_set(x_23, 0, x_29);
lean_ctor_set(x_22, 0, x_5);
x_30 = lean_st_ref_set(x_1, x_22, x_24);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_23);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
lean_inc(x_35);
lean_dec(x_23);
x_37 = lean_apply_1(x_7, x_35);
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_36);
lean_ctor_set(x_22, 0, x_5);
x_39 = lean_st_ref_set(x_1, x_22, x_24);
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
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_43 = lean_ctor_get(x_22, 1);
lean_inc(x_43);
lean_dec(x_22);
x_44 = lean_ctor_get(x_23, 0);
lean_inc(x_44);
x_45 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_46 = x_23;
} else {
 lean_dec_ref(x_23);
 x_46 = lean_box(0);
}
x_47 = lean_apply_1(x_7, x_44);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 1, 1);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_5);
lean_ctor_set(x_49, 1, x_43);
x_50 = lean_st_ref_set(x_1, x_49, x_24);
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
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_7);
lean_dec(x_5);
x_54 = !lean_is_exclusive(x_21);
if (x_54 == 0)
{
return x_21;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_21, 0);
x_56 = lean_ctor_get(x_21, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_21);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_58 = !lean_is_exclusive(x_18);
if (x_58 == 0)
{
return x_18;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_18, 0);
x_60 = lean_ctor_get(x_18, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_18);
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
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_62 = !lean_is_exclusive(x_15);
if (x_62 == 0)
{
return x_15;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_15, 0);
x_64 = lean_ctor_get(x_15, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_15);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_12 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__2___boxed), 10, 7);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_5);
lean_closure_set(x_12, 5, x_6);
lean_closure_set(x_12, 6, x_7);
x_13 = l_Lean_Server_RequestM_mapTaskCostly___rarg(x_8, x_12, x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__4___closed__1;
x_17 = l_Task_Priority_default;
x_18 = 1;
lean_inc(x_14);
x_19 = lean_task_map(x_16, x_14, x_17, x_18);
x_20 = lean_st_ref_set(x_9, x_19, x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_14);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__3___boxed), 11, 7);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_8);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_4);
lean_closure_set(x_11, 5, x_5);
lean_closure_set(x_11, 6, x_6);
x_12 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__5___closed__1;
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__4___rarg), 5, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_11);
x_14 = l_Std_Mutex_atomically___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__5(x_7, x_13, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__8___boxed), 9, 5);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_4);
lean_closure_set(x_9, 4, x_6);
x_10 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__5___closed__1;
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__4___rarg), 5, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_9);
x_12 = l_Std_Mutex_atomically___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__6(x_5, x_11, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___lambda__1), 3, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
x_13 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__10___closed__1;
x_14 = l_Std_Mutex_new___rarg(x_13, x_11);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_3);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 0, x_3);
lean_inc(x_14);
x_18 = lean_st_mk_ref(x_14, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_5);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__1___boxed), 9, 5);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_5);
lean_closure_set(x_21, 2, x_3);
lean_closure_set(x_21, 3, x_6);
lean_closure_set(x_21, 4, x_7);
lean_inc(x_16);
lean_inc(x_3);
lean_inc(x_5);
lean_inc(x_19);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__4), 10, 7);
lean_closure_set(x_22, 0, x_19);
lean_closure_set(x_22, 1, x_1);
lean_closure_set(x_22, 2, x_5);
lean_closure_set(x_22, 3, x_3);
lean_closure_set(x_22, 4, x_6);
lean_closure_set(x_22, 5, x_7);
lean_closure_set(x_22, 6, x_16);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_5);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__6___boxed), 7, 3);
lean_closure_set(x_23, 0, x_5);
lean_closure_set(x_23, 1, x_3);
lean_closure_set(x_23, 2, x_8);
lean_inc(x_16);
lean_inc(x_5);
lean_inc(x_19);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__5), 8, 5);
lean_closure_set(x_24, 0, x_19);
lean_closure_set(x_24, 1, x_5);
lean_closure_set(x_24, 2, x_3);
lean_closure_set(x_24, 3, x_8);
lean_closure_set(x_24, 4, x_16);
x_25 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__10___closed__2;
x_26 = lean_st_ref_take(x_25, x_20);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_22);
lean_ctor_set(x_29, 3, x_23);
lean_ctor_set(x_29, 4, x_24);
lean_ctor_set(x_29, 5, x_16);
lean_ctor_set(x_29, 6, x_14);
lean_ctor_set(x_29, 7, x_19);
lean_ctor_set(x_29, 8, x_9);
x_30 = l_Lean_PersistentHashMap_insert___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__7(x_27, x_5, x_29);
x_31 = lean_st_ref_set(x_25, x_30, x_28);
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
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_36 = lean_ctor_get(x_14, 0);
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_14);
lean_inc(x_3);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_3);
lean_ctor_set(x_38, 1, x_4);
lean_inc(x_38);
x_39 = lean_st_mk_ref(x_38, x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_5);
lean_inc(x_1);
x_42 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__1___boxed), 9, 5);
lean_closure_set(x_42, 0, x_1);
lean_closure_set(x_42, 1, x_5);
lean_closure_set(x_42, 2, x_3);
lean_closure_set(x_42, 3, x_6);
lean_closure_set(x_42, 4, x_7);
lean_inc(x_36);
lean_inc(x_3);
lean_inc(x_5);
lean_inc(x_40);
x_43 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__4), 10, 7);
lean_closure_set(x_43, 0, x_40);
lean_closure_set(x_43, 1, x_1);
lean_closure_set(x_43, 2, x_5);
lean_closure_set(x_43, 3, x_3);
lean_closure_set(x_43, 4, x_6);
lean_closure_set(x_43, 5, x_7);
lean_closure_set(x_43, 6, x_36);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_5);
x_44 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__6___boxed), 7, 3);
lean_closure_set(x_44, 0, x_5);
lean_closure_set(x_44, 1, x_3);
lean_closure_set(x_44, 2, x_8);
lean_inc(x_36);
lean_inc(x_5);
lean_inc(x_40);
x_45 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__5), 8, 5);
lean_closure_set(x_45, 0, x_40);
lean_closure_set(x_45, 1, x_5);
lean_closure_set(x_45, 2, x_3);
lean_closure_set(x_45, 3, x_8);
lean_closure_set(x_45, 4, x_36);
x_46 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__10___closed__2;
x_47 = lean_st_ref_take(x_46, x_41);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_50, 0, x_12);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set(x_50, 2, x_43);
lean_ctor_set(x_50, 3, x_44);
lean_ctor_set(x_50, 4, x_45);
lean_ctor_set(x_50, 5, x_36);
lean_ctor_set(x_50, 6, x_38);
lean_ctor_set(x_50, 7, x_40);
lean_ctor_set(x_50, 8, x_9);
x_51 = l_Lean_PersistentHashMap_insert___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__7(x_48, x_5, x_50);
x_52 = lean_st_ref_set(x_46, x_51, x_49);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_Lean_initializing(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___closed__1;
x_19 = lean_string_append(x_18, x_5);
lean_dec(x_5);
x_20 = l_Lean_Server_registerLspRequestHandler___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___closed__1;
x_25 = lean_string_append(x_24, x_5);
lean_dec(x_5);
x_26 = l_Lean_Server_registerLspRequestHandler___closed__1;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_23);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_dec(x_13);
x_31 = lean_box(0);
x_32 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__6(x_1, x_2, x_8, x_9, x_5, x_10, x_4, x_11, x_6, x_31, x_30);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg), 12, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_chainStatefulLspRequestHandler___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to convert response of previous request handler when chaining stateful LSP request handlers", 98, 98);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_chainStatefulLspRequestHandler___lambda__1___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 4;
x_2 = l_Lean_Server_chainStatefulLspRequestHandler___lambda__1___closed__1;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_7);
x_11 = lean_apply_1(x_1, x_7);
lean_inc(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_8);
lean_inc(x_9);
x_13 = lean_apply_4(x_3, x_11, x_12, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_apply_1(x_4, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_23 = l_Lean_Server_chainStatefulLspRequestHandler___lambda__1___closed__2;
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_23);
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_13);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
lean_ctor_set(x_15, 0, x_24);
x_25 = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(x_5, x_19, lean_box(0), x_2, x_9, x_17);
lean_dec(x_2);
lean_dec(x_19);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_apply_5(x_6, x_7, x_15, x_26, x_9, x_27);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_15, 0);
x_34 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
lean_inc(x_33);
lean_dec(x_15);
x_35 = lean_apply_1(x_4, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
lean_dec(x_35);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_36 = l_Lean_Server_chainStatefulLspRequestHandler___lambda__1___closed__2;
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_36);
return x_13;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_free_object(x_13);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_34);
x_39 = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(x_5, x_19, lean_box(0), x_2, x_9, x_17);
lean_dec(x_2);
lean_dec(x_19);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_apply_5(x_6, x_7, x_38, x_40, x_9, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_38);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
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
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_13, 1);
lean_inc(x_47);
lean_dec(x_13);
x_48 = lean_ctor_get(x_14, 1);
lean_inc(x_48);
lean_dec(x_14);
x_49 = lean_ctor_get(x_15, 0);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_51 = x_15;
} else {
 lean_dec_ref(x_15);
 x_51 = lean_box(0);
}
x_52 = lean_apply_1(x_4, x_49);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_53 = l_Lean_Server_chainStatefulLspRequestHandler___lambda__1___closed__2;
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_47);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
lean_dec(x_52);
if (lean_is_scalar(x_51)) {
 x_56 = lean_alloc_ctor(0, 1, 1);
} else {
 x_56 = x_51;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_50);
x_57 = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(x_5, x_48, lean_box(0), x_2, x_9, x_47);
lean_dec(x_2);
lean_dec(x_48);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_apply_5(x_6, x_7, x_56, x_58, x_9, x_59);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_56);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_61 = lean_ctor_get(x_57, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_63 = x_57;
} else {
 lean_dec_ref(x_57);
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
}
else
{
uint8_t x_65; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_6);
lean_inc(x_7);
lean_inc(x_5);
x_10 = lean_apply_4(x_2, x_5, x_9, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(x_3, x_13, lean_box(0), x_1, x_7, x_12);
lean_dec(x_1);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_apply_4(x_4, x_5, x_15, x_7, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_19, 0, x_22);
return x_17;
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
lean_ctor_set(x_17, 0, x_25);
return x_17;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
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
x_30 = lean_box(0);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
}
else
{
uint8_t x_33; 
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
else
{
uint8_t x_37; 
lean_dec(x_7);
lean_dec(x_5);
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
else
{
uint8_t x_41; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_10);
if (x_41 == 0)
{
return x_10;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_10, 0);
x_43 = lean_ctor_get(x_10, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_10);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
static lean_object* _init_l_Lean_Server_chainStatefulLspRequestHandler___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to chain stateful LSP request handler for '", 50, 50);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Server_lookupStatefulLspRequestHandler(x_1, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = l_Lean_Server_chainStatefulLspRequestHandler___lambda__3___closed__1;
x_17 = lean_string_append(x_16, x_1);
lean_dec(x_1);
x_18 = l_Lean_Server_chainLspRequestHandler___lambda__3___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_20);
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = l_Lean_Server_chainStatefulLspRequestHandler___lambda__3___closed__1;
x_23 = lean_string_append(x_22, x_1);
lean_dec(x_1);
x_24 = l_Lean_Server_chainLspRequestHandler___lambda__3___closed__2;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_dec(x_12);
x_29 = lean_ctor_get(x_13, 0);
lean_inc(x_29);
lean_dec(x_13);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 6);
lean_inc(x_32);
x_33 = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21(x_1, x_32, lean_box(0), x_2, x_28);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_1);
lean_inc(x_2);
x_36 = lean_alloc_closure((void*)(l_Lean_Server_chainStatefulLspRequestHandler___lambda__1___boxed), 10, 6);
lean_closure_set(x_36, 0, x_3);
lean_closure_set(x_36, 1, x_2);
lean_closure_set(x_36, 2, x_30);
lean_closure_set(x_36, 3, x_4);
lean_closure_set(x_36, 4, x_1);
lean_closure_set(x_36, 5, x_5);
lean_inc(x_1);
lean_inc(x_2);
x_37 = lean_alloc_closure((void*)(l_Lean_Server_chainStatefulLspRequestHandler___lambda__2___boxed), 8, 4);
lean_closure_set(x_37, 0, x_2);
lean_closure_set(x_37, 1, x_31);
lean_closure_set(x_37, 2, x_1);
lean_closure_set(x_37, 3, x_6);
x_38 = lean_ctor_get(x_29, 8);
lean_inc(x_38);
lean_dec(x_29);
x_39 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg(x_7, x_8, lean_box(0), x_9, x_1, x_38, lean_box(0), x_2, x_34, x_36, x_37, x_35);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_initializing(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = l_Lean_Server_chainStatefulLspRequestHandler___lambda__3___closed__1;
x_20 = lean_string_append(x_19, x_1);
lean_dec(x_1);
x_21 = l_Lean_Server_registerLspRequestHandler___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_dec(x_14);
x_25 = l_Lean_Server_chainStatefulLspRequestHandler___lambda__3___closed__1;
x_26 = lean_string_append(x_25, x_1);
lean_dec(x_1);
x_27 = l_Lean_Server_registerLspRequestHandler___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_box(0);
x_33 = l_Lean_Server_chainStatefulLspRequestHandler___lambda__3(x_1, x_10, x_4, x_7, x_11, x_12, x_3, x_5, x_8, x_32, x_31);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_chainStatefulLspRequestHandler___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_liftExcept___at_Lean_Server_chainStatefulLspRequestHandler___spec__2___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_chainStatefulLspRequestHandler___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_liftExcept___at_Lean_Server_chainStatefulLspRequestHandler___spec__3___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_chainStatefulLspRequestHandler___spec__1___rarg___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Server_chainStatefulLspRequestHandler___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Server_chainStatefulLspRequestHandler___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Server_chainStatefulLspRequestHandler___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_handleOnDidChange___spec__4___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_array_uget(x_2, x_3);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
lean_inc(x_6);
x_12 = lean_apply_5(x_1, x_5, x_10, x_11, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_5 = x_13;
x_7 = x_14;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_6);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
case 1:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_9, 0);
lean_inc(x_22);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_23 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_handleOnDidChange___spec__3___rarg(x_1, x_22, x_5, x_6, x_7);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = 1;
x_27 = lean_usize_add(x_3, x_26);
x_3 = x_27;
x_5 = x_24;
x_7 = x_25;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_6);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
return x_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
default: 
{
size_t x_33; size_t x_34; 
x_33 = 1;
x_34 = lean_usize_add(x_3, x_33);
x_3 = x_34;
goto _start;
}
}
}
else
{
lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_5);
lean_ctor_set(x_36, 1, x_7);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_handleOnDidChange___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Server_handleOnDidChange___spec__4___rarg___boxed), 7, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_handleOnDidChange___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_array_fget(x_2, x_5);
x_13 = lean_array_fget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_7);
x_14 = lean_apply_5(x_1, x_6, x_12, x_13, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_18;
x_6 = x_15;
x_8 = x_16;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_handleOnDidChange___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_handleOnDidChange___spec__5___rarg___boxed), 8, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_handleOnDidChange___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Server_handleOnDidChange___spec__4___rarg(x_1, x_6, x_13, x_14, x_3, x_4, x_5);
return x_15;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_handleOnDidChange___spec__5___rarg(x_1, x_16, x_17, lean_box(0), x_18, x_3, x_4, x_5);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_handleOnDidChange___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_handleOnDidChange___spec__3___rarg___boxed), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Server_handleOnDidChange___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_handleOnDidChange___spec__3___rarg(x_2, x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at_Lean_Server_handleOnDidChange___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_4(x_1, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at_Lean_Server_handleOnDidChange___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at_Lean_Server_handleOnDidChange___spec__1___lambda__1___boxed), 6, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = lean_box(0);
x_7 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_handleOnDidChange___spec__3___rarg(x_5, x_1, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 4);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_3(x_6, x_1, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__10___closed__2;
x_5 = lean_st_ref_get(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_Server_handleOnDidChange___lambda__1___boxed), 5, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = l_Lean_PersistentHashMap_forM___at_Lean_Server_handleOnDidChange___spec__1(x_6, x_8, x_2, x_7);
lean_dec(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_handleOnDidChange___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Server_handleOnDidChange___spec__4___rarg(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_handleOnDidChange___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_handleOnDidChange___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_handleOnDidChange___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_handleOnDidChange___spec__3___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Server_handleOnDidChange___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_foldlM___at_Lean_Server_handleOnDidChange___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at_Lean_Server_handleOnDidChange___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_forM___at_Lean_Server_handleOnDidChange___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at_Lean_Server_handleOnDidChange___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_forM___at_Lean_Server_handleOnDidChange___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_handleOnDidChange___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest___lambda__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 1;
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = 1;
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
static lean_object* _init_l_Lean_Server_handleLspRequest___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("request '", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_handleLspRequest___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' routed through watchdog but unknown in worker; are both using the same plugins\?", 81, 81);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_handleLspRequest___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_handleLspRequest___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_Server_isStatefulLspRequestMethod(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Lean_Server_lookupLspRequestHandler(x_1, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = l_Lean_Server_handleLspRequest___closed__1;
x_14 = lean_string_append(x_13, x_1);
x_15 = l_Lean_Server_handleLspRequest___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = 4;
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = l_Lean_Server_handleLspRequest___closed__1;
x_21 = lean_string_append(x_20, x_1);
x_22 = l_Lean_Server_handleLspRequest___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = 4;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_19);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_dec(x_9);
x_28 = lean_ctor_get(x_10, 0);
lean_inc(x_28);
lean_dec(x_10);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_apply_3(x_29, x_2, x_3, x_27);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = l_Lean_Server_handleLspRequest___closed__3;
x_34 = l_Task_Priority_default;
x_35 = 1;
x_36 = lean_task_map(x_33, x_32, x_34, x_35);
lean_ctor_set(x_30, 0, x_36);
return x_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_30, 0);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_30);
x_39 = l_Lean_Server_handleLspRequest___closed__3;
x_40 = l_Task_Priority_default;
x_41 = 1;
x_42 = lean_task_map(x_39, x_37, x_40, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
}
else
{
uint8_t x_44; 
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
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_5, 1);
lean_inc(x_48);
lean_dec(x_5);
x_49 = l_Lean_Server_lookupStatefulLspRequestHandler(x_1, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_49, 0);
lean_dec(x_52);
x_53 = l_Lean_Server_handleLspRequest___closed__1;
x_54 = lean_string_append(x_53, x_1);
x_55 = l_Lean_Server_handleLspRequest___closed__2;
x_56 = lean_string_append(x_54, x_55);
x_57 = 4;
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_57);
lean_ctor_set_tag(x_49, 1);
lean_ctor_set(x_49, 0, x_58);
return x_49;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_49, 1);
lean_inc(x_59);
lean_dec(x_49);
x_60 = l_Lean_Server_handleLspRequest___closed__1;
x_61 = lean_string_append(x_60, x_1);
x_62 = l_Lean_Server_handleLspRequest___closed__2;
x_63 = lean_string_append(x_61, x_62);
x_64 = 4;
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_59);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_49, 1);
lean_inc(x_67);
lean_dec(x_49);
x_68 = lean_ctor_get(x_50, 0);
lean_inc(x_68);
lean_dec(x_50);
x_69 = lean_ctor_get(x_68, 2);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_apply_3(x_69, x_2, x_3, x_67);
return x_70;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_handleLspRequest(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_routeLspRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Server_isStatefulLspRequestMethod(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = l_Lean_Server_lookupLspRequestHandler(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = l_Lean_Server_RequestError_methodNotFound(x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = l_Lean_Server_RequestError_methodNotFound(x_1);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_8, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_9, 0);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_apply_1(x_21, x_2);
lean_ctor_set(x_8, 0, x_22);
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_dec(x_8);
x_24 = lean_ctor_get(x_9, 0);
lean_inc(x_24);
lean_dec(x_9);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_apply_1(x_25, x_2);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_4, 1);
lean_inc(x_28);
lean_dec(x_4);
x_29 = l_Lean_Server_lookupStatefulLspRequestHandler(x_1, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = l_Lean_Server_RequestError_methodNotFound(x_1);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = l_Lean_Server_RequestError_methodNotFound(x_1);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_29);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_29, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_30, 0);
lean_inc(x_41);
lean_dec(x_30);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_apply_1(x_42, x_2);
lean_ctor_set(x_29, 0, x_43);
return x_29;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_29, 1);
lean_inc(x_44);
lean_dec(x_29);
x_45 = lean_ctor_get(x_30, 0);
lean_inc(x_45);
lean_dec(x_30);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_apply_1(x_46, x_2);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_routeLspRequest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_routeLspRequest(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Lean_DeclarationRange(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_RequestCancellation(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_ServerTask(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_FileSource(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_FileWorker_Utils(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Rpc_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sync_Mutex(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Requests(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_DeclarationRange(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_RequestCancellation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_ServerTask(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_FileSource(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_FileWorker_Utils(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Rpc_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sync_Mutex(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Language_SnapshotTree_foldSnaps___rarg___closed__1 = _init_l_Lean_Language_SnapshotTree_foldSnaps___rarg___closed__1();
lean_mark_persistent(l_Lean_Language_SnapshotTree_foldSnaps___rarg___closed__1);
l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__1___closed__1 = _init_l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__1___closed__1);
l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__3___closed__1 = _init_l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lambda__3___closed__1);
l_Lean_Server_instInhabitedRequestError___closed__1 = _init_l_Lean_Server_instInhabitedRequestError___closed__1();
lean_mark_persistent(l_Lean_Server_instInhabitedRequestError___closed__1);
l_Lean_Server_instInhabitedRequestError___closed__2 = _init_l_Lean_Server_instInhabitedRequestError___closed__2();
lean_mark_persistent(l_Lean_Server_instInhabitedRequestError___closed__2);
l_Lean_Server_instInhabitedRequestError = _init_l_Lean_Server_instInhabitedRequestError();
lean_mark_persistent(l_Lean_Server_instInhabitedRequestError);
l_Lean_Server_RequestError_fileChanged___closed__1 = _init_l_Lean_Server_RequestError_fileChanged___closed__1();
lean_mark_persistent(l_Lean_Server_RequestError_fileChanged___closed__1);
l_Lean_Server_RequestError_fileChanged___closed__2 = _init_l_Lean_Server_RequestError_fileChanged___closed__2();
lean_mark_persistent(l_Lean_Server_RequestError_fileChanged___closed__2);
l_Lean_Server_RequestError_fileChanged = _init_l_Lean_Server_RequestError_fileChanged();
lean_mark_persistent(l_Lean_Server_RequestError_fileChanged);
l_Lean_Server_RequestError_methodNotFound___closed__1 = _init_l_Lean_Server_RequestError_methodNotFound___closed__1();
lean_mark_persistent(l_Lean_Server_RequestError_methodNotFound___closed__1);
l_Lean_Server_RequestError_methodNotFound___closed__2 = _init_l_Lean_Server_RequestError_methodNotFound___closed__2();
lean_mark_persistent(l_Lean_Server_RequestError_methodNotFound___closed__2);
l_Lean_Server_RequestError_requestCancelled___closed__1 = _init_l_Lean_Server_RequestError_requestCancelled___closed__1();
lean_mark_persistent(l_Lean_Server_RequestError_requestCancelled___closed__1);
l_Lean_Server_RequestError_requestCancelled = _init_l_Lean_Server_RequestError_requestCancelled();
lean_mark_persistent(l_Lean_Server_RequestError_requestCancelled);
l_Lean_Server_parseRequestParams___rarg___closed__1 = _init_l_Lean_Server_parseRequestParams___rarg___closed__1();
lean_mark_persistent(l_Lean_Server_parseRequestParams___rarg___closed__1);
l_Lean_Server_parseRequestParams___rarg___closed__2 = _init_l_Lean_Server_parseRequestParams___rarg___closed__2();
lean_mark_persistent(l_Lean_Server_parseRequestParams___rarg___closed__2);
l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___closed__1 = _init_l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___closed__1();
lean_mark_persistent(l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___closed__1);
l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___closed__2 = _init_l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___closed__2();
lean_mark_persistent(l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___closed__2);
l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___closed__3 = _init_l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___closed__3();
lean_mark_persistent(l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___closed__3);
l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___closed__4 = _init_l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___closed__4();
lean_mark_persistent(l_Lean_Server_RequestM_withWaitFindSnapAtPos___rarg___closed__4);
l_Lean_Server_RequestM_findCmdParsedSnap_go___lambda__1___closed__1 = _init_l_Lean_Server_RequestM_findCmdParsedSnap_go___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Server_RequestM_findCmdParsedSnap_go___lambda__1___closed__1);
l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__1 = _init_l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__1);
l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__2 = _init_l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__2);
l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__3 = _init_l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__3);
l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__4 = _init_l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__4);
l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__5 = _init_l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__5);
l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__6 = _init_l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Server_RequestM_findCmdDataAtPos___lambda__1___closed__6);
l_Lean_Server_RequestM_findInfoTreeAtPos___closed__1 = _init_l_Lean_Server_RequestM_findInfoTreeAtPos___closed__1();
lean_mark_persistent(l_Lean_Server_RequestM_findInfoTreeAtPos___closed__1);
l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_2474____closed__1 = _init_l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_2474____closed__1();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_2474____closed__1);
l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_2474____closed__2 = _init_l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_2474____closed__2();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_2474____closed__2);
if (builtin) {res = l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_2474_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_requestHandlers = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_requestHandlers);
lean_dec_ref(res);
}l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__1();
l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__2 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__2();
l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__3 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__3();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__3);
l_Lean_Server_registerLspRequestHandler___lambda__3___closed__1 = _init_l_Lean_Server_registerLspRequestHandler___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Server_registerLspRequestHandler___lambda__3___closed__1);
l_Lean_Server_registerLspRequestHandler___lambda__4___closed__1 = _init_l_Lean_Server_registerLspRequestHandler___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Server_registerLspRequestHandler___lambda__4___closed__1);
l_Lean_Server_registerLspRequestHandler___lambda__4___closed__2 = _init_l_Lean_Server_registerLspRequestHandler___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Server_registerLspRequestHandler___lambda__4___closed__2);
l_Lean_Server_registerLspRequestHandler___closed__1 = _init_l_Lean_Server_registerLspRequestHandler___closed__1();
lean_mark_persistent(l_Lean_Server_registerLspRequestHandler___closed__1);
l_Lean_Server_chainLspRequestHandler___lambda__1___closed__1 = _init_l_Lean_Server_chainLspRequestHandler___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Server_chainLspRequestHandler___lambda__1___closed__1);
l_Lean_Server_chainLspRequestHandler___lambda__1___closed__2 = _init_l_Lean_Server_chainLspRequestHandler___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Server_chainLspRequestHandler___lambda__1___closed__2);
l_Lean_Server_chainLspRequestHandler___lambda__3___closed__1 = _init_l_Lean_Server_chainLspRequestHandler___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Server_chainLspRequestHandler___lambda__3___closed__1);
l_Lean_Server_chainLspRequestHandler___lambda__3___closed__2 = _init_l_Lean_Server_chainLspRequestHandler___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Server_chainLspRequestHandler___lambda__3___closed__2);
if (builtin) {res = l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_3332_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_statefulRequestHandlers = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_statefulRequestHandlers);
lean_dec_ref(res);
}l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___closed__1 = _init_l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___closed__1();
lean_mark_persistent(l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___closed__1);
l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__4___closed__1 = _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__4___closed__1();
lean_mark_persistent(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__4___closed__1);
l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__5___closed__1 = _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__5___closed__1();
lean_mark_persistent(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__5___closed__1);
l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__10___closed__1 = _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__10___closed__1();
lean_mark_persistent(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__10___closed__1);
l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__10___closed__2 = _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__10___closed__2();
lean_mark_persistent(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___lambda__10___closed__2);
l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___closed__1 = _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___closed__1();
lean_mark_persistent(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___closed__1);
l_Lean_PersistentHashMap_toArray___at_Lean_Server_partialLspRequestHandlerMethods___spec__1___closed__1 = _init_l_Lean_PersistentHashMap_toArray___at_Lean_Server_partialLspRequestHandlerMethods___spec__1___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_toArray___at_Lean_Server_partialLspRequestHandlerMethods___spec__1___closed__1);
l_Lean_PersistentHashMap_toArray___at_Lean_Server_partialLspRequestHandlerMethods___spec__1___closed__2 = _init_l_Lean_PersistentHashMap_toArray___at_Lean_Server_partialLspRequestHandlerMethods___spec__1___closed__2();
lean_mark_persistent(l_Lean_PersistentHashMap_toArray___at_Lean_Server_partialLspRequestHandlerMethods___spec__1___closed__2);
l_Lean_Server_chainStatefulLspRequestHandler___lambda__1___closed__1 = _init_l_Lean_Server_chainStatefulLspRequestHandler___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Server_chainStatefulLspRequestHandler___lambda__1___closed__1);
l_Lean_Server_chainStatefulLspRequestHandler___lambda__1___closed__2 = _init_l_Lean_Server_chainStatefulLspRequestHandler___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Server_chainStatefulLspRequestHandler___lambda__1___closed__2);
l_Lean_Server_chainStatefulLspRequestHandler___lambda__3___closed__1 = _init_l_Lean_Server_chainStatefulLspRequestHandler___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Server_chainStatefulLspRequestHandler___lambda__3___closed__1);
l_Lean_Server_handleLspRequest___closed__1 = _init_l_Lean_Server_handleLspRequest___closed__1();
lean_mark_persistent(l_Lean_Server_handleLspRequest___closed__1);
l_Lean_Server_handleLspRequest___closed__2 = _init_l_Lean_Server_handleLspRequest___closed__2();
lean_mark_persistent(l_Lean_Server_handleLspRequest___closed__2);
l_Lean_Server_handleLspRequest___closed__3 = _init_l_Lean_Server_handleLspRequest___closed__3();
lean_mark_persistent(l_Lean_Server_handleLspRequest___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
