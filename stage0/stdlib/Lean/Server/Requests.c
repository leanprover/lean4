// Lean compiler output
// Module: Lean.Server.Requests
// Imports: public import Lean.Server.RequestCancellation public import Lean.Server.FileSource public import Lean.Server.FileWorker.Utils public import Std.Sync.Mutex
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
lean_object* l_Lean_Elab_Info_range_x3f(lean_object*);
uint8_t l_Lean_Syntax_Range_overlaps(lean_object*, lean_object*, uint8_t, uint8_t);
uint64_t lean_string_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_initializing();
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_Range_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Lean_Server_ServerTask_bindCheap___redArg(lean_object*, lean_object*);
lean_object* l_instMonadFinallyEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageLog_append(lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* l_instMonadLiftBaseIOEIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_tryFinally___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonad___aux__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Mutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_AsyncList_waitFind_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_foldInfo___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_Range_includes(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_EIO_asTask___redArg(lean_object*);
uint8_t l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
LEAN_EXPORT uint8_t l_Lean_FileMap_rangeContainsHoverPos(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_FileMap_rangeContainsHoverPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_FileMap_rangeOverlapsRequestedRange(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_FileMap_rangeOverlapsRequestedRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_FileMap_rangeIncludesRequestedRange(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_FileMap_rangeIncludesRequestedRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Language_SnapshotTree_foldSnaps___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTree_foldSnaps___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1 = (const lean_object*)&l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_instInhabitedRequestError_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Server_instInhabitedRequestError_default___closed__0 = (const lean_object*)&l_Lean_Server_instInhabitedRequestError_default___closed__0_value;
static const lean_ctor_object l_Lean_Server_instInhabitedRequestError_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_instInhabitedRequestError_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_instInhabitedRequestError_default___closed__1 = (const lean_object*)&l_Lean_Server_instInhabitedRequestError_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instInhabitedRequestError_default = (const lean_object*)&l_Lean_Server_instInhabitedRequestError_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instInhabitedRequestError = (const lean_object*)&l_Lean_Server_instInhabitedRequestError_default___closed__1_value;
static const lean_string_object l_Lean_Server_RequestError_fileChanged___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "File changed."};
static const lean_object* l_Lean_Server_RequestError_fileChanged___closed__0 = (const lean_object*)&l_Lean_Server_RequestError_fileChanged___closed__0_value;
static const lean_ctor_object l_Lean_Server_RequestError_fileChanged___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_RequestError_fileChanged___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_RequestError_fileChanged___closed__1 = (const lean_object*)&l_Lean_Server_RequestError_fileChanged___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Server_RequestError_fileChanged = (const lean_object*)&l_Lean_Server_RequestError_fileChanged___closed__1_value;
static const lean_string_object l_Lean_Server_RequestError_methodNotFound___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "No request handler found for '"};
static const lean_object* l_Lean_Server_RequestError_methodNotFound___closed__0 = (const lean_object*)&l_Lean_Server_RequestError_methodNotFound___closed__0_value;
static const lean_string_object l_Lean_Server_RequestError_methodNotFound___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Server_RequestError_methodNotFound___closed__1 = (const lean_object*)&l_Lean_Server_RequestError_methodNotFound___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_methodNotFound(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_methodNotFound___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_invalidParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_internalError(lean_object*);
static const lean_ctor_object l_Lean_Server_RequestError_requestCancelled___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_instInhabitedRequestError_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(8, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_RequestError_requestCancelled___closed__0 = (const lean_object*)&l_Lean_Server_RequestError_requestCancelled___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_RequestError_requestCancelled = (const lean_object*)&l_Lean_Server_RequestError_requestCancelled___closed__0_value;
static const lean_string_object l_Lean_Server_RequestError_rpcNeedsReconnect___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Outdated RPC session"};
static const lean_object* l_Lean_Server_RequestError_rpcNeedsReconnect___closed__0 = (const lean_object*)&l_Lean_Server_RequestError_rpcNeedsReconnect___closed__0_value;
static const lean_ctor_object l_Lean_Server_RequestError_rpcNeedsReconnect___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_RequestError_rpcNeedsReconnect___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_RequestError_rpcNeedsReconnect___closed__1 = (const lean_object*)&l_Lean_Server_RequestError_rpcNeedsReconnect___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Server_RequestError_rpcNeedsReconnect = (const lean_object*)&l_Lean_Server_RequestError_rpcNeedsReconnect___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_ofException(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_ofException___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_ofIoError(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_toLspResponseError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_toLspResponseError___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_parseRequestParams___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Cannot parse request params: "};
static const lean_object* l_Lean_Server_parseRequestParams___redArg___closed__0 = (const lean_object*)&l_Lean_Server_parseRequestParams___redArg___closed__0_value;
static const lean_string_object l_Lean_Server_parseRequestParams___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_Server_parseRequestParams___redArg___closed__1 = (const lean_object*)&l_Lean_Server_parseRequestParams___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_success_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_success_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_failure_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_failure_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_instInhabitedRequestError_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0 = (const lean_object*)&l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse_default(lean_object*);
static lean_once_cell_t l_Lean_Server_instInhabitedServerRequestResponse___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instInhabitedServerRequestResponse___closed__0;
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestTask_pure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestTask_pure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_instMonadLiftIORequestM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_instMonadLiftIORequestM___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instMonadLiftIORequestM___closed__0 = (const lean_object*)&l_Lean_Server_instMonadLiftIORequestM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instMonadLiftIORequestM = (const lean_object*)&l_Lean_Server_instMonadLiftIORequestM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_instMonadLiftEIOExceptionRequestM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instMonadLiftEIOExceptionRequestM___closed__0 = (const lean_object*)&l_Lean_Server_instMonadLiftEIOExceptionRequestM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instMonadLiftEIOExceptionRequestM = (const lean_object*)&l_Lean_Server_instMonadLiftEIOExceptionRequestM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_instMonadLiftCancellableMRequestM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instMonadLiftCancellableMRequestM___closed__0 = (const lean_object*)&l_Lean_Server_instMonadLiftCancellableMRequestM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instMonadLiftCancellableMRequestM = (const lean_object*)&l_Lean_Server_instMonadLiftCancellableMRequestM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_checkCancelled(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_checkCancelled___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Cannot parse server request response: "};
static const lean_object* l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "no snapshot found at "};
static const lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__0 = (const lean_object*)&l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__0_value;
static const lean_string_object l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__1 = (const lean_object*)&l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__1_value;
static const lean_string_object l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__2 = (const lean_object*)&l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__2_value;
static const lean_string_object l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__3 = (const lean_object*)&l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_isAfterHoverPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_isAfterHoverPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_containsHoverPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_containsHoverPos___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdParsedSnap___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdParsedSnap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__0(lean_object*);
static const lean_string_object l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Server.Requests"};
static const lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__0 = (const lean_object*)&l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__0_value;
static const lean_string_object l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.Server.RequestM.findCmdDataAtPos"};
static const lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__1 = (const lean_object*)&l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__1_value;
static const lean_string_object l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "assertion violation: s.infoTree\?.isSome\n        "};
static const lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__2 = (const lean_object*)&l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lam__2(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findInfoTreeAtPos___lam__0(lean_object*);
static const lean_closure_object l_Lean_Server_RequestM_findInfoTreeAtPos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_RequestM_findInfoTreeAtPos___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_RequestM_findInfoTreeAtPos___closed__0 = (const lean_object*)&l_Lean_Server_RequestM_findInfoTreeAtPos___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findInfoTreeAtPos(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findInfoTreeAtPos___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__0 = (const lean_object*)&l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__0_value;
static const lean_string_object l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "\"id\":"};
static const lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__1 = (const lean_object*)&l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__1_value;
static const lean_string_object l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__2 = (const lean_object*)&l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__2_value;
static const lean_string_object l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "\"jsonrpc\":\"2.0\","};
static const lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__3 = (const lean_object*)&l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__3_value;
static const lean_string_object l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\"result\":"};
static const lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__4 = (const lean_object*)&l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__4_value;
static const lean_string_object l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__5 = (const lean_object*)&l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_requestHandlers;
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_registerLspRequestHandler___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Failed to register LSP request handler for '"};
static const lean_object* l_Lean_Server_registerLspRequestHandler___redArg___closed__0 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___redArg___closed__0_value;
static const lean_string_object l_Lean_Server_registerLspRequestHandler___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "': only possible during initialization"};
static const lean_object* l_Lean_Server_registerLspRequestHandler___redArg___closed__1 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___redArg___closed__1_value;
static const lean_closure_object l_Lean_Server_registerLspRequestHandler___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerLspRequestHandler___redArg___closed__2 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerLspRequestHandler___redArg___closed__3;
static const lean_string_object l_Lean_Server_registerLspRequestHandler___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "': already registered"};
static const lean_object* l_Lean_Server_registerLspRequestHandler___redArg___closed__4 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_lookupLspRequestHandler(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_lookupLspRequestHandler___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Failed to parse original LSP response for `"};
static const lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "` when chaining: "};
static const lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "Failed to parse original LSP response JSON for `"};
static const lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_chainLspRequestHandler___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Failed to chain LSP request handler for '"};
static const lean_object* l_Lean_Server_chainLspRequestHandler___redArg___closed__0 = (const lean_object*)&l_Lean_Server_chainLspRequestHandler___redArg___closed__0_value;
static const lean_string_object l_Lean_Server_chainLspRequestHandler___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "': no initial handler registered"};
static const lean_object* l_Lean_Server_chainLspRequestHandler___redArg___closed__1 = (const lean_object*)&l_Lean_Server_chainLspRequestHandler___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_complete_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_complete_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_partial_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_partial_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_statefulRequestHandlers;
static const lean_string_object l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "Got invalid state type in stateful LSP request handler for "};
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1;
static const lean_string_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "Failed to register stateful LSP request handler for '"};
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__4 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftBaseIOEIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__5 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__5_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__4_value),((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__5_value)} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__6 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__6_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__6_value),((lean_object*)&l_Lean_Server_instMonadLiftEIOExceptionRequestM___closed__0_value)} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__7 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__7_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadFinallyEIO___aux__1___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__8 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__8_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_tryFinally___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__8_value)} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__9 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__9_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__10 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__10_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__4_value),((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__10_value)} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__11 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__11_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__11_value),((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__5_value)} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__12 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__12_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__12_value),((lean_object*)&l_Lean_Server_instMonadLiftEIOExceptionRequestM___closed__0_value)} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__13 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__13_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__14 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__14_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_isStatefulLspRequestMethod(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_isStatefulLspRequestMethod___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_lookupStatefulLspRequestHandler(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_lookupStatefulLspRequestHandler___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__0_value;
static const lean_array_object l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_partialLspRequestHandlerMethods();
LEAN_EXPORT lean_object* l_Lean_Server_partialLspRequestHandlerMethods___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 99, .m_capacity = 99, .m_length = 98, .m_data = "Failed to convert response of previous request handler when chaining stateful LSP request handlers"};
static const lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1;
static const lean_string_object l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 97, .m_capacity = 97, .m_length = 96, .m_data = "Failed to parse response of previous request handler when chaining stateful LSP request handlers"};
static const lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "Failed to chain stateful LSP request handler for '"};
static const lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0 = (const lean_object*)&l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_handleLspRequest___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "request '"};
static const lean_object* l_Lean_Server_handleLspRequest___closed__0 = (const lean_object*)&l_Lean_Server_handleLspRequest___closed__0_value;
static const lean_string_object l_Lean_Server_handleLspRequest___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "' routed through watchdog but unknown in worker; are both using the same plugins\?"};
static const lean_object* l_Lean_Server_handleLspRequest___closed__1 = (const lean_object*)&l_Lean_Server_handleLspRequest___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_routeLspRequest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_routeLspRequest___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_FileMap_rangeContainsHoverPos(lean_object* v_text_1_, lean_object* v_r_2_, lean_object* v_hoverPos_3_, uint8_t v_includeStop_4_){
_start:
{
if (v_includeStop_4_ == 0)
{
lean_object* v_stop_5_; lean_object* v_source_6_; lean_object* v___x_7_; uint8_t v_isRangeAtEOF_8_; uint8_t v___x_9_; 
v_stop_5_ = lean_ctor_get(v_r_2_, 1);
v_source_6_ = lean_ctor_get(v_text_1_, 0);
v___x_7_ = lean_string_utf8_byte_size(v_source_6_);
v_isRangeAtEOF_8_ = lean_nat_dec_eq(v_stop_5_, v___x_7_);
v___x_9_ = l_Lean_Syntax_Range_contains(v_r_2_, v_hoverPos_3_, v_isRangeAtEOF_8_);
return v___x_9_;
}
else
{
uint8_t v___x_10_; 
v___x_10_ = l_Lean_Syntax_Range_contains(v_r_2_, v_hoverPos_3_, v_includeStop_4_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_rangeContainsHoverPos___boxed(lean_object* v_text_11_, lean_object* v_r_12_, lean_object* v_hoverPos_13_, lean_object* v_includeStop_14_){
_start:
{
uint8_t v_includeStop_boxed_15_; uint8_t v_res_16_; lean_object* v_r_17_; 
v_includeStop_boxed_15_ = lean_unbox(v_includeStop_14_);
v_res_16_ = l_Lean_FileMap_rangeContainsHoverPos(v_text_11_, v_r_12_, v_hoverPos_13_, v_includeStop_boxed_15_);
lean_dec(v_hoverPos_13_);
lean_dec_ref(v_r_12_);
lean_dec_ref(v_text_11_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
LEAN_EXPORT uint8_t l_Lean_FileMap_rangeOverlapsRequestedRange(lean_object* v_text_18_, lean_object* v_documentRange_19_, lean_object* v_requestedRange_20_, uint8_t v_includeDocumentRangeStop_21_, uint8_t v_includeRequestedRangeStop_22_){
_start:
{
if (v_includeDocumentRangeStop_21_ == 0)
{
lean_object* v_stop_23_; lean_object* v_source_24_; lean_object* v___x_25_; uint8_t v_isDocumentRangeAtEOF_26_; uint8_t v___x_27_; 
v_stop_23_ = lean_ctor_get(v_documentRange_19_, 1);
v_source_24_ = lean_ctor_get(v_text_18_, 0);
v___x_25_ = lean_string_utf8_byte_size(v_source_24_);
v_isDocumentRangeAtEOF_26_ = lean_nat_dec_eq(v_stop_23_, v___x_25_);
v___x_27_ = l_Lean_Syntax_Range_overlaps(v_documentRange_19_, v_requestedRange_20_, v_isDocumentRangeAtEOF_26_, v_includeRequestedRangeStop_22_);
return v___x_27_;
}
else
{
uint8_t v___x_28_; 
v___x_28_ = l_Lean_Syntax_Range_overlaps(v_documentRange_19_, v_requestedRange_20_, v_includeDocumentRangeStop_21_, v_includeRequestedRangeStop_22_);
return v___x_28_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_rangeOverlapsRequestedRange___boxed(lean_object* v_text_29_, lean_object* v_documentRange_30_, lean_object* v_requestedRange_31_, lean_object* v_includeDocumentRangeStop_32_, lean_object* v_includeRequestedRangeStop_33_){
_start:
{
uint8_t v_includeDocumentRangeStop_boxed_34_; uint8_t v_includeRequestedRangeStop_boxed_35_; uint8_t v_res_36_; lean_object* v_r_37_; 
v_includeDocumentRangeStop_boxed_34_ = lean_unbox(v_includeDocumentRangeStop_32_);
v_includeRequestedRangeStop_boxed_35_ = lean_unbox(v_includeRequestedRangeStop_33_);
v_res_36_ = l_Lean_FileMap_rangeOverlapsRequestedRange(v_text_29_, v_documentRange_30_, v_requestedRange_31_, v_includeDocumentRangeStop_boxed_34_, v_includeRequestedRangeStop_boxed_35_);
lean_dec_ref(v_requestedRange_31_);
lean_dec_ref(v_documentRange_30_);
lean_dec_ref(v_text_29_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
LEAN_EXPORT uint8_t l_Lean_FileMap_rangeIncludesRequestedRange(lean_object* v_text_38_, lean_object* v_documentRange_39_, lean_object* v_requestedRange_40_, uint8_t v_includeDocumentRangeStop_41_, uint8_t v_includeRequestedRangeStop_42_){
_start:
{
if (v_includeDocumentRangeStop_41_ == 0)
{
lean_object* v_stop_43_; lean_object* v_source_44_; lean_object* v___x_45_; uint8_t v_isDocumentRangeAtEOF_46_; uint8_t v___x_47_; 
v_stop_43_ = lean_ctor_get(v_documentRange_39_, 1);
v_source_44_ = lean_ctor_get(v_text_38_, 0);
v___x_45_ = lean_string_utf8_byte_size(v_source_44_);
v_isDocumentRangeAtEOF_46_ = lean_nat_dec_eq(v_stop_43_, v___x_45_);
v___x_47_ = l_Lean_Syntax_Range_includes(v_documentRange_39_, v_requestedRange_40_, v_isDocumentRangeAtEOF_46_, v_includeRequestedRangeStop_42_);
return v___x_47_;
}
else
{
uint8_t v___x_48_; 
v___x_48_ = l_Lean_Syntax_Range_includes(v_documentRange_39_, v_requestedRange_40_, v_includeDocumentRangeStop_41_, v_includeRequestedRangeStop_42_);
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_rangeIncludesRequestedRange___boxed(lean_object* v_text_49_, lean_object* v_documentRange_50_, lean_object* v_requestedRange_51_, lean_object* v_includeDocumentRangeStop_52_, lean_object* v_includeRequestedRangeStop_53_){
_start:
{
uint8_t v_includeDocumentRangeStop_boxed_54_; uint8_t v_includeRequestedRangeStop_boxed_55_; uint8_t v_res_56_; lean_object* v_r_57_; 
v_includeDocumentRangeStop_boxed_54_ = lean_unbox(v_includeDocumentRangeStop_52_);
v_includeRequestedRangeStop_boxed_55_ = lean_unbox(v_includeRequestedRangeStop_53_);
v_res_56_ = l_Lean_FileMap_rangeIncludesRequestedRange(v_text_49_, v_documentRange_50_, v_requestedRange_51_, v_includeDocumentRangeStop_boxed_54_, v_includeRequestedRangeStop_boxed_55_);
lean_dec_ref(v_requestedRange_51_);
lean_dec_ref(v_documentRange_50_);
lean_dec_ref(v_text_49_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorIdx(lean_object* v_x_58_){
_start:
{
if (lean_obj_tag(v_x_58_) == 0)
{
lean_object* v___x_59_; 
v___x_59_ = lean_unsigned_to_nat(0u);
return v___x_59_;
}
else
{
lean_object* v___x_60_; 
v___x_60_ = lean_unsigned_to_nat(1u);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorIdx___boxed(lean_object* v_x_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorIdx(v_x_61_);
lean_dec(v_x_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(lean_object* v_t_63_, lean_object* v_k_64_){
_start:
{
if (lean_obj_tag(v_t_63_) == 0)
{
return v_k_64_;
}
else
{
uint8_t v_foldChildren_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v_foldChildren_65_ = lean_ctor_get_uint8(v_t_63_, 0);
v___x_66_ = lean_box(v_foldChildren_65_);
v___x_67_ = lean_apply_1(v_k_64_, v___x_66_);
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg___boxed(lean_object* v_t_68_, lean_object* v_k_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_68_, v_k_69_);
lean_dec(v_t_68_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim(lean_object* v_motive_71_, lean_object* v_ctorIdx_72_, lean_object* v_t_73_, lean_object* v_h_74_, lean_object* v_k_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_73_, v_k_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___boxed(lean_object* v_motive_77_, lean_object* v_ctorIdx_78_, lean_object* v_t_79_, lean_object* v_h_80_, lean_object* v_k_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim(v_motive_77_, v_ctorIdx_78_, v_t_79_, v_h_80_, v_k_81_);
lean_dec(v_t_79_);
lean_dec(v_ctorIdx_78_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___redArg(lean_object* v_t_83_, lean_object* v_done_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_83_, v_done_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___redArg___boxed(lean_object* v_t_86_, lean_object* v_done_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___redArg(v_t_86_, v_done_87_);
lean_dec(v_t_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim(lean_object* v_motive_89_, lean_object* v_t_90_, lean_object* v_h_91_, lean_object* v_done_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_90_, v_done_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___boxed(lean_object* v_motive_94_, lean_object* v_t_95_, lean_object* v_h_96_, lean_object* v_done_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim(v_motive_94_, v_t_95_, v_h_96_, v_done_97_);
lean_dec(v_t_95_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___redArg(lean_object* v_t_99_, lean_object* v_proceed_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_99_, v_proceed_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___redArg___boxed(lean_object* v_t_102_, lean_object* v_proceed_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___redArg(v_t_102_, v_proceed_103_);
lean_dec(v_t_102_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim(lean_object* v_motive_105_, lean_object* v_t_106_, lean_object* v_h_107_, lean_object* v_proceed_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_106_, v_proceed_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___boxed(lean_object* v_motive_110_, lean_object* v_t_111_, lean_object* v_h_112_, lean_object* v_proceed_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim(v_motive_110_, v_t_111_, v_h_112_, v_proceed_113_);
lean_dec(v_t_111_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__0(lean_object* v_f_115_, lean_object* v_tail_116_, lean_object* v_x_117_){
_start:
{
lean_object* v_snd_118_; uint8_t v___x_119_; 
v_snd_118_ = lean_ctor_get(v_x_117_, 1);
v___x_119_ = lean_unbox(v_snd_118_);
if (v___x_119_ == 0)
{
lean_object* v_fst_120_; lean_object* v___x_121_; 
v_fst_120_ = lean_ctor_get(v_x_117_, 0);
lean_inc(v_fst_120_);
lean_dec_ref(v_x_117_);
v___x_121_ = l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(v_f_115_, v_fst_120_, v_tail_116_);
return v___x_121_;
}
else
{
lean_object* v___x_122_; 
lean_dec(v_tail_116_);
lean_dec_ref(v_f_115_);
v___x_122_ = lean_task_pure(v_x_117_);
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__2(lean_object* v_f_123_, lean_object* v_tail_124_, lean_object* v_head_125_, lean_object* v___f_126_, lean_object* v_x_127_){
_start:
{
lean_object* v_snd_128_; 
v_snd_128_ = lean_ctor_get(v_x_127_, 1);
if (lean_obj_tag(v_snd_128_) == 1)
{
uint8_t v_foldChildren_129_; 
v_foldChildren_129_ = lean_ctor_get_uint8(v_snd_128_, 0);
if (v_foldChildren_129_ == 0)
{
lean_object* v_fst_130_; lean_object* v___x_131_; 
lean_dec_ref(v___f_126_);
lean_dec_ref(v_head_125_);
v_fst_130_ = lean_ctor_get(v_x_127_, 0);
lean_inc(v_fst_130_);
lean_dec_ref(v_x_127_);
v___x_131_ = l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(v_f_123_, v_fst_130_, v_tail_124_);
return v___x_131_;
}
else
{
lean_object* v_fst_132_; lean_object* v_task_133_; lean_object* v___f_134_; lean_object* v_subtreeTask_135_; lean_object* v___x_136_; 
lean_dec(v_tail_124_);
v_fst_132_ = lean_ctor_get(v_x_127_, 0);
lean_inc(v_fst_132_);
lean_dec_ref(v_x_127_);
v_task_133_ = lean_ctor_get(v_head_125_, 3);
lean_inc_ref(v_task_133_);
lean_dec_ref(v_head_125_);
v___f_134_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_134_, 0, v_f_123_);
lean_closure_set(v___f_134_, 1, v_fst_132_);
v_subtreeTask_135_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_task_133_, v___f_134_);
v___x_136_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_subtreeTask_135_, v___f_126_);
return v___x_136_;
}
}
else
{
lean_object* v_fst_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_147_; 
lean_dec_ref(v___f_126_);
lean_dec_ref(v_head_125_);
lean_dec(v_tail_124_);
lean_dec_ref(v_f_123_);
v_fst_137_ = lean_ctor_get(v_x_127_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v_x_127_);
if (v_isSharedCheck_147_ == 0)
{
lean_object* v_unused_148_; 
v_unused_148_ = lean_ctor_get(v_x_127_, 1);
lean_dec(v_unused_148_);
v___x_139_ = v_x_127_;
v_isShared_140_ = v_isSharedCheck_147_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_fst_137_);
lean_dec(v_x_127_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_147_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_141_ = 1;
v___x_142_ = lean_box(v___x_141_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 1, v___x_142_);
v___x_144_ = v___x_139_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_fst_137_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v___x_142_);
v___x_144_ = v_reuseFailAlloc_146_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v___x_145_; 
v___x_145_ = lean_task_pure(v___x_144_);
return v___x_145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(lean_object* v_f_149_, lean_object* v_acc_150_, lean_object* v_a_151_){
_start:
{
if (lean_obj_tag(v_a_151_) == 0)
{
uint8_t v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec_ref(v_f_149_);
v___x_152_ = 0;
v___x_153_ = lean_box(v___x_152_);
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v_acc_150_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
v___x_155_ = lean_task_pure(v___x_154_);
return v___x_155_;
}
else
{
lean_object* v_head_156_; lean_object* v_tail_157_; lean_object* v___f_158_; lean_object* v___f_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_head_156_ = lean_ctor_get(v_a_151_, 0);
lean_inc_n(v_head_156_, 2);
v_tail_157_ = lean_ctor_get(v_a_151_, 1);
lean_inc_n(v_tail_157_, 2);
lean_dec_ref_known(v_a_151_, 2);
lean_inc_ref_n(v_f_149_, 2);
v___f_158_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_158_, 0, v_f_149_);
lean_closure_set(v___f_158_, 1, v_tail_157_);
v___f_159_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__2), 5, 4);
lean_closure_set(v___f_159_, 0, v_f_149_);
lean_closure_set(v___f_159_, 1, v_tail_157_);
lean_closure_set(v___f_159_, 2, v_head_156_);
lean_closure_set(v___f_159_, 3, v___f_158_);
v___x_160_ = lean_apply_2(v_f_149_, v_head_156_, v_acc_150_);
v___x_161_ = l_Lean_Server_ServerTask_bindCheap___redArg(v___x_160_, v___f_159_);
return v___x_161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree___redArg(lean_object* v_f_162_, lean_object* v_acc_163_, lean_object* v_tree_164_){
_start:
{
lean_object* v_children_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v_children_165_ = lean_ctor_get(v_tree_164_, 1);
lean_inc_ref(v_children_165_);
lean_dec_ref(v_tree_164_);
v___x_166_ = lean_array_to_list(v_children_165_);
v___x_167_ = l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(v_f_162_, v_acc_163_, v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__1(lean_object* v_f_168_, lean_object* v_fst_169_, lean_object* v_tree_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree___redArg(v_f_168_, v_fst_169_, v_tree_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree(lean_object* v_00_u03b1_172_, lean_object* v_f_173_, lean_object* v_acc_174_, lean_object* v_tree_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree___redArg(v_f_173_, v_acc_174_, v_tree_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren(lean_object* v_00_u03b1_177_, lean_object* v_f_178_, lean_object* v_acc_179_, lean_object* v_a_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(v_f_178_, v_acc_179_, v_a_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0(lean_object* v_x_182_){
_start:
{
lean_object* v_fst_183_; 
v_fst_183_ = lean_ctor_get(v_x_182_, 0);
lean_inc(v_fst_183_);
return v_fst_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0___boxed(lean_object* v_x_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0(v_x_184_);
lean_dec_ref(v_x_184_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg(lean_object* v_tree_187_, lean_object* v_init_188_, lean_object* v_f_189_){
_start:
{
lean_object* v___f_190_; lean_object* v_t_191_; lean_object* v___x_192_; 
v___f_190_ = ((lean_object*)(l_Lean_Language_SnapshotTree_foldSnaps___redArg___closed__0));
v_t_191_ = l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree___redArg(v_f_189_, v_init_188_, v_tree_187_);
v___x_192_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_190_, v_t_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps(lean_object* v_00_u03b1_193_, lean_object* v_tree_194_, lean_object* v_init_195_, lean_object* v_f_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_Language_SnapshotTree_foldSnaps___redArg(v_tree_194_, v_init_195_, v_f_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0(uint8_t v___x_198_, lean_object* v___x_199_, lean_object* v_tree_200_){
_start:
{
lean_object* v_element_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_214_; 
v_element_201_ = lean_ctor_get(v_tree_200_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v_tree_200_);
if (v_isSharedCheck_214_ == 0)
{
lean_object* v_unused_215_; 
v_unused_215_ = lean_ctor_get(v_tree_200_, 1);
lean_dec(v_unused_215_);
v___x_203_ = v_tree_200_;
v_isShared_204_ = v_isSharedCheck_214_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_element_201_);
lean_dec(v_tree_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_214_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v_infoTree_x3f_205_; 
v_infoTree_x3f_205_ = lean_ctor_get(v_element_201_, 2);
lean_inc(v_infoTree_x3f_205_);
lean_dec_ref(v_element_201_);
if (lean_obj_tag(v_infoTree_x3f_205_) == 1)
{
lean_object* v___x_206_; lean_object* v___x_208_; 
lean_dec(v___x_199_);
v___x_206_ = lean_box(0);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 1, v___x_206_);
lean_ctor_set(v___x_203_, 0, v_infoTree_x3f_205_);
v___x_208_ = v___x_203_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_infoTree_x3f_205_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v___x_206_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
else
{
lean_object* v___x_210_; lean_object* v___x_212_; 
lean_dec(v_infoTree_x3f_205_);
v___x_210_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_210_, 0, v___x_198_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 1, v___x_210_);
lean_ctor_set(v___x_203_, 0, v___x_199_);
v___x_212_ = v___x_203_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v___x_210_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0___boxed(lean_object* v___x_216_, lean_object* v___x_217_, lean_object* v_tree_218_){
_start:
{
uint8_t v___x_469__boxed_219_; lean_object* v_res_220_; 
v___x_469__boxed_219_ = lean_unbox(v___x_216_);
v_res_220_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0(v___x_469__boxed_219_, v___x_217_, v_tree_218_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1(lean_object* v_text_225_, lean_object* v_hoverPos_226_, uint8_t v_includeStop_227_, lean_object* v___x_228_, lean_object* v_snap_229_, lean_object* v_x_230_){
_start:
{
lean_object* v_stx_x3f_231_; 
v_stx_x3f_231_ = lean_ctor_get(v_snap_229_, 0);
lean_inc(v_stx_x3f_231_);
if (lean_obj_tag(v_stx_x3f_231_) == 1)
{
lean_object* v_task_232_; lean_object* v_val_233_; uint8_t v___x_234_; lean_object* v___x_235_; 
v_task_232_ = lean_ctor_get(v_snap_229_, 3);
lean_inc_ref(v_task_232_);
lean_dec_ref(v_snap_229_);
v_val_233_ = lean_ctor_get(v_stx_x3f_231_, 0);
lean_inc(v_val_233_);
lean_dec_ref_known(v_stx_x3f_231_, 1);
v___x_234_ = 1;
v___x_235_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_val_233_, v___x_234_);
lean_dec(v_val_233_);
if (lean_obj_tag(v___x_235_) == 1)
{
lean_object* v_val_236_; uint8_t v___x_237_; 
v_val_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_val_236_);
lean_dec_ref_known(v___x_235_, 1);
v___x_237_ = l_Lean_FileMap_rangeContainsHoverPos(v_text_225_, v_val_236_, v_hoverPos_226_, v_includeStop_227_);
lean_dec(v_val_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
lean_dec_ref(v_task_232_);
v___x_238_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_238_, 0, v___x_237_);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_228_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
v___x_240_ = lean_task_pure(v___x_239_);
return v___x_240_;
}
else
{
lean_object* v___x_241_; lean_object* v___f_242_; lean_object* v___x_243_; 
v___x_241_ = lean_box(v___x_237_);
v___f_242_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0___boxed), 3, 2);
lean_closure_set(v___f_242_, 0, v___x_241_);
lean_closure_set(v___f_242_, 1, v___x_228_);
v___x_243_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_242_, v_task_232_);
return v___x_243_;
}
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
lean_dec(v___x_235_);
lean_dec_ref(v_task_232_);
v___x_244_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0));
v___x_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_228_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
v___x_246_ = lean_task_pure(v___x_245_);
return v___x_246_;
}
}
else
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
lean_dec(v_stx_x3f_231_);
lean_dec_ref(v_snap_229_);
v___x_247_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1));
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_228_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = lean_task_pure(v___x_248_);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___boxed(lean_object* v_text_250_, lean_object* v_hoverPos_251_, lean_object* v_includeStop_252_, lean_object* v___x_253_, lean_object* v_snap_254_, lean_object* v_x_255_){
_start:
{
uint8_t v_includeStop_boxed_256_; lean_object* v_res_257_; 
v_includeStop_boxed_256_ = lean_unbox(v_includeStop_252_);
v_res_257_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1(v_text_250_, v_hoverPos_251_, v_includeStop_boxed_256_, v___x_253_, v_snap_254_, v_x_255_);
lean_dec(v_x_255_);
lean_dec(v_hoverPos_251_);
lean_dec_ref(v_text_250_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos(lean_object* v_text_258_, lean_object* v_tree_259_, lean_object* v_hoverPos_260_, uint8_t v_includeStop_261_){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___f_264_; lean_object* v___x_265_; 
v___x_262_ = lean_box(0);
v___x_263_ = lean_box(v_includeStop_261_);
v___f_264_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___boxed), 6, 4);
lean_closure_set(v___f_264_, 0, v_text_258_);
lean_closure_set(v___f_264_, 1, v_hoverPos_260_);
lean_closure_set(v___f_264_, 2, v___x_263_);
lean_closure_set(v___f_264_, 3, v___x_262_);
v___x_265_ = l_Lean_Language_SnapshotTree_foldSnaps___redArg(v_tree_259_, v___x_262_, v___f_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___boxed(lean_object* v_text_266_, lean_object* v_tree_267_, lean_object* v_hoverPos_268_, lean_object* v_includeStop_269_){
_start:
{
uint8_t v_includeStop_boxed_270_; lean_object* v_res_271_; 
v_includeStop_boxed_270_ = lean_unbox(v_includeStop_269_);
v_res_271_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos(v_text_266_, v_tree_267_, v_hoverPos_268_, v_includeStop_boxed_270_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0(lean_object* v_requestedRange_272_, uint8_t v___x_273_, lean_object* v_f_274_, lean_object* v_ctx_275_, lean_object* v_i_276_, lean_object* v_acc_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_Elab_Info_range_x3f(v_i_276_);
if (lean_obj_tag(v___x_278_) == 1)
{
lean_object* v_val_279_; uint8_t v___x_280_; 
v_val_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_val_279_);
lean_dec_ref_known(v___x_278_, 1);
v___x_280_ = l_Lean_Syntax_Range_overlaps(v_val_279_, v_requestedRange_272_, v___x_273_, v___x_273_);
lean_dec(v_val_279_);
if (v___x_280_ == 0)
{
lean_dec_ref(v_i_276_);
lean_dec_ref(v_ctx_275_);
lean_dec(v_f_274_);
return v_acc_277_;
}
else
{
lean_object* v___x_281_; 
v___x_281_ = lean_apply_3(v_f_274_, v_ctx_275_, v_i_276_, v_acc_277_);
return v___x_281_;
}
}
else
{
lean_dec(v___x_278_);
lean_dec_ref(v_i_276_);
lean_dec_ref(v_ctx_275_);
lean_dec(v_f_274_);
return v_acc_277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0___boxed(lean_object* v_requestedRange_282_, lean_object* v___x_283_, lean_object* v_f_284_, lean_object* v_ctx_285_, lean_object* v_i_286_, lean_object* v_acc_287_){
_start:
{
uint8_t v___x_631__boxed_288_; lean_object* v_res_289_; 
v___x_631__boxed_288_ = lean_unbox(v___x_283_);
v_res_289_ = l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0(v_requestedRange_282_, v___x_631__boxed_288_, v_f_284_, v_ctx_285_, v_i_286_, v_acc_287_);
lean_dec_ref(v_requestedRange_282_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1(lean_object* v___f_290_, lean_object* v_acc_291_, uint8_t v___x_292_, lean_object* v_tree_293_){
_start:
{
lean_object* v_element_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_309_; 
v_element_294_ = lean_ctor_get(v_tree_293_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v_tree_293_);
if (v_isSharedCheck_309_ == 0)
{
lean_object* v_unused_310_; 
v_unused_310_ = lean_ctor_get(v_tree_293_, 1);
lean_dec(v_unused_310_);
v___x_296_ = v_tree_293_;
v_isShared_297_ = v_isSharedCheck_309_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_element_294_);
lean_dec(v_tree_293_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_309_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v_infoTree_x3f_298_; 
v_infoTree_x3f_298_ = lean_ctor_get(v_element_294_, 2);
lean_inc(v_infoTree_x3f_298_);
lean_dec_ref(v_element_294_);
if (lean_obj_tag(v_infoTree_x3f_298_) == 1)
{
lean_object* v_val_299_; lean_object* v_acc_300_; lean_object* v___x_301_; lean_object* v___x_303_; 
v_val_299_ = lean_ctor_get(v_infoTree_x3f_298_, 0);
lean_inc(v_val_299_);
lean_dec_ref_known(v_infoTree_x3f_298_, 1);
v_acc_300_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_290_, v_acc_291_, v_val_299_);
v___x_301_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_301_, 0, v___x_292_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 1, v___x_301_);
lean_ctor_set(v___x_296_, 0, v_acc_300_);
v___x_303_ = v___x_296_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_acc_300_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v___x_301_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
else
{
lean_object* v___x_305_; lean_object* v___x_307_; 
lean_dec(v_infoTree_x3f_298_);
lean_dec(v___f_290_);
v___x_305_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_305_, 0, v___x_292_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 1, v___x_305_);
lean_ctor_set(v___x_296_, 0, v_acc_291_);
v___x_307_ = v___x_296_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_acc_291_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1___boxed(lean_object* v___f_311_, lean_object* v_acc_312_, lean_object* v___x_313_, lean_object* v_tree_314_){
_start:
{
uint8_t v___x_643__boxed_315_; lean_object* v_res_316_; 
v___x_643__boxed_315_ = lean_unbox(v___x_313_);
v_res_316_ = l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1(v___f_311_, v_acc_312_, v___x_643__boxed_315_, v_tree_314_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__2(lean_object* v_requestedRange_317_, lean_object* v_f_318_, lean_object* v_snap_319_, lean_object* v_acc_320_){
_start:
{
lean_object* v_stx_x3f_321_; 
v_stx_x3f_321_ = lean_ctor_get(v_snap_319_, 0);
lean_inc(v_stx_x3f_321_);
if (lean_obj_tag(v_stx_x3f_321_) == 1)
{
lean_object* v_task_322_; lean_object* v_val_323_; uint8_t v___x_324_; lean_object* v___x_325_; 
v_task_322_ = lean_ctor_get(v_snap_319_, 3);
lean_inc_ref(v_task_322_);
lean_dec_ref(v_snap_319_);
v_val_323_ = lean_ctor_get(v_stx_x3f_321_, 0);
lean_inc(v_val_323_);
lean_dec_ref_known(v_stx_x3f_321_, 1);
v___x_324_ = 1;
v___x_325_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_val_323_, v___x_324_);
lean_dec(v_val_323_);
if (lean_obj_tag(v___x_325_) == 1)
{
lean_object* v_val_326_; uint8_t v___x_327_; 
v_val_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_val_326_);
lean_dec_ref_known(v___x_325_, 1);
v___x_327_ = l_Lean_Syntax_Range_overlaps(v_val_326_, v_requestedRange_317_, v___x_324_, v___x_324_);
lean_dec(v_val_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
lean_dec_ref(v_task_322_);
lean_dec(v_f_318_);
lean_dec_ref(v_requestedRange_317_);
v___x_328_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_328_, 0, v___x_327_);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v_acc_320_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = lean_task_pure(v___x_329_);
return v___x_330_;
}
else
{
lean_object* v___x_331_; lean_object* v___f_332_; lean_object* v___x_333_; lean_object* v___f_334_; lean_object* v___x_335_; 
v___x_331_ = lean_box(v___x_324_);
v___f_332_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_332_, 0, v_requestedRange_317_);
lean_closure_set(v___f_332_, 1, v___x_331_);
lean_closure_set(v___f_332_, 2, v_f_318_);
v___x_333_ = lean_box(v___x_324_);
v___f_334_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_334_, 0, v___f_332_);
lean_closure_set(v___f_334_, 1, v_acc_320_);
lean_closure_set(v___f_334_, 2, v___x_333_);
v___x_335_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_334_, v_task_322_);
return v___x_335_;
}
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec(v___x_325_);
lean_dec_ref(v_task_322_);
lean_dec(v_f_318_);
lean_dec_ref(v_requestedRange_317_);
v___x_336_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0));
v___x_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_337_, 0, v_acc_320_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = lean_task_pure(v___x_337_);
return v___x_338_;
}
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
lean_dec(v_stx_x3f_321_);
lean_dec_ref(v_snap_319_);
lean_dec(v_f_318_);
lean_dec_ref(v_requestedRange_317_);
v___x_339_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1));
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v_acc_320_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
v___x_341_ = lean_task_pure(v___x_340_);
return v___x_341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg(lean_object* v_tree_342_, lean_object* v_requestedRange_343_, lean_object* v_init_344_, lean_object* v_f_345_){
_start:
{
lean_object* v___f_346_; lean_object* v___x_347_; 
v___f_346_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__2), 4, 2);
lean_closure_set(v___f_346_, 0, v_requestedRange_343_);
lean_closure_set(v___f_346_, 1, v_f_345_);
v___x_347_ = l_Lean_Language_SnapshotTree_foldSnaps___redArg(v_tree_342_, v_init_344_, v___f_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange(lean_object* v_00_u03b1_348_, lean_object* v_tree_349_, lean_object* v_requestedRange_350_, lean_object* v_init_351_, lean_object* v_f_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_Language_SnapshotTree_foldInfosInRange___redArg(v_tree_349_, v_requestedRange_350_, v_init_351_, v_f_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0(lean_object* v_log_354_, uint8_t v___x_355_, lean_object* v_tree_356_){
_start:
{
lean_object* v_element_357_; lean_object* v_diagnostics_358_; lean_object* v_msgLog_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_368_; 
v_element_357_ = lean_ctor_get(v_tree_356_, 0);
lean_inc_ref(v_element_357_);
lean_dec_ref(v_tree_356_);
v_diagnostics_358_ = lean_ctor_get(v_element_357_, 1);
lean_inc_ref(v_diagnostics_358_);
lean_dec_ref(v_element_357_);
v_msgLog_359_ = lean_ctor_get(v_diagnostics_358_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v_diagnostics_358_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; 
v_unused_369_ = lean_ctor_get(v_diagnostics_358_, 1);
lean_dec(v_unused_369_);
v___x_361_ = v_diagnostics_358_;
v_isShared_362_ = v_isSharedCheck_368_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_msgLog_359_);
lean_dec(v_diagnostics_358_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_368_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_363_ = l_Lean_MessageLog_append(v_log_354_, v_msgLog_359_);
v___x_364_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_364_, 0, v___x_355_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 1, v___x_364_);
lean_ctor_set(v___x_361_, 0, v___x_363_);
v___x_366_ = v___x_361_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v___x_364_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0___boxed(lean_object* v_log_370_, lean_object* v___x_371_, lean_object* v_tree_372_){
_start:
{
uint8_t v___x_422__boxed_373_; lean_object* v_res_374_; 
v___x_422__boxed_373_ = lean_unbox(v___x_371_);
v_res_374_ = l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0(v_log_370_, v___x_422__boxed_373_, v_tree_372_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1(lean_object* v_requestedRange_375_, lean_object* v_snap_376_, lean_object* v_log_377_){
_start:
{
lean_object* v_stx_x3f_378_; 
v_stx_x3f_378_ = lean_ctor_get(v_snap_376_, 0);
lean_inc(v_stx_x3f_378_);
if (lean_obj_tag(v_stx_x3f_378_) == 1)
{
lean_object* v_task_379_; lean_object* v_val_380_; uint8_t v___x_381_; lean_object* v___x_382_; 
v_task_379_ = lean_ctor_get(v_snap_376_, 3);
lean_inc_ref(v_task_379_);
lean_dec_ref(v_snap_376_);
v_val_380_ = lean_ctor_get(v_stx_x3f_378_, 0);
lean_inc(v_val_380_);
lean_dec_ref_known(v_stx_x3f_378_, 1);
v___x_381_ = 1;
v___x_382_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_val_380_, v___x_381_);
lean_dec(v_val_380_);
if (lean_obj_tag(v___x_382_) == 1)
{
lean_object* v_val_383_; uint8_t v___x_384_; 
v_val_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_val_383_);
lean_dec_ref_known(v___x_382_, 1);
v___x_384_ = l_Lean_Syntax_Range_overlaps(v_val_383_, v_requestedRange_375_, v___x_381_, v___x_381_);
lean_dec(v_val_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
lean_dec_ref(v_task_379_);
v___x_385_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_385_, 0, v___x_384_);
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v_log_377_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = lean_task_pure(v___x_386_);
return v___x_387_;
}
else
{
lean_object* v___x_388_; lean_object* v___f_389_; lean_object* v___x_390_; 
v___x_388_ = lean_box(v___x_381_);
v___f_389_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0___boxed), 3, 2);
lean_closure_set(v___f_389_, 0, v_log_377_);
lean_closure_set(v___f_389_, 1, v___x_388_);
v___x_390_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_389_, v_task_379_);
return v___x_390_;
}
}
else
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
lean_dec(v___x_382_);
lean_dec_ref(v_task_379_);
v___x_391_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0));
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v_log_377_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = lean_task_pure(v___x_392_);
return v___x_393_;
}
}
else
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
lean_dec(v_stx_x3f_378_);
lean_dec_ref(v_snap_376_);
v___x_394_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0));
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v_log_377_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
v___x_396_ = lean_task_pure(v___x_395_);
return v___x_396_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1___boxed(lean_object* v_requestedRange_397_, lean_object* v_snap_398_, lean_object* v_log_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1(v_requestedRange_397_, v_snap_398_, v_log_399_);
lean_dec_ref(v_requestedRange_397_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange(lean_object* v_tree_401_, lean_object* v_requestedRange_402_){
_start:
{
lean_object* v___f_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___f_403_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1___boxed), 3, 1);
lean_closure_set(v___f_403_, 0, v_requestedRange_402_);
v___x_404_ = l_Lean_MessageLog_empty;
v___x_405_ = l_Lean_Language_SnapshotTree_foldSnaps___redArg(v_tree_401_, v___x_404_, v___f_403_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_methodNotFound(lean_object* v_method_419_){
_start:
{
uint8_t v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_420_ = 2;
v___x_421_ = ((lean_object*)(l_Lean_Server_RequestError_methodNotFound___closed__0));
v___x_422_ = lean_string_append(v___x_421_, v_method_419_);
v___x_423_ = ((lean_object*)(l_Lean_Server_RequestError_methodNotFound___closed__1));
v___x_424_ = lean_string_append(v___x_422_, v___x_423_);
v___x_425_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set_uint8(v___x_425_, sizeof(void*)*1, v___x_420_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_methodNotFound___boxed(lean_object* v_method_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_Server_RequestError_methodNotFound(v_method_426_);
lean_dec_ref(v_method_426_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_invalidParams(lean_object* v_message_428_){
_start:
{
uint8_t v___x_429_; lean_object* v___x_430_; 
v___x_429_ = 3;
v___x_430_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_430_, 0, v_message_428_);
lean_ctor_set_uint8(v___x_430_, sizeof(void*)*1, v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_internalError(lean_object* v_message_431_){
_start:
{
uint8_t v___x_432_; lean_object* v___x_433_; 
v___x_432_ = 4;
v___x_433_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_433_, 0, v_message_431_);
lean_ctor_set_uint8(v___x_433_, sizeof(void*)*1, v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_ofException(lean_object* v_e_443_){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_445_ = l_Lean_Exception_toMessageData(v_e_443_);
v___x_446_ = l_Lean_MessageData_toString(v___x_445_);
v___x_447_ = l_Lean_Server_RequestError_internalError(v___x_446_);
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_ofException___boxed(lean_object* v_e_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_Server_RequestError_ofException(v_e_449_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_ofIoError(lean_object* v_e_452_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_io_error_to_string(v_e_452_);
v___x_454_ = l_Lean_Server_RequestError_internalError(v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_toLspResponseError(lean_object* v_id_455_, lean_object* v_e_456_){
_start:
{
uint8_t v_code_457_; lean_object* v_message_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v_code_457_ = lean_ctor_get_uint8(v_e_456_, sizeof(void*)*1);
v_message_458_ = lean_ctor_get(v_e_456_, 0);
v___x_459_ = lean_box(0);
lean_inc_ref(v_message_458_);
v___x_460_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_460_, 0, v_id_455_);
lean_ctor_set(v___x_460_, 1, v_message_458_);
lean_ctor_set(v___x_460_, 2, v___x_459_);
lean_ctor_set_uint8(v___x_460_, sizeof(void*)*3, v_code_457_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_toLspResponseError___boxed(lean_object* v_id_461_, lean_object* v_e_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Server_RequestError_toLspResponseError(v_id_461_, v_e_462_);
lean_dec_ref(v_e_462_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___redArg(lean_object* v_inst_466_, lean_object* v_params_467_){
_start:
{
lean_object* v___x_468_; 
lean_inc(v_params_467_);
v___x_468_ = lean_apply_1(v_inst_466_, v_params_467_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_484_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_484_ == 0)
{
v___x_471_ = v___x_468_;
v_isShared_472_ = v_isSharedCheck_484_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_484_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
uint8_t v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_482_; 
v___x_473_ = 3;
v___x_474_ = ((lean_object*)(l_Lean_Server_parseRequestParams___redArg___closed__0));
v___x_475_ = l_Lean_Json_compress(v_params_467_);
v___x_476_ = lean_string_append(v___x_474_, v___x_475_);
lean_dec_ref(v___x_475_);
v___x_477_ = ((lean_object*)(l_Lean_Server_parseRequestParams___redArg___closed__1));
v___x_478_ = lean_string_append(v___x_476_, v___x_477_);
v___x_479_ = lean_string_append(v___x_478_, v_a_469_);
lean_dec(v_a_469_);
v___x_480_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_480_, 0, v___x_479_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*1, v___x_473_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_480_);
v___x_482_ = v___x_471_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_dec(v_params_467_);
v_a_485_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_468_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_468_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams(lean_object* v_paramType_493_, lean_object* v_inst_494_, lean_object* v_params_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_Server_parseRequestParams___redArg(v_inst_494_, v_params_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___redArg(lean_object* v_x_497_){
_start:
{
if (lean_obj_tag(v_x_497_) == 0)
{
lean_object* v___x_498_; 
v___x_498_ = lean_unsigned_to_nat(0u);
return v___x_498_;
}
else
{
lean_object* v___x_499_; 
v___x_499_ = lean_unsigned_to_nat(1u);
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___redArg___boxed(lean_object* v_x_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Server_ServerRequestResponse_ctorIdx___redArg(v_x_500_);
lean_dec_ref(v_x_500_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx(lean_object* v_00_u03b1_502_, lean_object* v_x_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_Server_ServerRequestResponse_ctorIdx___redArg(v_x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___boxed(lean_object* v_00_u03b1_505_, lean_object* v_x_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_Server_ServerRequestResponse_ctorIdx(v_00_u03b1_505_, v_x_506_);
lean_dec_ref(v_x_506_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorElim___redArg(lean_object* v_t_508_, lean_object* v_k_509_){
_start:
{
if (lean_obj_tag(v_t_508_) == 0)
{
lean_object* v_response_510_; lean_object* v___x_511_; 
v_response_510_ = lean_ctor_get(v_t_508_, 0);
lean_inc(v_response_510_);
lean_dec_ref_known(v_t_508_, 1);
v___x_511_ = lean_apply_1(v_k_509_, v_response_510_);
return v___x_511_;
}
else
{
uint8_t v_code_512_; lean_object* v_message_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v_code_512_ = lean_ctor_get_uint8(v_t_508_, sizeof(void*)*1);
v_message_513_ = lean_ctor_get(v_t_508_, 0);
lean_inc_ref(v_message_513_);
lean_dec_ref_known(v_t_508_, 1);
v___x_514_ = lean_box(v_code_512_);
v___x_515_ = lean_apply_2(v_k_509_, v___x_514_, v_message_513_);
return v___x_515_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorElim(lean_object* v_00_u03b1_516_, lean_object* v_motive_517_, lean_object* v_ctorIdx_518_, lean_object* v_t_519_, lean_object* v_h_520_, lean_object* v_k_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_519_, v_k_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorElim___boxed(lean_object* v_00_u03b1_523_, lean_object* v_motive_524_, lean_object* v_ctorIdx_525_, lean_object* v_t_526_, lean_object* v_h_527_, lean_object* v_k_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_Server_ServerRequestResponse_ctorElim(v_00_u03b1_523_, v_motive_524_, v_ctorIdx_525_, v_t_526_, v_h_527_, v_k_528_);
lean_dec(v_ctorIdx_525_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_success_elim___redArg(lean_object* v_t_530_, lean_object* v_success_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_530_, v_success_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_success_elim(lean_object* v_00_u03b1_533_, lean_object* v_motive_534_, lean_object* v_t_535_, lean_object* v_h_536_, lean_object* v_success_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_535_, v_success_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_failure_elim___redArg(lean_object* v_t_539_, lean_object* v_failure_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_539_, v_failure_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_failure_elim(lean_object* v_00_u03b1_542_, lean_object* v_motive_543_, lean_object* v_t_544_, lean_object* v_h_545_, lean_object* v_failure_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_544_, v_failure_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse_default(lean_object* v_00_u03b1_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = ((lean_object*)(l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0));
return v___x_552_;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedServerRequestResponse___closed__0(void){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_Server_instInhabitedServerRequestResponse_default(lean_box(0));
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse(lean_object* v_a_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = lean_obj_once(&l_Lean_Server_instInhabitedServerRequestResponse___closed__0, &l_Lean_Server_instInhabitedServerRequestResponse___closed__0_once, _init_l_Lean_Server_instInhabitedServerRequestResponse___closed__0);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run___redArg(lean_object* v_act_556_, lean_object* v_rc_557_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = lean_apply_2(v_act_556_, v_rc_557_, lean_box(0));
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run___redArg___boxed(lean_object* v_act_560_, lean_object* v_rc_561_, lean_object* v_a_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_Server_RequestM_run___redArg(v_act_560_, v_rc_561_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run(lean_object* v_00_u03b1_564_, lean_object* v_act_565_, lean_object* v_rc_566_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = lean_apply_2(v_act_565_, v_rc_566_, lean_box(0));
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run___boxed(lean_object* v_00_u03b1_569_, lean_object* v_act_570_, lean_object* v_rc_571_, lean_object* v_a_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_Server_RequestM_run(v_00_u03b1_569_, v_act_570_, v_rc_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestTask_pure___redArg(lean_object* v_a_574_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_575_, 0, v_a_574_);
v___x_576_ = lean_task_pure(v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestTask_pure(lean_object* v_00_u03b1_577_, lean_object* v_a_578_){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_579_, 0, v_a_578_);
v___x_580_ = lean_task_pure(v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM___lam__0(lean_object* v_00_u03b1_581_, lean_object* v_x_582_, lean_object* v___y_583_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = lean_apply_1(v_x_582_, lean_box(0));
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_585_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_602_; 
v_a_594_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_602_ == 0)
{
v___x_596_ = v___x_585_;
v_isShared_597_ = v_isSharedCheck_602_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_585_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_602_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_598_ = l_Lean_Server_RequestError_ofIoError(v_a_594_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_598_);
v___x_600_ = v___x_596_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM___lam__0___boxed(lean_object* v_00_u03b1_603_, lean_object* v_x_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_Server_instMonadLiftIORequestM___lam__0(v_00_u03b1_603_, v_x_604_, v___y_605_);
lean_dec_ref(v___y_605_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0(lean_object* v_00_u03b1_610_, lean_object* v_x_611_, lean_object* v___y_612_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = lean_apply_1(v_x_611_, lean_box(0));
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_614_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_614_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_624_; lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
v_a_623_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v___x_614_, 1);
v___x_624_ = l_Lean_Server_RequestError_ofException(v_a_623_);
v_a_625_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_624_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_624_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
lean_ctor_set_tag(v___x_627_, 1);
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0___boxed(lean_object* v_00_u03b1_633_, lean_object* v_x_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0(v_00_u03b1_633_, v_x_634_, v___y_635_);
lean_dec_ref(v___y_635_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0(lean_object* v_00_u03b1_640_, lean_object* v_x_641_, lean_object* v___y_642_){
_start:
{
lean_object* v_cancelTk_644_; lean_object* v___x_645_; 
v_cancelTk_644_ = lean_ctor_get(v___y_642_, 4);
lean_inc_ref(v_cancelTk_644_);
v___x_645_ = lean_apply_2(v_x_641_, v_cancelTk_644_, lean_box(0));
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_658_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_658_ == 0)
{
v___x_648_ = v___x_645_;
v_isShared_649_ = v_isSharedCheck_658_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_645_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_658_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
if (lean_obj_tag(v_a_646_) == 0)
{
lean_object* v___x_650_; lean_object* v___x_652_; 
lean_dec_ref_known(v_a_646_, 1);
v___x_650_ = ((lean_object*)(l_Lean_Server_RequestError_requestCancelled));
if (v_isShared_649_ == 0)
{
lean_ctor_set_tag(v___x_648_, 1);
lean_ctor_set(v___x_648_, 0, v___x_650_);
v___x_652_ = v___x_648_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
else
{
lean_object* v_a_654_; lean_object* v___x_656_; 
v_a_654_ = lean_ctor_get(v_a_646_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v_a_646_, 1);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v_a_654_);
v___x_656_ = v___x_648_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
else
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_667_; 
v_a_659_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_667_ == 0)
{
v___x_661_ = v___x_645_;
v_isShared_662_ = v_isSharedCheck_667_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_645_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_667_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v___x_665_; 
v___x_663_ = l_Lean_Server_RequestError_ofIoError(v_a_659_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_663_);
v___x_665_ = v___x_661_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_663_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0___boxed(lean_object* v_00_u03b1_668_, lean_object* v_x_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0(v_00_u03b1_668_, v_x_669_, v___y_670_);
lean_dec_ref(v___y_670_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO___redArg(lean_object* v_x_675_, lean_object* v_ctx_676_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = lean_apply_2(v_x_675_, v_ctx_676_, lean_box(0));
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_678_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_678_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_696_; 
v_a_687_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_696_ == 0)
{
v___x_689_ = v___x_678_;
v_isShared_690_ = v_isSharedCheck_696_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_678_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_696_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v_message_691_; lean_object* v___x_692_; lean_object* v___x_694_; 
v_message_691_ = lean_ctor_get(v_a_687_, 0);
lean_inc_ref(v_message_691_);
lean_dec(v_a_687_);
v___x_692_ = lean_mk_io_user_error(v_message_691_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_692_);
v___x_694_ = v___x_689_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO___redArg___boxed(lean_object* v_x_697_, lean_object* v_ctx_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Server_RequestM_runInIO___redArg(v_x_697_, v_ctx_698_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO(lean_object* v_00_u03b1_701_, lean_object* v_x_702_, lean_object* v_ctx_703_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Lean_Server_RequestM_runInIO___redArg(v_x_702_, v_ctx_703_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO___boxed(lean_object* v_00_u03b1_706_, lean_object* v_x_707_, lean_object* v_ctx_708_, lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_Server_RequestM_runInIO(v_00_u03b1_706_, v_x_707_, v_ctx_708_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___redArg___lam__0(lean_object* v_toPure_711_, lean_object* v_rc_712_){
_start:
{
lean_object* v_doc_713_; lean_object* v___x_714_; 
v_doc_713_ = lean_ctor_get(v_rc_712_, 1);
lean_inc_ref(v_doc_713_);
lean_dec_ref(v_rc_712_);
v___x_714_ = lean_apply_2(v_toPure_711_, lean_box(0), v_doc_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___redArg(lean_object* v_inst_715_, lean_object* v_inst_716_){
_start:
{
lean_object* v_toApplicative_717_; lean_object* v_toBind_718_; lean_object* v_toPure_719_; lean_object* v___f_720_; lean_object* v___x_721_; 
v_toApplicative_717_ = lean_ctor_get(v_inst_715_, 0);
lean_inc_ref(v_toApplicative_717_);
v_toBind_718_ = lean_ctor_get(v_inst_715_, 1);
lean_inc(v_toBind_718_);
lean_dec_ref(v_inst_715_);
v_toPure_719_ = lean_ctor_get(v_toApplicative_717_, 1);
lean_inc(v_toPure_719_);
lean_dec_ref(v_toApplicative_717_);
v___f_720_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_readDoc___redArg___lam__0), 2, 1);
lean_closure_set(v___f_720_, 0, v_toPure_719_);
v___x_721_ = lean_apply_4(v_toBind_718_, lean_box(0), lean_box(0), v_inst_716_, v___f_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc(lean_object* v_m_722_, lean_object* v_inst_723_, lean_object* v_inst_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_Server_RequestM_readDoc___redArg(v_inst_723_, v_inst_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg___lam__0(lean_object* v_t_726_, lean_object* v_a_727_){
_start:
{
lean_object* v___x_729_; 
lean_inc_ref(v_a_727_);
v___x_729_ = lean_apply_2(v_t_726_, v_a_727_, lean_box(0));
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg___lam__0___boxed(lean_object* v_t_730_, lean_object* v_a_731_, lean_object* v___y_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_Server_RequestM_asTask___redArg___lam__0(v_t_730_, v_a_731_);
lean_dec_ref(v_a_731_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg(lean_object* v_t_734_, lean_object* v_a_735_){
_start:
{
lean_object* v___f_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
lean_inc_ref(v_a_735_);
v___f_737_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_asTask___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_737_, 0, v_t_734_);
lean_closure_set(v___f_737_, 1, v_a_735_);
v___x_738_ = l_Lean_Server_ServerTask_EIO_asTask___redArg(v___f_737_);
v___x_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg___boxed(lean_object* v_t_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_Server_RequestM_asTask___redArg(v_t_740_, v_a_741_);
lean_dec_ref(v_a_741_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask(lean_object* v_00_u03b1_744_, lean_object* v_t_745_, lean_object* v_a_746_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Lean_Server_RequestM_asTask___redArg(v_t_745_, v_a_746_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___boxed(lean_object* v_00_u03b1_749_, lean_object* v_t_750_, lean_object* v_a_751_, lean_object* v_a_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_Server_RequestM_asTask(v_00_u03b1_749_, v_t_750_, v_a_751_);
lean_dec_ref(v_a_751_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask___redArg(lean_object* v_t_754_, lean_object* v_a_755_){
_start:
{
lean_object* v___x_757_; 
lean_inc_ref(v_a_755_);
v___x_757_ = lean_apply_2(v_t_754_, v_a_755_, lean_box(0));
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_767_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_767_ == 0)
{
v___x_760_ = v___x_757_;
v_isShared_761_ = v_isSharedCheck_767_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_757_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_767_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_762_, 0, v_a_758_);
v___x_763_ = lean_task_pure(v___x_762_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 0, v___x_763_);
v___x_765_ = v___x_760_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_763_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
v_a_768_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_757_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_757_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask___redArg___boxed(lean_object* v_t_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_Server_RequestM_pureTask___redArg(v_t_776_, v_a_777_);
lean_dec_ref(v_a_777_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask(lean_object* v_00_u03b1_780_, lean_object* v_t_781_, lean_object* v_a_782_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_Server_RequestM_pureTask___redArg(v_t_781_, v_a_782_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask___boxed(lean_object* v_00_u03b1_785_, lean_object* v_t_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_Server_RequestM_pureTask(v_00_u03b1_785_, v_t_786_, v_a_787_);
lean_dec_ref(v_a_787_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0(lean_object* v_f_790_, lean_object* v_a_791_, lean_object* v_x_792_){
_start:
{
lean_object* v___x_794_; 
lean_inc_ref(v_a_791_);
v___x_794_ = lean_apply_3(v_f_790_, v_x_792_, v_a_791_, lean_box(0));
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0___boxed(lean_object* v_f_795_, lean_object* v_a_796_, lean_object* v_x_797_, lean_object* v___y_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0(v_f_795_, v_a_796_, v_x_797_);
lean_dec_ref(v_a_796_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg(lean_object* v_t_800_, lean_object* v_f_801_, lean_object* v_a_802_){
_start:
{
lean_object* v___f_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
lean_inc_ref(v_a_802_);
v___f_804_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_804_, 0, v_f_801_);
lean_closure_set(v___f_804_, 1, v_a_802_);
v___x_805_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(v___f_804_, v_t_800_);
v___x_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg___boxed(lean_object* v_t_807_, lean_object* v_f_808_, lean_object* v_a_809_, lean_object* v_a_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_t_807_, v_f_808_, v_a_809_);
lean_dec_ref(v_a_809_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap(lean_object* v_00_u03b1_812_, lean_object* v_00_u03b2_813_, lean_object* v_t_814_, lean_object* v_f_815_, lean_object* v_a_816_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_t_814_, v_f_815_, v_a_816_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___boxed(lean_object* v_00_u03b1_819_, lean_object* v_00_u03b2_820_, lean_object* v_t_821_, lean_object* v_f_822_, lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lean_Server_RequestM_mapTaskCheap(v_00_u03b1_819_, v_00_u03b2_820_, v_t_821_, v_f_822_, v_a_823_);
lean_dec_ref(v_a_823_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly___redArg(lean_object* v_t_826_, lean_object* v_f_827_, lean_object* v_a_828_){
_start:
{
lean_object* v___f_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
lean_inc_ref(v_a_828_);
v___f_830_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_830_, 0, v_f_827_);
lean_closure_set(v___f_830_, 1, v_a_828_);
v___x_831_ = l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(v___f_830_, v_t_826_);
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly___redArg___boxed(lean_object* v_t_833_, lean_object* v_f_834_, lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_t_833_, v_f_834_, v_a_835_);
lean_dec_ref(v_a_835_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly(lean_object* v_00_u03b1_838_, lean_object* v_00_u03b2_839_, lean_object* v_t_840_, lean_object* v_f_841_, lean_object* v_a_842_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_t_840_, v_f_841_, v_a_842_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly___boxed(lean_object* v_00_u03b1_845_, lean_object* v_00_u03b2_846_, lean_object* v_t_847_, lean_object* v_f_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_Server_RequestM_mapTaskCostly(v_00_u03b1_845_, v_00_u03b2_846_, v_t_847_, v_f_848_, v_a_849_);
lean_dec_ref(v_a_849_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0(lean_object* v_f_852_, lean_object* v_a_853_, lean_object* v_x_854_){
_start:
{
lean_object* v___x_856_; 
lean_inc_ref(v_a_853_);
v___x_856_ = lean_apply_3(v_f_852_, v_x_854_, v_a_853_, lean_box(0));
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0___boxed(lean_object* v_f_857_, lean_object* v_a_858_, lean_object* v_x_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0(v_f_857_, v_a_858_, v_x_859_);
lean_dec_ref(v_a_858_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg(lean_object* v_t_862_, lean_object* v_f_863_, lean_object* v_a_864_){
_start:
{
lean_object* v___f_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
lean_inc_ref(v_a_864_);
v___f_866_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_866_, 0, v_f_863_);
lean_closure_set(v___f_866_, 1, v_a_864_);
v___x_867_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(v_t_862_, v___f_866_);
v___x_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg___boxed(lean_object* v_t_869_, lean_object* v_f_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_Server_RequestM_bindTaskCheap___redArg(v_t_869_, v_f_870_, v_a_871_);
lean_dec_ref(v_a_871_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap(lean_object* v_00_u03b1_874_, lean_object* v_00_u03b2_875_, lean_object* v_t_876_, lean_object* v_f_877_, lean_object* v_a_878_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_Server_RequestM_bindTaskCheap___redArg(v_t_876_, v_f_877_, v_a_878_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___boxed(lean_object* v_00_u03b1_881_, lean_object* v_00_u03b2_882_, lean_object* v_t_883_, lean_object* v_f_884_, lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_Server_RequestM_bindTaskCheap(v_00_u03b1_881_, v_00_u03b2_882_, v_t_883_, v_f_884_, v_a_885_);
lean_dec_ref(v_a_885_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly___redArg(lean_object* v_t_888_, lean_object* v_f_889_, lean_object* v_a_890_){
_start:
{
lean_object* v___f_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
lean_inc_ref(v_a_890_);
v___f_892_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_892_, 0, v_f_889_);
lean_closure_set(v___f_892_, 1, v_a_890_);
v___x_893_ = l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(v_t_888_, v___f_892_);
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly___redArg___boxed(lean_object* v_t_895_, lean_object* v_f_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_t_895_, v_f_896_, v_a_897_);
lean_dec_ref(v_a_897_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly(lean_object* v_00_u03b1_900_, lean_object* v_00_u03b2_901_, lean_object* v_t_902_, lean_object* v_f_903_, lean_object* v_a_904_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_t_902_, v_f_903_, v_a_904_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly___boxed(lean_object* v_00_u03b1_907_, lean_object* v_00_u03b2_908_, lean_object* v_t_909_, lean_object* v_f_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_Server_RequestM_bindTaskCostly(v_00_u03b1_907_, v_00_u03b2_908_, v_t_909_, v_f_910_, v_a_911_);
lean_dec_ref(v_a_911_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0(lean_object* v_f_914_, lean_object* v_x_915_, lean_object* v___y_916_){
_start:
{
if (lean_obj_tag(v_x_915_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_dec_ref(v_f_914_);
v_a_918_ = lean_ctor_get(v_x_915_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v_x_915_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v_x_915_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v_x_915_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
lean_ctor_set_tag(v___x_920_, 1);
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_927_; 
v_a_926_ = lean_ctor_get(v_x_915_, 0);
lean_inc(v_a_926_);
lean_dec_ref_known(v_x_915_, 1);
lean_inc_ref(v___y_916_);
v___x_927_ = lean_apply_3(v_f_914_, v_a_926_, v___y_916_, lean_box(0));
return v___x_927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0___boxed(lean_object* v_f_928_, lean_object* v_x_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0(v_f_928_, v_x_929_, v___y_930_);
lean_dec_ref(v___y_930_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg(lean_object* v_t_933_, lean_object* v_f_934_, lean_object* v_a_935_){
_start:
{
lean_object* v___f_937_; lean_object* v___x_938_; 
v___f_937_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_937_, 0, v_f_934_);
v___x_938_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_t_933_, v___f_937_, v_a_935_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___boxed(lean_object* v_t_939_, lean_object* v_f_940_, lean_object* v_a_941_, lean_object* v_a_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_Server_RequestM_mapRequestTaskCheap___redArg(v_t_939_, v_f_940_, v_a_941_);
lean_dec_ref(v_a_941_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap(lean_object* v_00_u03b1_944_, lean_object* v_00_u03b2_945_, lean_object* v_t_946_, lean_object* v_f_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_Server_RequestM_mapRequestTaskCheap___redArg(v_t_946_, v_f_947_, v_a_948_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___boxed(lean_object* v_00_u03b1_951_, lean_object* v_00_u03b2_952_, lean_object* v_t_953_, lean_object* v_f_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_Server_RequestM_mapRequestTaskCheap(v_00_u03b1_951_, v_00_u03b2_952_, v_t_953_, v_f_954_, v_a_955_);
lean_dec_ref(v_a_955_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(lean_object* v_t_958_, lean_object* v_f_959_, lean_object* v_a_960_){
_start:
{
lean_object* v___f_962_; lean_object* v___x_963_; 
v___f_962_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_962_, 0, v_f_959_);
v___x_963_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_t_958_, v___f_962_, v_a_960_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly___redArg___boxed(lean_object* v_t_964_, lean_object* v_f_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(v_t_964_, v_f_965_, v_a_966_);
lean_dec_ref(v_a_966_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly(lean_object* v_00_u03b1_969_, lean_object* v_00_u03b2_970_, lean_object* v_t_971_, lean_object* v_f_972_, lean_object* v_a_973_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(v_t_971_, v_f_972_, v_a_973_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly___boxed(lean_object* v_00_u03b1_976_, lean_object* v_00_u03b2_977_, lean_object* v_t_978_, lean_object* v_f_979_, lean_object* v_a_980_, lean_object* v_a_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_Server_RequestM_mapRequestTaskCostly(v_00_u03b1_976_, v_00_u03b2_977_, v_t_978_, v_f_979_, v_a_980_);
lean_dec_ref(v_a_980_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0(lean_object* v_f_983_, lean_object* v_x_984_, lean_object* v___y_985_){
_start:
{
if (lean_obj_tag(v_x_984_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec_ref(v_f_983_);
v_a_987_ = lean_ctor_get(v_x_984_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v_x_984_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v_x_984_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v_x_984_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
lean_ctor_set_tag(v___x_989_, 1);
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_996_; 
v_a_995_ = lean_ctor_get(v_x_984_, 0);
lean_inc(v_a_995_);
lean_dec_ref_known(v_x_984_, 1);
lean_inc_ref(v___y_985_);
v___x_996_ = lean_apply_3(v_f_983_, v_a_995_, v___y_985_, lean_box(0));
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0___boxed(lean_object* v_f_997_, lean_object* v_x_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0(v_f_997_, v_x_998_, v___y_999_);
lean_dec_ref(v___y_999_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg(lean_object* v_t_1002_, lean_object* v_f_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v___f_1006_; lean_object* v___x_1007_; 
v___f_1006_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1006_, 0, v_f_1003_);
v___x_1007_ = l_Lean_Server_RequestM_bindTaskCheap___redArg(v_t_1002_, v___f_1006_, v_a_1004_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___boxed(lean_object* v_t_1008_, lean_object* v_f_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_Server_RequestM_bindRequestTaskCheap___redArg(v_t_1008_, v_f_1009_, v_a_1010_);
lean_dec_ref(v_a_1010_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap(lean_object* v_00_u03b1_1013_, lean_object* v_00_u03b2_1014_, lean_object* v_t_1015_, lean_object* v_f_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Lean_Server_RequestM_bindRequestTaskCheap___redArg(v_t_1015_, v_f_1016_, v_a_1017_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___boxed(lean_object* v_00_u03b1_1020_, lean_object* v_00_u03b2_1021_, lean_object* v_t_1022_, lean_object* v_f_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_Server_RequestM_bindRequestTaskCheap(v_00_u03b1_1020_, v_00_u03b2_1021_, v_t_1022_, v_f_1023_, v_a_1024_);
lean_dec_ref(v_a_1024_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly___redArg(lean_object* v_t_1027_, lean_object* v_f_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v___f_1031_; lean_object* v___x_1032_; 
v___f_1031_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1031_, 0, v_f_1028_);
v___x_1032_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_t_1027_, v___f_1031_, v_a_1029_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly___redArg___boxed(lean_object* v_t_1033_, lean_object* v_f_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_Server_RequestM_bindRequestTaskCostly___redArg(v_t_1033_, v_f_1034_, v_a_1035_);
lean_dec_ref(v_a_1035_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly(lean_object* v_00_u03b1_1038_, lean_object* v_00_u03b2_1039_, lean_object* v_t_1040_, lean_object* v_f_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_Server_RequestM_bindRequestTaskCostly___redArg(v_t_1040_, v_f_1041_, v_a_1042_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly___boxed(lean_object* v_00_u03b1_1045_, lean_object* v_00_u03b2_1046_, lean_object* v_t_1047_, lean_object* v_f_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_Server_RequestM_bindRequestTaskCostly(v_00_u03b1_1045_, v_00_u03b2_1046_, v_t_1047_, v_f_1048_, v_a_1049_);
lean_dec_ref(v_a_1049_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___redArg(lean_object* v_inst_1052_, lean_object* v_params_1053_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lean_Server_parseRequestParams___redArg(v_inst_1052_, v_params_1053_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1055_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1055_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
lean_ctor_set_tag(v___x_1058_, 1);
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
v_a_1064_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1055_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1055_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 0);
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___redArg___boxed(lean_object* v_inst_1072_, lean_object* v_params_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_1072_, v_params_1073_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams(lean_object* v_paramType_1076_, lean_object* v_inst_1077_, lean_object* v_params_1078_, lean_object* v_a_1079_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_1077_, v_params_1078_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___boxed(lean_object* v_paramType_1082_, lean_object* v_inst_1083_, lean_object* v_params_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Lean_Server_RequestM_parseRequestParams(v_paramType_1082_, v_inst_1083_, v_params_1084_, v_a_1085_);
lean_dec_ref(v_a_1085_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_checkCancelled(lean_object* v_a_1088_){
_start:
{
lean_object* v_cancelTk_1090_; uint8_t v___x_1091_; 
v_cancelTk_1090_ = lean_ctor_get(v_a_1088_, 4);
v___x_1091_ = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_cancelTk_1090_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = lean_box(0);
v___x_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
return v___x_1093_;
}
else
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = ((lean_object*)(l_Lean_Server_RequestError_requestCancelled));
v___x_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
return v___x_1095_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_checkCancelled___boxed(lean_object* v_a_1096_, lean_object* v_a_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Lean_Server_RequestM_checkCancelled(v_a_1096_);
lean_dec_ref(v_a_1096_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0(lean_object* v_inst_1100_, lean_object* v_x_1101_){
_start:
{
if (lean_obj_tag(v_x_1101_) == 0)
{
lean_object* v_response_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1120_; 
v_response_1102_ = lean_ctor_get(v_x_1101_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_x_1101_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1104_ = v_x_1101_;
v_isShared_1105_ = v_isSharedCheck_1120_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_response_1102_);
lean_dec(v_x_1101_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1120_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1106_; 
lean_inc(v_response_1102_);
v___x_1106_ = lean_apply_1(v_inst_1100_, v_response_1102_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; uint8_t v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_del_object(v___x_1104_);
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_a_1107_);
lean_dec_ref_known(v___x_1106_, 1);
v___x_1108_ = 0;
v___x_1109_ = ((lean_object*)(l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0___closed__0));
v___x_1110_ = l_Lean_Json_compress(v_response_1102_);
v___x_1111_ = lean_string_append(v___x_1109_, v___x_1110_);
lean_dec_ref(v___x_1110_);
v___x_1112_ = ((lean_object*)(l_Lean_Server_parseRequestParams___redArg___closed__1));
v___x_1113_ = lean_string_append(v___x_1111_, v___x_1112_);
v___x_1114_ = lean_string_append(v___x_1113_, v_a_1107_);
lean_dec(v_a_1107_);
v___x_1115_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
lean_ctor_set_uint8(v___x_1115_, sizeof(void*)*1, v___x_1108_);
return v___x_1115_;
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; 
lean_dec(v_response_1102_);
v_a_1116_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_a_1116_);
lean_dec_ref_known(v___x_1106_, 1);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v_a_1116_);
v___x_1118_ = v___x_1104_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1116_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
else
{
uint8_t v_code_1121_; lean_object* v_message_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_dec_ref(v_inst_1100_);
v_code_1121_ = lean_ctor_get_uint8(v_x_1101_, sizeof(void*)*1);
v_message_1122_ = lean_ctor_get(v_x_1101_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_x_1101_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v_x_1101_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_message_1122_);
lean_dec(v_x_1101_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_message_1122_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, sizeof(void*)*1, v_code_1121_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___redArg(lean_object* v_inst_1130_, lean_object* v_inst_1131_, lean_object* v_method_1132_, lean_object* v_param_1133_, lean_object* v_a_1134_){
_start:
{
lean_object* v_serverRequestEmitter_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___f_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v_serverRequestEmitter_1136_ = lean_ctor_get(v_a_1134_, 5);
v___x_1137_ = lean_apply_1(v_inst_1130_, v_param_1133_);
lean_inc_ref(v_serverRequestEmitter_1136_);
v___x_1138_ = lean_apply_3(v_serverRequestEmitter_1136_, v_method_1132_, v___x_1137_, lean_box(0));
v___f_1139_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1139_, 0, v_inst_1131_);
v___x_1140_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_1139_, v___x_1138_);
v___x_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___redArg___boxed(lean_object* v_inst_1142_, lean_object* v_inst_1143_, lean_object* v_method_1144_, lean_object* v_param_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_Server_RequestM_sendServerRequest___redArg(v_inst_1142_, v_inst_1143_, v_method_1144_, v_param_1145_, v_a_1146_);
lean_dec_ref(v_a_1146_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest(lean_object* v_paramType_1149_, lean_object* v_inst_1150_, lean_object* v_responseType_1151_, lean_object* v_inst_1152_, lean_object* v_inst_1153_, lean_object* v_method_1154_, lean_object* v_param_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Lean_Server_RequestM_sendServerRequest___redArg(v_inst_1150_, v_inst_1152_, v_method_1154_, v_param_1155_, v_a_1156_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___boxed(lean_object* v_paramType_1159_, lean_object* v_inst_1160_, lean_object* v_responseType_1161_, lean_object* v_inst_1162_, lean_object* v_inst_1163_, lean_object* v_method_1164_, lean_object* v_param_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Lean_Server_RequestM_sendServerRequest(v_paramType_1159_, v_inst_1160_, v_responseType_1161_, v_inst_1162_, v_inst_1163_, v_method_1164_, v_param_1165_, v_a_1166_);
lean_dec_ref(v_a_1166_);
lean_dec(v_inst_1163_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux___redArg(lean_object* v_notFoundX_1169_, lean_object* v_x_1170_, lean_object* v_x_1171_, lean_object* v_a_1172_){
_start:
{
if (lean_obj_tag(v_x_1171_) == 0)
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1182_; 
lean_dec_ref(v_x_1170_);
lean_dec_ref(v_notFoundX_1169_);
v_a_1174_ = lean_ctor_get(v_x_1171_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_x_1171_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1176_ = v_x_1171_;
v_isShared_1177_ = v_isSharedCheck_1182_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v_x_1171_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1182_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1178_ = l_Lean_Server_RequestError_ofIoError(v_a_1174_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set_tag(v___x_1176_, 1);
lean_ctor_set(v___x_1176_, 0, v___x_1178_);
v___x_1180_ = v___x_1176_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
else
{
lean_object* v_a_1183_; 
v_a_1183_ = lean_ctor_get(v_x_1171_, 0);
lean_inc(v_a_1183_);
lean_dec_ref_known(v_x_1171_, 1);
if (lean_obj_tag(v_a_1183_) == 0)
{
lean_object* v___x_1184_; 
lean_dec_ref(v_x_1170_);
lean_inc_ref(v_a_1172_);
v___x_1184_ = lean_apply_2(v_notFoundX_1169_, v_a_1172_, lean_box(0));
return v___x_1184_;
}
else
{
lean_object* v_val_1185_; lean_object* v___x_1186_; 
lean_dec_ref(v_notFoundX_1169_);
v_val_1185_ = lean_ctor_get(v_a_1183_, 0);
lean_inc(v_val_1185_);
lean_dec_ref_known(v_a_1183_, 1);
lean_inc_ref(v_a_1172_);
v___x_1186_ = lean_apply_3(v_x_1170_, v_val_1185_, v_a_1172_, lean_box(0));
return v___x_1186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux___redArg___boxed(lean_object* v_notFoundX_1187_, lean_object* v_x_1188_, lean_object* v_x_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_Server_RequestM_waitFindSnapAux___redArg(v_notFoundX_1187_, v_x_1188_, v_x_1189_, v_a_1190_);
lean_dec_ref(v_a_1190_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux(lean_object* v_00_u03b1_1193_, lean_object* v_notFoundX_1194_, lean_object* v_x_1195_, lean_object* v_x_1196_, lean_object* v_a_1197_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Lean_Server_RequestM_waitFindSnapAux___redArg(v_notFoundX_1194_, v_x_1195_, v_x_1196_, v_a_1197_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux___boxed(lean_object* v_00_u03b1_1200_, lean_object* v_notFoundX_1201_, lean_object* v_x_1202_, lean_object* v_x_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_Server_RequestM_waitFindSnapAux(v_00_u03b1_1200_, v_notFoundX_1201_, v_x_1202_, v_x_1203_, v_a_1204_);
lean_dec_ref(v_a_1204_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___redArg(lean_object* v_doc_1207_, lean_object* v_p_1208_, lean_object* v_notFoundX_1209_, lean_object* v_x_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v_toEditableDocumentCore_1213_; lean_object* v_cmdSnaps_1214_; lean_object* v_findTask_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v_toEditableDocumentCore_1213_ = lean_ctor_get(v_doc_1207_, 0);
lean_inc_ref(v_toEditableDocumentCore_1213_);
lean_dec_ref(v_doc_1207_);
v_cmdSnaps_1214_ = lean_ctor_get(v_toEditableDocumentCore_1213_, 2);
lean_inc(v_cmdSnaps_1214_);
lean_dec_ref(v_toEditableDocumentCore_1213_);
v_findTask_1215_ = l_IO_AsyncList_waitFind_x3f___redArg(v_p_1208_, v_cmdSnaps_1214_);
v___x_1216_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_waitFindSnapAux___boxed), 6, 3);
lean_closure_set(v___x_1216_, 0, lean_box(0));
lean_closure_set(v___x_1216_, 1, v_notFoundX_1209_);
lean_closure_set(v___x_1216_, 2, v_x_1210_);
v___x_1217_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_findTask_1215_, v___x_1216_, v_a_1211_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___redArg___boxed(lean_object* v_doc_1218_, lean_object* v_p_1219_, lean_object* v_notFoundX_1220_, lean_object* v_x_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_doc_1218_, v_p_1219_, v_notFoundX_1220_, v_x_1221_, v_a_1222_);
lean_dec_ref(v_a_1222_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap(lean_object* v_00_u03b2_1225_, lean_object* v_doc_1226_, lean_object* v_p_1227_, lean_object* v_notFoundX_1228_, lean_object* v_x_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_doc_1226_, v_p_1227_, v_notFoundX_1228_, v_x_1229_, v_a_1230_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___boxed(lean_object* v_00_u03b2_1233_, lean_object* v_doc_1234_, lean_object* v_p_1235_, lean_object* v_notFoundX_1236_, lean_object* v_x_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_Server_RequestM_withWaitFindSnap(v_00_u03b2_1233_, v_doc_1234_, v_p_1235_, v_notFoundX_1236_, v_x_1237_, v_a_1238_);
lean_dec_ref(v_a_1238_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___redArg(lean_object* v_doc_1241_, lean_object* v_p_1242_, lean_object* v_notFoundX_1243_, lean_object* v_x_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v_toEditableDocumentCore_1247_; lean_object* v_cmdSnaps_1248_; lean_object* v_findTask_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v_toEditableDocumentCore_1247_ = lean_ctor_get(v_doc_1241_, 0);
lean_inc_ref(v_toEditableDocumentCore_1247_);
lean_dec_ref(v_doc_1241_);
v_cmdSnaps_1248_ = lean_ctor_get(v_toEditableDocumentCore_1247_, 2);
lean_inc(v_cmdSnaps_1248_);
lean_dec_ref(v_toEditableDocumentCore_1247_);
v_findTask_1249_ = l_IO_AsyncList_waitFind_x3f___redArg(v_p_1242_, v_cmdSnaps_1248_);
v___x_1250_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_waitFindSnapAux___boxed), 6, 3);
lean_closure_set(v___x_1250_, 0, lean_box(0));
lean_closure_set(v___x_1250_, 1, v_notFoundX_1243_);
lean_closure_set(v___x_1250_, 2, v_x_1244_);
v___x_1251_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_findTask_1249_, v___x_1250_, v_a_1245_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___redArg___boxed(lean_object* v_doc_1252_, lean_object* v_p_1253_, lean_object* v_notFoundX_1254_, lean_object* v_x_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_Server_RequestM_bindWaitFindSnap___redArg(v_doc_1252_, v_p_1253_, v_notFoundX_1254_, v_x_1255_, v_a_1256_);
lean_dec_ref(v_a_1256_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap(lean_object* v_00_u03b2_1259_, lean_object* v_doc_1260_, lean_object* v_p_1261_, lean_object* v_notFoundX_1262_, lean_object* v_x_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_Server_RequestM_bindWaitFindSnap___redArg(v_doc_1260_, v_p_1261_, v_notFoundX_1262_, v_x_1263_, v_a_1264_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___boxed(lean_object* v_00_u03b2_1267_, lean_object* v_doc_1268_, lean_object* v_p_1269_, lean_object* v_notFoundX_1270_, lean_object* v_x_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_Server_RequestM_bindWaitFindSnap(v_00_u03b2_1267_, v_doc_1268_, v_p_1269_, v_notFoundX_1270_, v_x_1271_, v_a_1272_);
lean_dec_ref(v_a_1272_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(lean_object* v___y_1275_){
_start:
{
lean_object* v_doc_1277_; lean_object* v___x_1278_; 
v_doc_1277_ = lean_ctor_get(v___y_1275_, 1);
lean_inc_ref(v_doc_1277_);
v___x_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1278_, 0, v_doc_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0___boxed(lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(v___y_1279_);
lean_dec_ref(v___y_1279_);
return v_res_1281_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0(lean_object* v___x_1282_, lean_object* v_s_1283_){
_start:
{
lean_object* v___x_1284_; uint8_t v___x_1285_; 
v___x_1284_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_s_1283_);
v___x_1285_ = lean_nat_dec_le(v___x_1282_, v___x_1284_);
lean_dec(v___x_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0___boxed(lean_object* v___x_1286_, lean_object* v_s_1287_){
_start:
{
uint8_t v_res_1288_; lean_object* v_r_1289_; 
v_res_1288_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0(v___x_1286_, v_s_1287_);
lean_dec_ref(v_s_1287_);
lean_dec(v___x_1286_);
v_r_1289_ = lean_box(v_res_1288_);
return v_r_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1(lean_object* v___x_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1290_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1___boxed(lean_object* v___x_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1(v___x_1294_, v___y_1295_);
lean_dec_ref(v___y_1295_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg(lean_object* v_lspPos_1302_, lean_object* v_f_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v___x_1306_; lean_object* v_a_1307_; lean_object* v_toEditableDocumentCore_1308_; lean_object* v_meta_1309_; lean_object* v_text_1310_; lean_object* v_line_1311_; lean_object* v_character_1312_; lean_object* v___x_1313_; lean_object* v___f_1314_; uint8_t v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___f_1328_; lean_object* v___x_1329_; 
v___x_1306_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(v_a_1304_);
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_a_1307_);
lean_dec_ref(v___x_1306_);
v_toEditableDocumentCore_1308_ = lean_ctor_get(v_a_1307_, 0);
v_meta_1309_ = lean_ctor_get(v_toEditableDocumentCore_1308_, 0);
v_text_1310_ = lean_ctor_get(v_meta_1309_, 3);
v_line_1311_ = lean_ctor_get(v_lspPos_1302_, 0);
lean_inc(v_line_1311_);
v_character_1312_ = lean_ctor_get(v_lspPos_1302_, 1);
lean_inc(v_character_1312_);
v___x_1313_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1310_, v_lspPos_1302_);
v___f_1314_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1314_, 0, v___x_1313_);
v___x_1315_ = 3;
v___x_1316_ = ((lean_object*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__0));
v___x_1317_ = ((lean_object*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__1));
v___x_1318_ = l_Nat_reprFast(v_line_1311_);
v___x_1319_ = lean_string_append(v___x_1317_, v___x_1318_);
lean_dec_ref(v___x_1318_);
v___x_1320_ = ((lean_object*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__2));
v___x_1321_ = lean_string_append(v___x_1319_, v___x_1320_);
v___x_1322_ = l_Nat_reprFast(v_character_1312_);
v___x_1323_ = lean_string_append(v___x_1321_, v___x_1322_);
lean_dec_ref(v___x_1322_);
v___x_1324_ = ((lean_object*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__3));
v___x_1325_ = lean_string_append(v___x_1323_, v___x_1324_);
v___x_1326_ = lean_string_append(v___x_1316_, v___x_1325_);
lean_dec_ref(v___x_1325_);
v___x_1327_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
lean_ctor_set_uint8(v___x_1327_, sizeof(void*)*1, v___x_1315_);
v___f_1328_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1328_, 0, v___x_1327_);
v___x_1329_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_a_1307_, v___f_1314_, v___f_1328_, v_f_1303_, v_a_1304_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___boxed(lean_object* v_lspPos_1330_, lean_object* v_f_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg(v_lspPos_1330_, v_f_1331_, v_a_1332_);
lean_dec_ref(v_a_1332_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos(lean_object* v_00_u03b1_1335_, lean_object* v_lspPos_1336_, lean_object* v_f_1337_, lean_object* v_a_1338_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg(v_lspPos_1336_, v_f_1337_, v_a_1338_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___boxed(lean_object* v_00_u03b1_1341_, lean_object* v_lspPos_1342_, lean_object* v_f_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos(v_00_u03b1_1341_, v_lspPos_1342_, v_f_1343_, v_a_1344_);
lean_dec_ref(v_a_1344_);
return v_res_1346_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_isAfterHoverPos(lean_object* v_hoverPos_1347_, lean_object* v_cmdParsed_1348_){
_start:
{
lean_object* v_stx_1349_; uint8_t v___x_1350_; lean_object* v___x_1351_; 
v_stx_1349_ = lean_ctor_get(v_cmdParsed_1348_, 1);
v___x_1350_ = 1;
v___x_1351_ = l_Lean_Syntax_getPos_x3f(v_stx_1349_, v___x_1350_);
if (lean_obj_tag(v___x_1351_) == 1)
{
lean_object* v_val_1352_; uint8_t v___x_1353_; 
v_val_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_val_1352_);
lean_dec_ref_known(v___x_1351_, 1);
v___x_1353_ = lean_nat_dec_lt(v_hoverPos_1347_, v_val_1352_);
lean_dec(v_val_1352_);
return v___x_1353_;
}
else
{
uint8_t v___x_1354_; 
lean_dec(v___x_1351_);
v___x_1354_ = 0;
return v___x_1354_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_isAfterHoverPos___boxed(lean_object* v_hoverPos_1355_, lean_object* v_cmdParsed_1356_){
_start:
{
uint8_t v_res_1357_; lean_object* v_r_1358_; 
v_res_1357_ = l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_isAfterHoverPos(v_hoverPos_1355_, v_cmdParsed_1356_);
lean_dec_ref(v_cmdParsed_1356_);
lean_dec(v_hoverPos_1355_);
v_r_1358_ = lean_box(v_res_1357_);
return v_r_1358_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_containsHoverPos(lean_object* v_doc_1359_, lean_object* v_hoverPos_1360_, lean_object* v_cmdParsed_1361_){
_start:
{
lean_object* v_stx_1362_; uint8_t v___x_1363_; lean_object* v___x_1364_; 
v_stx_1362_ = lean_ctor_get(v_cmdParsed_1361_, 1);
v___x_1363_ = 1;
v___x_1364_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_1362_, v___x_1363_);
if (lean_obj_tag(v___x_1364_) == 1)
{
lean_object* v_toEditableDocumentCore_1365_; lean_object* v_meta_1366_; lean_object* v_val_1367_; lean_object* v_text_1368_; uint8_t v___x_1369_; uint8_t v___x_1370_; 
v_toEditableDocumentCore_1365_ = lean_ctor_get(v_doc_1359_, 0);
v_meta_1366_ = lean_ctor_get(v_toEditableDocumentCore_1365_, 0);
v_val_1367_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_val_1367_);
lean_dec_ref_known(v___x_1364_, 1);
v_text_1368_ = lean_ctor_get(v_meta_1366_, 3);
v___x_1369_ = 0;
v___x_1370_ = l_Lean_FileMap_rangeContainsHoverPos(v_text_1368_, v_val_1367_, v_hoverPos_1360_, v___x_1369_);
lean_dec(v_val_1367_);
return v___x_1370_;
}
else
{
uint8_t v___x_1371_; 
lean_dec(v___x_1364_);
v___x_1371_ = 0;
return v___x_1371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_containsHoverPos___boxed(lean_object* v_doc_1372_, lean_object* v_hoverPos_1373_, lean_object* v_cmdParsed_1374_){
_start:
{
uint8_t v_res_1375_; lean_object* v_r_1376_; 
v_res_1375_ = l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_containsHoverPos(v_doc_1372_, v_hoverPos_1373_, v_cmdParsed_1374_);
lean_dec_ref(v_cmdParsed_1374_);
lean_dec(v_hoverPos_1373_);
lean_dec_ref(v_doc_1372_);
v_r_1376_ = lean_box(v_res_1375_);
return v_r_1376_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0(void){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = lean_box(0);
v___x_1378_ = lean_task_pure(v___x_1377_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go(lean_object* v_doc_1379_, lean_object* v_hoverPos_1380_, lean_object* v_cmdParsed_1381_){
_start:
{
uint8_t v___x_1382_; 
v___x_1382_ = l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_containsHoverPos(v_doc_1379_, v_hoverPos_1380_, v_cmdParsed_1381_);
if (v___x_1382_ == 0)
{
uint8_t v___x_1383_; 
v___x_1383_ = l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_isAfterHoverPos(v_hoverPos_1380_, v_cmdParsed_1381_);
if (v___x_1383_ == 0)
{
lean_object* v_nextCmdSnap_x3f_1384_; 
v_nextCmdSnap_x3f_1384_ = lean_ctor_get(v_cmdParsed_1381_, 4);
lean_inc(v_nextCmdSnap_x3f_1384_);
lean_dec_ref(v_cmdParsed_1381_);
if (lean_obj_tag(v_nextCmdSnap_x3f_1384_) == 0)
{
lean_object* v___x_1385_; 
lean_dec(v_hoverPos_1380_);
lean_dec_ref(v_doc_1379_);
v___x_1385_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0, &l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0);
return v___x_1385_;
}
else
{
lean_object* v_val_1386_; lean_object* v_task_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v_val_1386_ = lean_ctor_get(v_nextCmdSnap_x3f_1384_, 0);
lean_inc(v_val_1386_);
lean_dec_ref_known(v_nextCmdSnap_x3f_1384_, 1);
v_task_1387_ = lean_ctor_get(v_val_1386_, 3);
lean_inc_ref(v_task_1387_);
lean_dec(v_val_1386_);
v___x_1388_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go), 3, 2);
lean_closure_set(v___x_1388_, 0, v_doc_1379_);
lean_closure_set(v___x_1388_, 1, v_hoverPos_1380_);
v___x_1389_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_task_1387_, v___x_1388_);
return v___x_1389_;
}
}
else
{
lean_object* v___x_1390_; 
lean_dec_ref(v_cmdParsed_1381_);
lean_dec(v_hoverPos_1380_);
lean_dec_ref(v_doc_1379_);
v___x_1390_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0, &l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0);
return v___x_1390_;
}
}
else
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
lean_dec(v_hoverPos_1380_);
lean_dec_ref(v_doc_1379_);
v___x_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1391_, 0, v_cmdParsed_1381_);
v___x_1392_ = lean_task_pure(v___x_1391_);
return v___x_1392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdParsedSnap___lam__0(lean_object* v_doc_1393_, lean_object* v_hoverPos_1394_, lean_object* v_headerProcessed_1395_){
_start:
{
lean_object* v_result_x3f_1396_; 
v_result_x3f_1396_ = lean_ctor_get(v_headerProcessed_1395_, 2);
lean_inc(v_result_x3f_1396_);
lean_dec_ref(v_headerProcessed_1395_);
if (lean_obj_tag(v_result_x3f_1396_) == 1)
{
lean_object* v_val_1397_; lean_object* v_firstCmdSnap_1398_; lean_object* v_task_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v_val_1397_ = lean_ctor_get(v_result_x3f_1396_, 0);
lean_inc(v_val_1397_);
lean_dec_ref_known(v_result_x3f_1396_, 1);
v_firstCmdSnap_1398_ = lean_ctor_get(v_val_1397_, 1);
lean_inc_ref(v_firstCmdSnap_1398_);
lean_dec(v_val_1397_);
v_task_1399_ = lean_ctor_get(v_firstCmdSnap_1398_, 3);
lean_inc_ref(v_task_1399_);
lean_dec_ref(v_firstCmdSnap_1398_);
v___x_1400_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go), 3, 2);
lean_closure_set(v___x_1400_, 0, v_doc_1393_);
lean_closure_set(v___x_1400_, 1, v_hoverPos_1394_);
v___x_1401_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_task_1399_, v___x_1400_);
return v___x_1401_;
}
else
{
lean_object* v___x_1402_; 
lean_dec(v_result_x3f_1396_);
lean_dec(v_hoverPos_1394_);
lean_dec_ref(v_doc_1393_);
v___x_1402_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0, &l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0);
return v___x_1402_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdParsedSnap(lean_object* v_doc_1403_, lean_object* v_hoverPos_1404_){
_start:
{
lean_object* v_toEditableDocumentCore_1405_; lean_object* v_initSnap_1406_; lean_object* v_result_x3f_1407_; 
v_toEditableDocumentCore_1405_ = lean_ctor_get(v_doc_1403_, 0);
v_initSnap_1406_ = lean_ctor_get(v_toEditableDocumentCore_1405_, 1);
v_result_x3f_1407_ = lean_ctor_get(v_initSnap_1406_, 4);
if (lean_obj_tag(v_result_x3f_1407_) == 1)
{
lean_object* v_val_1408_; lean_object* v_processedSnap_1409_; lean_object* v_task_1410_; lean_object* v___f_1411_; lean_object* v___x_1412_; 
v_val_1408_ = lean_ctor_get(v_result_x3f_1407_, 0);
v_processedSnap_1409_ = lean_ctor_get(v_val_1408_, 1);
v_task_1410_ = lean_ctor_get(v_processedSnap_1409_, 3);
lean_inc_ref(v_task_1410_);
v___f_1411_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_findCmdParsedSnap___lam__0), 3, 2);
lean_closure_set(v___f_1411_, 0, v_doc_1403_);
lean_closure_set(v___f_1411_, 1, v_hoverPos_1404_);
v___x_1412_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_task_1410_, v___f_1411_);
return v___x_1412_;
}
else
{
lean_object* v___x_1413_; 
lean_dec(v_hoverPos_1404_);
lean_dec_ref(v_doc_1403_);
v___x_1413_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0, &l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0);
return v___x_1413_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__0(lean_object* v_msg_1414_){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1415_ = lean_box(0);
v___x_1416_ = lean_panic_fn_borrowed(v___x_1415_, v_msg_1414_);
return v___x_1416_;
}
}
static lean_object* _init_l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1420_ = ((lean_object*)(l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__2));
v___x_1421_ = lean_unsigned_to_nat(8u);
v___x_1422_ = lean_unsigned_to_nat(418u);
v___x_1423_ = ((lean_object*)(l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__1));
v___x_1424_ = ((lean_object*)(l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__0));
v___x_1425_ = l_mkPanicMessageWithDecl(v___x_1424_, v___x_1423_, v___x_1422_, v___x_1421_, v___x_1420_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lam__0(lean_object* v_stx_1426_, lean_object* v_s_1427_){
_start:
{
lean_object* v_infoTree_x3f_1428_; 
v_infoTree_x3f_1428_ = lean_ctor_get(v_s_1427_, 2);
lean_inc(v_infoTree_x3f_1428_);
lean_dec_ref(v_s_1427_);
if (lean_obj_tag(v_infoTree_x3f_1428_) == 0)
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
lean_dec(v_stx_1426_);
v___x_1429_ = lean_obj_once(&l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__3, &l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__3_once, _init_l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__3);
v___x_1430_ = l_panic___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__0(v___x_1429_);
return v___x_1430_;
}
else
{
lean_object* v_val_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1439_; 
v_val_1431_ = lean_ctor_get(v_infoTree_x3f_1428_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_infoTree_x3f_1428_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1433_ = v_infoTree_x3f_1428_;
v_isShared_1434_ = v_isSharedCheck_1439_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_val_1431_);
lean_dec(v_infoTree_x3f_1428_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1439_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1435_, 0, v_stx_1426_);
lean_ctor_set(v___x_1435_, 1, v_val_1431_);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 0, v___x_1435_);
v___x_1437_ = v___x_1433_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lam__1(lean_object* v_elabSnap_1440_, lean_object* v___f_1441_, lean_object* v_stx_1442_, lean_object* v_x_1443_){
_start:
{
if (lean_obj_tag(v_x_1443_) == 0)
{
lean_object* v_infoTreeSnap_1444_; lean_object* v_task_1445_; lean_object* v___x_1446_; 
lean_dec(v_stx_1442_);
v_infoTreeSnap_1444_ = lean_ctor_get(v_elabSnap_1440_, 3);
lean_inc_ref(v_infoTreeSnap_1444_);
lean_dec_ref(v_elabSnap_1440_);
v_task_1445_ = lean_ctor_get(v_infoTreeSnap_1444_, 3);
lean_inc_ref(v_task_1445_);
lean_dec_ref(v_infoTreeSnap_1444_);
v___x_1446_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_1441_, v_task_1445_);
return v___x_1446_;
}
else
{
lean_object* v_val_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1456_; 
lean_dec_ref(v___f_1441_);
lean_dec_ref(v_elabSnap_1440_);
v_val_1447_ = lean_ctor_get(v_x_1443_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_x_1443_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1449_ = v_x_1443_;
v_isShared_1450_ = v_isSharedCheck_1456_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_val_1447_);
lean_dec(v_x_1443_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1456_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; lean_object* v___x_1453_; 
v___x_1451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1451_, 0, v_stx_1442_);
lean_ctor_set(v___x_1451_, 1, v_val_1447_);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 0, v___x_1451_);
v___x_1453_ = v___x_1449_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1451_);
v___x_1453_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1454_; 
v___x_1454_ = lean_task_pure(v___x_1453_);
return v___x_1454_;
}
}
}
}
}
static lean_object* _init_l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___closed__0(void){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1457_ = lean_box(0);
v___x_1458_ = lean_task_pure(v___x_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lam__2(lean_object* v_doc_1459_, lean_object* v_hoverPos_1460_, uint8_t v_includeStop_1461_, lean_object* v_x_1462_){
_start:
{
if (lean_obj_tag(v_x_1462_) == 0)
{
lean_object* v___x_1463_; 
lean_dec(v_hoverPos_1460_);
lean_dec_ref(v_doc_1459_);
v___x_1463_ = lean_obj_once(&l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___closed__0, &l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___closed__0_once, _init_l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___closed__0);
return v___x_1463_;
}
else
{
lean_object* v_toEditableDocumentCore_1464_; lean_object* v_meta_1465_; lean_object* v_val_1466_; lean_object* v_text_1467_; lean_object* v_stx_1468_; lean_object* v_elabSnap_1469_; lean_object* v___f_1470_; lean_object* v___f_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v_toEditableDocumentCore_1464_ = lean_ctor_get(v_doc_1459_, 0);
lean_inc_ref(v_toEditableDocumentCore_1464_);
lean_dec_ref(v_doc_1459_);
v_meta_1465_ = lean_ctor_get(v_toEditableDocumentCore_1464_, 0);
lean_inc_ref(v_meta_1465_);
lean_dec_ref(v_toEditableDocumentCore_1464_);
v_val_1466_ = lean_ctor_get(v_x_1462_, 0);
lean_inc(v_val_1466_);
lean_dec_ref_known(v_x_1462_, 1);
v_text_1467_ = lean_ctor_get(v_meta_1465_, 3);
lean_inc_ref(v_text_1467_);
lean_dec_ref(v_meta_1465_);
v_stx_1468_ = lean_ctor_get(v_val_1466_, 1);
lean_inc_n(v_stx_1468_, 2);
v_elabSnap_1469_ = lean_ctor_get(v_val_1466_, 3);
lean_inc_ref_n(v_elabSnap_1469_, 2);
lean_dec(v_val_1466_);
v___f_1470_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_findCmdDataAtPos___lam__0), 2, 1);
lean_closure_set(v___f_1470_, 0, v_stx_1468_);
v___f_1471_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_findCmdDataAtPos___lam__1), 4, 3);
lean_closure_set(v___f_1471_, 0, v_elabSnap_1469_);
lean_closure_set(v___f_1471_, 1, v___f_1470_);
lean_closure_set(v___f_1471_, 2, v_stx_1468_);
v___x_1472_ = l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go(v_elabSnap_1469_);
v___x_1473_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos(v_text_1467_, v___x_1472_, v_hoverPos_1460_, v_includeStop_1461_);
v___x_1474_ = l_Lean_Server_ServerTask_bindCheap___redArg(v___x_1473_, v___f_1471_);
return v___x_1474_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___boxed(lean_object* v_doc_1475_, lean_object* v_hoverPos_1476_, lean_object* v_includeStop_1477_, lean_object* v_x_1478_){
_start:
{
uint8_t v_includeStop_boxed_1479_; lean_object* v_res_1480_; 
v_includeStop_boxed_1479_ = lean_unbox(v_includeStop_1477_);
v_res_1480_ = l_Lean_Server_RequestM_findCmdDataAtPos___lam__2(v_doc_1475_, v_hoverPos_1476_, v_includeStop_boxed_1479_, v_x_1478_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos(lean_object* v_doc_1481_, lean_object* v_hoverPos_1482_, uint8_t v_includeStop_1483_){
_start:
{
lean_object* v___x_1484_; lean_object* v___f_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1484_ = lean_box(v_includeStop_1483_);
lean_inc(v_hoverPos_1482_);
lean_inc_ref(v_doc_1481_);
v___f_1485_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1485_, 0, v_doc_1481_);
lean_closure_set(v___f_1485_, 1, v_hoverPos_1482_);
lean_closure_set(v___f_1485_, 2, v___x_1484_);
v___x_1486_ = l_Lean_Server_RequestM_findCmdParsedSnap(v_doc_1481_, v_hoverPos_1482_);
v___x_1487_ = l_Lean_Server_ServerTask_bindCheap___redArg(v___x_1486_, v___f_1485_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___boxed(lean_object* v_doc_1488_, lean_object* v_hoverPos_1489_, lean_object* v_includeStop_1490_){
_start:
{
uint8_t v_includeStop_boxed_1491_; lean_object* v_res_1492_; 
v_includeStop_boxed_1491_ = lean_unbox(v_includeStop_1490_);
v_res_1492_ = l_Lean_Server_RequestM_findCmdDataAtPos(v_doc_1488_, v_hoverPos_1489_, v_includeStop_boxed_1491_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findInfoTreeAtPos___lam__0(lean_object* v_x_1493_){
_start:
{
if (lean_obj_tag(v_x_1493_) == 0)
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_box(0);
return v___x_1494_;
}
else
{
lean_object* v_val_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1503_; 
v_val_1495_ = lean_ctor_get(v_x_1493_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_x_1493_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1497_ = v_x_1493_;
v_isShared_1498_ = v_isSharedCheck_1503_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_val_1495_);
lean_dec(v_x_1493_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1503_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v_snd_1499_; lean_object* v___x_1501_; 
v_snd_1499_ = lean_ctor_get(v_val_1495_, 1);
lean_inc(v_snd_1499_);
lean_dec(v_val_1495_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v_snd_1499_);
v___x_1501_ = v___x_1497_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_snd_1499_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findInfoTreeAtPos(lean_object* v_doc_1505_, lean_object* v_hoverPos_1506_, uint8_t v_includeStop_1507_){
_start:
{
lean_object* v___f_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___f_1508_ = ((lean_object*)(l_Lean_Server_RequestM_findInfoTreeAtPos___closed__0));
v___x_1509_ = l_Lean_Server_RequestM_findCmdDataAtPos(v_doc_1505_, v_hoverPos_1506_, v_includeStop_1507_);
v___x_1510_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_1508_, v___x_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findInfoTreeAtPos___boxed(lean_object* v_doc_1511_, lean_object* v_hoverPos_1512_, lean_object* v_includeStop_1513_){
_start:
{
uint8_t v_includeStop_boxed_1514_; lean_object* v_res_1515_; 
v_includeStop_boxed_1514_ = lean_unbox(v_includeStop_1513_);
v_res_1515_ = l_Lean_Server_RequestM_findInfoTreeAtPos(v_doc_1511_, v_hoverPos_1512_, v_includeStop_boxed_1514_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___redArg(lean_object* v_snap_1516_, lean_object* v_c_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v_doc_1520_; lean_object* v_toEditableDocumentCore_1521_; lean_object* v_meta_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v_doc_1520_ = lean_ctor_get(v_a_1518_, 1);
v_toEditableDocumentCore_1521_ = lean_ctor_get(v_doc_1520_, 0);
v_meta_1522_ = lean_ctor_get(v_toEditableDocumentCore_1521_, 0);
lean_inc_ref(v_a_1518_);
v___x_1523_ = lean_apply_1(v_c_1517_, v_a_1518_);
v___x_1524_ = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(v_snap_1516_, v_meta_1522_, v___x_1523_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1537_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1527_ = v___x_1524_;
v_isShared_1528_ = v_isSharedCheck_1537_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1524_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1537_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
if (lean_obj_tag(v_a_1525_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1531_; 
v_a_1529_ = lean_ctor_get(v_a_1525_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v_a_1525_, 1);
if (v_isShared_1528_ == 0)
{
lean_ctor_set_tag(v___x_1527_, 1);
lean_ctor_set(v___x_1527_, 0, v_a_1529_);
v___x_1531_ = v___x_1527_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1529_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; 
v_a_1533_ = lean_ctor_get(v_a_1525_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v_a_1525_, 1);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v_a_1533_);
v___x_1535_ = v___x_1527_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1539_; lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
v_a_1538_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v___x_1524_, 1);
v___x_1539_ = l_Lean_Server_RequestError_ofException(v_a_1538_);
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1542_ = v___x_1539_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1539_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
lean_ctor_set_tag(v___x_1542_, 1);
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_a_1540_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___redArg___boxed(lean_object* v_snap_1548_, lean_object* v_c_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_Server_RequestM_runCommandElabM___redArg(v_snap_1548_, v_c_1549_, v_a_1550_);
lean_dec_ref(v_a_1550_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM(lean_object* v_00_u03b1_1553_, lean_object* v_snap_1554_, lean_object* v_c_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_Server_RequestM_runCommandElabM___redArg(v_snap_1554_, v_c_1555_, v_a_1556_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___boxed(lean_object* v_00_u03b1_1559_, lean_object* v_snap_1560_, lean_object* v_c_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Lean_Server_RequestM_runCommandElabM(v_00_u03b1_1559_, v_snap_1560_, v_c_1561_, v_a_1562_);
lean_dec_ref(v_a_1562_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___redArg(lean_object* v_snap_1565_, lean_object* v_c_1566_, lean_object* v_a_1567_){
_start:
{
lean_object* v_doc_1569_; lean_object* v_toEditableDocumentCore_1570_; lean_object* v_meta_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v_doc_1569_ = lean_ctor_get(v_a_1567_, 1);
v_toEditableDocumentCore_1570_ = lean_ctor_get(v_doc_1569_, 0);
v_meta_1571_ = lean_ctor_get(v_toEditableDocumentCore_1570_, 0);
lean_inc_ref(v_a_1567_);
v___x_1572_ = lean_apply_1(v_c_1566_, v_a_1567_);
v___x_1573_ = l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(v_snap_1565_, v_meta_1571_, v___x_1572_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1586_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1576_ = v___x_1573_;
v_isShared_1577_ = v_isSharedCheck_1586_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1586_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
if (lean_obj_tag(v_a_1574_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1580_; 
v_a_1578_ = lean_ctor_get(v_a_1574_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v_a_1574_, 1);
if (v_isShared_1577_ == 0)
{
lean_ctor_set_tag(v___x_1576_, 1);
lean_ctor_set(v___x_1576_, 0, v_a_1578_);
v___x_1580_ = v___x_1576_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1578_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; 
v_a_1582_ = lean_ctor_get(v_a_1574_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v_a_1574_, 1);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v_a_1582_);
v___x_1584_ = v___x_1576_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1582_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1588_; lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
v_a_1587_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1573_, 1);
v___x_1588_ = l_Lean_Server_RequestError_ofException(v_a_1587_);
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1588_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1588_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
lean_ctor_set_tag(v___x_1591_, 1);
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___redArg___boxed(lean_object* v_snap_1597_, lean_object* v_c_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Lean_Server_RequestM_runCoreM___redArg(v_snap_1597_, v_c_1598_, v_a_1599_);
lean_dec_ref(v_a_1599_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM(lean_object* v_00_u03b1_1602_, lean_object* v_snap_1603_, lean_object* v_c_1604_, lean_object* v_a_1605_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_Server_RequestM_runCoreM___redArg(v_snap_1603_, v_c_1604_, v_a_1605_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___boxed(lean_object* v_00_u03b1_1608_, lean_object* v_snap_1609_, lean_object* v_c_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Lean_Server_RequestM_runCoreM(v_00_u03b1_1608_, v_snap_1609_, v_c_1610_, v_a_1611_);
lean_dec_ref(v_a_1611_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___redArg(lean_object* v_snap_1614_, lean_object* v_c_1615_, lean_object* v_a_1616_){
_start:
{
lean_object* v_doc_1618_; lean_object* v_toEditableDocumentCore_1619_; lean_object* v_meta_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v_doc_1618_ = lean_ctor_get(v_a_1616_, 1);
v_toEditableDocumentCore_1619_ = lean_ctor_get(v_doc_1618_, 0);
v_meta_1620_ = lean_ctor_get(v_toEditableDocumentCore_1619_, 0);
lean_inc_ref(v_a_1616_);
v___x_1621_ = lean_apply_1(v_c_1615_, v_a_1616_);
v___x_1622_ = l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg(v_snap_1614_, v_meta_1620_, v___x_1621_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1635_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1625_ = v___x_1622_;
v_isShared_1626_ = v_isSharedCheck_1635_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1635_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
if (lean_obj_tag(v_a_1623_) == 0)
{
lean_object* v_a_1627_; lean_object* v___x_1629_; 
v_a_1627_ = lean_ctor_get(v_a_1623_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v_a_1623_, 1);
if (v_isShared_1626_ == 0)
{
lean_ctor_set_tag(v___x_1625_, 1);
lean_ctor_set(v___x_1625_, 0, v_a_1627_);
v___x_1629_ = v___x_1625_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; 
v_a_1631_ = lean_ctor_get(v_a_1623_, 0);
lean_inc(v_a_1631_);
lean_dec_ref_known(v_a_1623_, 1);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v_a_1631_);
v___x_1633_ = v___x_1625_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1631_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1637_; lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
v_a_1636_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1636_);
lean_dec_ref_known(v___x_1622_, 1);
v___x_1637_ = l_Lean_Server_RequestError_ofException(v_a_1636_);
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1637_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1637_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
lean_ctor_set_tag(v___x_1640_, 1);
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___redArg___boxed(lean_object* v_snap_1646_, lean_object* v_c_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_Server_RequestM_runTermElabM___redArg(v_snap_1646_, v_c_1647_, v_a_1648_);
lean_dec_ref(v_a_1648_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM(lean_object* v_00_u03b1_1651_, lean_object* v_snap_1652_, lean_object* v_c_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_Server_RequestM_runTermElabM___redArg(v_snap_1652_, v_c_1653_, v_a_1654_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___boxed(lean_object* v_00_u03b1_1657_, lean_object* v_snap_1658_, lean_object* v_c_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_Server_RequestM_runTermElabM(v_00_u03b1_1657_, v_snap_1658_, v_c_1659_, v_a_1660_);
lean_dec_ref(v_a_1660_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage(lean_object* v_id_1669_, lean_object* v_r_1670_){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___y_1674_; 
v___x_1671_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__0));
v___x_1672_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__1));
switch(lean_obj_tag(v_id_1669_))
{
case 0:
{
lean_object* v_s_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
v_s_1688_ = lean_ctor_get(v_id_1669_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_id_1669_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v_id_1669_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_s_1688_);
lean_dec(v_id_1669_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
lean_ctor_set_tag(v___x_1690_, 3);
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_s_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
v___y_1674_ = v___x_1693_;
goto v___jp_1673_;
}
}
}
case 1:
{
lean_object* v_n_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
v_n_1696_ = lean_ctor_get(v_id_1669_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_id_1669_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v_id_1669_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_n_1696_);
lean_dec(v_id_1669_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
lean_ctor_set_tag(v___x_1698_, 2);
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_n_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
v___y_1674_ = v___x_1701_;
goto v___jp_1673_;
}
}
}
default: 
{
lean_object* v___x_1704_; 
v___x_1704_ = lean_box(0);
v___y_1674_ = v___x_1704_;
goto v___jp_1673_;
}
}
v___jp_1673_:
{
lean_object* v_serialized_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v_serialized_1675_ = lean_ctor_get(v_r_1670_, 1);
v___x_1676_ = l_Lean_Json_compress(v___y_1674_);
v___x_1677_ = lean_string_append(v___x_1672_, v___x_1676_);
lean_dec_ref(v___x_1676_);
v___x_1678_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__2));
v___x_1679_ = lean_string_append(v___x_1677_, v___x_1678_);
v___x_1680_ = lean_string_append(v___x_1671_, v___x_1679_);
lean_dec_ref(v___x_1679_);
v___x_1681_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__3));
v___x_1682_ = lean_string_append(v___x_1680_, v___x_1681_);
v___x_1683_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__4));
v___x_1684_ = lean_string_append(v___x_1683_, v_serialized_1675_);
v___x_1685_ = lean_string_append(v___x_1682_, v___x_1684_);
lean_dec_ref(v___x_1684_);
v___x_1686_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__5));
v___x_1687_ = lean_string_append(v___x_1685_, v___x_1686_);
return v___x_1687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage___boxed(lean_object* v_id_1705_, lean_object* v_r_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_Server_SerializedLspResponse_toSerializedMessage(v_id_1705_, v_r_1706_);
lean_dec_ref(v_r_1706_);
return v_res_1707_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1708_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_);
v___x_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1712_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_);
v___x_1713_ = lean_st_mk_ref(v___x_1712_);
v___x_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2____boxed(lean_object* v_a_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_();
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__0(lean_object* v_inst_1717_, lean_object* v_inst_1718_, lean_object* v_j_1719_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Lean_Server_parseRequestParams___redArg(v_inst_1717_, v_j_1719_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_dec_ref(v_inst_1718_);
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1720_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1720_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1737_; 
v_a_1729_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1731_ = v___x_1720_;
v_isShared_1732_ = v_isSharedCheck_1737_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1720_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1737_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1735_; 
v___x_1733_ = lean_apply_1(v_inst_1718_, v_a_1729_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v___x_1733_);
v___x_1735_ = v___x_1731_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1733_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__1(lean_object* v_serialize_x3f_1738_, uint8_t v_a_1739_, lean_object* v_inst_1740_, lean_object* v_r_1741_){
_start:
{
if (lean_obj_tag(v_serialize_x3f_1738_) == 1)
{
lean_object* v_val_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
lean_dec_ref(v_inst_1740_);
v_val_1742_ = lean_ctor_get(v_serialize_x3f_1738_, 0);
lean_inc(v_val_1742_);
lean_dec_ref_known(v_serialize_x3f_1738_, 1);
v___x_1743_ = lean_box(0);
v___x_1744_ = lean_apply_1(v_val_1742_, v_r_1741_);
v___x_1745_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1745_, 0, v___x_1743_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
lean_ctor_set_uint8(v___x_1745_, sizeof(void*)*2, v_a_1739_);
return v___x_1745_;
}
else
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_dec(v_serialize_x3f_1738_);
v___x_1746_ = lean_apply_1(v_inst_1740_, v_r_1741_);
lean_inc(v___x_1746_);
v___x_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
v___x_1748_ = l_Lean_Json_compress(v___x_1746_);
v___x_1749_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1749_, 0, v___x_1747_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
lean_ctor_set_uint8(v___x_1749_, sizeof(void*)*2, v_a_1739_);
return v___x_1749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__1___boxed(lean_object* v_serialize_x3f_1750_, lean_object* v_a_1751_, lean_object* v_inst_1752_, lean_object* v_r_1753_){
_start:
{
uint8_t v_a_1617__boxed_1754_; lean_object* v_res_1755_; 
v_a_1617__boxed_1754_ = lean_unbox(v_a_1751_);
v_res_1755_ = l_Lean_Server_registerLspRequestHandler___redArg___lam__1(v_serialize_x3f_1750_, v_a_1617__boxed_1754_, v_inst_1752_, v_r_1753_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__2(lean_object* v_inst_1756_, lean_object* v_handler_1757_, lean_object* v___f_1758_, lean_object* v_j_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_1756_, v_j_1759_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1764_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref_known(v___x_1762_, 1);
lean_inc_ref(v___y_1760_);
v___x_1764_ = lean_apply_3(v_handler_1757_, v_a_1763_, v___y_1760_, lean_box(0));
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1774_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1767_ = v___x_1764_;
v_isShared_1768_ = v_isSharedCheck_1774_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1764_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1774_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1772_; 
v___x_1769_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_1769_, 0, lean_box(0));
lean_closure_set(v___x_1769_, 1, lean_box(0));
lean_closure_set(v___x_1769_, 2, lean_box(0));
lean_closure_set(v___x_1769_, 3, v___f_1758_);
v___x_1770_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___x_1769_, v_a_1765_);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 0, v___x_1770_);
v___x_1772_ = v___x_1767_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1770_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
else
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1782_; 
lean_dec_ref(v___f_1758_);
v_a_1775_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1777_ = v___x_1764_;
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1764_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1780_; 
if (v_isShared_1778_ == 0)
{
v___x_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_a_1775_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
lean_dec_ref(v___f_1758_);
lean_dec_ref(v_handler_1757_);
v_a_1783_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1762_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1762_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__2___boxed(lean_object* v_inst_1791_, lean_object* v_handler_1792_, lean_object* v___f_1793_, lean_object* v_j_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_Lean_Server_registerLspRequestHandler___redArg___lam__2(v_inst_1791_, v_handler_1792_, v___f_1793_, v_j_1794_, v___y_1795_);
lean_dec_ref(v___y_1795_);
return v_res_1797_;
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3(void){
_start:
{
lean_object* v___x_1801_; lean_object* v___f_1802_; 
v___x_1801_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___f_1802_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1802_, 0, v___x_1801_);
return v___f_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg(lean_object* v_method_1804_, lean_object* v_inst_1805_, lean_object* v_inst_1806_, lean_object* v_inst_1807_, lean_object* v_handler_1808_, lean_object* v_serialize_x3f_1809_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Lean_initializing();
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1848_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1814_ = v___x_1811_;
v_isShared_1815_ = v_isSharedCheck_1848_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1848_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
uint8_t v___x_1816_; 
v___x_1816_ = lean_unbox(v_a_1812_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1823_; 
lean_dec(v_a_1812_);
lean_dec(v_serialize_x3f_1809_);
lean_dec_ref(v_handler_1808_);
lean_dec_ref(v_inst_1807_);
lean_dec_ref(v_inst_1806_);
lean_dec_ref(v_inst_1805_);
v___x_1817_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__0));
v___x_1818_ = lean_string_append(v___x_1817_, v_method_1804_);
lean_dec_ref(v_method_1804_);
v___x_1819_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__1));
v___x_1820_ = lean_string_append(v___x_1818_, v___x_1819_);
v___x_1821_ = lean_mk_io_user_error(v___x_1820_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set_tag(v___x_1814_, 1);
lean_ctor_set(v___x_1814_, 0, v___x_1821_);
v___x_1823_ = v___x_1814_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
else
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___f_1828_; uint8_t v___x_1829_; 
v___x_1825_ = l_Lean_Server_requestHandlers;
v___x_1826_ = lean_st_ref_get(v___x_1825_);
v___x_1827_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___f_1828_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
lean_inc_ref(v_method_1804_);
v___x_1829_ = l_Lean_PersistentHashMap_contains___redArg(v___f_1828_, v___x_1827_, v___x_1826_, v_method_1804_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; lean_object* v___f_1831_; lean_object* v___f_1832_; lean_object* v___f_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1838_; 
v___x_1830_ = lean_st_ref_take(v___x_1825_);
lean_inc_ref(v_inst_1805_);
v___f_1831_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1831_, 0, v_inst_1805_);
lean_closure_set(v___f_1831_, 1, v_inst_1806_);
v___f_1832_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1832_, 0, v_serialize_x3f_1809_);
lean_closure_set(v___f_1832_, 1, v_a_1812_);
lean_closure_set(v___f_1832_, 2, v_inst_1807_);
v___f_1833_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1833_, 0, v_inst_1805_);
lean_closure_set(v___f_1833_, 1, v_handler_1808_);
lean_closure_set(v___f_1833_, 2, v___f_1832_);
v___x_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___f_1831_);
lean_ctor_set(v___x_1834_, 1, v___f_1833_);
v___x_1835_ = l_Lean_PersistentHashMap_insert___redArg(v___f_1828_, v___x_1827_, v___x_1830_, v_method_1804_, v___x_1834_);
v___x_1836_ = lean_st_ref_set(v___x_1825_, v___x_1835_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v___x_1836_);
v___x_1838_ = v___x_1814_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1846_; 
lean_dec(v_a_1812_);
lean_dec(v_serialize_x3f_1809_);
lean_dec_ref(v_handler_1808_);
lean_dec_ref(v_inst_1807_);
lean_dec_ref(v_inst_1806_);
lean_dec_ref(v_inst_1805_);
v___x_1840_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__0));
v___x_1841_ = lean_string_append(v___x_1840_, v_method_1804_);
lean_dec_ref(v_method_1804_);
v___x_1842_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__4));
v___x_1843_ = lean_string_append(v___x_1841_, v___x_1842_);
v___x_1844_ = lean_mk_io_user_error(v___x_1843_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set_tag(v___x_1814_, 1);
lean_ctor_set(v___x_1814_, 0, v___x_1844_);
v___x_1846_ = v___x_1814_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1844_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_dec(v_serialize_x3f_1809_);
lean_dec_ref(v_handler_1808_);
lean_dec_ref(v_inst_1807_);
lean_dec_ref(v_inst_1806_);
lean_dec_ref(v_inst_1805_);
lean_dec_ref(v_method_1804_);
v_a_1849_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1811_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1811_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___boxed(lean_object* v_method_1857_, lean_object* v_inst_1858_, lean_object* v_inst_1859_, lean_object* v_inst_1860_, lean_object* v_handler_1861_, lean_object* v_serialize_x3f_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_Server_registerLspRequestHandler___redArg(v_method_1857_, v_inst_1858_, v_inst_1859_, v_inst_1860_, v_handler_1861_, v_serialize_x3f_1862_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler(lean_object* v_method_1865_, lean_object* v_paramType_1866_, lean_object* v_inst_1867_, lean_object* v_inst_1868_, lean_object* v_respType_1869_, lean_object* v_inst_1870_, lean_object* v_handler_1871_, lean_object* v_serialize_x3f_1872_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Lean_Server_registerLspRequestHandler___redArg(v_method_1865_, v_inst_1867_, v_inst_1868_, v_inst_1870_, v_handler_1871_, v_serialize_x3f_1872_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___boxed(lean_object* v_method_1875_, lean_object* v_paramType_1876_, lean_object* v_inst_1877_, lean_object* v_inst_1878_, lean_object* v_respType_1879_, lean_object* v_inst_1880_, lean_object* v_handler_1881_, lean_object* v_serialize_x3f_1882_, lean_object* v_a_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_Server_registerLspRequestHandler(v_method_1875_, v_paramType_1876_, v_inst_1877_, v_inst_1878_, v_respType_1879_, v_inst_1880_, v_handler_1881_, v_serialize_x3f_1882_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1885_, lean_object* v_vals_1886_, lean_object* v_i_1887_, lean_object* v_k_1888_){
_start:
{
lean_object* v___x_1889_; uint8_t v___x_1890_; 
v___x_1889_ = lean_array_get_size(v_keys_1885_);
v___x_1890_ = lean_nat_dec_lt(v_i_1887_, v___x_1889_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; 
lean_dec(v_i_1887_);
v___x_1891_ = lean_box(0);
return v___x_1891_;
}
else
{
lean_object* v_k_x27_1892_; uint8_t v___x_1893_; 
v_k_x27_1892_ = lean_array_fget_borrowed(v_keys_1885_, v_i_1887_);
v___x_1893_ = lean_string_dec_eq(v_k_1888_, v_k_x27_1892_);
if (v___x_1893_ == 0)
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = lean_unsigned_to_nat(1u);
v___x_1895_ = lean_nat_add(v_i_1887_, v___x_1894_);
lean_dec(v_i_1887_);
v_i_1887_ = v___x_1895_;
goto _start;
}
else
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1897_ = lean_array_fget_borrowed(v_vals_1886_, v_i_1887_);
lean_dec(v_i_1887_);
lean_inc(v___x_1897_);
v___x_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
return v___x_1898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1899_, lean_object* v_vals_1900_, lean_object* v_i_1901_, lean_object* v_k_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(v_keys_1899_, v_vals_1900_, v_i_1901_, v_k_1902_);
lean_dec_ref(v_k_1902_);
lean_dec_ref(v_vals_1900_);
lean_dec_ref(v_keys_1899_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(lean_object* v_x_1904_, size_t v_x_1905_, lean_object* v_x_1906_){
_start:
{
if (lean_obj_tag(v_x_1904_) == 0)
{
lean_object* v_es_1907_; lean_object* v___x_1908_; size_t v___x_1909_; size_t v___x_1910_; lean_object* v_j_1911_; lean_object* v___x_1912_; 
v_es_1907_ = lean_ctor_get(v_x_1904_, 0);
v___x_1908_ = lean_box(2);
v___x_1909_ = ((size_t)31ULL);
v___x_1910_ = lean_usize_land(v_x_1905_, v___x_1909_);
v_j_1911_ = lean_usize_to_nat(v___x_1910_);
v___x_1912_ = lean_array_get_borrowed(v___x_1908_, v_es_1907_, v_j_1911_);
lean_dec(v_j_1911_);
switch(lean_obj_tag(v___x_1912_))
{
case 0:
{
lean_object* v_key_1913_; lean_object* v_val_1914_; uint8_t v___x_1915_; 
v_key_1913_ = lean_ctor_get(v___x_1912_, 0);
v_val_1914_ = lean_ctor_get(v___x_1912_, 1);
v___x_1915_ = lean_string_dec_eq(v_x_1906_, v_key_1913_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1916_; 
v___x_1916_ = lean_box(0);
return v___x_1916_;
}
else
{
lean_object* v___x_1917_; 
lean_inc(v_val_1914_);
v___x_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1917_, 0, v_val_1914_);
return v___x_1917_;
}
}
case 1:
{
lean_object* v_node_1918_; size_t v___x_1919_; size_t v___x_1920_; 
v_node_1918_ = lean_ctor_get(v___x_1912_, 0);
v___x_1919_ = ((size_t)5ULL);
v___x_1920_ = lean_usize_shift_right(v_x_1905_, v___x_1919_);
v_x_1904_ = v_node_1918_;
v_x_1905_ = v___x_1920_;
goto _start;
}
default: 
{
lean_object* v___x_1922_; 
v___x_1922_ = lean_box(0);
return v___x_1922_;
}
}
}
else
{
lean_object* v_ks_1923_; lean_object* v_vs_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v_ks_1923_ = lean_ctor_get(v_x_1904_, 0);
v_vs_1924_ = lean_ctor_get(v_x_1904_, 1);
v___x_1925_ = lean_unsigned_to_nat(0u);
v___x_1926_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(v_ks_1923_, v_vs_1924_, v___x_1925_, v_x_1906_);
return v___x_1926_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___boxed(lean_object* v_x_1927_, lean_object* v_x_1928_, lean_object* v_x_1929_){
_start:
{
size_t v_x_263__boxed_1930_; lean_object* v_res_1931_; 
v_x_263__boxed_1930_ = lean_unbox_usize(v_x_1928_);
lean_dec(v_x_1928_);
v_res_1931_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_1927_, v_x_263__boxed_1930_, v_x_1929_);
lean_dec_ref(v_x_1929_);
lean_dec_ref(v_x_1927_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(lean_object* v_x_1932_, lean_object* v_x_1933_){
_start:
{
uint64_t v___x_1934_; size_t v___x_1935_; lean_object* v___x_1936_; 
v___x_1934_ = lean_string_hash(v_x_1933_);
v___x_1935_ = lean_uint64_to_usize(v___x_1934_);
v___x_1936_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_1932_, v___x_1935_, v_x_1933_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg___boxed(lean_object* v_x_1937_, lean_object* v_x_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v_x_1937_, v_x_1938_);
lean_dec_ref(v_x_1938_);
lean_dec_ref(v_x_1937_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupLspRequestHandler(lean_object* v_method_1940_){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1942_ = l_Lean_Server_requestHandlers;
v___x_1943_ = lean_st_ref_get(v___x_1942_);
v___x_1944_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v___x_1943_, v_method_1940_);
lean_dec(v___x_1943_);
v___x_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupLspRequestHandler___boxed(lean_object* v_method_1946_, lean_object* v_a_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_Server_lookupLspRequestHandler(v_method_1946_);
lean_dec_ref(v_method_1946_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0(lean_object* v_00_u03b2_1949_, lean_object* v_x_1950_, lean_object* v_x_1951_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v_x_1950_, v_x_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___boxed(lean_object* v_00_u03b2_1953_, lean_object* v_x_1954_, lean_object* v_x_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0(v_00_u03b2_1953_, v_x_1954_, v_x_1955_);
lean_dec_ref(v_x_1955_);
lean_dec_ref(v_x_1954_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0(lean_object* v_00_u03b2_1957_, lean_object* v_x_1958_, size_t v_x_1959_, lean_object* v_x_1960_){
_start:
{
lean_object* v___x_1961_; 
v___x_1961_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_1958_, v_x_1959_, v_x_1960_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1962_, lean_object* v_x_1963_, lean_object* v_x_1964_, lean_object* v_x_1965_){
_start:
{
size_t v_x_341__boxed_1966_; lean_object* v_res_1967_; 
v_x_341__boxed_1966_ = lean_unbox_usize(v_x_1964_);
lean_dec(v_x_1964_);
v_res_1967_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0(v_00_u03b2_1962_, v_x_1963_, v_x_341__boxed_1966_, v_x_1965_);
lean_dec_ref(v_x_1965_);
lean_dec_ref(v_x_1963_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1968_, lean_object* v_keys_1969_, lean_object* v_vals_1970_, lean_object* v_heq_1971_, lean_object* v_i_1972_, lean_object* v_k_1973_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(v_keys_1969_, v_vals_1970_, v_i_1972_, v_k_1973_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1975_, lean_object* v_keys_1976_, lean_object* v_vals_1977_, lean_object* v_heq_1978_, lean_object* v_i_1979_, lean_object* v_k_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1(v_00_u03b2_1975_, v_keys_1976_, v_vals_1977_, v_heq_1978_, v_i_1979_, v_k_1980_);
lean_dec_ref(v_k_1980_);
lean_dec_ref(v_vals_1977_);
lean_dec_ref(v_keys_1976_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__0(lean_object* v_inst_1985_, lean_object* v_method_1986_, lean_object* v_x_1987_){
_start:
{
lean_object* v_response_1989_; 
if (lean_obj_tag(v_x_1987_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec_ref(v_inst_1985_);
v_a_2013_ = lean_ctor_get(v_x_1987_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v_x_1987_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v_x_1987_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v_x_1987_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
else
{
lean_object* v_a_2021_; lean_object* v_response_x3f_2022_; 
v_a_2021_ = lean_ctor_get(v_x_1987_, 0);
lean_inc(v_a_2021_);
lean_dec_ref_known(v_x_1987_, 1);
v_response_x3f_2022_ = lean_ctor_get(v_a_2021_, 0);
if (lean_obj_tag(v_response_x3f_2022_) == 0)
{
lean_object* v_serialized_2023_; lean_object* v___x_2024_; 
v_serialized_2023_ = lean_ctor_get(v_a_2021_, 1);
lean_inc_ref(v_serialized_2023_);
lean_dec(v_a_2021_);
v___x_2024_ = l_Lean_Json_parse(v_serialized_2023_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2038_; 
lean_dec_ref(v_inst_1985_);
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2027_ = v___x_2024_;
v_isShared_2028_ = v_isSharedCheck_2038_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2024_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2038_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2036_; 
v___x_2029_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__2));
v___x_2030_ = lean_string_append(v___x_2029_, v_method_1986_);
v___x_2031_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1));
v___x_2032_ = lean_string_append(v___x_2030_, v___x_2031_);
v___x_2033_ = lean_string_append(v___x_2032_, v_a_2025_);
lean_dec(v_a_2025_);
v___x_2034_ = l_Lean_Server_RequestError_internalError(v___x_2033_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 0, v___x_2034_);
v___x_2036_ = v___x_2027_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2034_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
else
{
lean_object* v_a_2039_; 
v_a_2039_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2024_, 1);
v_response_1989_ = v_a_2039_;
goto v___jp_1988_;
}
}
else
{
lean_object* v_val_2040_; 
lean_inc_ref(v_response_x3f_2022_);
lean_dec(v_a_2021_);
v_val_2040_ = lean_ctor_get(v_response_x3f_2022_, 0);
lean_inc(v_val_2040_);
lean_dec_ref_known(v_response_x3f_2022_, 1);
v_response_1989_ = v_val_2040_;
goto v___jp_1988_;
}
}
v___jp_1988_:
{
lean_object* v___x_1990_; 
v___x_1990_ = lean_apply_1(v_inst_1985_, v_response_1989_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2004_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1993_ = v___x_1990_;
v_isShared_1994_ = v_isSharedCheck_2004_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1990_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2004_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2002_; 
v___x_1995_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__0));
v___x_1996_ = lean_string_append(v___x_1995_, v_method_1986_);
v___x_1997_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1));
v___x_1998_ = lean_string_append(v___x_1996_, v___x_1997_);
v___x_1999_ = lean_string_append(v___x_1998_, v_a_1991_);
lean_dec(v_a_1991_);
v___x_2000_ = l_Lean_Server_RequestError_internalError(v___x_1999_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_2000_);
v___x_2002_ = v___x_1993_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_2000_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
v_a_2005_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_1990_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_1990_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__0___boxed(lean_object* v_inst_2041_, lean_object* v_method_2042_, lean_object* v_x_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__0(v_inst_2041_, v_method_2042_, v_x_2043_);
lean_dec_ref(v_method_2042_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__1(lean_object* v_inst_2045_, uint8_t v_a_2046_, lean_object* v_r_2047_){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2048_ = lean_apply_1(v_inst_2045_, v_r_2047_);
lean_inc(v___x_2048_);
v___x_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
v___x_2050_ = l_Lean_Json_compress(v___x_2048_);
v___x_2051_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2051_, 0, v___x_2049_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
lean_ctor_set_uint8(v___x_2051_, sizeof(void*)*2, v_a_2046_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__1___boxed(lean_object* v_inst_2052_, lean_object* v_a_2053_, lean_object* v_r_2054_){
_start:
{
uint8_t v_a_2455__boxed_2055_; lean_object* v_res_2056_; 
v_a_2455__boxed_2055_ = lean_unbox(v_a_2053_);
v_res_2056_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__1(v_inst_2052_, v_a_2455__boxed_2055_, v_r_2054_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__2(lean_object* v_handle_2057_, lean_object* v_inst_2058_, lean_object* v___f_2059_, lean_object* v_handler_2060_, lean_object* v___f_2061_, lean_object* v_j_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v___x_2065_; 
lean_inc_ref(v___y_2063_);
lean_inc(v_j_2062_);
v___x_2065_ = lean_apply_3(v_handle_2057_, v_j_2062_, v___y_2063_, lean_box(0));
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; lean_object* v___x_2067_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2066_);
lean_dec_ref_known(v___x_2065_, 1);
v___x_2067_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_2058_, v_j_2062_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_a_2068_);
lean_dec_ref_known(v___x_2067_, 1);
v___x_2069_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2059_, v_a_2066_);
lean_inc_ref(v___y_2063_);
v___x_2070_ = lean_apply_4(v_handler_2060_, v_a_2068_, v___x_2069_, v___y_2063_, lean_box(0));
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2080_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2073_ = v___x_2070_;
v_isShared_2074_ = v_isSharedCheck_2080_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2070_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2080_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2078_; 
v___x_2075_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_2075_, 0, lean_box(0));
lean_closure_set(v___x_2075_, 1, lean_box(0));
lean_closure_set(v___x_2075_, 2, lean_box(0));
lean_closure_set(v___x_2075_, 3, v___f_2061_);
v___x_2076_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___x_2075_, v_a_2071_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2076_);
v___x_2078_ = v___x_2073_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2076_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
lean_dec_ref(v___f_2061_);
v_a_2081_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2070_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2070_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec(v_a_2066_);
lean_dec_ref(v___f_2061_);
lean_dec_ref(v_handler_2060_);
lean_dec_ref(v___f_2059_);
v_a_2089_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2067_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2067_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
else
{
lean_dec(v_j_2062_);
lean_dec_ref(v___f_2061_);
lean_dec_ref(v_handler_2060_);
lean_dec_ref(v___f_2059_);
lean_dec_ref(v_inst_2058_);
return v___x_2065_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__2___boxed(lean_object* v_handle_2097_, lean_object* v_inst_2098_, lean_object* v___f_2099_, lean_object* v_handler_2100_, lean_object* v___f_2101_, lean_object* v_j_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__2(v_handle_2097_, v_inst_2098_, v___f_2099_, v_handler_2100_, v___f_2101_, v_j_2102_, v___y_2103_);
lean_dec_ref(v___y_2103_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg(lean_object* v_method_2108_, lean_object* v_inst_2109_, lean_object* v_inst_2110_, lean_object* v_inst_2111_, lean_object* v_handler_2112_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_Lean_initializing();
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2164_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2117_ = v___x_2114_;
v_isShared_2118_ = v_isSharedCheck_2164_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2114_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2164_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
uint8_t v___x_2119_; 
v___x_2119_ = lean_unbox(v_a_2115_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2126_; 
lean_dec(v_a_2115_);
lean_dec_ref(v_handler_2112_);
lean_dec_ref(v_inst_2111_);
lean_dec_ref(v_inst_2110_);
lean_dec_ref(v_inst_2109_);
v___x_2120_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__0));
v___x_2121_ = lean_string_append(v___x_2120_, v_method_2108_);
lean_dec_ref(v_method_2108_);
v___x_2122_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__1));
v___x_2123_ = lean_string_append(v___x_2121_, v___x_2122_);
v___x_2124_ = lean_mk_io_user_error(v___x_2123_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set_tag(v___x_2117_, 1);
lean_ctor_set(v___x_2117_, 0, v___x_2124_);
v___x_2126_ = v___x_2117_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
else
{
lean_object* v___x_2128_; lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2163_; 
lean_del_object(v___x_2117_);
v___x_2128_ = l_Lean_Server_lookupLspRequestHandler(v_method_2108_);
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2131_ = v___x_2128_;
v_isShared_2132_ = v_isSharedCheck_2163_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2128_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2163_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
if (lean_obj_tag(v_a_2129_) == 1)
{
lean_object* v_val_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v_fileSource_2136_; lean_object* v_handle_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2154_; 
v_val_2133_ = lean_ctor_get(v_a_2129_, 0);
lean_inc(v_val_2133_);
lean_dec_ref_known(v_a_2129_, 1);
v___x_2134_ = l_Lean_Server_requestHandlers;
v___x_2135_ = lean_st_ref_take(v___x_2134_);
v_fileSource_2136_ = lean_ctor_get(v_val_2133_, 0);
v_handle_2137_ = lean_ctor_get(v_val_2133_, 1);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_val_2133_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2139_ = v_val_2133_;
v_isShared_2140_ = v_isSharedCheck_2154_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_handle_2137_);
lean_inc(v_fileSource_2136_);
lean_dec(v_val_2133_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2154_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___f_2141_; lean_object* v___x_2142_; lean_object* v___f_2143_; lean_object* v___f_2144_; lean_object* v___f_2145_; lean_object* v___x_2147_; 
lean_inc_ref(v_method_2108_);
v___f_2141_ = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2141_, 0, v_inst_2110_);
lean_closure_set(v___f_2141_, 1, v_method_2108_);
v___x_2142_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___f_2143_ = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2143_, 0, v_inst_2111_);
lean_closure_set(v___f_2143_, 1, v_a_2115_);
v___f_2144_ = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2144_, 0, v_handle_2137_);
lean_closure_set(v___f_2144_, 1, v_inst_2109_);
lean_closure_set(v___f_2144_, 2, v___f_2141_);
lean_closure_set(v___f_2144_, 3, v_handler_2112_);
lean_closure_set(v___f_2144_, 4, v___f_2143_);
v___f_2145_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 1, v___f_2144_);
v___x_2147_ = v___x_2139_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_fileSource_2136_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v___f_2144_);
v___x_2147_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2151_; 
v___x_2148_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2145_, v___x_2142_, v___x_2135_, v_method_2108_, v___x_2147_);
v___x_2149_ = lean_st_ref_set(v___x_2134_, v___x_2148_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 0, v___x_2149_);
v___x_2151_ = v___x_2131_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2149_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2161_; 
lean_dec(v_a_2129_);
lean_dec(v_a_2115_);
lean_dec_ref(v_handler_2112_);
lean_dec_ref(v_inst_2111_);
lean_dec_ref(v_inst_2110_);
lean_dec_ref(v_inst_2109_);
v___x_2155_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__0));
v___x_2156_ = lean_string_append(v___x_2155_, v_method_2108_);
lean_dec_ref(v_method_2108_);
v___x_2157_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__1));
v___x_2158_ = lean_string_append(v___x_2156_, v___x_2157_);
v___x_2159_ = lean_mk_io_user_error(v___x_2158_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set_tag(v___x_2131_, 1);
lean_ctor_set(v___x_2131_, 0, v___x_2159_);
v___x_2161_ = v___x_2131_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_dec_ref(v_handler_2112_);
lean_dec_ref(v_inst_2111_);
lean_dec_ref(v_inst_2110_);
lean_dec_ref(v_inst_2109_);
lean_dec_ref(v_method_2108_);
v_a_2165_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2114_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2114_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___boxed(lean_object* v_method_2173_, lean_object* v_inst_2174_, lean_object* v_inst_2175_, lean_object* v_inst_2176_, lean_object* v_handler_2177_, lean_object* v_a_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l_Lean_Server_chainLspRequestHandler___redArg(v_method_2173_, v_inst_2174_, v_inst_2175_, v_inst_2176_, v_handler_2177_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler(lean_object* v_method_2180_, lean_object* v_paramType_2181_, lean_object* v_inst_2182_, lean_object* v_respType_2183_, lean_object* v_inst_2184_, lean_object* v_inst_2185_, lean_object* v_handler_2186_){
_start:
{
lean_object* v___x_2188_; 
v___x_2188_ = l_Lean_Server_chainLspRequestHandler___redArg(v_method_2180_, v_inst_2182_, v_inst_2184_, v_inst_2185_, v_handler_2186_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___boxed(lean_object* v_method_2189_, lean_object* v_paramType_2190_, lean_object* v_inst_2191_, lean_object* v_respType_2192_, lean_object* v_inst_2193_, lean_object* v_inst_2194_, lean_object* v_handler_2195_, lean_object* v_a_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l_Lean_Server_chainLspRequestHandler(v_method_2189_, v_paramType_2190_, v_inst_2191_, v_respType_2192_, v_inst_2193_, v_inst_2194_, v_handler_2195_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorIdx(lean_object* v_x_2198_){
_start:
{
if (lean_obj_tag(v_x_2198_) == 0)
{
lean_object* v___x_2199_; 
v___x_2199_ = lean_unsigned_to_nat(0u);
return v___x_2199_;
}
else
{
lean_object* v___x_2200_; 
v___x_2200_ = lean_unsigned_to_nat(1u);
return v___x_2200_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorIdx___boxed(lean_object* v_x_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_Server_RequestHandlerCompleteness_ctorIdx(v_x_2201_);
lean_dec(v_x_2201_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(lean_object* v_t_2203_, lean_object* v_k_2204_){
_start:
{
if (lean_obj_tag(v_t_2203_) == 0)
{
return v_k_2204_;
}
else
{
lean_object* v_refreshMethod_2205_; lean_object* v_refreshIntervalMs_2206_; lean_object* v___x_2207_; 
v_refreshMethod_2205_ = lean_ctor_get(v_t_2203_, 0);
lean_inc_ref(v_refreshMethod_2205_);
v_refreshIntervalMs_2206_ = lean_ctor_get(v_t_2203_, 1);
lean_inc(v_refreshIntervalMs_2206_);
lean_dec_ref_known(v_t_2203_, 2);
v___x_2207_ = lean_apply_2(v_k_2204_, v_refreshMethod_2205_, v_refreshIntervalMs_2206_);
return v___x_2207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim(lean_object* v_motive_2208_, lean_object* v_ctorIdx_2209_, lean_object* v_t_2210_, lean_object* v_h_2211_, lean_object* v_k_2212_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_2210_, v_k_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim___boxed(lean_object* v_motive_2214_, lean_object* v_ctorIdx_2215_, lean_object* v_t_2216_, lean_object* v_h_2217_, lean_object* v_k_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim(v_motive_2214_, v_ctorIdx_2215_, v_t_2216_, v_h_2217_, v_k_2218_);
lean_dec(v_ctorIdx_2215_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_complete_elim___redArg(lean_object* v_t_2220_, lean_object* v_complete_2221_){
_start:
{
lean_object* v___x_2222_; 
v___x_2222_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_2220_, v_complete_2221_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_complete_elim(lean_object* v_motive_2223_, lean_object* v_t_2224_, lean_object* v_h_2225_, lean_object* v_complete_2226_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_2224_, v_complete_2226_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_partial_elim___redArg(lean_object* v_t_2228_, lean_object* v_partial_2229_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_2228_, v_partial_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_partial_elim(lean_object* v_motive_2231_, lean_object* v_t_2232_, lean_object* v_h_2233_, lean_object* v_partial_2234_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_2232_, v_partial_2234_);
return v___x_2235_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2236_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_);
v___x_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2240_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_);
v___x_2241_ = lean_st_mk_ref(v___x_2240_);
v___x_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2____boxed(lean_object* v_a_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_();
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(lean_object* v_method_2246_, lean_object* v_state_2247_, lean_object* v_inst_2248_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_state_2247_, v_inst_2248_);
if (lean_obj_tag(v___x_2250_) == 1)
{
lean_object* v_val_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
v_val_2251_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2250_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_val_2251_);
lean_dec(v___x_2250_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
lean_ctor_set_tag(v___x_2253_, 0);
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_val_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
else
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
lean_dec(v___x_2250_);
v___x_2259_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0));
v___x_2260_ = lean_string_append(v___x_2259_, v_method_2246_);
v___x_2261_ = l_Lean_Server_RequestError_internalError(v___x_2260_);
v___x_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
return v___x_2262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___boxed(lean_object* v_method_2263_, lean_object* v_state_2264_, lean_object* v_inst_2265_, lean_object* v_a_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_2263_, v_state_2264_, v_inst_2265_);
lean_dec(v_inst_2265_);
lean_dec(v_state_2264_);
lean_dec_ref(v_method_2263_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(lean_object* v_method_2268_, lean_object* v_state_2269_, lean_object* v_stateType_2270_, lean_object* v_inst_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v___x_2274_; 
v___x_2274_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_2268_, v_state_2269_, v_inst_2271_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___boxed(lean_object* v_method_2275_, lean_object* v_state_2276_, lean_object* v_stateType_2277_, lean_object* v_inst_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_2275_, v_state_2276_, v_stateType_2277_, v_inst_2278_, v_a_2279_);
lean_dec_ref(v_a_2279_);
lean_dec(v_inst_2278_);
lean_dec(v_state_2276_);
lean_dec_ref(v_method_2275_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(lean_object* v_method_2282_, lean_object* v_state_2283_, lean_object* v_inst_2284_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_state_2283_, v_inst_2284_);
if (lean_obj_tag(v___x_2286_) == 1)
{
lean_object* v_val_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
v_val_2287_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2286_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_val_2287_);
lean_dec(v___x_2286_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2292_; 
if (v_isShared_2290_ == 0)
{
lean_ctor_set_tag(v___x_2289_, 0);
v___x_2292_ = v___x_2289_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_val_2287_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
else
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
lean_dec(v___x_2286_);
v___x_2295_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0));
v___x_2296_ = lean_string_append(v___x_2295_, v_method_2282_);
v___x_2297_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
v___x_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
return v___x_2298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg___boxed(lean_object* v_method_2299_, lean_object* v_state_2300_, lean_object* v_inst_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(v_method_2299_, v_state_2300_, v_inst_2301_);
lean_dec(v_inst_2301_);
lean_dec(v_state_2300_);
lean_dec_ref(v_method_2299_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21(lean_object* v_method_2304_, lean_object* v_state_2305_, lean_object* v_stateType_2306_, lean_object* v_inst_2307_){
_start:
{
lean_object* v___x_2309_; 
v___x_2309_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(v_method_2304_, v_state_2305_, v_inst_2307_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___boxed(lean_object* v_method_2310_, lean_object* v_state_2311_, lean_object* v_stateType_2312_, lean_object* v_inst_2313_, lean_object* v_a_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21(v_method_2310_, v_state_2311_, v_stateType_2312_, v_inst_2313_);
lean_dec(v_inst_2313_);
lean_dec(v_state_2311_);
lean_dec_ref(v_method_2310_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1(lean_object* v_inst_2316_, lean_object* v_method_2317_, lean_object* v_inst_2318_, lean_object* v_handler_2319_, lean_object* v_inst_2320_, lean_object* v_param_2321_, lean_object* v_state_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v___x_2325_; 
v___x_2325_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_2316_, v_param_2321_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2327_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2326_);
lean_dec_ref_known(v___x_2325_, 1);
v___x_2327_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_2317_, v_state_2322_, v_inst_2318_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; lean_object* v___x_2329_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2328_);
lean_dec_ref_known(v___x_2327_, 1);
lean_inc_ref(v___y_2323_);
v___x_2329_ = lean_apply_4(v_handler_2319_, v_a_2326_, v_a_2328_, v___y_2323_, lean_box(0));
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2353_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2332_ = v___x_2329_;
v_isShared_2333_ = v_isSharedCheck_2353_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2353_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v_fst_2334_; lean_object* v_snd_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2352_; 
v_fst_2334_ = lean_ctor_get(v_a_2330_, 0);
v_snd_2335_ = lean_ctor_get(v_a_2330_, 1);
v_isSharedCheck_2352_ = !lean_is_exclusive(v_a_2330_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2337_ = v_a_2330_;
v_isShared_2338_ = v_isSharedCheck_2352_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_snd_2335_);
lean_inc(v_fst_2334_);
lean_dec(v_a_2330_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2352_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v_response_2339_; uint8_t v_isComplete_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2346_; 
v_response_2339_ = lean_ctor_get(v_fst_2334_, 0);
lean_inc(v_response_2339_);
v_isComplete_2340_ = lean_ctor_get_uint8(v_fst_2334_, sizeof(void*)*1);
lean_dec(v_fst_2334_);
v___x_2341_ = lean_apply_1(v_inst_2320_, v_response_2339_);
lean_inc(v___x_2341_);
v___x_2342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2341_);
v___x_2343_ = l_Lean_Json_compress(v___x_2341_);
v___x_2344_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2344_, 0, v___x_2342_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
lean_ctor_set_uint8(v___x_2344_, sizeof(void*)*2, v_isComplete_2340_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 0, v_inst_2318_);
v___x_2346_ = v___x_2337_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_inst_2318_);
lean_ctor_set(v_reuseFailAlloc_2351_, 1, v_snd_2335_);
v___x_2346_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
lean_object* v___x_2347_; lean_object* v___x_2349_; 
v___x_2347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2344_);
lean_ctor_set(v___x_2347_, 1, v___x_2346_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v___x_2347_);
v___x_2349_ = v___x_2332_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
lean_dec_ref(v_inst_2320_);
lean_dec(v_inst_2318_);
v_a_2354_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2329_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2329_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_dec(v_a_2326_);
lean_dec_ref(v_inst_2320_);
lean_dec_ref(v_handler_2319_);
lean_dec(v_inst_2318_);
v_a_2362_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2327_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2327_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
else
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2377_; 
lean_dec_ref(v_inst_2320_);
lean_dec_ref(v_handler_2319_);
lean_dec(v_inst_2318_);
v_a_2370_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2372_ = v___x_2325_;
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2325_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2370_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1___boxed(lean_object* v_inst_2378_, lean_object* v_method_2379_, lean_object* v_inst_2380_, lean_object* v_handler_2381_, lean_object* v_inst_2382_, lean_object* v_param_2383_, lean_object* v_state_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1(v_inst_2378_, v_method_2379_, v_inst_2380_, v_handler_2381_, v_inst_2382_, v_param_2383_, v_state_2384_, v___y_2385_);
lean_dec_ref(v___y_2385_);
lean_dec(v_state_2384_);
lean_dec_ref(v_method_2379_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0(lean_object* v_method_2388_, lean_object* v_inst_2389_, lean_object* v_onDidChange_2390_, lean_object* v_param_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_2388_, v___y_2392_, v_inst_2389_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; lean_object* v___x_2397_; 
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_a_2396_);
lean_dec_ref_known(v___x_2395_, 1);
lean_inc_ref(v___y_2393_);
v___x_2397_ = lean_apply_4(v_onDidChange_2390_, v_param_2391_, v_a_2396_, v___y_2393_, lean_box(0));
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2416_; 
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2400_ = v___x_2397_;
v_isShared_2401_ = v_isSharedCheck_2416_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2397_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2416_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v_snd_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2414_; 
v_snd_2402_ = lean_ctor_get(v_a_2398_, 1);
v_isSharedCheck_2414_ = !lean_is_exclusive(v_a_2398_);
if (v_isSharedCheck_2414_ == 0)
{
lean_object* v_unused_2415_; 
v_unused_2415_ = lean_ctor_get(v_a_2398_, 0);
lean_dec(v_unused_2415_);
v___x_2404_ = v_a_2398_;
v_isShared_2405_ = v_isSharedCheck_2414_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_snd_2402_);
lean_dec(v_a_2398_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2414_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 0, v_inst_2389_);
v___x_2407_ = v___x_2404_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_inst_2389_);
lean_ctor_set(v_reuseFailAlloc_2413_, 1, v_snd_2402_);
v___x_2407_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2411_; 
v___x_2408_ = lean_box(0);
v___x_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
lean_ctor_set(v___x_2409_, 1, v___x_2407_);
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 0, v___x_2409_);
v___x_2411_ = v___x_2400_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
lean_dec(v_inst_2389_);
v_a_2417_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2397_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2397_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2417_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
lean_dec_ref(v_param_2391_);
lean_dec_ref(v_onDidChange_2390_);
lean_dec(v_inst_2389_);
v_a_2425_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___x_2395_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2395_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object* v_method_2433_, lean_object* v_inst_2434_, lean_object* v_onDidChange_2435_, lean_object* v_param_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0(v_method_2433_, v_inst_2434_, v_onDidChange_2435_, v_param_2436_, v___y_2437_, v___y_2438_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v_method_2433_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2(lean_object* v___x_2441_, lean_object* v_x_2442_){
_start:
{
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2___boxed(lean_object* v___x_2443_, lean_object* v_x_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2(v___x_2443_, v_x_2444_);
lean_dec_ref(v_x_2444_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3(lean_object* v___x_2446_, lean_object* v_x_2447_){
_start:
{
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3___boxed(lean_object* v___x_2448_, lean_object* v_x_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3(v___x_2448_, v_x_2449_);
lean_dec_ref(v_x_2449_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4(lean_object* v_val_2451_, lean_object* v___f_2452_, lean_object* v_param_2453_, lean_object* v_x_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = lean_st_ref_get(v_val_2451_);
lean_inc_ref(v___y_2455_);
v___x_2458_ = lean_apply_4(v___f_2452_, v_param_2453_, v___x_2457_, v___y_2455_, lean_box(0));
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2469_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2461_ = v___x_2458_;
v_isShared_2462_ = v_isSharedCheck_2469_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2458_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2469_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v_fst_2463_; lean_object* v_snd_2464_; lean_object* v___x_2465_; lean_object* v___x_2467_; 
v_fst_2463_ = lean_ctor_get(v_a_2459_, 0);
lean_inc(v_fst_2463_);
v_snd_2464_ = lean_ctor_get(v_a_2459_, 1);
lean_inc(v_snd_2464_);
lean_dec(v_a_2459_);
v___x_2465_ = lean_st_ref_set(v_val_2451_, v_snd_2464_);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v_fst_2463_);
v___x_2467_ = v___x_2461_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_fst_2463_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
v_a_2470_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2458_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2458_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4___boxed(lean_object* v_val_2478_, lean_object* v___f_2479_, lean_object* v_param_2480_, lean_object* v_x_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4(v_val_2478_, v___f_2479_, v_param_2480_, v_x_2481_, v___y_2482_);
lean_dec_ref(v___y_2482_);
lean_dec(v_val_2478_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5(lean_object* v___f_2485_, lean_object* v___f_2486_, lean_object* v_lastTask_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v___x_2491_; lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2501_; 
v___x_2491_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_lastTask_2487_, v___f_2485_, v___y_2489_);
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2494_ = v___x_2491_;
v_isShared_2495_ = v_isSharedCheck_2501_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2491_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2501_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2499_; 
lean_inc(v_a_2492_);
v___x_2496_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2486_, v_a_2492_);
v___x_2497_ = lean_st_ref_set(v___y_2488_, v___x_2496_);
if (v_isShared_2495_ == 0)
{
v___x_2499_ = v___x_2494_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2492_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5___boxed(lean_object* v___f_2502_, lean_object* v___f_2503_, lean_object* v_lastTask_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5(v___f_2502_, v___f_2503_, v_lastTask_2504_, v___y_2505_, v___y_2506_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6(lean_object* v_val_2509_, lean_object* v___f_2510_, lean_object* v___f_2511_, lean_object* v___f_2512_, lean_object* v___x_2513_, lean_object* v___f_2514_, lean_object* v___f_2515_, lean_object* v_val_2516_, lean_object* v_param_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v___f_2520_; lean_object* v___f_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_6410__overap_2524_; lean_object* v___x_2525_; 
v___f_2520_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2520_, 0, v_val_2509_);
lean_closure_set(v___f_2520_, 1, v___f_2510_);
lean_closure_set(v___f_2520_, 2, v_param_2517_);
v___f_2521_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5___boxed), 6, 2);
lean_closure_set(v___f_2521_, 0, v___f_2520_);
lean_closure_set(v___f_2521_, 1, v___f_2511_);
v___x_2522_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_2522_, 0, lean_box(0));
lean_closure_set(v___x_2522_, 1, lean_box(0));
lean_closure_set(v___x_2522_, 2, lean_box(0));
lean_closure_set(v___x_2522_, 3, v___f_2512_);
lean_inc_ref(v___x_2513_);
v___x_2523_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_2523_, 0, lean_box(0));
lean_closure_set(v___x_2523_, 1, lean_box(0));
lean_closure_set(v___x_2523_, 2, lean_box(0));
lean_closure_set(v___x_2523_, 3, v___x_2513_);
lean_closure_set(v___x_2523_, 4, lean_box(0));
lean_closure_set(v___x_2523_, 5, lean_box(0));
lean_closure_set(v___x_2523_, 6, v___x_2522_);
lean_closure_set(v___x_2523_, 7, v___f_2521_);
v___x_6410__overap_2524_ = l_Std_Mutex_atomically___redArg(v___x_2513_, v___f_2514_, v___f_2515_, v_val_2516_, v___x_2523_);
lean_inc_ref(v___y_2518_);
v___x_2525_ = lean_apply_2(v___x_6410__overap_2524_, v___y_2518_, lean_box(0));
return v___x_2525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6___boxed(lean_object* v_val_2526_, lean_object* v___f_2527_, lean_object* v___f_2528_, lean_object* v___f_2529_, lean_object* v___x_2530_, lean_object* v___f_2531_, lean_object* v___f_2532_, lean_object* v_val_2533_, lean_object* v_param_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6(v_val_2526_, v___f_2527_, v___f_2528_, v___f_2529_, v___x_2530_, v___f_2531_, v___f_2532_, v_val_2533_, v_param_2534_, v___y_2535_);
lean_dec_ref(v___y_2535_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7(lean_object* v_val_2538_, lean_object* v___f_2539_, lean_object* v_param_2540_, lean_object* v_x_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2544_ = lean_st_ref_get(v_val_2538_);
lean_inc_ref(v___y_2542_);
v___x_2545_ = lean_apply_4(v___f_2539_, v_param_2540_, v___x_2544_, v___y_2542_, lean_box(0));
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2555_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2548_ = v___x_2545_;
v_isShared_2549_ = v_isSharedCheck_2555_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2545_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2555_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v_snd_2550_; lean_object* v___x_2551_; lean_object* v___x_2553_; 
v_snd_2550_ = lean_ctor_get(v_a_2546_, 1);
lean_inc(v_snd_2550_);
lean_dec(v_a_2546_);
v___x_2551_ = lean_st_ref_set(v_val_2538_, v_snd_2550_);
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 0, v___x_2551_);
v___x_2553_ = v___x_2548_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2551_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
v_a_2556_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2545_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2545_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7___boxed(lean_object* v_val_2564_, lean_object* v___f_2565_, lean_object* v_param_2566_, lean_object* v_x_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7(v_val_2564_, v___f_2565_, v_param_2566_, v_x_2567_, v___y_2568_);
lean_dec_ref(v___y_2568_);
lean_dec(v_val_2564_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8(lean_object* v___f_2571_, lean_object* v___f_2572_, lean_object* v_lastTask_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v___x_2577_; lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2587_; 
v___x_2577_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_lastTask_2573_, v___f_2571_, v___y_2575_);
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2580_ = v___x_2577_;
v_isShared_2581_ = v_isSharedCheck_2587_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2587_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2585_; 
v___x_2582_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2572_, v_a_2578_);
v___x_2583_ = lean_st_ref_set(v___y_2574_, v___x_2582_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2583_);
v___x_2585_ = v___x_2580_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2583_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8___boxed(lean_object* v___f_2588_, lean_object* v___f_2589_, lean_object* v_lastTask_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8(v___f_2588_, v___f_2589_, v_lastTask_2590_, v___y_2591_, v___y_2592_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9(lean_object* v_val_2595_, lean_object* v___f_2596_, lean_object* v___f_2597_, lean_object* v___f_2598_, lean_object* v___x_2599_, lean_object* v___f_2600_, lean_object* v___f_2601_, lean_object* v_val_2602_, lean_object* v_param_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v___f_2606_; lean_object* v___f_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_6461__overap_2610_; lean_object* v___x_2611_; 
v___f_2606_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7___boxed), 6, 3);
lean_closure_set(v___f_2606_, 0, v_val_2595_);
lean_closure_set(v___f_2606_, 1, v___f_2596_);
lean_closure_set(v___f_2606_, 2, v_param_2603_);
v___f_2607_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8___boxed), 6, 2);
lean_closure_set(v___f_2607_, 0, v___f_2606_);
lean_closure_set(v___f_2607_, 1, v___f_2597_);
v___x_2608_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_2608_, 0, lean_box(0));
lean_closure_set(v___x_2608_, 1, lean_box(0));
lean_closure_set(v___x_2608_, 2, lean_box(0));
lean_closure_set(v___x_2608_, 3, v___f_2598_);
lean_inc_ref(v___x_2599_);
v___x_2609_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_2609_, 0, lean_box(0));
lean_closure_set(v___x_2609_, 1, lean_box(0));
lean_closure_set(v___x_2609_, 2, lean_box(0));
lean_closure_set(v___x_2609_, 3, v___x_2599_);
lean_closure_set(v___x_2609_, 4, lean_box(0));
lean_closure_set(v___x_2609_, 5, lean_box(0));
lean_closure_set(v___x_2609_, 6, v___x_2608_);
lean_closure_set(v___x_2609_, 7, v___f_2607_);
v___x_6461__overap_2610_ = l_Std_Mutex_atomically___redArg(v___x_2599_, v___f_2600_, v___f_2601_, v_val_2602_, v___x_2609_);
lean_inc_ref(v___y_2604_);
v___x_2611_ = lean_apply_2(v___x_6461__overap_2610_, v___y_2604_, lean_box(0));
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9___boxed(lean_object* v_val_2612_, lean_object* v___f_2613_, lean_object* v___f_2614_, lean_object* v___f_2615_, lean_object* v___x_2616_, lean_object* v___f_2617_, lean_object* v___f_2618_, lean_object* v_val_2619_, lean_object* v_param_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9(v_val_2612_, v___f_2613_, v___f_2614_, v___f_2615_, v___x_2616_, v___f_2617_, v___f_2618_, v_val_2619_, v_param_2620_, v___y_2621_);
lean_dec_ref(v___y_2621_);
return v_res_2623_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0(void){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = l_instMonadEIO(lean_box(0));
return v___x_2624_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1(void){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2625_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0);
v___x_2626_ = l_ReaderT_instMonad___redArg(v___x_2625_);
return v___x_2626_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3(void){
_start:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2628_ = lean_box(0);
v___x_2629_ = lean_task_pure(v___x_2628_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(lean_object* v_method_2655_, lean_object* v_completeness_2656_, lean_object* v_inst_2657_, lean_object* v_inst_2658_, lean_object* v_inst_2659_, lean_object* v_inst_2660_, lean_object* v_initState_2661_, lean_object* v_handler_2662_, lean_object* v_onDidChange_2663_){
_start:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2665_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1);
v___x_2666_ = l_Lean_initializing();
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2704_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2669_ = v___x_2666_;
v_isShared_2670_ = v_isSharedCheck_2704_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2666_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2704_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
uint8_t v___x_2671_; 
v___x_2671_ = lean_unbox(v_a_2667_);
lean_dec(v_a_2667_);
if (v___x_2671_ == 0)
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2678_; 
lean_dec_ref(v_onDidChange_2663_);
lean_dec_ref(v_handler_2662_);
lean_dec(v_initState_2661_);
lean_dec(v_inst_2660_);
lean_dec_ref(v_inst_2659_);
lean_dec_ref(v_inst_2658_);
lean_dec_ref(v_inst_2657_);
lean_dec(v_completeness_2656_);
v___x_2672_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2));
v___x_2673_ = lean_string_append(v___x_2672_, v_method_2655_);
lean_dec_ref(v_method_2655_);
v___x_2674_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__1));
v___x_2675_ = lean_string_append(v___x_2673_, v___x_2674_);
v___x_2676_ = lean_mk_io_user_error(v___x_2675_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set_tag(v___x_2669_, 1);
lean_ctor_set(v___x_2669_, 0, v___x_2676_);
v___x_2678_ = v___x_2669_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2676_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
else
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___f_2686_; lean_object* v___f_2687_; lean_object* v___f_2688_; lean_object* v___f_2689_; lean_object* v___f_2690_; lean_object* v___f_2691_; lean_object* v___x_2692_; lean_object* v___f_2693_; lean_object* v___f_2694_; lean_object* v___f_2695_; lean_object* v___f_2696_; lean_object* v___f_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2702_; 
v___x_2680_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3);
v___x_2681_ = l_Std_Mutex_new___redArg(v___x_2680_);
lean_inc_n(v_inst_2660_, 2);
v___x_2682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2682_, 0, v_inst_2660_);
lean_ctor_set(v___x_2682_, 1, v_initState_2661_);
lean_inc_ref(v___x_2682_);
v___x_2683_ = lean_st_mk_ref(v___x_2682_);
v___x_2684_ = l_Lean_Server_statefulRequestHandlers;
v___x_2685_ = lean_st_ref_take(v___x_2684_);
v___f_2686_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__7));
lean_inc_ref(v_inst_2657_);
v___f_2687_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2687_, 0, v_inst_2657_);
lean_closure_set(v___f_2687_, 1, v_inst_2658_);
lean_inc_ref_n(v_method_2655_, 2);
v___f_2688_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1___boxed), 9, 5);
lean_closure_set(v___f_2688_, 0, v_inst_2657_);
lean_closure_set(v___f_2688_, 1, v_method_2655_);
lean_closure_set(v___f_2688_, 2, v_inst_2660_);
lean_closure_set(v___f_2688_, 3, v_handler_2662_);
lean_closure_set(v___f_2688_, 4, v_inst_2659_);
v___f_2689_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0___boxed), 7, 3);
lean_closure_set(v___f_2689_, 0, v_method_2655_);
lean_closure_set(v___f_2689_, 1, v_inst_2660_);
lean_closure_set(v___f_2689_, 2, v_onDidChange_2663_);
v___f_2690_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__9));
v___f_2691_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__13));
v___x_2692_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___f_2693_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__14));
v___f_2694_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15));
lean_inc_ref_n(v___x_2681_, 2);
lean_inc_ref(v___f_2688_);
lean_inc_n(v___x_2683_, 2);
v___f_2695_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6___boxed), 11, 8);
lean_closure_set(v___f_2695_, 0, v___x_2683_);
lean_closure_set(v___f_2695_, 1, v___f_2688_);
lean_closure_set(v___f_2695_, 2, v___f_2693_);
lean_closure_set(v___f_2695_, 3, v___f_2691_);
lean_closure_set(v___f_2695_, 4, v___x_2665_);
lean_closure_set(v___f_2695_, 5, v___f_2686_);
lean_closure_set(v___f_2695_, 6, v___f_2690_);
lean_closure_set(v___f_2695_, 7, v___x_2681_);
lean_inc_ref(v___f_2689_);
v___f_2696_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9___boxed), 11, 8);
lean_closure_set(v___f_2696_, 0, v___x_2683_);
lean_closure_set(v___f_2696_, 1, v___f_2689_);
lean_closure_set(v___f_2696_, 2, v___f_2694_);
lean_closure_set(v___f_2696_, 3, v___f_2691_);
lean_closure_set(v___f_2696_, 4, v___x_2665_);
lean_closure_set(v___f_2696_, 5, v___f_2686_);
lean_closure_set(v___f_2696_, 6, v___f_2690_);
lean_closure_set(v___f_2696_, 7, v___x_2681_);
v___f_2697_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
v___x_2698_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2698_, 0, v___f_2687_);
lean_ctor_set(v___x_2698_, 1, v___f_2688_);
lean_ctor_set(v___x_2698_, 2, v___f_2695_);
lean_ctor_set(v___x_2698_, 3, v___f_2689_);
lean_ctor_set(v___x_2698_, 4, v___f_2696_);
lean_ctor_set(v___x_2698_, 5, v___x_2681_);
lean_ctor_set(v___x_2698_, 6, v___x_2682_);
lean_ctor_set(v___x_2698_, 7, v___x_2683_);
lean_ctor_set(v___x_2698_, 8, v_completeness_2656_);
v___x_2699_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2697_, v___x_2692_, v___x_2685_, v_method_2655_, v___x_2698_);
v___x_2700_ = lean_st_ref_set(v___x_2684_, v___x_2699_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v___x_2700_);
v___x_2702_ = v___x_2669_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2700_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
else
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2712_; 
lean_dec_ref(v_onDidChange_2663_);
lean_dec_ref(v_handler_2662_);
lean_dec(v_initState_2661_);
lean_dec(v_inst_2660_);
lean_dec_ref(v_inst_2659_);
lean_dec_ref(v_inst_2658_);
lean_dec_ref(v_inst_2657_);
lean_dec(v_completeness_2656_);
lean_dec_ref(v_method_2655_);
v_a_2705_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2707_ = v___x_2666_;
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2666_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2710_; 
if (v_isShared_2708_ == 0)
{
v___x_2710_ = v___x_2707_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_a_2705_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2713_, lean_object* v_completeness_2714_, lean_object* v_inst_2715_, lean_object* v_inst_2716_, lean_object* v_inst_2717_, lean_object* v_inst_2718_, lean_object* v_initState_2719_, lean_object* v_handler_2720_, lean_object* v_onDidChange_2721_, lean_object* v_a_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2713_, v_completeness_2714_, v_inst_2715_, v_inst_2716_, v_inst_2717_, v_inst_2718_, v_initState_2719_, v_handler_2720_, v_onDidChange_2721_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(lean_object* v_method_2724_, lean_object* v_completeness_2725_, lean_object* v_paramType_2726_, lean_object* v_inst_2727_, lean_object* v_inst_2728_, lean_object* v_respType_2729_, lean_object* v_inst_2730_, lean_object* v_stateType_2731_, lean_object* v_inst_2732_, lean_object* v_initState_2733_, lean_object* v_handler_2734_, lean_object* v_onDidChange_2735_){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2724_, v_completeness_2725_, v_inst_2727_, v_inst_2728_, v_inst_2730_, v_inst_2732_, v_initState_2733_, v_handler_2734_, v_onDidChange_2735_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___boxed(lean_object* v_method_2738_, lean_object* v_completeness_2739_, lean_object* v_paramType_2740_, lean_object* v_inst_2741_, lean_object* v_inst_2742_, lean_object* v_respType_2743_, lean_object* v_inst_2744_, lean_object* v_stateType_2745_, lean_object* v_inst_2746_, lean_object* v_initState_2747_, lean_object* v_handler_2748_, lean_object* v_onDidChange_2749_, lean_object* v_a_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(v_method_2738_, v_completeness_2739_, v_paramType_2740_, v_inst_2741_, v_inst_2742_, v_respType_2743_, v_inst_2744_, v_stateType_2745_, v_inst_2746_, v_initState_2747_, v_handler_2748_, v_onDidChange_2749_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(lean_object* v_method_2752_, lean_object* v_completeness_2753_, lean_object* v_inst_2754_, lean_object* v_inst_2755_, lean_object* v_inst_2756_, lean_object* v_inst_2757_, lean_object* v_initState_2758_, lean_object* v_handler_2759_, lean_object* v_onDidChange_2760_){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___f_2765_; uint8_t v___x_2766_; 
v___x_2762_ = l_Lean_Server_requestHandlers;
v___x_2763_ = lean_st_ref_get(v___x_2762_);
v___x_2764_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___f_2765_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
lean_inc_ref(v_method_2752_);
v___x_2766_ = l_Lean_PersistentHashMap_contains___redArg(v___f_2765_, v___x_2764_, v___x_2763_, v_method_2752_);
if (v___x_2766_ == 0)
{
lean_object* v___x_2767_; 
v___x_2767_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2752_, v_completeness_2753_, v_inst_2754_, v_inst_2755_, v_inst_2756_, v_inst_2757_, v_initState_2758_, v_handler_2759_, v_onDidChange_2760_);
return v___x_2767_;
}
else
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
lean_dec_ref(v_onDidChange_2760_);
lean_dec_ref(v_handler_2759_);
lean_dec(v_initState_2758_);
lean_dec(v_inst_2757_);
lean_dec_ref(v_inst_2756_);
lean_dec_ref(v_inst_2755_);
lean_dec_ref(v_inst_2754_);
lean_dec(v_completeness_2753_);
v___x_2768_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2));
v___x_2769_ = lean_string_append(v___x_2768_, v_method_2752_);
lean_dec_ref(v_method_2752_);
v___x_2770_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__4));
v___x_2771_ = lean_string_append(v___x_2769_, v___x_2770_);
v___x_2772_ = lean_mk_io_user_error(v___x_2771_);
v___x_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2772_);
return v___x_2773_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2774_, lean_object* v_completeness_2775_, lean_object* v_inst_2776_, lean_object* v_inst_2777_, lean_object* v_inst_2778_, lean_object* v_inst_2779_, lean_object* v_initState_2780_, lean_object* v_handler_2781_, lean_object* v_onDidChange_2782_, lean_object* v_a_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2774_, v_completeness_2775_, v_inst_2776_, v_inst_2777_, v_inst_2778_, v_inst_2779_, v_initState_2780_, v_handler_2781_, v_onDidChange_2782_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler(lean_object* v_method_2785_, lean_object* v_completeness_2786_, lean_object* v_paramType_2787_, lean_object* v_inst_2788_, lean_object* v_inst_2789_, lean_object* v_respType_2790_, lean_object* v_inst_2791_, lean_object* v_stateType_2792_, lean_object* v_inst_2793_, lean_object* v_initState_2794_, lean_object* v_handler_2795_, lean_object* v_onDidChange_2796_){
_start:
{
lean_object* v___x_2798_; 
v___x_2798_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2785_, v_completeness_2786_, v_inst_2788_, v_inst_2789_, v_inst_2791_, v_inst_2793_, v_initState_2794_, v_handler_2795_, v_onDidChange_2796_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___boxed(lean_object* v_method_2799_, lean_object* v_completeness_2800_, lean_object* v_paramType_2801_, lean_object* v_inst_2802_, lean_object* v_inst_2803_, lean_object* v_respType_2804_, lean_object* v_inst_2805_, lean_object* v_stateType_2806_, lean_object* v_inst_2807_, lean_object* v_initState_2808_, lean_object* v_handler_2809_, lean_object* v_onDidChange_2810_, lean_object* v_a_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler(v_method_2799_, v_completeness_2800_, v_paramType_2801_, v_inst_2802_, v_inst_2803_, v_respType_2804_, v_inst_2805_, v_stateType_2806_, v_inst_2807_, v_initState_2808_, v_handler_2809_, v_onDidChange_2810_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0(lean_object* v_handler_2813_, lean_object* v_p_2814_, lean_object* v_s_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v___x_2818_; 
lean_inc_ref(v___y_2816_);
v___x_2818_ = lean_apply_4(v_handler_2813_, v_p_2814_, v_s_2815_, v___y_2816_, lean_box(0));
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2837_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2821_ = v___x_2818_;
v_isShared_2822_ = v_isSharedCheck_2837_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2818_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2837_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v_fst_2823_; lean_object* v_snd_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2836_; 
v_fst_2823_ = lean_ctor_get(v_a_2819_, 0);
v_snd_2824_ = lean_ctor_get(v_a_2819_, 1);
v_isSharedCheck_2836_ = !lean_is_exclusive(v_a_2819_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2826_ = v_a_2819_;
v_isShared_2827_ = v_isSharedCheck_2836_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_snd_2824_);
lean_inc(v_fst_2823_);
lean_dec(v_a_2819_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2836_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
uint8_t v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2831_; 
v___x_2828_ = 1;
v___x_2829_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2829_, 0, v_fst_2823_);
lean_ctor_set_uint8(v___x_2829_, sizeof(void*)*1, v___x_2828_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 0, v___x_2829_);
v___x_2831_ = v___x_2826_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v___x_2829_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v_snd_2824_);
v___x_2831_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
lean_object* v___x_2833_; 
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 0, v___x_2831_);
v___x_2833_ = v___x_2821_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2831_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
}
else
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
v_a_2838_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v___x_2818_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2818_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2838_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object* v_handler_2846_, lean_object* v_p_2847_, lean_object* v_s_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0(v_handler_2846_, v_p_2847_, v_s_2848_, v___y_2849_);
lean_dec_ref(v___y_2849_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(lean_object* v_method_2852_, lean_object* v_inst_2853_, lean_object* v_inst_2854_, lean_object* v_inst_2855_, lean_object* v_inst_2856_, lean_object* v_initState_2857_, lean_object* v_handler_2858_, lean_object* v_onDidChange_2859_){
_start:
{
lean_object* v_handler_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v_handler_2861_ = lean_alloc_closure((void*)(l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v_handler_2861_, 0, v_handler_2858_);
v___x_2862_ = lean_box(0);
v___x_2863_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2852_, v___x_2862_, v_inst_2853_, v_inst_2854_, v_inst_2855_, v_inst_2856_, v_initState_2857_, v_handler_2861_, v_onDidChange_2859_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2864_, lean_object* v_inst_2865_, lean_object* v_inst_2866_, lean_object* v_inst_2867_, lean_object* v_inst_2868_, lean_object* v_initState_2869_, lean_object* v_handler_2870_, lean_object* v_onDidChange_2871_, lean_object* v_a_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(v_method_2864_, v_inst_2865_, v_inst_2866_, v_inst_2867_, v_inst_2868_, v_initState_2869_, v_handler_2870_, v_onDidChange_2871_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler(lean_object* v_method_2874_, lean_object* v_paramType_2875_, lean_object* v_inst_2876_, lean_object* v_inst_2877_, lean_object* v_respType_2878_, lean_object* v_inst_2879_, lean_object* v_stateType_2880_, lean_object* v_inst_2881_, lean_object* v_initState_2882_, lean_object* v_handler_2883_, lean_object* v_onDidChange_2884_){
_start:
{
lean_object* v___x_2886_; 
v___x_2886_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(v_method_2874_, v_inst_2876_, v_inst_2877_, v_inst_2879_, v_inst_2881_, v_initState_2882_, v_handler_2883_, v_onDidChange_2884_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___boxed(lean_object* v_method_2887_, lean_object* v_paramType_2888_, lean_object* v_inst_2889_, lean_object* v_inst_2890_, lean_object* v_respType_2891_, lean_object* v_inst_2892_, lean_object* v_stateType_2893_, lean_object* v_inst_2894_, lean_object* v_initState_2895_, lean_object* v_handler_2896_, lean_object* v_onDidChange_2897_, lean_object* v_a_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler(v_method_2887_, v_paramType_2888_, v_inst_2889_, v_inst_2890_, v_respType_2891_, v_inst_2892_, v_stateType_2893_, v_inst_2894_, v_initState_2895_, v_handler_2896_, v_onDidChange_2897_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(lean_object* v_method_2900_, lean_object* v_refreshMethod_2901_, lean_object* v_refreshIntervalMs_2902_, lean_object* v_inst_2903_, lean_object* v_inst_2904_, lean_object* v_inst_2905_, lean_object* v_inst_2906_, lean_object* v_initState_2907_, lean_object* v_handler_2908_, lean_object* v_onDidChange_2909_){
_start:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2911_, 0, v_refreshMethod_2901_);
lean_ctor_set(v___x_2911_, 1, v_refreshIntervalMs_2902_);
v___x_2912_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2900_, v___x_2911_, v_inst_2903_, v_inst_2904_, v_inst_2905_, v_inst_2906_, v_initState_2907_, v_handler_2908_, v_onDidChange_2909_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2913_, lean_object* v_refreshMethod_2914_, lean_object* v_refreshIntervalMs_2915_, lean_object* v_inst_2916_, lean_object* v_inst_2917_, lean_object* v_inst_2918_, lean_object* v_inst_2919_, lean_object* v_initState_2920_, lean_object* v_handler_2921_, lean_object* v_onDidChange_2922_, lean_object* v_a_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(v_method_2913_, v_refreshMethod_2914_, v_refreshIntervalMs_2915_, v_inst_2916_, v_inst_2917_, v_inst_2918_, v_inst_2919_, v_initState_2920_, v_handler_2921_, v_onDidChange_2922_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler(lean_object* v_method_2925_, lean_object* v_refreshMethod_2926_, lean_object* v_refreshIntervalMs_2927_, lean_object* v_paramType_2928_, lean_object* v_inst_2929_, lean_object* v_inst_2930_, lean_object* v_respType_2931_, lean_object* v_inst_2932_, lean_object* v_stateType_2933_, lean_object* v_inst_2934_, lean_object* v_initState_2935_, lean_object* v_handler_2936_, lean_object* v_onDidChange_2937_){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(v_method_2925_, v_refreshMethod_2926_, v_refreshIntervalMs_2927_, v_inst_2929_, v_inst_2930_, v_inst_2932_, v_inst_2934_, v_initState_2935_, v_handler_2936_, v_onDidChange_2937_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___boxed(lean_object* v_method_2940_, lean_object* v_refreshMethod_2941_, lean_object* v_refreshIntervalMs_2942_, lean_object* v_paramType_2943_, lean_object* v_inst_2944_, lean_object* v_inst_2945_, lean_object* v_respType_2946_, lean_object* v_inst_2947_, lean_object* v_stateType_2948_, lean_object* v_inst_2949_, lean_object* v_initState_2950_, lean_object* v_handler_2951_, lean_object* v_onDidChange_2952_, lean_object* v_a_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_Lean_Server_registerPartialStatefulLspRequestHandler(v_method_2940_, v_refreshMethod_2941_, v_refreshIntervalMs_2942_, v_paramType_2943_, v_inst_2944_, v_inst_2945_, v_respType_2946_, v_inst_2947_, v_stateType_2948_, v_inst_2949_, v_initState_2950_, v_handler_2951_, v_onDidChange_2952_);
return v_res_2954_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2955_, lean_object* v_i_2956_, lean_object* v_k_2957_){
_start:
{
lean_object* v___x_2958_; uint8_t v___x_2959_; 
v___x_2958_ = lean_array_get_size(v_keys_2955_);
v___x_2959_ = lean_nat_dec_lt(v_i_2956_, v___x_2958_);
if (v___x_2959_ == 0)
{
lean_dec(v_i_2956_);
return v___x_2959_;
}
else
{
lean_object* v_k_x27_2960_; uint8_t v___x_2961_; 
v_k_x27_2960_ = lean_array_fget_borrowed(v_keys_2955_, v_i_2956_);
v___x_2961_ = lean_string_dec_eq(v_k_2957_, v_k_x27_2960_);
if (v___x_2961_ == 0)
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2962_ = lean_unsigned_to_nat(1u);
v___x_2963_ = lean_nat_add(v_i_2956_, v___x_2962_);
lean_dec(v_i_2956_);
v_i_2956_ = v___x_2963_;
goto _start;
}
else
{
lean_dec(v_i_2956_);
return v___x_2961_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2965_, lean_object* v_i_2966_, lean_object* v_k_2967_){
_start:
{
uint8_t v_res_2968_; lean_object* v_r_2969_; 
v_res_2968_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_keys_2965_, v_i_2966_, v_k_2967_);
lean_dec_ref(v_k_2967_);
lean_dec_ref(v_keys_2965_);
v_r_2969_ = lean_box(v_res_2968_);
return v_r_2969_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(lean_object* v_x_2970_, size_t v_x_2971_, lean_object* v_x_2972_){
_start:
{
if (lean_obj_tag(v_x_2970_) == 0)
{
lean_object* v_es_2973_; lean_object* v___x_2974_; size_t v___x_2975_; size_t v___x_2976_; lean_object* v_j_2977_; lean_object* v___x_2978_; 
v_es_2973_ = lean_ctor_get(v_x_2970_, 0);
v___x_2974_ = lean_box(2);
v___x_2975_ = ((size_t)31ULL);
v___x_2976_ = lean_usize_land(v_x_2971_, v___x_2975_);
v_j_2977_ = lean_usize_to_nat(v___x_2976_);
v___x_2978_ = lean_array_get_borrowed(v___x_2974_, v_es_2973_, v_j_2977_);
lean_dec(v_j_2977_);
switch(lean_obj_tag(v___x_2978_))
{
case 0:
{
lean_object* v_key_2979_; uint8_t v___x_2980_; 
v_key_2979_ = lean_ctor_get(v___x_2978_, 0);
v___x_2980_ = lean_string_dec_eq(v_x_2972_, v_key_2979_);
return v___x_2980_;
}
case 1:
{
lean_object* v_node_2981_; size_t v___x_2982_; size_t v___x_2983_; 
v_node_2981_ = lean_ctor_get(v___x_2978_, 0);
v___x_2982_ = ((size_t)5ULL);
v___x_2983_ = lean_usize_shift_right(v_x_2971_, v___x_2982_);
v_x_2970_ = v_node_2981_;
v_x_2971_ = v___x_2983_;
goto _start;
}
default: 
{
uint8_t v___x_2985_; 
v___x_2985_ = 0;
return v___x_2985_;
}
}
}
else
{
lean_object* v_ks_2986_; lean_object* v___x_2987_; uint8_t v___x_2988_; 
v_ks_2986_ = lean_ctor_get(v_x_2970_, 0);
v___x_2987_ = lean_unsigned_to_nat(0u);
v___x_2988_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_ks_2986_, v___x_2987_, v_x_2972_);
return v___x_2988_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg___boxed(lean_object* v_x_2989_, lean_object* v_x_2990_, lean_object* v_x_2991_){
_start:
{
size_t v_x_214__boxed_2992_; uint8_t v_res_2993_; lean_object* v_r_2994_; 
v_x_214__boxed_2992_ = lean_unbox_usize(v_x_2990_);
lean_dec(v_x_2990_);
v_res_2993_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_2989_, v_x_214__boxed_2992_, v_x_2991_);
lean_dec_ref(v_x_2991_);
lean_dec_ref(v_x_2989_);
v_r_2994_ = lean_box(v_res_2993_);
return v_r_2994_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(lean_object* v_x_2995_, lean_object* v_x_2996_){
_start:
{
uint64_t v___x_2997_; size_t v___x_2998_; uint8_t v___x_2999_; 
v___x_2997_ = lean_string_hash(v_x_2996_);
v___x_2998_ = lean_uint64_to_usize(v___x_2997_);
v___x_2999_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_2995_, v___x_2998_, v_x_2996_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg___boxed(lean_object* v_x_3000_, lean_object* v_x_3001_){
_start:
{
uint8_t v_res_3002_; lean_object* v_r_3003_; 
v_res_3002_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v_x_3000_, v_x_3001_);
lean_dec_ref(v_x_3001_);
lean_dec_ref(v_x_3000_);
v_r_3003_ = lean_box(v_res_3002_);
return v_r_3003_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_isStatefulLspRequestMethod(lean_object* v_method_3004_){
_start:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; uint8_t v___x_3008_; 
v___x_3006_ = l_Lean_Server_statefulRequestHandlers;
v___x_3007_ = lean_st_ref_get(v___x_3006_);
v___x_3008_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v___x_3007_, v_method_3004_);
lean_dec(v___x_3007_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_isStatefulLspRequestMethod___boxed(lean_object* v_method_3009_, lean_object* v_a_3010_){
_start:
{
uint8_t v_res_3011_; lean_object* v_r_3012_; 
v_res_3011_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_3009_);
lean_dec_ref(v_method_3009_);
v_r_3012_ = lean_box(v_res_3011_);
return v_r_3012_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0(lean_object* v_00_u03b2_3013_, lean_object* v_x_3014_, lean_object* v_x_3015_){
_start:
{
uint8_t v___x_3016_; 
v___x_3016_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v_x_3014_, v_x_3015_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___boxed(lean_object* v_00_u03b2_3017_, lean_object* v_x_3018_, lean_object* v_x_3019_){
_start:
{
uint8_t v_res_3020_; lean_object* v_r_3021_; 
v_res_3020_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0(v_00_u03b2_3017_, v_x_3018_, v_x_3019_);
lean_dec_ref(v_x_3019_);
lean_dec_ref(v_x_3018_);
v_r_3021_ = lean_box(v_res_3020_);
return v_r_3021_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0(lean_object* v_00_u03b2_3022_, lean_object* v_x_3023_, size_t v_x_3024_, lean_object* v_x_3025_){
_start:
{
uint8_t v___x_3026_; 
v___x_3026_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_3023_, v_x_3024_, v_x_3025_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3027_, lean_object* v_x_3028_, lean_object* v_x_3029_, lean_object* v_x_3030_){
_start:
{
size_t v_x_284__boxed_3031_; uint8_t v_res_3032_; lean_object* v_r_3033_; 
v_x_284__boxed_3031_ = lean_unbox_usize(v_x_3029_);
lean_dec(v_x_3029_);
v_res_3032_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0(v_00_u03b2_3027_, v_x_3028_, v_x_284__boxed_3031_, v_x_3030_);
lean_dec_ref(v_x_3030_);
lean_dec_ref(v_x_3028_);
v_r_3033_ = lean_box(v_res_3032_);
return v_r_3033_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3034_, lean_object* v_keys_3035_, lean_object* v_vals_3036_, lean_object* v_heq_3037_, lean_object* v_i_3038_, lean_object* v_k_3039_){
_start:
{
uint8_t v___x_3040_; 
v___x_3040_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_keys_3035_, v_i_3038_, v_k_3039_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3041_, lean_object* v_keys_3042_, lean_object* v_vals_3043_, lean_object* v_heq_3044_, lean_object* v_i_3045_, lean_object* v_k_3046_){
_start:
{
uint8_t v_res_3047_; lean_object* v_r_3048_; 
v_res_3047_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1(v_00_u03b2_3041_, v_keys_3042_, v_vals_3043_, v_heq_3044_, v_i_3045_, v_k_3046_);
lean_dec_ref(v_k_3046_);
lean_dec_ref(v_vals_3043_);
lean_dec_ref(v_keys_3042_);
v_r_3048_ = lean_box(v_res_3047_);
return v_r_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupStatefulLspRequestHandler(lean_object* v_method_3049_){
_start:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3051_ = l_Lean_Server_statefulRequestHandlers;
v___x_3052_ = lean_st_ref_get(v___x_3051_);
v___x_3053_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v___x_3052_, v_method_3049_);
lean_dec(v___x_3052_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupStatefulLspRequestHandler___boxed(lean_object* v_method_3054_, lean_object* v_a_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_3054_);
lean_dec_ref(v_method_3054_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(lean_object* v_as_3057_, size_t v_i_3058_, size_t v_stop_3059_, lean_object* v_b_3060_){
_start:
{
lean_object* v___y_3062_; uint8_t v___x_3066_; 
v___x_3066_ = lean_usize_dec_eq(v_i_3058_, v_stop_3059_);
if (v___x_3066_ == 0)
{
lean_object* v___x_3067_; lean_object* v_snd_3068_; lean_object* v_completeness_3069_; 
v___x_3067_ = lean_array_uget(v_as_3057_, v_i_3058_);
v_snd_3068_ = lean_ctor_get(v___x_3067_, 1);
v_completeness_3069_ = lean_ctor_get(v_snd_3068_, 8);
lean_inc(v_completeness_3069_);
if (lean_obj_tag(v_completeness_3069_) == 1)
{
lean_object* v_fst_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3087_; 
v_fst_3070_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3087_ == 0)
{
lean_object* v_unused_3088_; 
v_unused_3088_ = lean_ctor_get(v___x_3067_, 1);
lean_dec(v_unused_3088_);
v___x_3072_ = v___x_3067_;
v_isShared_3073_ = v_isSharedCheck_3087_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_fst_3070_);
lean_dec(v___x_3067_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3087_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v_refreshMethod_3074_; lean_object* v_refreshIntervalMs_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3086_; 
v_refreshMethod_3074_ = lean_ctor_get(v_completeness_3069_, 0);
v_refreshIntervalMs_3075_ = lean_ctor_get(v_completeness_3069_, 1);
v_isSharedCheck_3086_ = !lean_is_exclusive(v_completeness_3069_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3077_ = v_completeness_3069_;
v_isShared_3078_ = v_isSharedCheck_3086_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_refreshIntervalMs_3075_);
lean_inc(v_refreshMethod_3074_);
lean_dec(v_completeness_3069_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3086_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 1, v_refreshIntervalMs_3075_);
lean_ctor_set(v___x_3072_, 0, v_refreshMethod_3074_);
v___x_3080_ = v___x_3072_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_refreshMethod_3074_);
lean_ctor_set(v_reuseFailAlloc_3085_, 1, v_refreshIntervalMs_3075_);
v___x_3080_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
lean_object* v___x_3082_; 
if (v_isShared_3078_ == 0)
{
lean_ctor_set_tag(v___x_3077_, 0);
lean_ctor_set(v___x_3077_, 1, v___x_3080_);
lean_ctor_set(v___x_3077_, 0, v_fst_3070_);
v___x_3082_ = v___x_3077_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_fst_3070_);
lean_ctor_set(v_reuseFailAlloc_3084_, 1, v___x_3080_);
v___x_3082_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
lean_object* v___x_3083_; 
v___x_3083_ = lean_array_push(v_b_3060_, v___x_3082_);
v___y_3062_ = v___x_3083_;
goto v___jp_3061_;
}
}
}
}
}
else
{
lean_dec(v_completeness_3069_);
lean_dec(v___x_3067_);
v___y_3062_ = v_b_3060_;
goto v___jp_3061_;
}
}
else
{
return v_b_3060_;
}
v___jp_3061_:
{
size_t v___x_3063_; size_t v___x_3064_; 
v___x_3063_ = ((size_t)1ULL);
v___x_3064_ = lean_usize_add(v_i_3058_, v___x_3063_);
v_i_3058_ = v___x_3064_;
v_b_3060_ = v___y_3062_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2___boxed(lean_object* v_as_3089_, lean_object* v_i_3090_, lean_object* v_stop_3091_, lean_object* v_b_3092_){
_start:
{
size_t v_i_boxed_3093_; size_t v_stop_boxed_3094_; lean_object* v_res_3095_; 
v_i_boxed_3093_ = lean_unbox_usize(v_i_3090_);
lean_dec(v_i_3090_);
v_stop_boxed_3094_ = lean_unbox_usize(v_stop_3091_);
lean_dec(v_stop_3091_);
v_res_3095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_3089_, v_i_boxed_3093_, v_stop_boxed_3094_, v_b_3092_);
lean_dec_ref(v_as_3089_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(lean_object* v_as_3098_, lean_object* v_start_3099_, lean_object* v_stop_3100_){
_start:
{
lean_object* v___x_3101_; uint8_t v___x_3102_; 
v___x_3101_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___closed__0));
v___x_3102_ = lean_nat_dec_lt(v_start_3099_, v_stop_3100_);
if (v___x_3102_ == 0)
{
return v___x_3101_;
}
else
{
lean_object* v___x_3103_; uint8_t v___x_3104_; 
v___x_3103_ = lean_array_get_size(v_as_3098_);
v___x_3104_ = lean_nat_dec_le(v_stop_3100_, v___x_3103_);
if (v___x_3104_ == 0)
{
uint8_t v___x_3105_; 
v___x_3105_ = lean_nat_dec_lt(v_start_3099_, v___x_3103_);
if (v___x_3105_ == 0)
{
return v___x_3101_;
}
else
{
size_t v___x_3106_; size_t v___x_3107_; lean_object* v___x_3108_; 
v___x_3106_ = lean_usize_of_nat(v_start_3099_);
v___x_3107_ = lean_usize_of_nat(v___x_3103_);
v___x_3108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_3098_, v___x_3106_, v___x_3107_, v___x_3101_);
return v___x_3108_;
}
}
else
{
size_t v___x_3109_; size_t v___x_3110_; lean_object* v___x_3111_; 
v___x_3109_ = lean_usize_of_nat(v_start_3099_);
v___x_3110_ = lean_usize_of_nat(v_stop_3100_);
v___x_3111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_3098_, v___x_3109_, v___x_3110_, v___x_3101_);
return v___x_3111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___boxed(lean_object* v_as_3112_, lean_object* v_start_3113_, lean_object* v_stop_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(v_as_3112_, v_start_3113_, v_stop_3114_);
lean_dec(v_stop_3114_);
lean_dec(v_start_3113_);
lean_dec_ref(v_as_3112_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_f_3116_, lean_object* v_keys_3117_, lean_object* v_vals_3118_, lean_object* v_i_3119_, lean_object* v_acc_3120_){
_start:
{
lean_object* v___x_3121_; uint8_t v___x_3122_; 
v___x_3121_ = lean_array_get_size(v_keys_3117_);
v___x_3122_ = lean_nat_dec_lt(v_i_3119_, v___x_3121_);
if (v___x_3122_ == 0)
{
lean_dec(v_i_3119_);
lean_dec(v_f_3116_);
return v_acc_3120_;
}
else
{
lean_object* v_k_3123_; lean_object* v_v_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v_k_3123_ = lean_array_fget_borrowed(v_keys_3117_, v_i_3119_);
v_v_3124_ = lean_array_fget_borrowed(v_vals_3118_, v_i_3119_);
lean_inc(v_f_3116_);
lean_inc(v_v_3124_);
lean_inc(v_k_3123_);
v___x_3125_ = lean_apply_3(v_f_3116_, v_acc_3120_, v_k_3123_, v_v_3124_);
v___x_3126_ = lean_unsigned_to_nat(1u);
v___x_3127_ = lean_nat_add(v_i_3119_, v___x_3126_);
lean_dec(v_i_3119_);
v_i_3119_ = v___x_3127_;
v_acc_3120_ = v___x_3125_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_f_3129_, lean_object* v_keys_3130_, lean_object* v_vals_3131_, lean_object* v_i_3132_, lean_object* v_acc_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_3129_, v_keys_3130_, v_vals_3131_, v_i_3132_, v_acc_3133_);
lean_dec_ref(v_vals_3131_);
lean_dec_ref(v_keys_3130_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_3135_, lean_object* v_x_3136_, lean_object* v_x_3137_){
_start:
{
if (lean_obj_tag(v_x_3136_) == 0)
{
lean_object* v_es_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; uint8_t v___x_3141_; 
v_es_3138_ = lean_ctor_get(v_x_3136_, 0);
v___x_3139_ = lean_unsigned_to_nat(0u);
v___x_3140_ = lean_array_get_size(v_es_3138_);
v___x_3141_ = lean_nat_dec_lt(v___x_3139_, v___x_3140_);
if (v___x_3141_ == 0)
{
lean_dec(v_f_3135_);
return v_x_3137_;
}
else
{
uint8_t v___x_3142_; 
v___x_3142_ = lean_nat_dec_le(v___x_3140_, v___x_3140_);
if (v___x_3142_ == 0)
{
if (v___x_3141_ == 0)
{
lean_dec(v_f_3135_);
return v_x_3137_;
}
else
{
size_t v___x_3143_; size_t v___x_3144_; lean_object* v___x_3145_; 
v___x_3143_ = ((size_t)0ULL);
v___x_3144_ = lean_usize_of_nat(v___x_3140_);
v___x_3145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_3135_, v_es_3138_, v___x_3143_, v___x_3144_, v_x_3137_);
return v___x_3145_;
}
}
else
{
size_t v___x_3146_; size_t v___x_3147_; lean_object* v___x_3148_; 
v___x_3146_ = ((size_t)0ULL);
v___x_3147_ = lean_usize_of_nat(v___x_3140_);
v___x_3148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_3135_, v_es_3138_, v___x_3146_, v___x_3147_, v_x_3137_);
return v___x_3148_;
}
}
}
else
{
lean_object* v_ks_3149_; lean_object* v_vs_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v_ks_3149_ = lean_ctor_get(v_x_3136_, 0);
v_vs_3150_ = lean_ctor_get(v_x_3136_, 1);
v___x_3151_ = lean_unsigned_to_nat(0u);
v___x_3152_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_3135_, v_ks_3149_, v_vs_3150_, v___x_3151_, v_x_3137_);
return v___x_3152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_f_3153_, lean_object* v_as_3154_, size_t v_i_3155_, size_t v_stop_3156_, lean_object* v_b_3157_){
_start:
{
lean_object* v___y_3159_; uint8_t v___x_3163_; 
v___x_3163_ = lean_usize_dec_eq(v_i_3155_, v_stop_3156_);
if (v___x_3163_ == 0)
{
lean_object* v___x_3164_; 
v___x_3164_ = lean_array_uget_borrowed(v_as_3154_, v_i_3155_);
switch(lean_obj_tag(v___x_3164_))
{
case 0:
{
lean_object* v_key_3165_; lean_object* v_val_3166_; lean_object* v___x_3167_; 
v_key_3165_ = lean_ctor_get(v___x_3164_, 0);
v_val_3166_ = lean_ctor_get(v___x_3164_, 1);
lean_inc(v_f_3153_);
lean_inc(v_val_3166_);
lean_inc(v_key_3165_);
v___x_3167_ = lean_apply_3(v_f_3153_, v_b_3157_, v_key_3165_, v_val_3166_);
v___y_3159_ = v___x_3167_;
goto v___jp_3158_;
}
case 1:
{
lean_object* v_node_3168_; lean_object* v___x_3169_; 
v_node_3168_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_f_3153_);
v___x_3169_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3153_, v_node_3168_, v_b_3157_);
v___y_3159_ = v___x_3169_;
goto v___jp_3158_;
}
default: 
{
v___y_3159_ = v_b_3157_;
goto v___jp_3158_;
}
}
}
else
{
lean_dec(v_f_3153_);
return v_b_3157_;
}
v___jp_3158_:
{
size_t v___x_3160_; size_t v___x_3161_; 
v___x_3160_ = ((size_t)1ULL);
v___x_3161_ = lean_usize_add(v_i_3155_, v___x_3160_);
v_i_3155_ = v___x_3161_;
v_b_3157_ = v___y_3159_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_f_3170_, lean_object* v_as_3171_, lean_object* v_i_3172_, lean_object* v_stop_3173_, lean_object* v_b_3174_){
_start:
{
size_t v_i_boxed_3175_; size_t v_stop_boxed_3176_; lean_object* v_res_3177_; 
v_i_boxed_3175_ = lean_unbox_usize(v_i_3172_);
lean_dec(v_i_3172_);
v_stop_boxed_3176_ = lean_unbox_usize(v_stop_3173_);
lean_dec(v_stop_3173_);
v_res_3177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_3170_, v_as_3171_, v_i_boxed_3175_, v_stop_boxed_3176_, v_b_3174_);
lean_dec_ref(v_as_3171_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_3178_, lean_object* v_x_3179_, lean_object* v_x_3180_){
_start:
{
lean_object* v_res_3181_; 
v_res_3181_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3178_, v_x_3179_, v_x_3180_);
lean_dec_ref(v_x_3179_);
return v_res_3181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___lam__0(lean_object* v_f_3182_, lean_object* v_x1_3183_, lean_object* v_x2_3184_, lean_object* v_x3_3185_){
_start:
{
lean_object* v___x_3186_; 
v___x_3186_ = lean_apply_3(v_f_3182_, v_x1_3183_, v_x2_3184_, v_x3_3185_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(lean_object* v_map_3187_, lean_object* v_f_3188_, lean_object* v_init_3189_){
_start:
{
lean_object* v___f_3190_; lean_object* v___x_3191_; 
v___f_3190_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3190_, 0, v_f_3188_);
v___x_3191_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v___f_3190_, v_map_3187_, v_init_3189_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___boxed(lean_object* v_map_3192_, lean_object* v_f_3193_, lean_object* v_init_3194_){
_start:
{
lean_object* v_res_3195_; 
v_res_3195_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_map_3192_, v_f_3193_, v_init_3194_);
lean_dec_ref(v_map_3192_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___lam__0(lean_object* v_ps_3196_, lean_object* v_k_3197_, lean_object* v_v_3198_){
_start:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3199_, 0, v_k_3197_);
lean_ctor_set(v___x_3199_, 1, v_v_3198_);
v___x_3200_ = lean_array_push(v_ps_3196_, v___x_3199_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(lean_object* v_m_3204_){
_start:
{
lean_object* v___f_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___f_3205_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__0));
v___x_3206_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__1));
v___x_3207_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_m_3204_, v___f_3205_, v___x_3206_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___boxed(lean_object* v_m_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v_m_3208_);
lean_dec_ref(v_m_3208_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_partialLspRequestHandlerMethods(){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3211_ = l_Lean_Server_statefulRequestHandlers;
v___x_3212_ = lean_st_ref_get(v___x_3211_);
v___x_3213_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v___x_3212_);
lean_dec(v___x_3212_);
v___x_3214_ = lean_unsigned_to_nat(0u);
v___x_3215_ = lean_array_get_size(v___x_3213_);
v___x_3216_ = l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(v___x_3213_, v___x_3214_, v___x_3215_);
lean_dec_ref(v___x_3213_);
v___x_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3216_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_partialLspRequestHandlerMethods___boxed(lean_object* v_a_3218_){
_start:
{
lean_object* v_res_3219_; 
v_res_3219_ = l_Lean_Server_partialLspRequestHandlerMethods();
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0(lean_object* v_00_u03b2_3220_, lean_object* v_m_3221_){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v_m_3221_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___boxed(lean_object* v_00_u03b2_3223_, lean_object* v_m_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0(v_00_u03b2_3223_, v_m_3224_);
lean_dec_ref(v_m_3224_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0(lean_object* v_00_u03c3_3226_, lean_object* v_00_u03b2_3227_, lean_object* v_map_3228_, lean_object* v_f_3229_, lean_object* v_init_3230_){
_start:
{
lean_object* v___x_3231_; 
v___x_3231_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_map_3228_, v_f_3229_, v_init_3230_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3232_, lean_object* v_00_u03b2_3233_, lean_object* v_map_3234_, lean_object* v_f_3235_, lean_object* v_init_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0(v_00_u03c3_3232_, v_00_u03b2_3233_, v_map_3234_, v_f_3235_, v_init_3236_);
lean_dec_ref(v_map_3234_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg(lean_object* v_map_3238_, lean_object* v_f_3239_, lean_object* v_init_3240_){
_start:
{
lean_object* v___x_3241_; 
v___x_3241_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3239_, v_map_3238_, v_init_3240_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_3242_, lean_object* v_f_3243_, lean_object* v_init_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg(v_map_3242_, v_f_3243_, v_init_3244_);
lean_dec_ref(v_map_3242_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3246_, lean_object* v_00_u03b2_3247_, lean_object* v_map_3248_, lean_object* v_f_3249_, lean_object* v_init_3250_){
_start:
{
lean_object* v___x_3251_; 
v___x_3251_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3249_, v_map_3248_, v_init_3250_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3252_, lean_object* v_00_u03b2_3253_, lean_object* v_map_3254_, lean_object* v_f_3255_, lean_object* v_init_3256_){
_start:
{
lean_object* v_res_3257_; 
v_res_3257_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1(v_00_u03c3_3252_, v_00_u03b2_3253_, v_map_3254_, v_f_3255_, v_init_3256_);
lean_dec_ref(v_map_3254_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3258_, lean_object* v_00_u03b1_3259_, lean_object* v_00_u03b2_3260_, lean_object* v_f_3261_, lean_object* v_x_3262_, lean_object* v_x_3263_){
_start:
{
lean_object* v___x_3264_; 
v___x_3264_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3261_, v_x_3262_, v_x_3263_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3265_, lean_object* v_00_u03b1_3266_, lean_object* v_00_u03b2_3267_, lean_object* v_f_3268_, lean_object* v_x_3269_, lean_object* v_x_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3265_, v_00_u03b1_3266_, v_00_u03b2_3267_, v_f_3268_, v_x_3269_, v_x_3270_);
lean_dec_ref(v_x_3269_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_3272_, lean_object* v_00_u03b2_3273_, lean_object* v_00_u03c3_3274_, lean_object* v_f_3275_, lean_object* v_as_3276_, size_t v_i_3277_, size_t v_stop_3278_, lean_object* v_b_3279_){
_start:
{
lean_object* v___x_3280_; 
v___x_3280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_3275_, v_as_3276_, v_i_3277_, v_stop_3278_, v_b_3279_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_3281_, lean_object* v_00_u03b2_3282_, lean_object* v_00_u03c3_3283_, lean_object* v_f_3284_, lean_object* v_as_3285_, lean_object* v_i_3286_, lean_object* v_stop_3287_, lean_object* v_b_3288_){
_start:
{
size_t v_i_boxed_3289_; size_t v_stop_boxed_3290_; lean_object* v_res_3291_; 
v_i_boxed_3289_ = lean_unbox_usize(v_i_3286_);
lean_dec(v_i_3286_);
v_stop_boxed_3290_ = lean_unbox_usize(v_stop_3287_);
lean_dec(v_stop_3287_);
v_res_3291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_3281_, v_00_u03b2_3282_, v_00_u03c3_3283_, v_f_3284_, v_as_3285_, v_i_boxed_3289_, v_stop_boxed_3290_, v_b_3288_);
lean_dec_ref(v_as_3285_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03c3_3292_, lean_object* v_00_u03b1_3293_, lean_object* v_00_u03b2_3294_, lean_object* v_f_3295_, lean_object* v_keys_3296_, lean_object* v_vals_3297_, lean_object* v_heq_3298_, lean_object* v_i_3299_, lean_object* v_acc_3300_){
_start:
{
lean_object* v___x_3301_; 
v___x_3301_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_3295_, v_keys_3296_, v_vals_3297_, v_i_3299_, v_acc_3300_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03c3_3302_, lean_object* v_00_u03b1_3303_, lean_object* v_00_u03b2_3304_, lean_object* v_f_3305_, lean_object* v_keys_3306_, lean_object* v_vals_3307_, lean_object* v_heq_3308_, lean_object* v_i_3309_, lean_object* v_acc_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6(v_00_u03c3_3302_, v_00_u03b1_3303_, v_00_u03b2_3304_, v_f_3305_, v_keys_3306_, v_vals_3307_, v_heq_3308_, v_i_3309_, v_acc_3310_);
lean_dec_ref(v_vals_3307_);
lean_dec_ref(v_keys_3306_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0(lean_object* v_inst_3312_, lean_object* v_pureOnDidChange_3313_, lean_object* v_method_3314_, lean_object* v_onDidChange_3315_, lean_object* v_p_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_){
_start:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; 
lean_inc(v_inst_3312_);
v___x_3320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3320_, 0, v_inst_3312_);
lean_ctor_set(v___x_3320_, 1, v___y_3317_);
lean_inc_ref(v___y_3318_);
lean_inc_ref(v_p_3316_);
v___x_3321_ = lean_apply_4(v_pureOnDidChange_3313_, v_p_3316_, v___x_3320_, v___y_3318_, lean_box(0));
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_object* v_a_3322_; lean_object* v_snd_3323_; lean_object* v___x_3324_; 
v_a_3322_ = lean_ctor_get(v___x_3321_, 0);
lean_inc(v_a_3322_);
lean_dec_ref_known(v___x_3321_, 1);
v_snd_3323_ = lean_ctor_get(v_a_3322_, 1);
lean_inc(v_snd_3323_);
lean_dec(v_a_3322_);
v___x_3324_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_3314_, v_snd_3323_, v_inst_3312_);
lean_dec(v_inst_3312_);
lean_dec(v_snd_3323_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v_a_3325_; lean_object* v___x_3326_; 
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
lean_inc(v_a_3325_);
lean_dec_ref_known(v___x_3324_, 1);
lean_inc_ref(v___y_3318_);
v___x_3326_ = lean_apply_4(v_onDidChange_3315_, v_p_3316_, v_a_3325_, v___y_3318_, lean_box(0));
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3344_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3329_ = v___x_3326_;
v_isShared_3330_ = v_isSharedCheck_3344_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3326_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3344_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v_snd_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3342_; 
v_snd_3331_ = lean_ctor_get(v_a_3327_, 1);
v_isSharedCheck_3342_ = !lean_is_exclusive(v_a_3327_);
if (v_isSharedCheck_3342_ == 0)
{
lean_object* v_unused_3343_; 
v_unused_3343_ = lean_ctor_get(v_a_3327_, 0);
lean_dec(v_unused_3343_);
v___x_3333_ = v_a_3327_;
v_isShared_3334_ = v_isSharedCheck_3342_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_snd_3331_);
lean_dec(v_a_3327_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3342_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3335_; lean_object* v___x_3337_; 
v___x_3335_ = lean_box(0);
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 0, v___x_3335_);
v___x_3337_ = v___x_3333_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v___x_3335_);
lean_ctor_set(v_reuseFailAlloc_3341_, 1, v_snd_3331_);
v___x_3337_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
lean_object* v___x_3339_; 
if (v_isShared_3330_ == 0)
{
lean_ctor_set(v___x_3329_, 0, v___x_3337_);
v___x_3339_ = v___x_3329_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3337_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
}
}
else
{
return v___x_3326_;
}
}
else
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
lean_dec_ref(v_p_3316_);
lean_dec_ref(v_onDidChange_3315_);
v_a_3345_ = lean_ctor_get(v___x_3324_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3324_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3324_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
else
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3360_; 
lean_dec_ref(v_p_3316_);
lean_dec_ref(v_onDidChange_3315_);
lean_dec(v_inst_3312_);
v_a_3353_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3355_ = v___x_3321_;
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3321_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3358_; 
if (v_isShared_3356_ == 0)
{
v___x_3358_ = v___x_3355_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_a_3353_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object* v_inst_3361_, lean_object* v_pureOnDidChange_3362_, lean_object* v_method_3363_, lean_object* v_onDidChange_3364_, lean_object* v_p_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_){
_start:
{
lean_object* v_res_3369_; 
v_res_3369_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0(v_inst_3361_, v_pureOnDidChange_3362_, v_method_3363_, v_onDidChange_3364_, v_p_3365_, v___y_3366_, v___y_3367_);
lean_dec_ref(v___y_3367_);
lean_dec_ref(v_method_3363_);
return v_res_3369_;
}
}
static lean_object* _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3371_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__0));
v___x_3372_ = l_Lean_Server_RequestError_internalError(v___x_3371_);
return v___x_3372_;
}
}
static lean_object* _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3374_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__2));
v___x_3375_ = l_Lean_Server_RequestError_internalError(v___x_3374_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1(lean_object* v_inst_3376_, lean_object* v_inst_3377_, lean_object* v_pureHandle_3378_, lean_object* v_inst_3379_, lean_object* v_method_3380_, lean_object* v_handler_3381_, lean_object* v_p_3382_, lean_object* v_s_3383_, lean_object* v___y_3384_){
_start:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
lean_inc(v_p_3382_);
v___x_3386_ = lean_apply_1(v_inst_3376_, v_p_3382_);
lean_inc(v_inst_3377_);
v___x_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3387_, 0, v_inst_3377_);
lean_ctor_set(v___x_3387_, 1, v_s_3383_);
lean_inc_ref(v___y_3384_);
v___x_3388_ = lean_apply_4(v_pureHandle_3378_, v___x_3386_, v___x_3387_, v___y_3384_, lean_box(0));
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3423_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3391_ = v___x_3388_;
v_isShared_3392_ = v_isSharedCheck_3423_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3388_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3423_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v_fst_3393_; lean_object* v_snd_3394_; lean_object* v_response_x3f_3395_; lean_object* v_serialized_3396_; uint8_t v_isComplete_3397_; lean_object* v_a_3399_; 
v_fst_3393_ = lean_ctor_get(v_a_3389_, 0);
lean_inc(v_fst_3393_);
v_snd_3394_ = lean_ctor_get(v_a_3389_, 1);
lean_inc(v_snd_3394_);
lean_dec(v_a_3389_);
v_response_x3f_3395_ = lean_ctor_get(v_fst_3393_, 0);
lean_inc(v_response_x3f_3395_);
v_serialized_3396_ = lean_ctor_get(v_fst_3393_, 1);
lean_inc_ref(v_serialized_3396_);
v_isComplete_3397_ = lean_ctor_get_uint8(v_fst_3393_, sizeof(void*)*2);
lean_dec(v_fst_3393_);
if (lean_obj_tag(v_response_x3f_3395_) == 0)
{
lean_object* v___x_3418_; 
v___x_3418_ = l_Lean_Json_parse(v_serialized_3396_);
if (lean_obj_tag(v___x_3418_) == 1)
{
lean_object* v_a_3419_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc(v_a_3419_);
lean_dec_ref_known(v___x_3418_, 1);
v_a_3399_ = v_a_3419_;
goto v___jp_3398_;
}
else
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
lean_dec_ref(v___x_3418_);
lean_dec(v_snd_3394_);
lean_del_object(v___x_3391_);
lean_dec(v_p_3382_);
lean_dec_ref(v_handler_3381_);
lean_dec_ref(v_inst_3379_);
lean_dec(v_inst_3377_);
v___x_3420_ = lean_obj_once(&l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3, &l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3_once, _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3);
v___x_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3420_);
return v___x_3421_;
}
}
else
{
lean_object* v_val_3422_; 
lean_dec_ref(v_serialized_3396_);
v_val_3422_ = lean_ctor_get(v_response_x3f_3395_, 0);
lean_inc(v_val_3422_);
lean_dec_ref_known(v_response_x3f_3395_, 1);
v_a_3399_ = v_val_3422_;
goto v___jp_3398_;
}
v___jp_3398_:
{
lean_object* v___x_3400_; 
v___x_3400_ = lean_apply_1(v_inst_3379_, v_a_3399_);
if (lean_obj_tag(v___x_3400_) == 1)
{
lean_object* v_a_3401_; lean_object* v___x_3402_; 
lean_del_object(v___x_3391_);
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_a_3401_);
lean_dec_ref_known(v___x_3400_, 1);
v___x_3402_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_3380_, v_snd_3394_, v_inst_3377_);
lean_dec(v_inst_3377_);
lean_dec(v_snd_3394_);
if (lean_obj_tag(v___x_3402_) == 0)
{
lean_object* v_a_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v_a_3403_ = lean_ctor_get(v___x_3402_, 0);
lean_inc(v_a_3403_);
lean_dec_ref_known(v___x_3402_, 1);
v___x_3404_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3404_, 0, v_a_3401_);
lean_ctor_set_uint8(v___x_3404_, sizeof(void*)*1, v_isComplete_3397_);
lean_inc_ref(v___y_3384_);
v___x_3405_ = lean_apply_5(v_handler_3381_, v_p_3382_, v___x_3404_, v_a_3403_, v___y_3384_, lean_box(0));
return v___x_3405_;
}
else
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
lean_dec(v_a_3401_);
lean_dec(v_p_3382_);
lean_dec_ref(v_handler_3381_);
v_a_3406_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v___x_3402_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3402_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3411_; 
if (v_isShared_3409_ == 0)
{
v___x_3411_ = v___x_3408_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_a_3406_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
}
else
{
lean_object* v___x_3414_; lean_object* v___x_3416_; 
lean_dec_ref(v___x_3400_);
lean_dec(v_snd_3394_);
lean_dec(v_p_3382_);
lean_dec_ref(v_handler_3381_);
lean_dec(v_inst_3377_);
v___x_3414_ = lean_obj_once(&l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1, &l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1_once, _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1);
if (v_isShared_3392_ == 0)
{
lean_ctor_set_tag(v___x_3391_, 1);
lean_ctor_set(v___x_3391_, 0, v___x_3414_);
v___x_3416_ = v___x_3391_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v___x_3414_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
}
else
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3431_; 
lean_dec(v_p_3382_);
lean_dec_ref(v_handler_3381_);
lean_dec_ref(v_inst_3379_);
lean_dec(v_inst_3377_);
v_a_3424_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3426_ = v___x_3388_;
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3388_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3429_; 
if (v_isShared_3427_ == 0)
{
v___x_3429_ = v___x_3426_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3424_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___boxed(lean_object* v_inst_3432_, lean_object* v_inst_3433_, lean_object* v_pureHandle_3434_, lean_object* v_inst_3435_, lean_object* v_method_3436_, lean_object* v_handler_3437_, lean_object* v_p_3438_, lean_object* v_s_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1(v_inst_3432_, v_inst_3433_, v_pureHandle_3434_, v_inst_3435_, v_method_3436_, v_handler_3437_, v_p_3438_, v_s_3439_, v___y_3440_);
lean_dec_ref(v___y_3440_);
lean_dec_ref(v_method_3436_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg(lean_object* v_method_3444_, lean_object* v_inst_3445_, lean_object* v_inst_3446_, lean_object* v_inst_3447_, lean_object* v_inst_3448_, lean_object* v_inst_3449_, lean_object* v_inst_3450_, lean_object* v_handler_3451_, lean_object* v_onDidChange_3452_){
_start:
{
lean_object* v___x_3454_; 
v___x_3454_ = l_Lean_initializing();
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3495_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3457_ = v___x_3454_;
v_isShared_3458_ = v_isSharedCheck_3495_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3454_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3495_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
uint8_t v___x_3459_; 
v___x_3459_ = lean_unbox(v_a_3455_);
lean_dec(v_a_3455_);
if (v___x_3459_ == 0)
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3466_; 
lean_dec_ref(v_onDidChange_3452_);
lean_dec_ref(v_handler_3451_);
lean_dec(v_inst_3450_);
lean_dec_ref(v_inst_3449_);
lean_dec_ref(v_inst_3448_);
lean_dec_ref(v_inst_3447_);
lean_dec_ref(v_inst_3446_);
lean_dec_ref(v_inst_3445_);
v___x_3460_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0));
v___x_3461_ = lean_string_append(v___x_3460_, v_method_3444_);
lean_dec_ref(v_method_3444_);
v___x_3462_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__1));
v___x_3463_ = lean_string_append(v___x_3461_, v___x_3462_);
v___x_3464_ = lean_mk_io_user_error(v___x_3463_);
if (v_isShared_3458_ == 0)
{
lean_ctor_set_tag(v___x_3457_, 1);
lean_ctor_set(v___x_3457_, 0, v___x_3464_);
v___x_3466_ = v___x_3457_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3464_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
else
{
lean_object* v___x_3468_; 
v___x_3468_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_3444_);
if (lean_obj_tag(v___x_3468_) == 1)
{
lean_object* v_val_3469_; lean_object* v_pureHandle_3470_; lean_object* v_pureOnDidChange_3471_; lean_object* v_initState_3472_; lean_object* v_completeness_3473_; lean_object* v___x_3474_; 
lean_del_object(v___x_3457_);
v_val_3469_ = lean_ctor_get(v___x_3468_, 0);
lean_inc(v_val_3469_);
lean_dec_ref_known(v___x_3468_, 1);
v_pureHandle_3470_ = lean_ctor_get(v_val_3469_, 1);
lean_inc_ref(v_pureHandle_3470_);
v_pureOnDidChange_3471_ = lean_ctor_get(v_val_3469_, 3);
lean_inc_ref(v_pureOnDidChange_3471_);
v_initState_3472_ = lean_ctor_get(v_val_3469_, 6);
lean_inc(v_initState_3472_);
v_completeness_3473_ = lean_ctor_get(v_val_3469_, 8);
lean_inc(v_completeness_3473_);
lean_dec(v_val_3469_);
v___x_3474_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(v_method_3444_, v_initState_3472_, v_inst_3450_);
lean_dec(v_initState_3472_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3475_; lean_object* v___f_3476_; lean_object* v___f_3477_; lean_object* v___x_3478_; 
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_a_3475_);
lean_dec_ref_known(v___x_3474_, 1);
lean_inc_ref_n(v_method_3444_, 2);
lean_inc_n(v_inst_3450_, 2);
v___f_3476_ = lean_alloc_closure((void*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_3476_, 0, v_inst_3450_);
lean_closure_set(v___f_3476_, 1, v_pureOnDidChange_3471_);
lean_closure_set(v___f_3476_, 2, v_method_3444_);
lean_closure_set(v___f_3476_, 3, v_onDidChange_3452_);
v___f_3477_ = lean_alloc_closure((void*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___boxed), 10, 6);
lean_closure_set(v___f_3477_, 0, v_inst_3446_);
lean_closure_set(v___f_3477_, 1, v_inst_3450_);
lean_closure_set(v___f_3477_, 2, v_pureHandle_3470_);
lean_closure_set(v___f_3477_, 3, v_inst_3448_);
lean_closure_set(v___f_3477_, 4, v_method_3444_);
lean_closure_set(v___f_3477_, 5, v_handler_3451_);
v___x_3478_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_3444_, v_completeness_3473_, v_inst_3445_, v_inst_3447_, v_inst_3449_, v_inst_3450_, v_a_3475_, v___f_3477_, v___f_3476_);
return v___x_3478_;
}
else
{
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3486_; 
lean_dec(v_completeness_3473_);
lean_dec_ref(v_pureOnDidChange_3471_);
lean_dec_ref(v_pureHandle_3470_);
lean_dec_ref(v_onDidChange_3452_);
lean_dec_ref(v_handler_3451_);
lean_dec(v_inst_3450_);
lean_dec_ref(v_inst_3449_);
lean_dec_ref(v_inst_3448_);
lean_dec_ref(v_inst_3447_);
lean_dec_ref(v_inst_3446_);
lean_dec_ref(v_inst_3445_);
lean_dec_ref(v_method_3444_);
v_a_3479_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3481_ = v___x_3474_;
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3474_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3484_; 
if (v_isShared_3482_ == 0)
{
v___x_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_a_3479_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
}
else
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3493_; 
lean_dec(v___x_3468_);
lean_dec_ref(v_onDidChange_3452_);
lean_dec_ref(v_handler_3451_);
lean_dec(v_inst_3450_);
lean_dec_ref(v_inst_3449_);
lean_dec_ref(v_inst_3448_);
lean_dec_ref(v_inst_3447_);
lean_dec_ref(v_inst_3446_);
lean_dec_ref(v_inst_3445_);
v___x_3487_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0));
v___x_3488_ = lean_string_append(v___x_3487_, v_method_3444_);
lean_dec_ref(v_method_3444_);
v___x_3489_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__1));
v___x_3490_ = lean_string_append(v___x_3488_, v___x_3489_);
v___x_3491_ = lean_mk_io_user_error(v___x_3490_);
if (v_isShared_3458_ == 0)
{
lean_ctor_set_tag(v___x_3457_, 1);
lean_ctor_set(v___x_3457_, 0, v___x_3491_);
v___x_3493_ = v___x_3457_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3491_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
}
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
lean_dec_ref(v_onDidChange_3452_);
lean_dec_ref(v_handler_3451_);
lean_dec(v_inst_3450_);
lean_dec_ref(v_inst_3449_);
lean_dec_ref(v_inst_3448_);
lean_dec_ref(v_inst_3447_);
lean_dec_ref(v_inst_3446_);
lean_dec_ref(v_inst_3445_);
lean_dec_ref(v_method_3444_);
v_a_3496_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_3454_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3454_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3501_; 
if (v_isShared_3499_ == 0)
{
v___x_3501_ = v___x_3498_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3496_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_3504_, lean_object* v_inst_3505_, lean_object* v_inst_3506_, lean_object* v_inst_3507_, lean_object* v_inst_3508_, lean_object* v_inst_3509_, lean_object* v_inst_3510_, lean_object* v_handler_3511_, lean_object* v_onDidChange_3512_, lean_object* v_a_3513_){
_start:
{
lean_object* v_res_3514_; 
v_res_3514_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg(v_method_3504_, v_inst_3505_, v_inst_3506_, v_inst_3507_, v_inst_3508_, v_inst_3509_, v_inst_3510_, v_handler_3511_, v_onDidChange_3512_);
return v_res_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler(lean_object* v_method_3515_, lean_object* v_paramType_3516_, lean_object* v_inst_3517_, lean_object* v_inst_3518_, lean_object* v_inst_3519_, lean_object* v_respType_3520_, lean_object* v_inst_3521_, lean_object* v_inst_3522_, lean_object* v_stateType_3523_, lean_object* v_inst_3524_, lean_object* v_handler_3525_, lean_object* v_onDidChange_3526_){
_start:
{
lean_object* v___x_3528_; 
v___x_3528_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg(v_method_3515_, v_inst_3517_, v_inst_3518_, v_inst_3519_, v_inst_3521_, v_inst_3522_, v_inst_3524_, v_handler_3525_, v_onDidChange_3526_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___boxed(lean_object* v_method_3529_, lean_object* v_paramType_3530_, lean_object* v_inst_3531_, lean_object* v_inst_3532_, lean_object* v_inst_3533_, lean_object* v_respType_3534_, lean_object* v_inst_3535_, lean_object* v_inst_3536_, lean_object* v_stateType_3537_, lean_object* v_inst_3538_, lean_object* v_handler_3539_, lean_object* v_onDidChange_3540_, lean_object* v_a_3541_){
_start:
{
lean_object* v_res_3542_; 
v_res_3542_ = l_Lean_Server_chainStatefulLspRequestHandler(v_method_3529_, v_paramType_3530_, v_inst_3531_, v_inst_3532_, v_inst_3533_, v_respType_3534_, v_inst_3535_, v_inst_3536_, v_stateType_3537_, v_inst_3538_, v_handler_3539_, v_onDidChange_3540_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___lam__0(lean_object* v_p_3543_, lean_object* v_x_3544_, lean_object* v_handler_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v_onDidChange_3548_; lean_object* v___x_3549_; 
v_onDidChange_3548_ = lean_ctor_get(v_handler_3545_, 4);
lean_inc_ref(v_onDidChange_3548_);
lean_dec_ref(v_handler_3545_);
lean_inc_ref(v___y_3546_);
v___x_3549_ = lean_apply_3(v_onDidChange_3548_, v_p_3543_, v___y_3546_, lean_box(0));
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___lam__0___boxed(lean_object* v_p_3550_, lean_object* v_x_3551_, lean_object* v_handler_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
lean_object* v_res_3555_; 
v_res_3555_ = l_Lean_Server_handleOnDidChange___lam__0(v_p_3550_, v_x_3551_, v_handler_3552_, v___y_3553_);
lean_dec_ref(v___y_3553_);
lean_dec_ref(v_x_3551_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0(lean_object* v_f_3556_, lean_object* v_x_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_){
_start:
{
lean_object* v___x_3562_; 
lean_inc_ref(v___y_3560_);
v___x_3562_ = lean_apply_4(v_f_3556_, v___y_3558_, v___y_3559_, v___y_3560_, lean_box(0));
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0___boxed(lean_object* v_f_3563_, lean_object* v_x_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0(v_f_3563_, v_x_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
lean_dec_ref(v___y_3567_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_3570_, lean_object* v_keys_3571_, lean_object* v_vals_3572_, lean_object* v_i_3573_, lean_object* v_acc_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v___x_3577_; uint8_t v___x_3578_; 
v___x_3577_ = lean_array_get_size(v_keys_3571_);
v___x_3578_ = lean_nat_dec_lt(v_i_3573_, v___x_3577_);
if (v___x_3578_ == 0)
{
lean_object* v___x_3579_; 
lean_dec(v_i_3573_);
lean_dec_ref(v_f_3570_);
v___x_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3579_, 0, v_acc_3574_);
return v___x_3579_;
}
else
{
lean_object* v_k_3580_; lean_object* v_v_3581_; lean_object* v___x_3582_; 
v_k_3580_ = lean_array_fget_borrowed(v_keys_3571_, v_i_3573_);
v_v_3581_ = lean_array_fget_borrowed(v_vals_3572_, v_i_3573_);
lean_inc_ref(v_f_3570_);
lean_inc_ref(v___y_3575_);
lean_inc(v_v_3581_);
lean_inc(v_k_3580_);
v___x_3582_ = lean_apply_5(v_f_3570_, v_acc_3574_, v_k_3580_, v_v_3581_, v___y_3575_, lean_box(0));
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v_a_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v_a_3583_ = lean_ctor_get(v___x_3582_, 0);
lean_inc(v_a_3583_);
lean_dec_ref_known(v___x_3582_, 1);
v___x_3584_ = lean_unsigned_to_nat(1u);
v___x_3585_ = lean_nat_add(v_i_3573_, v___x_3584_);
lean_dec(v_i_3573_);
v_i_3573_ = v___x_3585_;
v_acc_3574_ = v_a_3583_;
goto _start;
}
else
{
lean_dec(v_i_3573_);
lean_dec_ref(v_f_3570_);
return v___x_3582_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_3587_, lean_object* v_keys_3588_, lean_object* v_vals_3589_, lean_object* v_i_3590_, lean_object* v_acc_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3587_, v_keys_3588_, v_vals_3589_, v_i_3590_, v_acc_3591_, v___y_3592_);
lean_dec_ref(v___y_3592_);
lean_dec_ref(v_vals_3589_);
lean_dec_ref(v_keys_3588_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(lean_object* v_f_3595_, lean_object* v_x_3596_, lean_object* v_x_3597_, lean_object* v___y_3598_){
_start:
{
if (lean_obj_tag(v_x_3596_) == 0)
{
lean_object* v_es_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3620_; 
v_es_3600_ = lean_ctor_get(v_x_3596_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v_x_3596_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3602_ = v_x_3596_;
v_isShared_3603_ = v_isSharedCheck_3620_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_es_3600_);
lean_dec(v_x_3596_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3620_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3604_; lean_object* v___x_3605_; uint8_t v___x_3606_; 
v___x_3604_ = lean_unsigned_to_nat(0u);
v___x_3605_ = lean_array_get_size(v_es_3600_);
v___x_3606_ = lean_nat_dec_lt(v___x_3604_, v___x_3605_);
if (v___x_3606_ == 0)
{
lean_object* v___x_3608_; 
lean_dec_ref(v_es_3600_);
lean_dec_ref(v_f_3595_);
if (v_isShared_3603_ == 0)
{
lean_ctor_set(v___x_3602_, 0, v_x_3597_);
v___x_3608_ = v___x_3602_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_x_3597_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
else
{
uint8_t v___x_3610_; 
v___x_3610_ = lean_nat_dec_le(v___x_3605_, v___x_3605_);
if (v___x_3610_ == 0)
{
if (v___x_3606_ == 0)
{
lean_object* v___x_3612_; 
lean_dec_ref(v_es_3600_);
lean_dec_ref(v_f_3595_);
if (v_isShared_3603_ == 0)
{
lean_ctor_set(v___x_3602_, 0, v_x_3597_);
v___x_3612_ = v___x_3602_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_x_3597_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
else
{
size_t v___x_3614_; size_t v___x_3615_; lean_object* v___x_3616_; 
lean_del_object(v___x_3602_);
v___x_3614_ = ((size_t)0ULL);
v___x_3615_ = lean_usize_of_nat(v___x_3605_);
v___x_3616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3595_, v_es_3600_, v___x_3614_, v___x_3615_, v_x_3597_, v___y_3598_);
lean_dec_ref(v_es_3600_);
return v___x_3616_;
}
}
else
{
size_t v___x_3617_; size_t v___x_3618_; lean_object* v___x_3619_; 
lean_del_object(v___x_3602_);
v___x_3617_ = ((size_t)0ULL);
v___x_3618_ = lean_usize_of_nat(v___x_3605_);
v___x_3619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3595_, v_es_3600_, v___x_3617_, v___x_3618_, v_x_3597_, v___y_3598_);
lean_dec_ref(v_es_3600_);
return v___x_3619_;
}
}
}
}
else
{
lean_object* v_ks_3621_; lean_object* v_vs_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; 
v_ks_3621_ = lean_ctor_get(v_x_3596_, 0);
lean_inc_ref(v_ks_3621_);
v_vs_3622_ = lean_ctor_get(v_x_3596_, 1);
lean_inc_ref(v_vs_3622_);
lean_dec_ref_known(v_x_3596_, 2);
v___x_3623_ = lean_unsigned_to_nat(0u);
v___x_3624_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3595_, v_ks_3621_, v_vs_3622_, v___x_3623_, v_x_3597_, v___y_3598_);
lean_dec_ref(v_vs_3622_);
lean_dec_ref(v_ks_3621_);
return v___x_3624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_3625_, lean_object* v_as_3626_, size_t v_i_3627_, size_t v_stop_3628_, lean_object* v_b_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v_a_3633_; lean_object* v___y_3638_; uint8_t v___x_3640_; 
v___x_3640_ = lean_usize_dec_eq(v_i_3627_, v_stop_3628_);
if (v___x_3640_ == 0)
{
lean_object* v___x_3641_; 
v___x_3641_ = lean_array_uget_borrowed(v_as_3626_, v_i_3627_);
switch(lean_obj_tag(v___x_3641_))
{
case 0:
{
lean_object* v_key_3642_; lean_object* v_val_3643_; lean_object* v___x_3644_; 
v_key_3642_ = lean_ctor_get(v___x_3641_, 0);
v_val_3643_ = lean_ctor_get(v___x_3641_, 1);
lean_inc_ref(v_f_3625_);
lean_inc_ref(v___y_3630_);
lean_inc(v_val_3643_);
lean_inc(v_key_3642_);
v___x_3644_ = lean_apply_5(v_f_3625_, v_b_3629_, v_key_3642_, v_val_3643_, v___y_3630_, lean_box(0));
v___y_3638_ = v___x_3644_;
goto v___jp_3637_;
}
case 1:
{
lean_object* v_node_3645_; lean_object* v___x_3646_; 
v_node_3645_ = lean_ctor_get(v___x_3641_, 0);
lean_inc(v_node_3645_);
lean_inc_ref(v_f_3625_);
v___x_3646_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3625_, v_node_3645_, v_b_3629_, v___y_3630_);
v___y_3638_ = v___x_3646_;
goto v___jp_3637_;
}
default: 
{
v_a_3633_ = v_b_3629_;
goto v___jp_3632_;
}
}
}
else
{
lean_object* v___x_3647_; 
lean_dec_ref(v_f_3625_);
v___x_3647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3647_, 0, v_b_3629_);
return v___x_3647_;
}
v___jp_3632_:
{
size_t v___x_3634_; size_t v___x_3635_; 
v___x_3634_ = ((size_t)1ULL);
v___x_3635_ = lean_usize_add(v_i_3627_, v___x_3634_);
v_i_3627_ = v___x_3635_;
v_b_3629_ = v_a_3633_;
goto _start;
}
v___jp_3637_:
{
if (lean_obj_tag(v___y_3638_) == 0)
{
lean_object* v_a_3639_; 
v_a_3639_ = lean_ctor_get(v___y_3638_, 0);
lean_inc(v_a_3639_);
lean_dec_ref_known(v___y_3638_, 1);
v_a_3633_ = v_a_3639_;
goto v___jp_3632_;
}
else
{
lean_dec_ref(v_f_3625_);
return v___y_3638_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_3648_, lean_object* v_as_3649_, lean_object* v_i_3650_, lean_object* v_stop_3651_, lean_object* v_b_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_){
_start:
{
size_t v_i_boxed_3655_; size_t v_stop_boxed_3656_; lean_object* v_res_3657_; 
v_i_boxed_3655_ = lean_unbox_usize(v_i_3650_);
lean_dec(v_i_3650_);
v_stop_boxed_3656_ = lean_unbox_usize(v_stop_3651_);
lean_dec(v_stop_3651_);
v_res_3657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3648_, v_as_3649_, v_i_boxed_3655_, v_stop_boxed_3656_, v_b_3652_, v___y_3653_);
lean_dec_ref(v___y_3653_);
lean_dec_ref(v_as_3649_);
return v_res_3657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_3658_, lean_object* v_x_3659_, lean_object* v_x_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
lean_object* v_res_3663_; 
v_res_3663_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3658_, v_x_3659_, v_x_3660_, v___y_3661_);
lean_dec_ref(v___y_3661_);
return v_res_3663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(lean_object* v_map_3664_, lean_object* v_f_3665_, lean_object* v___y_3666_){
_start:
{
lean_object* v___f_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___f_3668_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3668_, 0, v_f_3665_);
v___x_3669_ = lean_box(0);
v___x_3670_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v___f_3668_, v_map_3664_, v___x_3669_, v___y_3666_);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___boxed(lean_object* v_map_3671_, lean_object* v_f_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_){
_start:
{
lean_object* v_res_3675_; 
v_res_3675_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(v_map_3671_, v_f_3672_, v___y_3673_);
lean_dec_ref(v___y_3673_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange(lean_object* v_p_3676_, lean_object* v_a_3677_){
_start:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___f_3681_; lean_object* v___x_3682_; 
v___x_3679_ = l_Lean_Server_statefulRequestHandlers;
v___x_3680_ = lean_st_ref_get(v___x_3679_);
v___f_3681_ = lean_alloc_closure((void*)(l_Lean_Server_handleOnDidChange___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3681_, 0, v_p_3676_);
v___x_3682_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(v___x_3680_, v___f_3681_, v_a_3677_);
return v___x_3682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___boxed(lean_object* v_p_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_){
_start:
{
lean_object* v_res_3686_; 
v_res_3686_ = l_Lean_Server_handleOnDidChange(v_p_3683_, v_a_3684_);
lean_dec_ref(v_a_3684_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0(lean_object* v_00_u03b2_3687_, lean_object* v_map_3688_, lean_object* v_f_3689_, lean_object* v___y_3690_){
_start:
{
lean_object* v___x_3692_; 
v___x_3692_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(v_map_3688_, v_f_3689_, v___y_3690_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___boxed(lean_object* v_00_u03b2_3693_, lean_object* v_map_3694_, lean_object* v_f_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_){
_start:
{
lean_object* v_res_3698_; 
v_res_3698_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0(v_00_u03b2_3693_, v_map_3694_, v_f_3695_, v___y_3696_);
lean_dec_ref(v___y_3696_);
return v_res_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg(lean_object* v_map_3699_, lean_object* v_f_3700_, lean_object* v_init_3701_, lean_object* v___y_3702_){
_start:
{
lean_object* v___x_3704_; 
v___x_3704_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3700_, v_map_3699_, v_init_3701_, v___y_3702_);
return v___x_3704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg___boxed(lean_object* v_map_3705_, lean_object* v_f_3706_, lean_object* v_init_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg(v_map_3705_, v_f_3706_, v_init_3707_, v___y_3708_);
lean_dec_ref(v___y_3708_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0(lean_object* v_00_u03c3_3711_, lean_object* v_00_u03b2_3712_, lean_object* v_map_3713_, lean_object* v_f_3714_, lean_object* v_init_3715_, lean_object* v___y_3716_){
_start:
{
lean_object* v___x_3718_; 
v___x_3718_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3714_, v_map_3713_, v_init_3715_, v___y_3716_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3719_, lean_object* v_00_u03b2_3720_, lean_object* v_map_3721_, lean_object* v_f_3722_, lean_object* v_init_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_){
_start:
{
lean_object* v_res_3726_; 
v_res_3726_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0(v_00_u03c3_3719_, v_00_u03b2_3720_, v_map_3721_, v_f_3722_, v_init_3723_, v___y_3724_);
lean_dec_ref(v___y_3724_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3727_, lean_object* v_00_u03b1_3728_, lean_object* v_00_u03b2_3729_, lean_object* v_f_3730_, lean_object* v_x_3731_, lean_object* v_x_3732_, lean_object* v___y_3733_){
_start:
{
lean_object* v___x_3735_; 
v___x_3735_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3730_, v_x_3731_, v_x_3732_, v___y_3733_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3736_, lean_object* v_00_u03b1_3737_, lean_object* v_00_u03b2_3738_, lean_object* v_f_3739_, lean_object* v_x_3740_, lean_object* v_x_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
lean_object* v_res_3744_; 
v_res_3744_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1(v_00_u03c3_3736_, v_00_u03b1_3737_, v_00_u03b2_3738_, v_f_3739_, v_x_3740_, v_x_3741_, v___y_3742_);
lean_dec_ref(v___y_3742_);
return v_res_3744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3745_, lean_object* v_00_u03b2_3746_, lean_object* v_00_u03c3_3747_, lean_object* v_f_3748_, lean_object* v_as_3749_, size_t v_i_3750_, size_t v_stop_3751_, lean_object* v_b_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v___x_3755_; 
v___x_3755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3748_, v_as_3749_, v_i_3750_, v_stop_3751_, v_b_3752_, v___y_3753_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3756_, lean_object* v_00_u03b2_3757_, lean_object* v_00_u03c3_3758_, lean_object* v_f_3759_, lean_object* v_as_3760_, lean_object* v_i_3761_, lean_object* v_stop_3762_, lean_object* v_b_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_){
_start:
{
size_t v_i_boxed_3766_; size_t v_stop_boxed_3767_; lean_object* v_res_3768_; 
v_i_boxed_3766_ = lean_unbox_usize(v_i_3761_);
lean_dec(v_i_3761_);
v_stop_boxed_3767_ = lean_unbox_usize(v_stop_3762_);
lean_dec(v_stop_3762_);
v_res_3768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3756_, v_00_u03b2_3757_, v_00_u03c3_3758_, v_f_3759_, v_as_3760_, v_i_boxed_3766_, v_stop_boxed_3767_, v_b_3763_, v___y_3764_);
lean_dec_ref(v___y_3764_);
lean_dec_ref(v_as_3760_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3769_, lean_object* v_00_u03b1_3770_, lean_object* v_00_u03b2_3771_, lean_object* v_f_3772_, lean_object* v_keys_3773_, lean_object* v_vals_3774_, lean_object* v_heq_3775_, lean_object* v_i_3776_, lean_object* v_acc_3777_, lean_object* v___y_3778_){
_start:
{
lean_object* v___x_3780_; 
v___x_3780_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3772_, v_keys_3773_, v_vals_3774_, v_i_3776_, v_acc_3777_, v___y_3778_);
return v___x_3780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3781_, lean_object* v_00_u03b1_3782_, lean_object* v_00_u03b2_3783_, lean_object* v_f_3784_, lean_object* v_keys_3785_, lean_object* v_vals_3786_, lean_object* v_heq_3787_, lean_object* v_i_3788_, lean_object* v_acc_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_){
_start:
{
lean_object* v_res_3792_; 
v_res_3792_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3781_, v_00_u03b1_3782_, v_00_u03b2_3783_, v_f_3784_, v_keys_3785_, v_vals_3786_, v_heq_3787_, v_i_3788_, v_acc_3789_, v___y_3790_);
lean_dec_ref(v___y_3790_);
lean_dec_ref(v_vals_3786_);
lean_dec_ref(v_keys_3785_);
return v_res_3792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest(lean_object* v_method_3795_, lean_object* v_params_3796_, lean_object* v_a_3797_){
_start:
{
uint8_t v___x_3799_; 
v___x_3799_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_3795_);
if (v___x_3799_ == 0)
{
lean_object* v___x_3800_; lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3816_; 
v___x_3800_ = l_Lean_Server_lookupLspRequestHandler(v_method_3795_);
v_a_3801_ = lean_ctor_get(v___x_3800_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3800_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3803_ = v___x_3800_;
v_isShared_3804_ = v_isSharedCheck_3816_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v___x_3800_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3816_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
if (lean_obj_tag(v_a_3801_) == 0)
{
lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3811_; 
lean_dec(v_params_3796_);
v___x_3805_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__0));
v___x_3806_ = lean_string_append(v___x_3805_, v_method_3795_);
v___x_3807_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__1));
v___x_3808_ = lean_string_append(v___x_3806_, v___x_3807_);
v___x_3809_ = l_Lean_Server_RequestError_internalError(v___x_3808_);
if (v_isShared_3804_ == 0)
{
lean_ctor_set_tag(v___x_3803_, 1);
lean_ctor_set(v___x_3803_, 0, v___x_3809_);
v___x_3811_ = v___x_3803_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3809_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
else
{
lean_object* v_val_3813_; lean_object* v_handle_3814_; lean_object* v___x_3815_; 
lean_del_object(v___x_3803_);
v_val_3813_ = lean_ctor_get(v_a_3801_, 0);
lean_inc(v_val_3813_);
lean_dec_ref_known(v_a_3801_, 1);
v_handle_3814_ = lean_ctor_get(v_val_3813_, 1);
lean_inc_ref(v_handle_3814_);
lean_dec(v_val_3813_);
lean_inc_ref(v_a_3797_);
v___x_3815_ = lean_apply_3(v_handle_3814_, v_params_3796_, v_a_3797_, lean_box(0));
return v___x_3815_;
}
}
}
else
{
lean_object* v___x_3817_; 
v___x_3817_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_3795_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; 
lean_dec(v_params_3796_);
v___x_3818_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__0));
v___x_3819_ = lean_string_append(v___x_3818_, v_method_3795_);
v___x_3820_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__1));
v___x_3821_ = lean_string_append(v___x_3819_, v___x_3820_);
v___x_3822_ = l_Lean_Server_RequestError_internalError(v___x_3821_);
v___x_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3822_);
return v___x_3823_;
}
else
{
lean_object* v_val_3824_; lean_object* v_handle_3825_; lean_object* v___x_3826_; 
v_val_3824_ = lean_ctor_get(v___x_3817_, 0);
lean_inc(v_val_3824_);
lean_dec_ref_known(v___x_3817_, 1);
v_handle_3825_ = lean_ctor_get(v_val_3824_, 2);
lean_inc_ref(v_handle_3825_);
lean_dec(v_val_3824_);
lean_inc_ref(v_a_3797_);
v___x_3826_ = lean_apply_3(v_handle_3825_, v_params_3796_, v_a_3797_, lean_box(0));
return v___x_3826_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest___boxed(lean_object* v_method_3827_, lean_object* v_params_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_){
_start:
{
lean_object* v_res_3831_; 
v_res_3831_ = l_Lean_Server_handleLspRequest(v_method_3827_, v_params_3828_, v_a_3829_);
lean_dec_ref(v_a_3829_);
lean_dec_ref(v_method_3827_);
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_routeLspRequest(lean_object* v_method_3832_, lean_object* v_params_3833_){
_start:
{
uint8_t v___x_3835_; 
v___x_3835_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_3832_);
if (v___x_3835_ == 0)
{
lean_object* v___x_3836_; lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3852_; 
v___x_3836_ = l_Lean_Server_lookupLspRequestHandler(v_method_3832_);
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3839_ = v___x_3836_;
v_isShared_3840_ = v_isSharedCheck_3852_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3836_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3852_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
if (lean_obj_tag(v_a_3837_) == 0)
{
lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3844_; 
lean_dec(v_params_3833_);
v___x_3841_ = l_Lean_Server_RequestError_methodNotFound(v_method_3832_);
v___x_3842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3842_, 0, v___x_3841_);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 0, v___x_3842_);
v___x_3844_ = v___x_3839_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v___x_3842_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
else
{
lean_object* v_val_3846_; lean_object* v_fileSource_3847_; lean_object* v___x_3848_; lean_object* v___x_3850_; 
v_val_3846_ = lean_ctor_get(v_a_3837_, 0);
lean_inc(v_val_3846_);
lean_dec_ref_known(v_a_3837_, 1);
v_fileSource_3847_ = lean_ctor_get(v_val_3846_, 0);
lean_inc_ref(v_fileSource_3847_);
lean_dec(v_val_3846_);
v___x_3848_ = lean_apply_1(v_fileSource_3847_, v_params_3833_);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 0, v___x_3848_);
v___x_3850_ = v___x_3839_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3848_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
else
{
lean_object* v___x_3853_; 
v___x_3853_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_3832_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; 
lean_dec(v_params_3833_);
v___x_3854_ = l_Lean_Server_RequestError_methodNotFound(v_method_3832_);
v___x_3855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3854_);
v___x_3856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3856_, 0, v___x_3855_);
return v___x_3856_;
}
else
{
lean_object* v_val_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3866_; 
v_val_3857_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3859_ = v___x_3853_;
v_isShared_3860_ = v_isSharedCheck_3866_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_val_3857_);
lean_dec(v___x_3853_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3866_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v_fileSource_3861_; lean_object* v___x_3862_; lean_object* v___x_3864_; 
v_fileSource_3861_ = lean_ctor_get(v_val_3857_, 0);
lean_inc_ref(v_fileSource_3861_);
lean_dec(v_val_3857_);
v___x_3862_ = lean_apply_1(v_fileSource_3861_, v_params_3833_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set_tag(v___x_3859_, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3862_);
v___x_3864_ = v___x_3859_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3862_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
return v___x_3864_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_routeLspRequest___boxed(lean_object* v_method_3867_, lean_object* v_params_3868_, lean_object* v_a_3869_){
_start:
{
lean_object* v_res_3870_; 
v_res_3870_ = l_Lean_Server_routeLspRequest(v_method_3867_, v_params_3868_);
lean_dec_ref(v_method_3867_);
return v_res_3870_;
}
}
lean_object* runtime_initialize_Lean_Server_RequestCancellation(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_FileSource(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_FileWorker_Utils(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_Mutex(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Requests(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Server_RequestCancellation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_FileSource(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_FileWorker_Utils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_Mutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_requestHandlers = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_requestHandlers);
lean_dec_ref(res);
res = l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_statefulRequestHandlers = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_statefulRequestHandlers);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_Requests(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Server_RequestCancellation(uint8_t builtin);
lean_object* initialize_Lean_Server_FileSource(uint8_t builtin);
lean_object* initialize_Lean_Server_FileWorker_Utils(uint8_t builtin);
lean_object* initialize_Std_Sync_Mutex(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Requests(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_RequestCancellation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_FileSource(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_FileWorker_Utils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sync_Mutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Requests(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_Requests(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_Requests(builtin);
}
#ifdef __cplusplus
}
#endif
