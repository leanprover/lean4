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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__1;
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
lean_dec_ref(v_a_151_);
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
lean_dec_ref(v_stx_x3f_231_);
v___x_234_ = 1;
v___x_235_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_val_233_, v___x_234_);
lean_dec(v_val_233_);
if (lean_obj_tag(v___x_235_) == 1)
{
lean_object* v_val_236_; uint8_t v___x_237_; 
v_val_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_val_236_);
lean_dec_ref(v___x_235_);
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
lean_dec_ref(v___x_278_);
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
lean_dec_ref(v_infoTree_x3f_298_);
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
lean_dec_ref(v_stx_x3f_321_);
v___x_324_ = 1;
v___x_325_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_val_323_, v___x_324_);
lean_dec(v_val_323_);
if (lean_obj_tag(v___x_325_) == 1)
{
lean_object* v_val_326_; uint8_t v___x_327_; 
v_val_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_val_326_);
lean_dec_ref(v___x_325_);
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
lean_dec_ref(v_stx_x3f_378_);
v___x_381_ = 1;
v___x_382_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_val_380_, v___x_381_);
lean_dec(v_val_380_);
if (lean_obj_tag(v___x_382_) == 1)
{
lean_object* v_val_383_; uint8_t v___x_384_; 
v_val_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_val_383_);
lean_dec_ref(v___x_382_);
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
lean_dec_ref(v_t_508_);
v___x_511_ = lean_apply_1(v_k_509_, v_response_510_);
return v___x_511_;
}
else
{
uint8_t v_code_512_; lean_object* v_message_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v_code_512_ = lean_ctor_get_uint8(v_t_508_, sizeof(void*)*1);
v_message_513_ = lean_ctor_get(v_t_508_, 0);
lean_inc_ref(v_message_513_);
lean_dec_ref(v_t_508_);
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
lean_dec_ref(v___x_614_);
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
lean_dec_ref(v_a_646_);
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
lean_dec_ref(v_a_646_);
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
lean_dec_ref(v_x_915_);
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
lean_dec_ref(v_x_984_);
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
lean_dec_ref(v___x_1106_);
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
lean_dec_ref(v___x_1106_);
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
lean_dec_ref(v_x_1171_);
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
lean_dec_ref(v_a_1183_);
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
lean_dec_ref(v___x_1351_);
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
lean_dec_ref(v___x_1364_);
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
lean_dec_ref(v_nextCmdSnap_x3f_1384_);
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
lean_dec_ref(v_result_x3f_1396_);
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
lean_dec_ref(v_x_1462_);
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
lean_dec_ref(v_a_1525_);
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
lean_dec_ref(v_a_1525_);
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
lean_dec_ref(v___x_1524_);
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
lean_dec_ref(v_a_1574_);
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
lean_dec_ref(v_a_1574_);
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
lean_dec_ref(v___x_1573_);
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
lean_dec_ref(v_a_1623_);
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
lean_dec_ref(v_a_1623_);
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
lean_dec_ref(v___x_1622_);
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
lean_dec_ref(v_serialize_x3f_1738_);
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
lean_dec_ref(v___x_1762_);
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
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1904_; size_t v___x_1905_; size_t v___x_1906_; 
v___x_1904_ = ((size_t)5ULL);
v___x_1905_ = ((size_t)1ULL);
v___x_1906_ = lean_usize_shift_left(v___x_1905_, v___x_1904_);
return v___x_1906_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1907_; size_t v___x_1908_; size_t v___x_1909_; 
v___x_1907_ = ((size_t)1ULL);
v___x_1908_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__0);
v___x_1909_ = lean_usize_sub(v___x_1908_, v___x_1907_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(lean_object* v_x_1910_, size_t v_x_1911_, lean_object* v_x_1912_){
_start:
{
if (lean_obj_tag(v_x_1910_) == 0)
{
lean_object* v_es_1913_; lean_object* v___x_1914_; size_t v___x_1915_; size_t v___x_1916_; size_t v___x_1917_; lean_object* v_j_1918_; lean_object* v___x_1919_; 
v_es_1913_ = lean_ctor_get(v_x_1910_, 0);
v___x_1914_ = lean_box(2);
v___x_1915_ = ((size_t)5ULL);
v___x_1916_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__1);
v___x_1917_ = lean_usize_land(v_x_1911_, v___x_1916_);
v_j_1918_ = lean_usize_to_nat(v___x_1917_);
v___x_1919_ = lean_array_get_borrowed(v___x_1914_, v_es_1913_, v_j_1918_);
lean_dec(v_j_1918_);
switch(lean_obj_tag(v___x_1919_))
{
case 0:
{
lean_object* v_key_1920_; lean_object* v_val_1921_; uint8_t v___x_1922_; 
v_key_1920_ = lean_ctor_get(v___x_1919_, 0);
v_val_1921_ = lean_ctor_get(v___x_1919_, 1);
v___x_1922_ = lean_string_dec_eq(v_x_1912_, v_key_1920_);
if (v___x_1922_ == 0)
{
lean_object* v___x_1923_; 
v___x_1923_ = lean_box(0);
return v___x_1923_;
}
else
{
lean_object* v___x_1924_; 
lean_inc(v_val_1921_);
v___x_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1924_, 0, v_val_1921_);
return v___x_1924_;
}
}
case 1:
{
lean_object* v_node_1925_; size_t v___x_1926_; 
v_node_1925_ = lean_ctor_get(v___x_1919_, 0);
v___x_1926_ = lean_usize_shift_right(v_x_1911_, v___x_1915_);
v_x_1910_ = v_node_1925_;
v_x_1911_ = v___x_1926_;
goto _start;
}
default: 
{
lean_object* v___x_1928_; 
v___x_1928_ = lean_box(0);
return v___x_1928_;
}
}
}
else
{
lean_object* v_ks_1929_; lean_object* v_vs_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v_ks_1929_ = lean_ctor_get(v_x_1910_, 0);
v_vs_1930_ = lean_ctor_get(v_x_1910_, 1);
v___x_1931_ = lean_unsigned_to_nat(0u);
v___x_1932_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(v_ks_1929_, v_vs_1930_, v___x_1931_, v_x_1912_);
return v___x_1932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___boxed(lean_object* v_x_1933_, lean_object* v_x_1934_, lean_object* v_x_1935_){
_start:
{
size_t v_x_279__boxed_1936_; lean_object* v_res_1937_; 
v_x_279__boxed_1936_ = lean_unbox_usize(v_x_1934_);
lean_dec(v_x_1934_);
v_res_1937_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_1933_, v_x_279__boxed_1936_, v_x_1935_);
lean_dec_ref(v_x_1935_);
lean_dec_ref(v_x_1933_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(lean_object* v_x_1938_, lean_object* v_x_1939_){
_start:
{
uint64_t v___x_1940_; size_t v___x_1941_; lean_object* v___x_1942_; 
v___x_1940_ = lean_string_hash(v_x_1939_);
v___x_1941_ = lean_uint64_to_usize(v___x_1940_);
v___x_1942_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_1938_, v___x_1941_, v_x_1939_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg___boxed(lean_object* v_x_1943_, lean_object* v_x_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v_x_1943_, v_x_1944_);
lean_dec_ref(v_x_1944_);
lean_dec_ref(v_x_1943_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupLspRequestHandler(lean_object* v_method_1946_){
_start:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1948_ = l_Lean_Server_requestHandlers;
v___x_1949_ = lean_st_ref_get(v___x_1948_);
v___x_1950_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v___x_1949_, v_method_1946_);
lean_dec(v___x_1949_);
v___x_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupLspRequestHandler___boxed(lean_object* v_method_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_Server_lookupLspRequestHandler(v_method_1952_);
lean_dec_ref(v_method_1952_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0(lean_object* v_00_u03b2_1955_, lean_object* v_x_1956_, lean_object* v_x_1957_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v_x_1956_, v_x_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___boxed(lean_object* v_00_u03b2_1959_, lean_object* v_x_1960_, lean_object* v_x_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0(v_00_u03b2_1959_, v_x_1960_, v_x_1961_);
lean_dec_ref(v_x_1961_);
lean_dec_ref(v_x_1960_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0(lean_object* v_00_u03b2_1963_, lean_object* v_x_1964_, size_t v_x_1965_, lean_object* v_x_1966_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_1964_, v_x_1965_, v_x_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1968_, lean_object* v_x_1969_, lean_object* v_x_1970_, lean_object* v_x_1971_){
_start:
{
size_t v_x_363__boxed_1972_; lean_object* v_res_1973_; 
v_x_363__boxed_1972_ = lean_unbox_usize(v_x_1970_);
lean_dec(v_x_1970_);
v_res_1973_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0(v_00_u03b2_1968_, v_x_1969_, v_x_363__boxed_1972_, v_x_1971_);
lean_dec_ref(v_x_1971_);
lean_dec_ref(v_x_1969_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1974_, lean_object* v_keys_1975_, lean_object* v_vals_1976_, lean_object* v_heq_1977_, lean_object* v_i_1978_, lean_object* v_k_1979_){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(v_keys_1975_, v_vals_1976_, v_i_1978_, v_k_1979_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1981_, lean_object* v_keys_1982_, lean_object* v_vals_1983_, lean_object* v_heq_1984_, lean_object* v_i_1985_, lean_object* v_k_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1(v_00_u03b2_1981_, v_keys_1982_, v_vals_1983_, v_heq_1984_, v_i_1985_, v_k_1986_);
lean_dec_ref(v_k_1986_);
lean_dec_ref(v_vals_1983_);
lean_dec_ref(v_keys_1982_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__0(lean_object* v_inst_1991_, lean_object* v_method_1992_, lean_object* v_x_1993_){
_start:
{
lean_object* v_response_1995_; 
if (lean_obj_tag(v_x_1993_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
lean_dec_ref(v_inst_1991_);
v_a_2019_ = lean_ctor_get(v_x_1993_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_x_1993_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v_x_1993_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v_x_1993_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
else
{
lean_object* v_a_2027_; lean_object* v_response_x3f_2028_; 
v_a_2027_ = lean_ctor_get(v_x_1993_, 0);
lean_inc(v_a_2027_);
lean_dec_ref(v_x_1993_);
v_response_x3f_2028_ = lean_ctor_get(v_a_2027_, 0);
if (lean_obj_tag(v_response_x3f_2028_) == 0)
{
lean_object* v_serialized_2029_; lean_object* v___x_2030_; 
v_serialized_2029_ = lean_ctor_get(v_a_2027_, 1);
lean_inc_ref(v_serialized_2029_);
lean_dec(v_a_2027_);
v___x_2030_ = l_Lean_Json_parse(v_serialized_2029_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2044_; 
lean_dec_ref(v_inst_1991_);
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2033_ = v___x_2030_;
v_isShared_2034_ = v_isSharedCheck_2044_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2030_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2044_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2042_; 
v___x_2035_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__2));
v___x_2036_ = lean_string_append(v___x_2035_, v_method_1992_);
v___x_2037_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1));
v___x_2038_ = lean_string_append(v___x_2036_, v___x_2037_);
v___x_2039_ = lean_string_append(v___x_2038_, v_a_2031_);
lean_dec(v_a_2031_);
v___x_2040_ = l_Lean_Server_RequestError_internalError(v___x_2039_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 0, v___x_2040_);
v___x_2042_ = v___x_2033_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
else
{
lean_object* v_a_2045_; 
v_a_2045_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_a_2045_);
lean_dec_ref(v___x_2030_);
v_response_1995_ = v_a_2045_;
goto v___jp_1994_;
}
}
else
{
lean_object* v_val_2046_; 
lean_inc_ref(v_response_x3f_2028_);
lean_dec(v_a_2027_);
v_val_2046_ = lean_ctor_get(v_response_x3f_2028_, 0);
lean_inc(v_val_2046_);
lean_dec_ref(v_response_x3f_2028_);
v_response_1995_ = v_val_2046_;
goto v___jp_1994_;
}
}
v___jp_1994_:
{
lean_object* v___x_1996_; 
v___x_1996_ = lean_apply_1(v_inst_1991_, v_response_1995_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2010_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_1999_ = v___x_1996_;
v_isShared_2000_ = v_isSharedCheck_2010_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1996_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2010_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2008_; 
v___x_2001_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__0));
v___x_2002_ = lean_string_append(v___x_2001_, v_method_1992_);
v___x_2003_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1));
v___x_2004_ = lean_string_append(v___x_2002_, v___x_2003_);
v___x_2005_ = lean_string_append(v___x_2004_, v_a_1997_);
lean_dec(v_a_1997_);
v___x_2006_ = l_Lean_Server_RequestError_internalError(v___x_2005_);
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 0, v___x_2006_);
v___x_2008_ = v___x_1999_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2006_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
v_a_2011_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_1996_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_1996_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__0___boxed(lean_object* v_inst_2047_, lean_object* v_method_2048_, lean_object* v_x_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__0(v_inst_2047_, v_method_2048_, v_x_2049_);
lean_dec_ref(v_method_2048_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__1(lean_object* v_inst_2051_, uint8_t v_a_2052_, lean_object* v_r_2053_){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2054_ = lean_apply_1(v_inst_2051_, v_r_2053_);
lean_inc(v___x_2054_);
v___x_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
v___x_2056_ = l_Lean_Json_compress(v___x_2054_);
v___x_2057_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2057_, 0, v___x_2055_);
lean_ctor_set(v___x_2057_, 1, v___x_2056_);
lean_ctor_set_uint8(v___x_2057_, sizeof(void*)*2, v_a_2052_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__1___boxed(lean_object* v_inst_2058_, lean_object* v_a_2059_, lean_object* v_r_2060_){
_start:
{
uint8_t v_a_2455__boxed_2061_; lean_object* v_res_2062_; 
v_a_2455__boxed_2061_ = lean_unbox(v_a_2059_);
v_res_2062_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__1(v_inst_2058_, v_a_2455__boxed_2061_, v_r_2060_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__2(lean_object* v_handle_2063_, lean_object* v_inst_2064_, lean_object* v___f_2065_, lean_object* v_handler_2066_, lean_object* v___f_2067_, lean_object* v_j_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v___x_2071_; 
lean_inc_ref(v___y_2069_);
lean_inc(v_j_2068_);
v___x_2071_ = lean_apply_3(v_handle_2063_, v_j_2068_, v___y_2069_, lean_box(0));
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; lean_object* v___x_2073_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2072_);
lean_dec_ref(v___x_2071_);
v___x_2073_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_2064_, v_j_2068_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2074_);
lean_dec_ref(v___x_2073_);
v___x_2075_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2065_, v_a_2072_);
lean_inc_ref(v___y_2069_);
v___x_2076_ = lean_apply_4(v_handler_2066_, v_a_2074_, v___x_2075_, v___y_2069_, lean_box(0));
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2086_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2079_ = v___x_2076_;
v_isShared_2080_ = v_isSharedCheck_2086_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2076_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2086_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2084_; 
v___x_2081_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_2081_, 0, lean_box(0));
lean_closure_set(v___x_2081_, 1, lean_box(0));
lean_closure_set(v___x_2081_, 2, lean_box(0));
lean_closure_set(v___x_2081_, 3, v___f_2067_);
v___x_2082_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___x_2081_, v_a_2077_);
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 0, v___x_2082_);
v___x_2084_ = v___x_2079_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2082_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec_ref(v___f_2067_);
v_a_2087_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2076_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2076_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_dec(v_a_2072_);
lean_dec_ref(v___f_2067_);
lean_dec_ref(v_handler_2066_);
lean_dec_ref(v___f_2065_);
v_a_2095_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2073_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2073_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
else
{
lean_dec(v_j_2068_);
lean_dec_ref(v___f_2067_);
lean_dec_ref(v_handler_2066_);
lean_dec_ref(v___f_2065_);
lean_dec_ref(v_inst_2064_);
return v___x_2071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__2___boxed(lean_object* v_handle_2103_, lean_object* v_inst_2104_, lean_object* v___f_2105_, lean_object* v_handler_2106_, lean_object* v___f_2107_, lean_object* v_j_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__2(v_handle_2103_, v_inst_2104_, v___f_2105_, v_handler_2106_, v___f_2107_, v_j_2108_, v___y_2109_);
lean_dec_ref(v___y_2109_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg(lean_object* v_method_2114_, lean_object* v_inst_2115_, lean_object* v_inst_2116_, lean_object* v_inst_2117_, lean_object* v_handler_2118_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_Lean_initializing();
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2170_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2123_ = v___x_2120_;
v_isShared_2124_ = v_isSharedCheck_2170_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2120_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2170_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
uint8_t v___x_2125_; 
v___x_2125_ = lean_unbox(v_a_2121_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2132_; 
lean_dec(v_a_2121_);
lean_dec_ref(v_handler_2118_);
lean_dec_ref(v_inst_2117_);
lean_dec_ref(v_inst_2116_);
lean_dec_ref(v_inst_2115_);
v___x_2126_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__0));
v___x_2127_ = lean_string_append(v___x_2126_, v_method_2114_);
lean_dec_ref(v_method_2114_);
v___x_2128_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__1));
v___x_2129_ = lean_string_append(v___x_2127_, v___x_2128_);
v___x_2130_ = lean_mk_io_user_error(v___x_2129_);
if (v_isShared_2124_ == 0)
{
lean_ctor_set_tag(v___x_2123_, 1);
lean_ctor_set(v___x_2123_, 0, v___x_2130_);
v___x_2132_ = v___x_2123_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v___x_2130_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
else
{
lean_object* v___x_2134_; lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2169_; 
lean_del_object(v___x_2123_);
v___x_2134_ = l_Lean_Server_lookupLspRequestHandler(v_method_2114_);
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2137_ = v___x_2134_;
v_isShared_2138_ = v_isSharedCheck_2169_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2134_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2169_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
if (lean_obj_tag(v_a_2135_) == 1)
{
lean_object* v_val_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v_fileSource_2142_; lean_object* v_handle_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2160_; 
v_val_2139_ = lean_ctor_get(v_a_2135_, 0);
lean_inc(v_val_2139_);
lean_dec_ref(v_a_2135_);
v___x_2140_ = l_Lean_Server_requestHandlers;
v___x_2141_ = lean_st_ref_take(v___x_2140_);
v_fileSource_2142_ = lean_ctor_get(v_val_2139_, 0);
v_handle_2143_ = lean_ctor_get(v_val_2139_, 1);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_val_2139_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2145_ = v_val_2139_;
v_isShared_2146_ = v_isSharedCheck_2160_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_handle_2143_);
lean_inc(v_fileSource_2142_);
lean_dec(v_val_2139_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2160_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___f_2147_; lean_object* v___x_2148_; lean_object* v___f_2149_; lean_object* v___f_2150_; lean_object* v___f_2151_; lean_object* v___x_2153_; 
lean_inc_ref(v_method_2114_);
v___f_2147_ = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2147_, 0, v_inst_2116_);
lean_closure_set(v___f_2147_, 1, v_method_2114_);
v___x_2148_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___f_2149_ = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2149_, 0, v_inst_2117_);
lean_closure_set(v___f_2149_, 1, v_a_2121_);
v___f_2150_ = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2150_, 0, v_handle_2143_);
lean_closure_set(v___f_2150_, 1, v_inst_2115_);
lean_closure_set(v___f_2150_, 2, v___f_2147_);
lean_closure_set(v___f_2150_, 3, v_handler_2118_);
lean_closure_set(v___f_2150_, 4, v___f_2149_);
v___f_2151_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 1, v___f_2150_);
v___x_2153_ = v___x_2145_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_fileSource_2142_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v___f_2150_);
v___x_2153_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2157_; 
v___x_2154_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2151_, v___x_2148_, v___x_2141_, v_method_2114_, v___x_2153_);
v___x_2155_ = lean_st_ref_set(v___x_2140_, v___x_2154_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v___x_2155_);
v___x_2157_ = v___x_2137_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2155_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2167_; 
lean_dec(v_a_2135_);
lean_dec(v_a_2121_);
lean_dec_ref(v_handler_2118_);
lean_dec_ref(v_inst_2117_);
lean_dec_ref(v_inst_2116_);
lean_dec_ref(v_inst_2115_);
v___x_2161_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__0));
v___x_2162_ = lean_string_append(v___x_2161_, v_method_2114_);
lean_dec_ref(v_method_2114_);
v___x_2163_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__1));
v___x_2164_ = lean_string_append(v___x_2162_, v___x_2163_);
v___x_2165_ = lean_mk_io_user_error(v___x_2164_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set_tag(v___x_2137_, 1);
lean_ctor_set(v___x_2137_, 0, v___x_2165_);
v___x_2167_ = v___x_2137_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec_ref(v_handler_2118_);
lean_dec_ref(v_inst_2117_);
lean_dec_ref(v_inst_2116_);
lean_dec_ref(v_inst_2115_);
lean_dec_ref(v_method_2114_);
v_a_2171_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2120_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2120_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___boxed(lean_object* v_method_2179_, lean_object* v_inst_2180_, lean_object* v_inst_2181_, lean_object* v_inst_2182_, lean_object* v_handler_2183_, lean_object* v_a_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Lean_Server_chainLspRequestHandler___redArg(v_method_2179_, v_inst_2180_, v_inst_2181_, v_inst_2182_, v_handler_2183_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler(lean_object* v_method_2186_, lean_object* v_paramType_2187_, lean_object* v_inst_2188_, lean_object* v_respType_2189_, lean_object* v_inst_2190_, lean_object* v_inst_2191_, lean_object* v_handler_2192_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_Server_chainLspRequestHandler___redArg(v_method_2186_, v_inst_2188_, v_inst_2190_, v_inst_2191_, v_handler_2192_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___boxed(lean_object* v_method_2195_, lean_object* v_paramType_2196_, lean_object* v_inst_2197_, lean_object* v_respType_2198_, lean_object* v_inst_2199_, lean_object* v_inst_2200_, lean_object* v_handler_2201_, lean_object* v_a_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_Server_chainLspRequestHandler(v_method_2195_, v_paramType_2196_, v_inst_2197_, v_respType_2198_, v_inst_2199_, v_inst_2200_, v_handler_2201_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorIdx(lean_object* v_x_2204_){
_start:
{
if (lean_obj_tag(v_x_2204_) == 0)
{
lean_object* v___x_2205_; 
v___x_2205_ = lean_unsigned_to_nat(0u);
return v___x_2205_;
}
else
{
lean_object* v___x_2206_; 
v___x_2206_ = lean_unsigned_to_nat(1u);
return v___x_2206_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorIdx___boxed(lean_object* v_x_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Lean_Server_RequestHandlerCompleteness_ctorIdx(v_x_2207_);
lean_dec(v_x_2207_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(lean_object* v_t_2209_, lean_object* v_k_2210_){
_start:
{
if (lean_obj_tag(v_t_2209_) == 0)
{
return v_k_2210_;
}
else
{
lean_object* v_refreshMethod_2211_; lean_object* v_refreshIntervalMs_2212_; lean_object* v___x_2213_; 
v_refreshMethod_2211_ = lean_ctor_get(v_t_2209_, 0);
lean_inc_ref(v_refreshMethod_2211_);
v_refreshIntervalMs_2212_ = lean_ctor_get(v_t_2209_, 1);
lean_inc(v_refreshIntervalMs_2212_);
lean_dec_ref(v_t_2209_);
v___x_2213_ = lean_apply_2(v_k_2210_, v_refreshMethod_2211_, v_refreshIntervalMs_2212_);
return v___x_2213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim(lean_object* v_motive_2214_, lean_object* v_ctorIdx_2215_, lean_object* v_t_2216_, lean_object* v_h_2217_, lean_object* v_k_2218_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_2216_, v_k_2218_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim___boxed(lean_object* v_motive_2220_, lean_object* v_ctorIdx_2221_, lean_object* v_t_2222_, lean_object* v_h_2223_, lean_object* v_k_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim(v_motive_2220_, v_ctorIdx_2221_, v_t_2222_, v_h_2223_, v_k_2224_);
lean_dec(v_ctorIdx_2221_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_complete_elim___redArg(lean_object* v_t_2226_, lean_object* v_complete_2227_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_2226_, v_complete_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_complete_elim(lean_object* v_motive_2229_, lean_object* v_t_2230_, lean_object* v_h_2231_, lean_object* v_complete_2232_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_2230_, v_complete_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_partial_elim___redArg(lean_object* v_t_2234_, lean_object* v_partial_2235_){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_2234_, v_partial_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_partial_elim(lean_object* v_motive_2237_, lean_object* v_t_2238_, lean_object* v_h_2239_, lean_object* v_partial_2240_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_2238_, v_partial_2240_);
return v___x_2241_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2242_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_);
v___x_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2246_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_);
v___x_2247_ = lean_st_mk_ref(v___x_2246_);
v___x_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2____boxed(lean_object* v_a_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_();
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(lean_object* v_method_2252_, lean_object* v_state_2253_, lean_object* v_inst_2254_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_state_2253_, v_inst_2254_);
if (lean_obj_tag(v___x_2256_) == 1)
{
lean_object* v_val_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
v_val_2257_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2256_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_val_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
lean_ctor_set_tag(v___x_2259_, 0);
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_val_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
else
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
lean_dec(v___x_2256_);
v___x_2265_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0));
v___x_2266_ = lean_string_append(v___x_2265_, v_method_2252_);
v___x_2267_ = l_Lean_Server_RequestError_internalError(v___x_2266_);
v___x_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
return v___x_2268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___boxed(lean_object* v_method_2269_, lean_object* v_state_2270_, lean_object* v_inst_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_2269_, v_state_2270_, v_inst_2271_);
lean_dec(v_inst_2271_);
lean_dec(v_state_2270_);
lean_dec_ref(v_method_2269_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(lean_object* v_method_2274_, lean_object* v_state_2275_, lean_object* v_stateType_2276_, lean_object* v_inst_2277_, lean_object* v_a_2278_){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_2274_, v_state_2275_, v_inst_2277_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___boxed(lean_object* v_method_2281_, lean_object* v_state_2282_, lean_object* v_stateType_2283_, lean_object* v_inst_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_2281_, v_state_2282_, v_stateType_2283_, v_inst_2284_, v_a_2285_);
lean_dec_ref(v_a_2285_);
lean_dec(v_inst_2284_);
lean_dec(v_state_2282_);
lean_dec_ref(v_method_2281_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(lean_object* v_method_2288_, lean_object* v_state_2289_, lean_object* v_inst_2290_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_state_2289_, v_inst_2290_);
if (lean_obj_tag(v___x_2292_) == 1)
{
lean_object* v_val_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
v_val_2293_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2292_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_val_2293_);
lean_dec(v___x_2292_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
lean_ctor_set_tag(v___x_2295_, 0);
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_val_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
else
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
lean_dec(v___x_2292_);
v___x_2301_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0));
v___x_2302_ = lean_string_append(v___x_2301_, v_method_2288_);
v___x_2303_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
v___x_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
return v___x_2304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg___boxed(lean_object* v_method_2305_, lean_object* v_state_2306_, lean_object* v_inst_2307_, lean_object* v_a_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(v_method_2305_, v_state_2306_, v_inst_2307_);
lean_dec(v_inst_2307_);
lean_dec(v_state_2306_);
lean_dec_ref(v_method_2305_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21(lean_object* v_method_2310_, lean_object* v_state_2311_, lean_object* v_stateType_2312_, lean_object* v_inst_2313_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(v_method_2310_, v_state_2311_, v_inst_2313_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___boxed(lean_object* v_method_2316_, lean_object* v_state_2317_, lean_object* v_stateType_2318_, lean_object* v_inst_2319_, lean_object* v_a_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21(v_method_2316_, v_state_2317_, v_stateType_2318_, v_inst_2319_);
lean_dec(v_inst_2319_);
lean_dec(v_state_2317_);
lean_dec_ref(v_method_2316_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1(lean_object* v_inst_2322_, lean_object* v_method_2323_, lean_object* v_inst_2324_, lean_object* v_handler_2325_, lean_object* v_inst_2326_, lean_object* v_param_2327_, lean_object* v_state_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v___x_2331_; 
v___x_2331_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_2322_, v_param_2327_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v___x_2333_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2332_);
lean_dec_ref(v___x_2331_);
v___x_2333_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_2323_, v_state_2328_, v_inst_2324_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2335_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_a_2334_);
lean_dec_ref(v___x_2333_);
lean_inc_ref(v___y_2329_);
v___x_2335_ = lean_apply_4(v_handler_2325_, v_a_2332_, v_a_2334_, v___y_2329_, lean_box(0));
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2359_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2338_ = v___x_2335_;
v_isShared_2339_ = v_isSharedCheck_2359_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2335_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2359_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v_fst_2340_; lean_object* v_snd_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2358_; 
v_fst_2340_ = lean_ctor_get(v_a_2336_, 0);
v_snd_2341_ = lean_ctor_get(v_a_2336_, 1);
v_isSharedCheck_2358_ = !lean_is_exclusive(v_a_2336_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2343_ = v_a_2336_;
v_isShared_2344_ = v_isSharedCheck_2358_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_snd_2341_);
lean_inc(v_fst_2340_);
lean_dec(v_a_2336_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2358_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v_response_2345_; uint8_t v_isComplete_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2352_; 
v_response_2345_ = lean_ctor_get(v_fst_2340_, 0);
lean_inc(v_response_2345_);
v_isComplete_2346_ = lean_ctor_get_uint8(v_fst_2340_, sizeof(void*)*1);
lean_dec(v_fst_2340_);
v___x_2347_ = lean_apply_1(v_inst_2326_, v_response_2345_);
lean_inc(v___x_2347_);
v___x_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2347_);
v___x_2349_ = l_Lean_Json_compress(v___x_2347_);
v___x_2350_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2350_, 0, v___x_2348_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
lean_ctor_set_uint8(v___x_2350_, sizeof(void*)*2, v_isComplete_2346_);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 0, v_inst_2324_);
v___x_2352_ = v___x_2343_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_inst_2324_);
lean_ctor_set(v_reuseFailAlloc_2357_, 1, v_snd_2341_);
v___x_2352_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
lean_object* v___x_2353_; lean_object* v___x_2355_; 
v___x_2353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2350_);
lean_ctor_set(v___x_2353_, 1, v___x_2352_);
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 0, v___x_2353_);
v___x_2355_ = v___x_2338_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2353_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec_ref(v_inst_2326_);
lean_dec(v_inst_2324_);
v_a_2360_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2335_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2335_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec(v_a_2332_);
lean_dec_ref(v_inst_2326_);
lean_dec_ref(v_handler_2325_);
lean_dec(v_inst_2324_);
v_a_2368_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2333_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2333_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
lean_dec_ref(v_inst_2326_);
lean_dec_ref(v_handler_2325_);
lean_dec(v_inst_2324_);
v_a_2376_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2331_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2331_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1___boxed(lean_object* v_inst_2384_, lean_object* v_method_2385_, lean_object* v_inst_2386_, lean_object* v_handler_2387_, lean_object* v_inst_2388_, lean_object* v_param_2389_, lean_object* v_state_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1(v_inst_2384_, v_method_2385_, v_inst_2386_, v_handler_2387_, v_inst_2388_, v_param_2389_, v_state_2390_, v___y_2391_);
lean_dec_ref(v___y_2391_);
lean_dec(v_state_2390_);
lean_dec_ref(v_method_2385_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0(lean_object* v_method_2394_, lean_object* v_inst_2395_, lean_object* v_onDidChange_2396_, lean_object* v_param_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_2394_, v___y_2398_, v_inst_2395_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; lean_object* v___x_2403_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
lean_inc(v_a_2402_);
lean_dec_ref(v___x_2401_);
lean_inc_ref(v___y_2399_);
v___x_2403_ = lean_apply_4(v_onDidChange_2396_, v_param_2397_, v_a_2402_, v___y_2399_, lean_box(0));
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2422_; 
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2406_ = v___x_2403_;
v_isShared_2407_ = v_isSharedCheck_2422_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2403_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2422_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v_snd_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2420_; 
v_snd_2408_ = lean_ctor_get(v_a_2404_, 1);
v_isSharedCheck_2420_ = !lean_is_exclusive(v_a_2404_);
if (v_isSharedCheck_2420_ == 0)
{
lean_object* v_unused_2421_; 
v_unused_2421_ = lean_ctor_get(v_a_2404_, 0);
lean_dec(v_unused_2421_);
v___x_2410_ = v_a_2404_;
v_isShared_2411_ = v_isSharedCheck_2420_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_snd_2408_);
lean_dec(v_a_2404_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2420_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2413_; 
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 0, v_inst_2395_);
v___x_2413_ = v___x_2410_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_inst_2395_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v_snd_2408_);
v___x_2413_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2417_; 
v___x_2414_ = lean_box(0);
v___x_2415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
lean_ctor_set(v___x_2415_, 1, v___x_2413_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 0, v___x_2415_);
v___x_2417_ = v___x_2406_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2415_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
}
else
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2430_; 
lean_dec(v_inst_2395_);
v_a_2423_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2425_ = v___x_2403_;
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2403_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2428_; 
if (v_isShared_2426_ == 0)
{
v___x_2428_ = v___x_2425_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2423_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
lean_dec_ref(v_param_2397_);
lean_dec_ref(v_onDidChange_2396_);
lean_dec(v_inst_2395_);
v_a_2431_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2401_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2401_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object* v_method_2439_, lean_object* v_inst_2440_, lean_object* v_onDidChange_2441_, lean_object* v_param_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0(v_method_2439_, v_inst_2440_, v_onDidChange_2441_, v_param_2442_, v___y_2443_, v___y_2444_);
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
lean_dec_ref(v_method_2439_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2(lean_object* v___x_2447_, lean_object* v_x_2448_){
_start:
{
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2___boxed(lean_object* v___x_2449_, lean_object* v_x_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2(v___x_2449_, v_x_2450_);
lean_dec_ref(v_x_2450_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3(lean_object* v___x_2452_, lean_object* v_x_2453_){
_start:
{
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3___boxed(lean_object* v___x_2454_, lean_object* v_x_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3(v___x_2454_, v_x_2455_);
lean_dec_ref(v_x_2455_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4(lean_object* v_val_2457_, lean_object* v___f_2458_, lean_object* v_param_2459_, lean_object* v_x_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2463_ = lean_st_ref_get(v_val_2457_);
lean_inc_ref(v___y_2461_);
v___x_2464_ = lean_apply_4(v___f_2458_, v_param_2459_, v___x_2463_, v___y_2461_, lean_box(0));
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2475_; 
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2467_ = v___x_2464_;
v_isShared_2468_ = v_isSharedCheck_2475_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2464_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2475_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v_fst_2469_; lean_object* v_snd_2470_; lean_object* v___x_2471_; lean_object* v___x_2473_; 
v_fst_2469_ = lean_ctor_get(v_a_2465_, 0);
lean_inc(v_fst_2469_);
v_snd_2470_ = lean_ctor_get(v_a_2465_, 1);
lean_inc(v_snd_2470_);
lean_dec(v_a_2465_);
v___x_2471_ = lean_st_ref_set(v_val_2457_, v_snd_2470_);
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 0, v_fst_2469_);
v___x_2473_ = v___x_2467_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_fst_2469_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
v_a_2476_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2464_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2464_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4___boxed(lean_object* v_val_2484_, lean_object* v___f_2485_, lean_object* v_param_2486_, lean_object* v_x_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4(v_val_2484_, v___f_2485_, v_param_2486_, v_x_2487_, v___y_2488_);
lean_dec_ref(v___y_2488_);
lean_dec(v_val_2484_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5(lean_object* v___f_2491_, lean_object* v___f_2492_, lean_object* v_lastTask_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v___x_2497_; lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2507_; 
v___x_2497_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_lastTask_2493_, v___f_2491_, v___y_2495_);
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2500_ = v___x_2497_;
v_isShared_2501_ = v_isSharedCheck_2507_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2497_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2507_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2505_; 
lean_inc(v_a_2498_);
v___x_2502_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2492_, v_a_2498_);
v___x_2503_ = lean_st_ref_set(v___y_2494_, v___x_2502_);
if (v_isShared_2501_ == 0)
{
v___x_2505_ = v___x_2500_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2498_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5___boxed(lean_object* v___f_2508_, lean_object* v___f_2509_, lean_object* v_lastTask_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5(v___f_2508_, v___f_2509_, v_lastTask_2510_, v___y_2511_, v___y_2512_);
lean_dec_ref(v___y_2512_);
lean_dec(v___y_2511_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6(lean_object* v_val_2515_, lean_object* v___f_2516_, lean_object* v___f_2517_, lean_object* v___f_2518_, lean_object* v___x_2519_, lean_object* v___f_2520_, lean_object* v___f_2521_, lean_object* v_val_2522_, lean_object* v_param_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v___f_2526_; lean_object* v___f_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_6410__overap_2530_; lean_object* v___x_2531_; 
v___f_2526_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2526_, 0, v_val_2515_);
lean_closure_set(v___f_2526_, 1, v___f_2516_);
lean_closure_set(v___f_2526_, 2, v_param_2523_);
v___f_2527_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5___boxed), 6, 2);
lean_closure_set(v___f_2527_, 0, v___f_2526_);
lean_closure_set(v___f_2527_, 1, v___f_2517_);
v___x_2528_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_2528_, 0, lean_box(0));
lean_closure_set(v___x_2528_, 1, lean_box(0));
lean_closure_set(v___x_2528_, 2, lean_box(0));
lean_closure_set(v___x_2528_, 3, v___f_2518_);
lean_inc_ref(v___x_2519_);
v___x_2529_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_2529_, 0, lean_box(0));
lean_closure_set(v___x_2529_, 1, lean_box(0));
lean_closure_set(v___x_2529_, 2, lean_box(0));
lean_closure_set(v___x_2529_, 3, v___x_2519_);
lean_closure_set(v___x_2529_, 4, lean_box(0));
lean_closure_set(v___x_2529_, 5, lean_box(0));
lean_closure_set(v___x_2529_, 6, v___x_2528_);
lean_closure_set(v___x_2529_, 7, v___f_2527_);
v___x_6410__overap_2530_ = l_Std_Mutex_atomically___redArg(v___x_2519_, v___f_2520_, v___f_2521_, v_val_2522_, v___x_2529_);
lean_inc_ref(v___y_2524_);
v___x_2531_ = lean_apply_2(v___x_6410__overap_2530_, v___y_2524_, lean_box(0));
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6___boxed(lean_object* v_val_2532_, lean_object* v___f_2533_, lean_object* v___f_2534_, lean_object* v___f_2535_, lean_object* v___x_2536_, lean_object* v___f_2537_, lean_object* v___f_2538_, lean_object* v_val_2539_, lean_object* v_param_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6(v_val_2532_, v___f_2533_, v___f_2534_, v___f_2535_, v___x_2536_, v___f_2537_, v___f_2538_, v_val_2539_, v_param_2540_, v___y_2541_);
lean_dec_ref(v___y_2541_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7(lean_object* v_val_2544_, lean_object* v___f_2545_, lean_object* v_param_2546_, lean_object* v_x_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = lean_st_ref_get(v_val_2544_);
lean_inc_ref(v___y_2548_);
v___x_2551_ = lean_apply_4(v___f_2545_, v_param_2546_, v___x_2550_, v___y_2548_, lean_box(0));
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2561_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2554_ = v___x_2551_;
v_isShared_2555_ = v_isSharedCheck_2561_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2551_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2561_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v_snd_2556_; lean_object* v___x_2557_; lean_object* v___x_2559_; 
v_snd_2556_ = lean_ctor_get(v_a_2552_, 1);
lean_inc(v_snd_2556_);
lean_dec(v_a_2552_);
v___x_2557_ = lean_st_ref_set(v_val_2544_, v_snd_2556_);
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 0, v___x_2557_);
v___x_2559_ = v___x_2554_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2557_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2569_; 
v_a_2562_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2564_ = v___x_2551_;
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2551_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2562_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7___boxed(lean_object* v_val_2570_, lean_object* v___f_2571_, lean_object* v_param_2572_, lean_object* v_x_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7(v_val_2570_, v___f_2571_, v_param_2572_, v_x_2573_, v___y_2574_);
lean_dec_ref(v___y_2574_);
lean_dec(v_val_2570_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8(lean_object* v___f_2577_, lean_object* v___f_2578_, lean_object* v_lastTask_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v___x_2583_; lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2593_; 
v___x_2583_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_lastTask_2579_, v___f_2577_, v___y_2581_);
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2586_ = v___x_2583_;
v_isShared_2587_ = v_isSharedCheck_2593_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2583_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2593_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2591_; 
v___x_2588_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2578_, v_a_2584_);
v___x_2589_ = lean_st_ref_set(v___y_2580_, v___x_2588_);
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 0, v___x_2589_);
v___x_2591_ = v___x_2586_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v___x_2589_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8___boxed(lean_object* v___f_2594_, lean_object* v___f_2595_, lean_object* v_lastTask_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8(v___f_2594_, v___f_2595_, v_lastTask_2596_, v___y_2597_, v___y_2598_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9(lean_object* v_val_2601_, lean_object* v___f_2602_, lean_object* v___f_2603_, lean_object* v___f_2604_, lean_object* v___x_2605_, lean_object* v___f_2606_, lean_object* v___f_2607_, lean_object* v_val_2608_, lean_object* v_param_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v___f_2612_; lean_object* v___f_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_6461__overap_2616_; lean_object* v___x_2617_; 
v___f_2612_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7___boxed), 6, 3);
lean_closure_set(v___f_2612_, 0, v_val_2601_);
lean_closure_set(v___f_2612_, 1, v___f_2602_);
lean_closure_set(v___f_2612_, 2, v_param_2609_);
v___f_2613_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8___boxed), 6, 2);
lean_closure_set(v___f_2613_, 0, v___f_2612_);
lean_closure_set(v___f_2613_, 1, v___f_2603_);
v___x_2614_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_2614_, 0, lean_box(0));
lean_closure_set(v___x_2614_, 1, lean_box(0));
lean_closure_set(v___x_2614_, 2, lean_box(0));
lean_closure_set(v___x_2614_, 3, v___f_2604_);
lean_inc_ref(v___x_2605_);
v___x_2615_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_2615_, 0, lean_box(0));
lean_closure_set(v___x_2615_, 1, lean_box(0));
lean_closure_set(v___x_2615_, 2, lean_box(0));
lean_closure_set(v___x_2615_, 3, v___x_2605_);
lean_closure_set(v___x_2615_, 4, lean_box(0));
lean_closure_set(v___x_2615_, 5, lean_box(0));
lean_closure_set(v___x_2615_, 6, v___x_2614_);
lean_closure_set(v___x_2615_, 7, v___f_2613_);
v___x_6461__overap_2616_ = l_Std_Mutex_atomically___redArg(v___x_2605_, v___f_2606_, v___f_2607_, v_val_2608_, v___x_2615_);
lean_inc_ref(v___y_2610_);
v___x_2617_ = lean_apply_2(v___x_6461__overap_2616_, v___y_2610_, lean_box(0));
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9___boxed(lean_object* v_val_2618_, lean_object* v___f_2619_, lean_object* v___f_2620_, lean_object* v___f_2621_, lean_object* v___x_2622_, lean_object* v___f_2623_, lean_object* v___f_2624_, lean_object* v_val_2625_, lean_object* v_param_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9(v_val_2618_, v___f_2619_, v___f_2620_, v___f_2621_, v___x_2622_, v___f_2623_, v___f_2624_, v_val_2625_, v_param_2626_, v___y_2627_);
lean_dec_ref(v___y_2627_);
return v_res_2629_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0(void){
_start:
{
lean_object* v___x_2630_; 
v___x_2630_ = l_instMonadEIO(lean_box(0));
return v___x_2630_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1(void){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2631_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0);
v___x_2632_ = l_ReaderT_instMonad___redArg(v___x_2631_);
return v___x_2632_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3(void){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = lean_box(0);
v___x_2635_ = lean_task_pure(v___x_2634_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(lean_object* v_method_2661_, lean_object* v_completeness_2662_, lean_object* v_inst_2663_, lean_object* v_inst_2664_, lean_object* v_inst_2665_, lean_object* v_inst_2666_, lean_object* v_initState_2667_, lean_object* v_handler_2668_, lean_object* v_onDidChange_2669_){
_start:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2671_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1);
v___x_2672_ = l_Lean_initializing();
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2710_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2675_ = v___x_2672_;
v_isShared_2676_ = v_isSharedCheck_2710_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2672_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2710_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
uint8_t v___x_2677_; 
v___x_2677_ = lean_unbox(v_a_2673_);
lean_dec(v_a_2673_);
if (v___x_2677_ == 0)
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2684_; 
lean_dec_ref(v_onDidChange_2669_);
lean_dec_ref(v_handler_2668_);
lean_dec(v_initState_2667_);
lean_dec(v_inst_2666_);
lean_dec_ref(v_inst_2665_);
lean_dec_ref(v_inst_2664_);
lean_dec_ref(v_inst_2663_);
lean_dec(v_completeness_2662_);
v___x_2678_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2));
v___x_2679_ = lean_string_append(v___x_2678_, v_method_2661_);
lean_dec_ref(v_method_2661_);
v___x_2680_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__1));
v___x_2681_ = lean_string_append(v___x_2679_, v___x_2680_);
v___x_2682_ = lean_mk_io_user_error(v___x_2681_);
if (v_isShared_2676_ == 0)
{
lean_ctor_set_tag(v___x_2675_, 1);
lean_ctor_set(v___x_2675_, 0, v___x_2682_);
v___x_2684_ = v___x_2675_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2682_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
else
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___f_2692_; lean_object* v___f_2693_; lean_object* v___f_2694_; lean_object* v___f_2695_; lean_object* v___f_2696_; lean_object* v___f_2697_; lean_object* v___x_2698_; lean_object* v___f_2699_; lean_object* v___f_2700_; lean_object* v___f_2701_; lean_object* v___f_2702_; lean_object* v___f_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2708_; 
v___x_2686_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3);
v___x_2687_ = l_Std_Mutex_new___redArg(v___x_2686_);
lean_inc_n(v_inst_2666_, 2);
v___x_2688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2688_, 0, v_inst_2666_);
lean_ctor_set(v___x_2688_, 1, v_initState_2667_);
lean_inc_ref(v___x_2688_);
v___x_2689_ = lean_st_mk_ref(v___x_2688_);
v___x_2690_ = l_Lean_Server_statefulRequestHandlers;
v___x_2691_ = lean_st_ref_take(v___x_2690_);
v___f_2692_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__7));
lean_inc_ref(v_inst_2663_);
v___f_2693_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2693_, 0, v_inst_2663_);
lean_closure_set(v___f_2693_, 1, v_inst_2664_);
lean_inc_ref_n(v_method_2661_, 2);
v___f_2694_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1___boxed), 9, 5);
lean_closure_set(v___f_2694_, 0, v_inst_2663_);
lean_closure_set(v___f_2694_, 1, v_method_2661_);
lean_closure_set(v___f_2694_, 2, v_inst_2666_);
lean_closure_set(v___f_2694_, 3, v_handler_2668_);
lean_closure_set(v___f_2694_, 4, v_inst_2665_);
v___f_2695_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0___boxed), 7, 3);
lean_closure_set(v___f_2695_, 0, v_method_2661_);
lean_closure_set(v___f_2695_, 1, v_inst_2666_);
lean_closure_set(v___f_2695_, 2, v_onDidChange_2669_);
v___f_2696_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__9));
v___f_2697_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__13));
v___x_2698_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___f_2699_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__14));
v___f_2700_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15));
lean_inc_ref_n(v___x_2687_, 2);
lean_inc_ref(v___f_2694_);
lean_inc_n(v___x_2689_, 2);
v___f_2701_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6___boxed), 11, 8);
lean_closure_set(v___f_2701_, 0, v___x_2689_);
lean_closure_set(v___f_2701_, 1, v___f_2694_);
lean_closure_set(v___f_2701_, 2, v___f_2699_);
lean_closure_set(v___f_2701_, 3, v___f_2697_);
lean_closure_set(v___f_2701_, 4, v___x_2671_);
lean_closure_set(v___f_2701_, 5, v___f_2692_);
lean_closure_set(v___f_2701_, 6, v___f_2696_);
lean_closure_set(v___f_2701_, 7, v___x_2687_);
lean_inc_ref(v___f_2695_);
v___f_2702_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9___boxed), 11, 8);
lean_closure_set(v___f_2702_, 0, v___x_2689_);
lean_closure_set(v___f_2702_, 1, v___f_2695_);
lean_closure_set(v___f_2702_, 2, v___f_2700_);
lean_closure_set(v___f_2702_, 3, v___f_2697_);
lean_closure_set(v___f_2702_, 4, v___x_2671_);
lean_closure_set(v___f_2702_, 5, v___f_2692_);
lean_closure_set(v___f_2702_, 6, v___f_2696_);
lean_closure_set(v___f_2702_, 7, v___x_2687_);
v___f_2703_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
v___x_2704_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2704_, 0, v___f_2693_);
lean_ctor_set(v___x_2704_, 1, v___f_2694_);
lean_ctor_set(v___x_2704_, 2, v___f_2701_);
lean_ctor_set(v___x_2704_, 3, v___f_2695_);
lean_ctor_set(v___x_2704_, 4, v___f_2702_);
lean_ctor_set(v___x_2704_, 5, v___x_2687_);
lean_ctor_set(v___x_2704_, 6, v___x_2688_);
lean_ctor_set(v___x_2704_, 7, v___x_2689_);
lean_ctor_set(v___x_2704_, 8, v_completeness_2662_);
v___x_2705_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2703_, v___x_2698_, v___x_2691_, v_method_2661_, v___x_2704_);
v___x_2706_ = lean_st_ref_set(v___x_2690_, v___x_2705_);
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 0, v___x_2706_);
v___x_2708_ = v___x_2675_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v___x_2706_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
lean_dec_ref(v_onDidChange_2669_);
lean_dec_ref(v_handler_2668_);
lean_dec(v_initState_2667_);
lean_dec(v_inst_2666_);
lean_dec_ref(v_inst_2665_);
lean_dec_ref(v_inst_2664_);
lean_dec_ref(v_inst_2663_);
lean_dec(v_completeness_2662_);
lean_dec_ref(v_method_2661_);
v_a_2711_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2672_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2672_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2719_, lean_object* v_completeness_2720_, lean_object* v_inst_2721_, lean_object* v_inst_2722_, lean_object* v_inst_2723_, lean_object* v_inst_2724_, lean_object* v_initState_2725_, lean_object* v_handler_2726_, lean_object* v_onDidChange_2727_, lean_object* v_a_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2719_, v_completeness_2720_, v_inst_2721_, v_inst_2722_, v_inst_2723_, v_inst_2724_, v_initState_2725_, v_handler_2726_, v_onDidChange_2727_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(lean_object* v_method_2730_, lean_object* v_completeness_2731_, lean_object* v_paramType_2732_, lean_object* v_inst_2733_, lean_object* v_inst_2734_, lean_object* v_respType_2735_, lean_object* v_inst_2736_, lean_object* v_stateType_2737_, lean_object* v_inst_2738_, lean_object* v_initState_2739_, lean_object* v_handler_2740_, lean_object* v_onDidChange_2741_){
_start:
{
lean_object* v___x_2743_; 
v___x_2743_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2730_, v_completeness_2731_, v_inst_2733_, v_inst_2734_, v_inst_2736_, v_inst_2738_, v_initState_2739_, v_handler_2740_, v_onDidChange_2741_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___boxed(lean_object* v_method_2744_, lean_object* v_completeness_2745_, lean_object* v_paramType_2746_, lean_object* v_inst_2747_, lean_object* v_inst_2748_, lean_object* v_respType_2749_, lean_object* v_inst_2750_, lean_object* v_stateType_2751_, lean_object* v_inst_2752_, lean_object* v_initState_2753_, lean_object* v_handler_2754_, lean_object* v_onDidChange_2755_, lean_object* v_a_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(v_method_2744_, v_completeness_2745_, v_paramType_2746_, v_inst_2747_, v_inst_2748_, v_respType_2749_, v_inst_2750_, v_stateType_2751_, v_inst_2752_, v_initState_2753_, v_handler_2754_, v_onDidChange_2755_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(lean_object* v_method_2758_, lean_object* v_completeness_2759_, lean_object* v_inst_2760_, lean_object* v_inst_2761_, lean_object* v_inst_2762_, lean_object* v_inst_2763_, lean_object* v_initState_2764_, lean_object* v_handler_2765_, lean_object* v_onDidChange_2766_){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___f_2771_; uint8_t v___x_2772_; 
v___x_2768_ = l_Lean_Server_requestHandlers;
v___x_2769_ = lean_st_ref_get(v___x_2768_);
v___x_2770_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___f_2771_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
lean_inc_ref(v_method_2758_);
v___x_2772_ = l_Lean_PersistentHashMap_contains___redArg(v___f_2771_, v___x_2770_, v___x_2769_, v_method_2758_);
if (v___x_2772_ == 0)
{
lean_object* v___x_2773_; 
v___x_2773_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2758_, v_completeness_2759_, v_inst_2760_, v_inst_2761_, v_inst_2762_, v_inst_2763_, v_initState_2764_, v_handler_2765_, v_onDidChange_2766_);
return v___x_2773_;
}
else
{
lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
lean_dec_ref(v_onDidChange_2766_);
lean_dec_ref(v_handler_2765_);
lean_dec(v_initState_2764_);
lean_dec(v_inst_2763_);
lean_dec_ref(v_inst_2762_);
lean_dec_ref(v_inst_2761_);
lean_dec_ref(v_inst_2760_);
lean_dec(v_completeness_2759_);
v___x_2774_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2));
v___x_2775_ = lean_string_append(v___x_2774_, v_method_2758_);
lean_dec_ref(v_method_2758_);
v___x_2776_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__4));
v___x_2777_ = lean_string_append(v___x_2775_, v___x_2776_);
v___x_2778_ = lean_mk_io_user_error(v___x_2777_);
v___x_2779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2778_);
return v___x_2779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2780_, lean_object* v_completeness_2781_, lean_object* v_inst_2782_, lean_object* v_inst_2783_, lean_object* v_inst_2784_, lean_object* v_inst_2785_, lean_object* v_initState_2786_, lean_object* v_handler_2787_, lean_object* v_onDidChange_2788_, lean_object* v_a_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2780_, v_completeness_2781_, v_inst_2782_, v_inst_2783_, v_inst_2784_, v_inst_2785_, v_initState_2786_, v_handler_2787_, v_onDidChange_2788_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler(lean_object* v_method_2791_, lean_object* v_completeness_2792_, lean_object* v_paramType_2793_, lean_object* v_inst_2794_, lean_object* v_inst_2795_, lean_object* v_respType_2796_, lean_object* v_inst_2797_, lean_object* v_stateType_2798_, lean_object* v_inst_2799_, lean_object* v_initState_2800_, lean_object* v_handler_2801_, lean_object* v_onDidChange_2802_){
_start:
{
lean_object* v___x_2804_; 
v___x_2804_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2791_, v_completeness_2792_, v_inst_2794_, v_inst_2795_, v_inst_2797_, v_inst_2799_, v_initState_2800_, v_handler_2801_, v_onDidChange_2802_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___boxed(lean_object* v_method_2805_, lean_object* v_completeness_2806_, lean_object* v_paramType_2807_, lean_object* v_inst_2808_, lean_object* v_inst_2809_, lean_object* v_respType_2810_, lean_object* v_inst_2811_, lean_object* v_stateType_2812_, lean_object* v_inst_2813_, lean_object* v_initState_2814_, lean_object* v_handler_2815_, lean_object* v_onDidChange_2816_, lean_object* v_a_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler(v_method_2805_, v_completeness_2806_, v_paramType_2807_, v_inst_2808_, v_inst_2809_, v_respType_2810_, v_inst_2811_, v_stateType_2812_, v_inst_2813_, v_initState_2814_, v_handler_2815_, v_onDidChange_2816_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0(lean_object* v_handler_2819_, lean_object* v_p_2820_, lean_object* v_s_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v___x_2824_; 
lean_inc_ref(v___y_2822_);
v___x_2824_ = lean_apply_4(v_handler_2819_, v_p_2820_, v_s_2821_, v___y_2822_, lean_box(0));
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2843_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2827_ = v___x_2824_;
v_isShared_2828_ = v_isSharedCheck_2843_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2824_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2843_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v_fst_2829_; lean_object* v_snd_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2842_; 
v_fst_2829_ = lean_ctor_get(v_a_2825_, 0);
v_snd_2830_ = lean_ctor_get(v_a_2825_, 1);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_a_2825_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2832_ = v_a_2825_;
v_isShared_2833_ = v_isSharedCheck_2842_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_snd_2830_);
lean_inc(v_fst_2829_);
lean_dec(v_a_2825_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2842_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
uint8_t v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2837_; 
v___x_2834_ = 1;
v___x_2835_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2835_, 0, v_fst_2829_);
lean_ctor_set_uint8(v___x_2835_, sizeof(void*)*1, v___x_2834_);
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 0, v___x_2835_);
v___x_2837_ = v___x_2832_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2835_);
lean_ctor_set(v_reuseFailAlloc_2841_, 1, v_snd_2830_);
v___x_2837_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
lean_object* v___x_2839_; 
if (v_isShared_2828_ == 0)
{
lean_ctor_set(v___x_2827_, 0, v___x_2837_);
v___x_2839_ = v___x_2827_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2837_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
}
else
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2851_; 
v_a_2844_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2846_ = v___x_2824_;
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___x_2824_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2849_; 
if (v_isShared_2847_ == 0)
{
v___x_2849_ = v___x_2846_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_a_2844_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object* v_handler_2852_, lean_object* v_p_2853_, lean_object* v_s_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0(v_handler_2852_, v_p_2853_, v_s_2854_, v___y_2855_);
lean_dec_ref(v___y_2855_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(lean_object* v_method_2858_, lean_object* v_inst_2859_, lean_object* v_inst_2860_, lean_object* v_inst_2861_, lean_object* v_inst_2862_, lean_object* v_initState_2863_, lean_object* v_handler_2864_, lean_object* v_onDidChange_2865_){
_start:
{
lean_object* v_handler_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v_handler_2867_ = lean_alloc_closure((void*)(l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v_handler_2867_, 0, v_handler_2864_);
v___x_2868_ = lean_box(0);
v___x_2869_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2858_, v___x_2868_, v_inst_2859_, v_inst_2860_, v_inst_2861_, v_inst_2862_, v_initState_2863_, v_handler_2867_, v_onDidChange_2865_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2870_, lean_object* v_inst_2871_, lean_object* v_inst_2872_, lean_object* v_inst_2873_, lean_object* v_inst_2874_, lean_object* v_initState_2875_, lean_object* v_handler_2876_, lean_object* v_onDidChange_2877_, lean_object* v_a_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(v_method_2870_, v_inst_2871_, v_inst_2872_, v_inst_2873_, v_inst_2874_, v_initState_2875_, v_handler_2876_, v_onDidChange_2877_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler(lean_object* v_method_2880_, lean_object* v_paramType_2881_, lean_object* v_inst_2882_, lean_object* v_inst_2883_, lean_object* v_respType_2884_, lean_object* v_inst_2885_, lean_object* v_stateType_2886_, lean_object* v_inst_2887_, lean_object* v_initState_2888_, lean_object* v_handler_2889_, lean_object* v_onDidChange_2890_){
_start:
{
lean_object* v___x_2892_; 
v___x_2892_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(v_method_2880_, v_inst_2882_, v_inst_2883_, v_inst_2885_, v_inst_2887_, v_initState_2888_, v_handler_2889_, v_onDidChange_2890_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___boxed(lean_object* v_method_2893_, lean_object* v_paramType_2894_, lean_object* v_inst_2895_, lean_object* v_inst_2896_, lean_object* v_respType_2897_, lean_object* v_inst_2898_, lean_object* v_stateType_2899_, lean_object* v_inst_2900_, lean_object* v_initState_2901_, lean_object* v_handler_2902_, lean_object* v_onDidChange_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler(v_method_2893_, v_paramType_2894_, v_inst_2895_, v_inst_2896_, v_respType_2897_, v_inst_2898_, v_stateType_2899_, v_inst_2900_, v_initState_2901_, v_handler_2902_, v_onDidChange_2903_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(lean_object* v_method_2906_, lean_object* v_refreshMethod_2907_, lean_object* v_refreshIntervalMs_2908_, lean_object* v_inst_2909_, lean_object* v_inst_2910_, lean_object* v_inst_2911_, lean_object* v_inst_2912_, lean_object* v_initState_2913_, lean_object* v_handler_2914_, lean_object* v_onDidChange_2915_){
_start:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2917_, 0, v_refreshMethod_2907_);
lean_ctor_set(v___x_2917_, 1, v_refreshIntervalMs_2908_);
v___x_2918_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2906_, v___x_2917_, v_inst_2909_, v_inst_2910_, v_inst_2911_, v_inst_2912_, v_initState_2913_, v_handler_2914_, v_onDidChange_2915_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2919_, lean_object* v_refreshMethod_2920_, lean_object* v_refreshIntervalMs_2921_, lean_object* v_inst_2922_, lean_object* v_inst_2923_, lean_object* v_inst_2924_, lean_object* v_inst_2925_, lean_object* v_initState_2926_, lean_object* v_handler_2927_, lean_object* v_onDidChange_2928_, lean_object* v_a_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(v_method_2919_, v_refreshMethod_2920_, v_refreshIntervalMs_2921_, v_inst_2922_, v_inst_2923_, v_inst_2924_, v_inst_2925_, v_initState_2926_, v_handler_2927_, v_onDidChange_2928_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler(lean_object* v_method_2931_, lean_object* v_refreshMethod_2932_, lean_object* v_refreshIntervalMs_2933_, lean_object* v_paramType_2934_, lean_object* v_inst_2935_, lean_object* v_inst_2936_, lean_object* v_respType_2937_, lean_object* v_inst_2938_, lean_object* v_stateType_2939_, lean_object* v_inst_2940_, lean_object* v_initState_2941_, lean_object* v_handler_2942_, lean_object* v_onDidChange_2943_){
_start:
{
lean_object* v___x_2945_; 
v___x_2945_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(v_method_2931_, v_refreshMethod_2932_, v_refreshIntervalMs_2933_, v_inst_2935_, v_inst_2936_, v_inst_2938_, v_inst_2940_, v_initState_2941_, v_handler_2942_, v_onDidChange_2943_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___boxed(lean_object* v_method_2946_, lean_object* v_refreshMethod_2947_, lean_object* v_refreshIntervalMs_2948_, lean_object* v_paramType_2949_, lean_object* v_inst_2950_, lean_object* v_inst_2951_, lean_object* v_respType_2952_, lean_object* v_inst_2953_, lean_object* v_stateType_2954_, lean_object* v_inst_2955_, lean_object* v_initState_2956_, lean_object* v_handler_2957_, lean_object* v_onDidChange_2958_, lean_object* v_a_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l_Lean_Server_registerPartialStatefulLspRequestHandler(v_method_2946_, v_refreshMethod_2947_, v_refreshIntervalMs_2948_, v_paramType_2949_, v_inst_2950_, v_inst_2951_, v_respType_2952_, v_inst_2953_, v_stateType_2954_, v_inst_2955_, v_initState_2956_, v_handler_2957_, v_onDidChange_2958_);
return v_res_2960_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2961_, lean_object* v_i_2962_, lean_object* v_k_2963_){
_start:
{
lean_object* v___x_2964_; uint8_t v___x_2965_; 
v___x_2964_ = lean_array_get_size(v_keys_2961_);
v___x_2965_ = lean_nat_dec_lt(v_i_2962_, v___x_2964_);
if (v___x_2965_ == 0)
{
lean_dec(v_i_2962_);
return v___x_2965_;
}
else
{
lean_object* v_k_x27_2966_; uint8_t v___x_2967_; 
v_k_x27_2966_ = lean_array_fget_borrowed(v_keys_2961_, v_i_2962_);
v___x_2967_ = lean_string_dec_eq(v_k_2963_, v_k_x27_2966_);
if (v___x_2967_ == 0)
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2968_ = lean_unsigned_to_nat(1u);
v___x_2969_ = lean_nat_add(v_i_2962_, v___x_2968_);
lean_dec(v_i_2962_);
v_i_2962_ = v___x_2969_;
goto _start;
}
else
{
lean_dec(v_i_2962_);
return v___x_2967_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2971_, lean_object* v_i_2972_, lean_object* v_k_2973_){
_start:
{
uint8_t v_res_2974_; lean_object* v_r_2975_; 
v_res_2974_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_keys_2971_, v_i_2972_, v_k_2973_);
lean_dec_ref(v_k_2973_);
lean_dec_ref(v_keys_2971_);
v_r_2975_ = lean_box(v_res_2974_);
return v_r_2975_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(lean_object* v_x_2976_, size_t v_x_2977_, lean_object* v_x_2978_){
_start:
{
if (lean_obj_tag(v_x_2976_) == 0)
{
lean_object* v_es_2979_; lean_object* v___x_2980_; size_t v___x_2981_; size_t v___x_2982_; size_t v___x_2983_; lean_object* v_j_2984_; lean_object* v___x_2985_; 
v_es_2979_ = lean_ctor_get(v_x_2976_, 0);
v___x_2980_ = lean_box(2);
v___x_2981_ = ((size_t)5ULL);
v___x_2982_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___closed__1);
v___x_2983_ = lean_usize_land(v_x_2977_, v___x_2982_);
v_j_2984_ = lean_usize_to_nat(v___x_2983_);
v___x_2985_ = lean_array_get_borrowed(v___x_2980_, v_es_2979_, v_j_2984_);
lean_dec(v_j_2984_);
switch(lean_obj_tag(v___x_2985_))
{
case 0:
{
lean_object* v_key_2986_; uint8_t v___x_2987_; 
v_key_2986_ = lean_ctor_get(v___x_2985_, 0);
v___x_2987_ = lean_string_dec_eq(v_x_2978_, v_key_2986_);
return v___x_2987_;
}
case 1:
{
lean_object* v_node_2988_; size_t v___x_2989_; 
v_node_2988_ = lean_ctor_get(v___x_2985_, 0);
v___x_2989_ = lean_usize_shift_right(v_x_2977_, v___x_2981_);
v_x_2976_ = v_node_2988_;
v_x_2977_ = v___x_2989_;
goto _start;
}
default: 
{
uint8_t v___x_2991_; 
v___x_2991_ = 0;
return v___x_2991_;
}
}
}
else
{
lean_object* v_ks_2992_; lean_object* v___x_2993_; uint8_t v___x_2994_; 
v_ks_2992_ = lean_ctor_get(v_x_2976_, 0);
v___x_2993_ = lean_unsigned_to_nat(0u);
v___x_2994_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_ks_2992_, v___x_2993_, v_x_2978_);
return v___x_2994_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg___boxed(lean_object* v_x_2995_, lean_object* v_x_2996_, lean_object* v_x_2997_){
_start:
{
size_t v_x_224__boxed_2998_; uint8_t v_res_2999_; lean_object* v_r_3000_; 
v_x_224__boxed_2998_ = lean_unbox_usize(v_x_2996_);
lean_dec(v_x_2996_);
v_res_2999_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_2995_, v_x_224__boxed_2998_, v_x_2997_);
lean_dec_ref(v_x_2997_);
lean_dec_ref(v_x_2995_);
v_r_3000_ = lean_box(v_res_2999_);
return v_r_3000_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(lean_object* v_x_3001_, lean_object* v_x_3002_){
_start:
{
uint64_t v___x_3003_; size_t v___x_3004_; uint8_t v___x_3005_; 
v___x_3003_ = lean_string_hash(v_x_3002_);
v___x_3004_ = lean_uint64_to_usize(v___x_3003_);
v___x_3005_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_3001_, v___x_3004_, v_x_3002_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg___boxed(lean_object* v_x_3006_, lean_object* v_x_3007_){
_start:
{
uint8_t v_res_3008_; lean_object* v_r_3009_; 
v_res_3008_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v_x_3006_, v_x_3007_);
lean_dec_ref(v_x_3007_);
lean_dec_ref(v_x_3006_);
v_r_3009_ = lean_box(v_res_3008_);
return v_r_3009_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_isStatefulLspRequestMethod(lean_object* v_method_3010_){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; 
v___x_3012_ = l_Lean_Server_statefulRequestHandlers;
v___x_3013_ = lean_st_ref_get(v___x_3012_);
v___x_3014_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v___x_3013_, v_method_3010_);
lean_dec(v___x_3013_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_isStatefulLspRequestMethod___boxed(lean_object* v_method_3015_, lean_object* v_a_3016_){
_start:
{
uint8_t v_res_3017_; lean_object* v_r_3018_; 
v_res_3017_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_3015_);
lean_dec_ref(v_method_3015_);
v_r_3018_ = lean_box(v_res_3017_);
return v_r_3018_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0(lean_object* v_00_u03b2_3019_, lean_object* v_x_3020_, lean_object* v_x_3021_){
_start:
{
uint8_t v___x_3022_; 
v___x_3022_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v_x_3020_, v_x_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___boxed(lean_object* v_00_u03b2_3023_, lean_object* v_x_3024_, lean_object* v_x_3025_){
_start:
{
uint8_t v_res_3026_; lean_object* v_r_3027_; 
v_res_3026_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0(v_00_u03b2_3023_, v_x_3024_, v_x_3025_);
lean_dec_ref(v_x_3025_);
lean_dec_ref(v_x_3024_);
v_r_3027_ = lean_box(v_res_3026_);
return v_r_3027_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0(lean_object* v_00_u03b2_3028_, lean_object* v_x_3029_, size_t v_x_3030_, lean_object* v_x_3031_){
_start:
{
uint8_t v___x_3032_; 
v___x_3032_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_3029_, v_x_3030_, v_x_3031_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3033_, lean_object* v_x_3034_, lean_object* v_x_3035_, lean_object* v_x_3036_){
_start:
{
size_t v_x_296__boxed_3037_; uint8_t v_res_3038_; lean_object* v_r_3039_; 
v_x_296__boxed_3037_ = lean_unbox_usize(v_x_3035_);
lean_dec(v_x_3035_);
v_res_3038_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0(v_00_u03b2_3033_, v_x_3034_, v_x_296__boxed_3037_, v_x_3036_);
lean_dec_ref(v_x_3036_);
lean_dec_ref(v_x_3034_);
v_r_3039_ = lean_box(v_res_3038_);
return v_r_3039_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3040_, lean_object* v_keys_3041_, lean_object* v_vals_3042_, lean_object* v_heq_3043_, lean_object* v_i_3044_, lean_object* v_k_3045_){
_start:
{
uint8_t v___x_3046_; 
v___x_3046_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_keys_3041_, v_i_3044_, v_k_3045_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3047_, lean_object* v_keys_3048_, lean_object* v_vals_3049_, lean_object* v_heq_3050_, lean_object* v_i_3051_, lean_object* v_k_3052_){
_start:
{
uint8_t v_res_3053_; lean_object* v_r_3054_; 
v_res_3053_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1(v_00_u03b2_3047_, v_keys_3048_, v_vals_3049_, v_heq_3050_, v_i_3051_, v_k_3052_);
lean_dec_ref(v_k_3052_);
lean_dec_ref(v_vals_3049_);
lean_dec_ref(v_keys_3048_);
v_r_3054_ = lean_box(v_res_3053_);
return v_r_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupStatefulLspRequestHandler(lean_object* v_method_3055_){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3057_ = l_Lean_Server_statefulRequestHandlers;
v___x_3058_ = lean_st_ref_get(v___x_3057_);
v___x_3059_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v___x_3058_, v_method_3055_);
lean_dec(v___x_3058_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupStatefulLspRequestHandler___boxed(lean_object* v_method_3060_, lean_object* v_a_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_3060_);
lean_dec_ref(v_method_3060_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(lean_object* v_as_3063_, size_t v_i_3064_, size_t v_stop_3065_, lean_object* v_b_3066_){
_start:
{
lean_object* v___y_3068_; uint8_t v___x_3072_; 
v___x_3072_ = lean_usize_dec_eq(v_i_3064_, v_stop_3065_);
if (v___x_3072_ == 0)
{
lean_object* v___x_3073_; lean_object* v_snd_3074_; lean_object* v_completeness_3075_; 
v___x_3073_ = lean_array_uget(v_as_3063_, v_i_3064_);
v_snd_3074_ = lean_ctor_get(v___x_3073_, 1);
v_completeness_3075_ = lean_ctor_get(v_snd_3074_, 8);
lean_inc(v_completeness_3075_);
if (lean_obj_tag(v_completeness_3075_) == 1)
{
lean_object* v_fst_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3093_; 
v_fst_3076_ = lean_ctor_get(v___x_3073_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3093_ == 0)
{
lean_object* v_unused_3094_; 
v_unused_3094_ = lean_ctor_get(v___x_3073_, 1);
lean_dec(v_unused_3094_);
v___x_3078_ = v___x_3073_;
v_isShared_3079_ = v_isSharedCheck_3093_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_fst_3076_);
lean_dec(v___x_3073_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3093_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v_refreshMethod_3080_; lean_object* v_refreshIntervalMs_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3092_; 
v_refreshMethod_3080_ = lean_ctor_get(v_completeness_3075_, 0);
v_refreshIntervalMs_3081_ = lean_ctor_get(v_completeness_3075_, 1);
v_isSharedCheck_3092_ = !lean_is_exclusive(v_completeness_3075_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3083_ = v_completeness_3075_;
v_isShared_3084_ = v_isSharedCheck_3092_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_refreshIntervalMs_3081_);
lean_inc(v_refreshMethod_3080_);
lean_dec(v_completeness_3075_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3092_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 1, v_refreshIntervalMs_3081_);
lean_ctor_set(v___x_3078_, 0, v_refreshMethod_3080_);
v___x_3086_ = v___x_3078_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_refreshMethod_3080_);
lean_ctor_set(v_reuseFailAlloc_3091_, 1, v_refreshIntervalMs_3081_);
v___x_3086_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
lean_object* v___x_3088_; 
if (v_isShared_3084_ == 0)
{
lean_ctor_set_tag(v___x_3083_, 0);
lean_ctor_set(v___x_3083_, 1, v___x_3086_);
lean_ctor_set(v___x_3083_, 0, v_fst_3076_);
v___x_3088_ = v___x_3083_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_fst_3076_);
lean_ctor_set(v_reuseFailAlloc_3090_, 1, v___x_3086_);
v___x_3088_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
lean_object* v___x_3089_; 
v___x_3089_ = lean_array_push(v_b_3066_, v___x_3088_);
v___y_3068_ = v___x_3089_;
goto v___jp_3067_;
}
}
}
}
}
else
{
lean_dec(v_completeness_3075_);
lean_dec(v___x_3073_);
v___y_3068_ = v_b_3066_;
goto v___jp_3067_;
}
}
else
{
return v_b_3066_;
}
v___jp_3067_:
{
size_t v___x_3069_; size_t v___x_3070_; 
v___x_3069_ = ((size_t)1ULL);
v___x_3070_ = lean_usize_add(v_i_3064_, v___x_3069_);
v_i_3064_ = v___x_3070_;
v_b_3066_ = v___y_3068_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2___boxed(lean_object* v_as_3095_, lean_object* v_i_3096_, lean_object* v_stop_3097_, lean_object* v_b_3098_){
_start:
{
size_t v_i_boxed_3099_; size_t v_stop_boxed_3100_; lean_object* v_res_3101_; 
v_i_boxed_3099_ = lean_unbox_usize(v_i_3096_);
lean_dec(v_i_3096_);
v_stop_boxed_3100_ = lean_unbox_usize(v_stop_3097_);
lean_dec(v_stop_3097_);
v_res_3101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_3095_, v_i_boxed_3099_, v_stop_boxed_3100_, v_b_3098_);
lean_dec_ref(v_as_3095_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(lean_object* v_as_3104_, lean_object* v_start_3105_, lean_object* v_stop_3106_){
_start:
{
lean_object* v___x_3107_; uint8_t v___x_3108_; 
v___x_3107_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___closed__0));
v___x_3108_ = lean_nat_dec_lt(v_start_3105_, v_stop_3106_);
if (v___x_3108_ == 0)
{
return v___x_3107_;
}
else
{
lean_object* v___x_3109_; uint8_t v___x_3110_; 
v___x_3109_ = lean_array_get_size(v_as_3104_);
v___x_3110_ = lean_nat_dec_le(v_stop_3106_, v___x_3109_);
if (v___x_3110_ == 0)
{
uint8_t v___x_3111_; 
v___x_3111_ = lean_nat_dec_lt(v_start_3105_, v___x_3109_);
if (v___x_3111_ == 0)
{
return v___x_3107_;
}
else
{
size_t v___x_3112_; size_t v___x_3113_; lean_object* v___x_3114_; 
v___x_3112_ = lean_usize_of_nat(v_start_3105_);
v___x_3113_ = lean_usize_of_nat(v___x_3109_);
v___x_3114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_3104_, v___x_3112_, v___x_3113_, v___x_3107_);
return v___x_3114_;
}
}
else
{
size_t v___x_3115_; size_t v___x_3116_; lean_object* v___x_3117_; 
v___x_3115_ = lean_usize_of_nat(v_start_3105_);
v___x_3116_ = lean_usize_of_nat(v_stop_3106_);
v___x_3117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_3104_, v___x_3115_, v___x_3116_, v___x_3107_);
return v___x_3117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___boxed(lean_object* v_as_3118_, lean_object* v_start_3119_, lean_object* v_stop_3120_){
_start:
{
lean_object* v_res_3121_; 
v_res_3121_ = l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(v_as_3118_, v_start_3119_, v_stop_3120_);
lean_dec(v_stop_3120_);
lean_dec(v_start_3119_);
lean_dec_ref(v_as_3118_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_f_3122_, lean_object* v_keys_3123_, lean_object* v_vals_3124_, lean_object* v_i_3125_, lean_object* v_acc_3126_){
_start:
{
lean_object* v___x_3127_; uint8_t v___x_3128_; 
v___x_3127_ = lean_array_get_size(v_keys_3123_);
v___x_3128_ = lean_nat_dec_lt(v_i_3125_, v___x_3127_);
if (v___x_3128_ == 0)
{
lean_dec(v_i_3125_);
lean_dec(v_f_3122_);
return v_acc_3126_;
}
else
{
lean_object* v_k_3129_; lean_object* v_v_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v_k_3129_ = lean_array_fget_borrowed(v_keys_3123_, v_i_3125_);
v_v_3130_ = lean_array_fget_borrowed(v_vals_3124_, v_i_3125_);
lean_inc(v_f_3122_);
lean_inc(v_v_3130_);
lean_inc(v_k_3129_);
v___x_3131_ = lean_apply_3(v_f_3122_, v_acc_3126_, v_k_3129_, v_v_3130_);
v___x_3132_ = lean_unsigned_to_nat(1u);
v___x_3133_ = lean_nat_add(v_i_3125_, v___x_3132_);
lean_dec(v_i_3125_);
v_i_3125_ = v___x_3133_;
v_acc_3126_ = v___x_3131_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_f_3135_, lean_object* v_keys_3136_, lean_object* v_vals_3137_, lean_object* v_i_3138_, lean_object* v_acc_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_3135_, v_keys_3136_, v_vals_3137_, v_i_3138_, v_acc_3139_);
lean_dec_ref(v_vals_3137_);
lean_dec_ref(v_keys_3136_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_3141_, lean_object* v_x_3142_, lean_object* v_x_3143_){
_start:
{
if (lean_obj_tag(v_x_3142_) == 0)
{
lean_object* v_es_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; uint8_t v___x_3147_; 
v_es_3144_ = lean_ctor_get(v_x_3142_, 0);
v___x_3145_ = lean_unsigned_to_nat(0u);
v___x_3146_ = lean_array_get_size(v_es_3144_);
v___x_3147_ = lean_nat_dec_lt(v___x_3145_, v___x_3146_);
if (v___x_3147_ == 0)
{
lean_dec(v_f_3141_);
return v_x_3143_;
}
else
{
uint8_t v___x_3148_; 
v___x_3148_ = lean_nat_dec_le(v___x_3146_, v___x_3146_);
if (v___x_3148_ == 0)
{
if (v___x_3147_ == 0)
{
lean_dec(v_f_3141_);
return v_x_3143_;
}
else
{
size_t v___x_3149_; size_t v___x_3150_; lean_object* v___x_3151_; 
v___x_3149_ = ((size_t)0ULL);
v___x_3150_ = lean_usize_of_nat(v___x_3146_);
v___x_3151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_3141_, v_es_3144_, v___x_3149_, v___x_3150_, v_x_3143_);
return v___x_3151_;
}
}
else
{
size_t v___x_3152_; size_t v___x_3153_; lean_object* v___x_3154_; 
v___x_3152_ = ((size_t)0ULL);
v___x_3153_ = lean_usize_of_nat(v___x_3146_);
v___x_3154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_3141_, v_es_3144_, v___x_3152_, v___x_3153_, v_x_3143_);
return v___x_3154_;
}
}
}
else
{
lean_object* v_ks_3155_; lean_object* v_vs_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v_ks_3155_ = lean_ctor_get(v_x_3142_, 0);
v_vs_3156_ = lean_ctor_get(v_x_3142_, 1);
v___x_3157_ = lean_unsigned_to_nat(0u);
v___x_3158_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_3141_, v_ks_3155_, v_vs_3156_, v___x_3157_, v_x_3143_);
return v___x_3158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_f_3159_, lean_object* v_as_3160_, size_t v_i_3161_, size_t v_stop_3162_, lean_object* v_b_3163_){
_start:
{
lean_object* v___y_3165_; uint8_t v___x_3169_; 
v___x_3169_ = lean_usize_dec_eq(v_i_3161_, v_stop_3162_);
if (v___x_3169_ == 0)
{
lean_object* v___x_3170_; 
v___x_3170_ = lean_array_uget_borrowed(v_as_3160_, v_i_3161_);
switch(lean_obj_tag(v___x_3170_))
{
case 0:
{
lean_object* v_key_3171_; lean_object* v_val_3172_; lean_object* v___x_3173_; 
v_key_3171_ = lean_ctor_get(v___x_3170_, 0);
v_val_3172_ = lean_ctor_get(v___x_3170_, 1);
lean_inc(v_f_3159_);
lean_inc(v_val_3172_);
lean_inc(v_key_3171_);
v___x_3173_ = lean_apply_3(v_f_3159_, v_b_3163_, v_key_3171_, v_val_3172_);
v___y_3165_ = v___x_3173_;
goto v___jp_3164_;
}
case 1:
{
lean_object* v_node_3174_; lean_object* v___x_3175_; 
v_node_3174_ = lean_ctor_get(v___x_3170_, 0);
lean_inc(v_f_3159_);
v___x_3175_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3159_, v_node_3174_, v_b_3163_);
v___y_3165_ = v___x_3175_;
goto v___jp_3164_;
}
default: 
{
v___y_3165_ = v_b_3163_;
goto v___jp_3164_;
}
}
}
else
{
lean_dec(v_f_3159_);
return v_b_3163_;
}
v___jp_3164_:
{
size_t v___x_3166_; size_t v___x_3167_; 
v___x_3166_ = ((size_t)1ULL);
v___x_3167_ = lean_usize_add(v_i_3161_, v___x_3166_);
v_i_3161_ = v___x_3167_;
v_b_3163_ = v___y_3165_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_f_3176_, lean_object* v_as_3177_, lean_object* v_i_3178_, lean_object* v_stop_3179_, lean_object* v_b_3180_){
_start:
{
size_t v_i_boxed_3181_; size_t v_stop_boxed_3182_; lean_object* v_res_3183_; 
v_i_boxed_3181_ = lean_unbox_usize(v_i_3178_);
lean_dec(v_i_3178_);
v_stop_boxed_3182_ = lean_unbox_usize(v_stop_3179_);
lean_dec(v_stop_3179_);
v_res_3183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_3176_, v_as_3177_, v_i_boxed_3181_, v_stop_boxed_3182_, v_b_3180_);
lean_dec_ref(v_as_3177_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_3184_, lean_object* v_x_3185_, lean_object* v_x_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3184_, v_x_3185_, v_x_3186_);
lean_dec_ref(v_x_3185_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___lam__0(lean_object* v_f_3188_, lean_object* v_x1_3189_, lean_object* v_x2_3190_, lean_object* v_x3_3191_){
_start:
{
lean_object* v___x_3192_; 
v___x_3192_ = lean_apply_3(v_f_3188_, v_x1_3189_, v_x2_3190_, v_x3_3191_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(lean_object* v_map_3193_, lean_object* v_f_3194_, lean_object* v_init_3195_){
_start:
{
lean_object* v___f_3196_; lean_object* v___x_3197_; 
v___f_3196_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3196_, 0, v_f_3194_);
v___x_3197_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v___f_3196_, v_map_3193_, v_init_3195_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___boxed(lean_object* v_map_3198_, lean_object* v_f_3199_, lean_object* v_init_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_map_3198_, v_f_3199_, v_init_3200_);
lean_dec_ref(v_map_3198_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___lam__0(lean_object* v_ps_3202_, lean_object* v_k_3203_, lean_object* v_v_3204_){
_start:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3205_, 0, v_k_3203_);
lean_ctor_set(v___x_3205_, 1, v_v_3204_);
v___x_3206_ = lean_array_push(v_ps_3202_, v___x_3205_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(lean_object* v_m_3210_){
_start:
{
lean_object* v___f_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___f_3211_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__0));
v___x_3212_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__1));
v___x_3213_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_m_3210_, v___f_3211_, v___x_3212_);
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___boxed(lean_object* v_m_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v_m_3214_);
lean_dec_ref(v_m_3214_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_partialLspRequestHandlerMethods(){
_start:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3217_ = l_Lean_Server_statefulRequestHandlers;
v___x_3218_ = lean_st_ref_get(v___x_3217_);
v___x_3219_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v___x_3218_);
lean_dec(v___x_3218_);
v___x_3220_ = lean_unsigned_to_nat(0u);
v___x_3221_ = lean_array_get_size(v___x_3219_);
v___x_3222_ = l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(v___x_3219_, v___x_3220_, v___x_3221_);
lean_dec_ref(v___x_3219_);
v___x_3223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_partialLspRequestHandlerMethods___boxed(lean_object* v_a_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Lean_Server_partialLspRequestHandlerMethods();
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0(lean_object* v_00_u03b2_3226_, lean_object* v_m_3227_){
_start:
{
lean_object* v___x_3228_; 
v___x_3228_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v_m_3227_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___boxed(lean_object* v_00_u03b2_3229_, lean_object* v_m_3230_){
_start:
{
lean_object* v_res_3231_; 
v_res_3231_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0(v_00_u03b2_3229_, v_m_3230_);
lean_dec_ref(v_m_3230_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0(lean_object* v_00_u03c3_3232_, lean_object* v_00_u03b2_3233_, lean_object* v_map_3234_, lean_object* v_f_3235_, lean_object* v_init_3236_){
_start:
{
lean_object* v___x_3237_; 
v___x_3237_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_map_3234_, v_f_3235_, v_init_3236_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3238_, lean_object* v_00_u03b2_3239_, lean_object* v_map_3240_, lean_object* v_f_3241_, lean_object* v_init_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0(v_00_u03c3_3238_, v_00_u03b2_3239_, v_map_3240_, v_f_3241_, v_init_3242_);
lean_dec_ref(v_map_3240_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg(lean_object* v_map_3244_, lean_object* v_f_3245_, lean_object* v_init_3246_){
_start:
{
lean_object* v___x_3247_; 
v___x_3247_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3245_, v_map_3244_, v_init_3246_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_3248_, lean_object* v_f_3249_, lean_object* v_init_3250_){
_start:
{
lean_object* v_res_3251_; 
v_res_3251_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg(v_map_3248_, v_f_3249_, v_init_3250_);
lean_dec_ref(v_map_3248_);
return v_res_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3252_, lean_object* v_00_u03b2_3253_, lean_object* v_map_3254_, lean_object* v_f_3255_, lean_object* v_init_3256_){
_start:
{
lean_object* v___x_3257_; 
v___x_3257_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3255_, v_map_3254_, v_init_3256_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3258_, lean_object* v_00_u03b2_3259_, lean_object* v_map_3260_, lean_object* v_f_3261_, lean_object* v_init_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1(v_00_u03c3_3258_, v_00_u03b2_3259_, v_map_3260_, v_f_3261_, v_init_3262_);
lean_dec_ref(v_map_3260_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3264_, lean_object* v_00_u03b1_3265_, lean_object* v_00_u03b2_3266_, lean_object* v_f_3267_, lean_object* v_x_3268_, lean_object* v_x_3269_){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3267_, v_x_3268_, v_x_3269_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3271_, lean_object* v_00_u03b1_3272_, lean_object* v_00_u03b2_3273_, lean_object* v_f_3274_, lean_object* v_x_3275_, lean_object* v_x_3276_){
_start:
{
lean_object* v_res_3277_; 
v_res_3277_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3271_, v_00_u03b1_3272_, v_00_u03b2_3273_, v_f_3274_, v_x_3275_, v_x_3276_);
lean_dec_ref(v_x_3275_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_3278_, lean_object* v_00_u03b2_3279_, lean_object* v_00_u03c3_3280_, lean_object* v_f_3281_, lean_object* v_as_3282_, size_t v_i_3283_, size_t v_stop_3284_, lean_object* v_b_3285_){
_start:
{
lean_object* v___x_3286_; 
v___x_3286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_3281_, v_as_3282_, v_i_3283_, v_stop_3284_, v_b_3285_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_3287_, lean_object* v_00_u03b2_3288_, lean_object* v_00_u03c3_3289_, lean_object* v_f_3290_, lean_object* v_as_3291_, lean_object* v_i_3292_, lean_object* v_stop_3293_, lean_object* v_b_3294_){
_start:
{
size_t v_i_boxed_3295_; size_t v_stop_boxed_3296_; lean_object* v_res_3297_; 
v_i_boxed_3295_ = lean_unbox_usize(v_i_3292_);
lean_dec(v_i_3292_);
v_stop_boxed_3296_ = lean_unbox_usize(v_stop_3293_);
lean_dec(v_stop_3293_);
v_res_3297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_3287_, v_00_u03b2_3288_, v_00_u03c3_3289_, v_f_3290_, v_as_3291_, v_i_boxed_3295_, v_stop_boxed_3296_, v_b_3294_);
lean_dec_ref(v_as_3291_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03c3_3298_, lean_object* v_00_u03b1_3299_, lean_object* v_00_u03b2_3300_, lean_object* v_f_3301_, lean_object* v_keys_3302_, lean_object* v_vals_3303_, lean_object* v_heq_3304_, lean_object* v_i_3305_, lean_object* v_acc_3306_){
_start:
{
lean_object* v___x_3307_; 
v___x_3307_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_3301_, v_keys_3302_, v_vals_3303_, v_i_3305_, v_acc_3306_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03c3_3308_, lean_object* v_00_u03b1_3309_, lean_object* v_00_u03b2_3310_, lean_object* v_f_3311_, lean_object* v_keys_3312_, lean_object* v_vals_3313_, lean_object* v_heq_3314_, lean_object* v_i_3315_, lean_object* v_acc_3316_){
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6(v_00_u03c3_3308_, v_00_u03b1_3309_, v_00_u03b2_3310_, v_f_3311_, v_keys_3312_, v_vals_3313_, v_heq_3314_, v_i_3315_, v_acc_3316_);
lean_dec_ref(v_vals_3313_);
lean_dec_ref(v_keys_3312_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0(lean_object* v_inst_3318_, lean_object* v_pureOnDidChange_3319_, lean_object* v_method_3320_, lean_object* v_onDidChange_3321_, lean_object* v_p_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; 
lean_inc(v_inst_3318_);
v___x_3326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3326_, 0, v_inst_3318_);
lean_ctor_set(v___x_3326_, 1, v___y_3323_);
lean_inc_ref(v___y_3324_);
lean_inc_ref(v_p_3322_);
v___x_3327_ = lean_apply_4(v_pureOnDidChange_3319_, v_p_3322_, v___x_3326_, v___y_3324_, lean_box(0));
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v_a_3328_; lean_object* v_snd_3329_; lean_object* v___x_3330_; 
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_a_3328_);
lean_dec_ref(v___x_3327_);
v_snd_3329_ = lean_ctor_get(v_a_3328_, 1);
lean_inc(v_snd_3329_);
lean_dec(v_a_3328_);
v___x_3330_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_3320_, v_snd_3329_, v_inst_3318_);
lean_dec(v_inst_3318_);
lean_dec(v_snd_3329_);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_object* v_a_3331_; lean_object* v___x_3332_; 
v_a_3331_ = lean_ctor_get(v___x_3330_, 0);
lean_inc(v_a_3331_);
lean_dec_ref(v___x_3330_);
lean_inc_ref(v___y_3324_);
v___x_3332_ = lean_apply_4(v_onDidChange_3321_, v_p_3322_, v_a_3331_, v___y_3324_, lean_box(0));
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3350_; 
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3335_ = v___x_3332_;
v_isShared_3336_ = v_isSharedCheck_3350_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3332_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3350_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v_snd_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3348_; 
v_snd_3337_ = lean_ctor_get(v_a_3333_, 1);
v_isSharedCheck_3348_ = !lean_is_exclusive(v_a_3333_);
if (v_isSharedCheck_3348_ == 0)
{
lean_object* v_unused_3349_; 
v_unused_3349_ = lean_ctor_get(v_a_3333_, 0);
lean_dec(v_unused_3349_);
v___x_3339_ = v_a_3333_;
v_isShared_3340_ = v_isSharedCheck_3348_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_snd_3337_);
lean_dec(v_a_3333_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3348_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3341_; lean_object* v___x_3343_; 
v___x_3341_ = lean_box(0);
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 0, v___x_3341_);
v___x_3343_ = v___x_3339_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v___x_3341_);
lean_ctor_set(v_reuseFailAlloc_3347_, 1, v_snd_3337_);
v___x_3343_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
lean_object* v___x_3345_; 
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 0, v___x_3343_);
v___x_3345_ = v___x_3335_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3343_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
}
else
{
return v___x_3332_;
}
}
else
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3358_; 
lean_dec_ref(v_p_3322_);
lean_dec_ref(v_onDidChange_3321_);
v_a_3351_ = lean_ctor_get(v___x_3330_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3330_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3353_ = v___x_3330_;
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3330_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3356_; 
if (v_isShared_3354_ == 0)
{
v___x_3356_ = v___x_3353_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_a_3351_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
else
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3366_; 
lean_dec_ref(v_p_3322_);
lean_dec_ref(v_onDidChange_3321_);
lean_dec(v_inst_3318_);
v_a_3359_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3327_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3327_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3364_; 
if (v_isShared_3362_ == 0)
{
v___x_3364_ = v___x_3361_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3359_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object* v_inst_3367_, lean_object* v_pureOnDidChange_3368_, lean_object* v_method_3369_, lean_object* v_onDidChange_3370_, lean_object* v_p_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0(v_inst_3367_, v_pureOnDidChange_3368_, v_method_3369_, v_onDidChange_3370_, v_p_3371_, v___y_3372_, v___y_3373_);
lean_dec_ref(v___y_3373_);
lean_dec_ref(v_method_3369_);
return v_res_3375_;
}
}
static lean_object* _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3377_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__0));
v___x_3378_ = l_Lean_Server_RequestError_internalError(v___x_3377_);
return v___x_3378_;
}
}
static lean_object* _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3380_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__2));
v___x_3381_ = l_Lean_Server_RequestError_internalError(v___x_3380_);
return v___x_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1(lean_object* v_inst_3382_, lean_object* v_inst_3383_, lean_object* v_pureHandle_3384_, lean_object* v_inst_3385_, lean_object* v_method_3386_, lean_object* v_handler_3387_, lean_object* v_p_3388_, lean_object* v_s_3389_, lean_object* v___y_3390_){
_start:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
lean_inc(v_p_3388_);
v___x_3392_ = lean_apply_1(v_inst_3382_, v_p_3388_);
lean_inc(v_inst_3383_);
v___x_3393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3393_, 0, v_inst_3383_);
lean_ctor_set(v___x_3393_, 1, v_s_3389_);
lean_inc_ref(v___y_3390_);
v___x_3394_ = lean_apply_4(v_pureHandle_3384_, v___x_3392_, v___x_3393_, v___y_3390_, lean_box(0));
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3429_; 
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3397_ = v___x_3394_;
v_isShared_3398_ = v_isSharedCheck_3429_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3394_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3429_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v_fst_3399_; lean_object* v_snd_3400_; lean_object* v_response_x3f_3401_; lean_object* v_serialized_3402_; uint8_t v_isComplete_3403_; lean_object* v_a_3405_; 
v_fst_3399_ = lean_ctor_get(v_a_3395_, 0);
lean_inc(v_fst_3399_);
v_snd_3400_ = lean_ctor_get(v_a_3395_, 1);
lean_inc(v_snd_3400_);
lean_dec(v_a_3395_);
v_response_x3f_3401_ = lean_ctor_get(v_fst_3399_, 0);
lean_inc(v_response_x3f_3401_);
v_serialized_3402_ = lean_ctor_get(v_fst_3399_, 1);
lean_inc_ref(v_serialized_3402_);
v_isComplete_3403_ = lean_ctor_get_uint8(v_fst_3399_, sizeof(void*)*2);
lean_dec(v_fst_3399_);
if (lean_obj_tag(v_response_x3f_3401_) == 0)
{
lean_object* v___x_3424_; 
v___x_3424_ = l_Lean_Json_parse(v_serialized_3402_);
if (lean_obj_tag(v___x_3424_) == 1)
{
lean_object* v_a_3425_; 
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3425_);
lean_dec_ref(v___x_3424_);
v_a_3405_ = v_a_3425_;
goto v___jp_3404_;
}
else
{
lean_object* v___x_3426_; lean_object* v___x_3427_; 
lean_dec_ref(v___x_3424_);
lean_dec(v_snd_3400_);
lean_del_object(v___x_3397_);
lean_dec(v_p_3388_);
lean_dec_ref(v_handler_3387_);
lean_dec_ref(v_inst_3385_);
lean_dec(v_inst_3383_);
v___x_3426_ = lean_obj_once(&l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3, &l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3_once, _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3);
v___x_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3426_);
return v___x_3427_;
}
}
else
{
lean_object* v_val_3428_; 
lean_dec_ref(v_serialized_3402_);
v_val_3428_ = lean_ctor_get(v_response_x3f_3401_, 0);
lean_inc(v_val_3428_);
lean_dec_ref(v_response_x3f_3401_);
v_a_3405_ = v_val_3428_;
goto v___jp_3404_;
}
v___jp_3404_:
{
lean_object* v___x_3406_; 
v___x_3406_ = lean_apply_1(v_inst_3385_, v_a_3405_);
if (lean_obj_tag(v___x_3406_) == 1)
{
lean_object* v_a_3407_; lean_object* v___x_3408_; 
lean_del_object(v___x_3397_);
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
lean_inc(v_a_3407_);
lean_dec_ref(v___x_3406_);
v___x_3408_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_3386_, v_snd_3400_, v_inst_3383_);
lean_dec(v_inst_3383_);
lean_dec(v_snd_3400_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
lean_inc(v_a_3409_);
lean_dec_ref(v___x_3408_);
v___x_3410_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3410_, 0, v_a_3407_);
lean_ctor_set_uint8(v___x_3410_, sizeof(void*)*1, v_isComplete_3403_);
lean_inc_ref(v___y_3390_);
v___x_3411_ = lean_apply_5(v_handler_3387_, v_p_3388_, v___x_3410_, v_a_3409_, v___y_3390_, lean_box(0));
return v___x_3411_;
}
else
{
lean_object* v_a_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3419_; 
lean_dec(v_a_3407_);
lean_dec(v_p_3388_);
lean_dec_ref(v_handler_3387_);
v_a_3412_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3414_ = v___x_3408_;
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_a_3412_);
lean_dec(v___x_3408_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3417_; 
if (v_isShared_3415_ == 0)
{
v___x_3417_ = v___x_3414_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_a_3412_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
}
else
{
lean_object* v___x_3420_; lean_object* v___x_3422_; 
lean_dec_ref(v___x_3406_);
lean_dec(v_snd_3400_);
lean_dec(v_p_3388_);
lean_dec_ref(v_handler_3387_);
lean_dec(v_inst_3383_);
v___x_3420_ = lean_obj_once(&l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1, &l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1_once, _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1);
if (v_isShared_3398_ == 0)
{
lean_ctor_set_tag(v___x_3397_, 1);
lean_ctor_set(v___x_3397_, 0, v___x_3420_);
v___x_3422_ = v___x_3397_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3420_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
lean_dec(v_p_3388_);
lean_dec_ref(v_handler_3387_);
lean_dec_ref(v_inst_3385_);
lean_dec(v_inst_3383_);
v_a_3430_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3394_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3394_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___boxed(lean_object* v_inst_3438_, lean_object* v_inst_3439_, lean_object* v_pureHandle_3440_, lean_object* v_inst_3441_, lean_object* v_method_3442_, lean_object* v_handler_3443_, lean_object* v_p_3444_, lean_object* v_s_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_){
_start:
{
lean_object* v_res_3448_; 
v_res_3448_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1(v_inst_3438_, v_inst_3439_, v_pureHandle_3440_, v_inst_3441_, v_method_3442_, v_handler_3443_, v_p_3444_, v_s_3445_, v___y_3446_);
lean_dec_ref(v___y_3446_);
lean_dec_ref(v_method_3442_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg(lean_object* v_method_3450_, lean_object* v_inst_3451_, lean_object* v_inst_3452_, lean_object* v_inst_3453_, lean_object* v_inst_3454_, lean_object* v_inst_3455_, lean_object* v_inst_3456_, lean_object* v_handler_3457_, lean_object* v_onDidChange_3458_){
_start:
{
lean_object* v___x_3460_; 
v___x_3460_ = l_Lean_initializing();
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3501_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3463_ = v___x_3460_;
v_isShared_3464_ = v_isSharedCheck_3501_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3460_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3501_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
uint8_t v___x_3465_; 
v___x_3465_ = lean_unbox(v_a_3461_);
lean_dec(v_a_3461_);
if (v___x_3465_ == 0)
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3472_; 
lean_dec_ref(v_onDidChange_3458_);
lean_dec_ref(v_handler_3457_);
lean_dec(v_inst_3456_);
lean_dec_ref(v_inst_3455_);
lean_dec_ref(v_inst_3454_);
lean_dec_ref(v_inst_3453_);
lean_dec_ref(v_inst_3452_);
lean_dec_ref(v_inst_3451_);
v___x_3466_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0));
v___x_3467_ = lean_string_append(v___x_3466_, v_method_3450_);
lean_dec_ref(v_method_3450_);
v___x_3468_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__1));
v___x_3469_ = lean_string_append(v___x_3467_, v___x_3468_);
v___x_3470_ = lean_mk_io_user_error(v___x_3469_);
if (v_isShared_3464_ == 0)
{
lean_ctor_set_tag(v___x_3463_, 1);
lean_ctor_set(v___x_3463_, 0, v___x_3470_);
v___x_3472_ = v___x_3463_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3470_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
else
{
lean_object* v___x_3474_; 
v___x_3474_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_3450_);
if (lean_obj_tag(v___x_3474_) == 1)
{
lean_object* v_val_3475_; lean_object* v_pureHandle_3476_; lean_object* v_pureOnDidChange_3477_; lean_object* v_initState_3478_; lean_object* v_completeness_3479_; lean_object* v___x_3480_; 
lean_del_object(v___x_3463_);
v_val_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_val_3475_);
lean_dec_ref(v___x_3474_);
v_pureHandle_3476_ = lean_ctor_get(v_val_3475_, 1);
lean_inc_ref(v_pureHandle_3476_);
v_pureOnDidChange_3477_ = lean_ctor_get(v_val_3475_, 3);
lean_inc_ref(v_pureOnDidChange_3477_);
v_initState_3478_ = lean_ctor_get(v_val_3475_, 6);
lean_inc(v_initState_3478_);
v_completeness_3479_ = lean_ctor_get(v_val_3475_, 8);
lean_inc(v_completeness_3479_);
lean_dec(v_val_3475_);
v___x_3480_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(v_method_3450_, v_initState_3478_, v_inst_3456_);
lean_dec(v_initState_3478_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_a_3481_; lean_object* v___f_3482_; lean_object* v___f_3483_; lean_object* v___x_3484_; 
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
lean_inc(v_a_3481_);
lean_dec_ref(v___x_3480_);
lean_inc_ref_n(v_method_3450_, 2);
lean_inc_n(v_inst_3456_, 2);
v___f_3482_ = lean_alloc_closure((void*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_3482_, 0, v_inst_3456_);
lean_closure_set(v___f_3482_, 1, v_pureOnDidChange_3477_);
lean_closure_set(v___f_3482_, 2, v_method_3450_);
lean_closure_set(v___f_3482_, 3, v_onDidChange_3458_);
v___f_3483_ = lean_alloc_closure((void*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___boxed), 10, 6);
lean_closure_set(v___f_3483_, 0, v_inst_3452_);
lean_closure_set(v___f_3483_, 1, v_inst_3456_);
lean_closure_set(v___f_3483_, 2, v_pureHandle_3476_);
lean_closure_set(v___f_3483_, 3, v_inst_3454_);
lean_closure_set(v___f_3483_, 4, v_method_3450_);
lean_closure_set(v___f_3483_, 5, v_handler_3457_);
v___x_3484_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_3450_, v_completeness_3479_, v_inst_3451_, v_inst_3453_, v_inst_3455_, v_inst_3456_, v_a_3481_, v___f_3483_, v___f_3482_);
return v___x_3484_;
}
else
{
lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3492_; 
lean_dec(v_completeness_3479_);
lean_dec_ref(v_pureOnDidChange_3477_);
lean_dec_ref(v_pureHandle_3476_);
lean_dec_ref(v_onDidChange_3458_);
lean_dec_ref(v_handler_3457_);
lean_dec(v_inst_3456_);
lean_dec_ref(v_inst_3455_);
lean_dec_ref(v_inst_3454_);
lean_dec_ref(v_inst_3453_);
lean_dec_ref(v_inst_3452_);
lean_dec_ref(v_inst_3451_);
lean_dec_ref(v_method_3450_);
v_a_3485_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___x_3480_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_3480_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_a_3485_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
else
{
lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3499_; 
lean_dec(v___x_3474_);
lean_dec_ref(v_onDidChange_3458_);
lean_dec_ref(v_handler_3457_);
lean_dec(v_inst_3456_);
lean_dec_ref(v_inst_3455_);
lean_dec_ref(v_inst_3454_);
lean_dec_ref(v_inst_3453_);
lean_dec_ref(v_inst_3452_);
lean_dec_ref(v_inst_3451_);
v___x_3493_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0));
v___x_3494_ = lean_string_append(v___x_3493_, v_method_3450_);
lean_dec_ref(v_method_3450_);
v___x_3495_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__1));
v___x_3496_ = lean_string_append(v___x_3494_, v___x_3495_);
v___x_3497_ = lean_mk_io_user_error(v___x_3496_);
if (v_isShared_3464_ == 0)
{
lean_ctor_set_tag(v___x_3463_, 1);
lean_ctor_set(v___x_3463_, 0, v___x_3497_);
v___x_3499_ = v___x_3463_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v___x_3497_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
}
else
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3509_; 
lean_dec_ref(v_onDidChange_3458_);
lean_dec_ref(v_handler_3457_);
lean_dec(v_inst_3456_);
lean_dec_ref(v_inst_3455_);
lean_dec_ref(v_inst_3454_);
lean_dec_ref(v_inst_3453_);
lean_dec_ref(v_inst_3452_);
lean_dec_ref(v_inst_3451_);
lean_dec_ref(v_method_3450_);
v_a_3502_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___x_3460_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3460_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3507_; 
if (v_isShared_3505_ == 0)
{
v___x_3507_ = v___x_3504_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_a_3502_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_3510_, lean_object* v_inst_3511_, lean_object* v_inst_3512_, lean_object* v_inst_3513_, lean_object* v_inst_3514_, lean_object* v_inst_3515_, lean_object* v_inst_3516_, lean_object* v_handler_3517_, lean_object* v_onDidChange_3518_, lean_object* v_a_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg(v_method_3510_, v_inst_3511_, v_inst_3512_, v_inst_3513_, v_inst_3514_, v_inst_3515_, v_inst_3516_, v_handler_3517_, v_onDidChange_3518_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler(lean_object* v_method_3521_, lean_object* v_paramType_3522_, lean_object* v_inst_3523_, lean_object* v_inst_3524_, lean_object* v_inst_3525_, lean_object* v_respType_3526_, lean_object* v_inst_3527_, lean_object* v_inst_3528_, lean_object* v_stateType_3529_, lean_object* v_inst_3530_, lean_object* v_handler_3531_, lean_object* v_onDidChange_3532_){
_start:
{
lean_object* v___x_3534_; 
v___x_3534_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg(v_method_3521_, v_inst_3523_, v_inst_3524_, v_inst_3525_, v_inst_3527_, v_inst_3528_, v_inst_3530_, v_handler_3531_, v_onDidChange_3532_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___boxed(lean_object* v_method_3535_, lean_object* v_paramType_3536_, lean_object* v_inst_3537_, lean_object* v_inst_3538_, lean_object* v_inst_3539_, lean_object* v_respType_3540_, lean_object* v_inst_3541_, lean_object* v_inst_3542_, lean_object* v_stateType_3543_, lean_object* v_inst_3544_, lean_object* v_handler_3545_, lean_object* v_onDidChange_3546_, lean_object* v_a_3547_){
_start:
{
lean_object* v_res_3548_; 
v_res_3548_ = l_Lean_Server_chainStatefulLspRequestHandler(v_method_3535_, v_paramType_3536_, v_inst_3537_, v_inst_3538_, v_inst_3539_, v_respType_3540_, v_inst_3541_, v_inst_3542_, v_stateType_3543_, v_inst_3544_, v_handler_3545_, v_onDidChange_3546_);
return v_res_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___lam__0(lean_object* v_p_3549_, lean_object* v_x_3550_, lean_object* v_handler_3551_, lean_object* v___y_3552_){
_start:
{
lean_object* v_onDidChange_3554_; lean_object* v___x_3555_; 
v_onDidChange_3554_ = lean_ctor_get(v_handler_3551_, 4);
lean_inc_ref(v_onDidChange_3554_);
lean_dec_ref(v_handler_3551_);
lean_inc_ref(v___y_3552_);
v___x_3555_ = lean_apply_3(v_onDidChange_3554_, v_p_3549_, v___y_3552_, lean_box(0));
return v___x_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___lam__0___boxed(lean_object* v_p_3556_, lean_object* v_x_3557_, lean_object* v_handler_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_){
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l_Lean_Server_handleOnDidChange___lam__0(v_p_3556_, v_x_3557_, v_handler_3558_, v___y_3559_);
lean_dec_ref(v___y_3559_);
lean_dec_ref(v_x_3557_);
return v_res_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0(lean_object* v_f_3562_, lean_object* v_x_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_){
_start:
{
lean_object* v___x_3568_; 
lean_inc_ref(v___y_3566_);
v___x_3568_ = lean_apply_4(v_f_3562_, v___y_3564_, v___y_3565_, v___y_3566_, lean_box(0));
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0___boxed(lean_object* v_f_3569_, lean_object* v_x_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0(v_f_3569_, v_x_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
lean_dec_ref(v___y_3573_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_3576_, lean_object* v_keys_3577_, lean_object* v_vals_3578_, lean_object* v_i_3579_, lean_object* v_acc_3580_, lean_object* v___y_3581_){
_start:
{
lean_object* v___x_3583_; uint8_t v___x_3584_; 
v___x_3583_ = lean_array_get_size(v_keys_3577_);
v___x_3584_ = lean_nat_dec_lt(v_i_3579_, v___x_3583_);
if (v___x_3584_ == 0)
{
lean_object* v___x_3585_; 
lean_dec(v_i_3579_);
lean_dec_ref(v_f_3576_);
v___x_3585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3585_, 0, v_acc_3580_);
return v___x_3585_;
}
else
{
lean_object* v_k_3586_; lean_object* v_v_3587_; lean_object* v___x_3588_; 
v_k_3586_ = lean_array_fget_borrowed(v_keys_3577_, v_i_3579_);
v_v_3587_ = lean_array_fget_borrowed(v_vals_3578_, v_i_3579_);
lean_inc_ref(v_f_3576_);
lean_inc_ref(v___y_3581_);
lean_inc(v_v_3587_);
lean_inc(v_k_3586_);
v___x_3588_ = lean_apply_5(v_f_3576_, v_acc_3580_, v_k_3586_, v_v_3587_, v___y_3581_, lean_box(0));
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v_a_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; 
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_a_3589_);
lean_dec_ref(v___x_3588_);
v___x_3590_ = lean_unsigned_to_nat(1u);
v___x_3591_ = lean_nat_add(v_i_3579_, v___x_3590_);
lean_dec(v_i_3579_);
v_i_3579_ = v___x_3591_;
v_acc_3580_ = v_a_3589_;
goto _start;
}
else
{
lean_dec(v_i_3579_);
lean_dec_ref(v_f_3576_);
return v___x_3588_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_3593_, lean_object* v_keys_3594_, lean_object* v_vals_3595_, lean_object* v_i_3596_, lean_object* v_acc_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_){
_start:
{
lean_object* v_res_3600_; 
v_res_3600_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3593_, v_keys_3594_, v_vals_3595_, v_i_3596_, v_acc_3597_, v___y_3598_);
lean_dec_ref(v___y_3598_);
lean_dec_ref(v_vals_3595_);
lean_dec_ref(v_keys_3594_);
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(lean_object* v_f_3601_, lean_object* v_x_3602_, lean_object* v_x_3603_, lean_object* v___y_3604_){
_start:
{
if (lean_obj_tag(v_x_3602_) == 0)
{
lean_object* v_es_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3626_; 
v_es_3606_ = lean_ctor_get(v_x_3602_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v_x_3602_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3608_ = v_x_3602_;
v_isShared_3609_ = v_isSharedCheck_3626_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_es_3606_);
lean_dec(v_x_3602_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3626_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3610_; lean_object* v___x_3611_; uint8_t v___x_3612_; 
v___x_3610_ = lean_unsigned_to_nat(0u);
v___x_3611_ = lean_array_get_size(v_es_3606_);
v___x_3612_ = lean_nat_dec_lt(v___x_3610_, v___x_3611_);
if (v___x_3612_ == 0)
{
lean_object* v___x_3614_; 
lean_dec_ref(v_es_3606_);
lean_dec_ref(v_f_3601_);
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 0, v_x_3603_);
v___x_3614_ = v___x_3608_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_x_3603_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
else
{
uint8_t v___x_3616_; 
v___x_3616_ = lean_nat_dec_le(v___x_3611_, v___x_3611_);
if (v___x_3616_ == 0)
{
if (v___x_3612_ == 0)
{
lean_object* v___x_3618_; 
lean_dec_ref(v_es_3606_);
lean_dec_ref(v_f_3601_);
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 0, v_x_3603_);
v___x_3618_ = v___x_3608_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_x_3603_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
else
{
size_t v___x_3620_; size_t v___x_3621_; lean_object* v___x_3622_; 
lean_del_object(v___x_3608_);
v___x_3620_ = ((size_t)0ULL);
v___x_3621_ = lean_usize_of_nat(v___x_3611_);
v___x_3622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3601_, v_es_3606_, v___x_3620_, v___x_3621_, v_x_3603_, v___y_3604_);
lean_dec_ref(v_es_3606_);
return v___x_3622_;
}
}
else
{
size_t v___x_3623_; size_t v___x_3624_; lean_object* v___x_3625_; 
lean_del_object(v___x_3608_);
v___x_3623_ = ((size_t)0ULL);
v___x_3624_ = lean_usize_of_nat(v___x_3611_);
v___x_3625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3601_, v_es_3606_, v___x_3623_, v___x_3624_, v_x_3603_, v___y_3604_);
lean_dec_ref(v_es_3606_);
return v___x_3625_;
}
}
}
}
else
{
lean_object* v_ks_3627_; lean_object* v_vs_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; 
v_ks_3627_ = lean_ctor_get(v_x_3602_, 0);
lean_inc_ref(v_ks_3627_);
v_vs_3628_ = lean_ctor_get(v_x_3602_, 1);
lean_inc_ref(v_vs_3628_);
lean_dec_ref(v_x_3602_);
v___x_3629_ = lean_unsigned_to_nat(0u);
v___x_3630_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3601_, v_ks_3627_, v_vs_3628_, v___x_3629_, v_x_3603_, v___y_3604_);
lean_dec_ref(v_vs_3628_);
lean_dec_ref(v_ks_3627_);
return v___x_3630_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_3631_, lean_object* v_as_3632_, size_t v_i_3633_, size_t v_stop_3634_, lean_object* v_b_3635_, lean_object* v___y_3636_){
_start:
{
lean_object* v_a_3639_; lean_object* v___y_3644_; uint8_t v___x_3646_; 
v___x_3646_ = lean_usize_dec_eq(v_i_3633_, v_stop_3634_);
if (v___x_3646_ == 0)
{
lean_object* v___x_3647_; 
v___x_3647_ = lean_array_uget_borrowed(v_as_3632_, v_i_3633_);
switch(lean_obj_tag(v___x_3647_))
{
case 0:
{
lean_object* v_key_3648_; lean_object* v_val_3649_; lean_object* v___x_3650_; 
v_key_3648_ = lean_ctor_get(v___x_3647_, 0);
v_val_3649_ = lean_ctor_get(v___x_3647_, 1);
lean_inc_ref(v_f_3631_);
lean_inc_ref(v___y_3636_);
lean_inc(v_val_3649_);
lean_inc(v_key_3648_);
v___x_3650_ = lean_apply_5(v_f_3631_, v_b_3635_, v_key_3648_, v_val_3649_, v___y_3636_, lean_box(0));
v___y_3644_ = v___x_3650_;
goto v___jp_3643_;
}
case 1:
{
lean_object* v_node_3651_; lean_object* v___x_3652_; 
v_node_3651_ = lean_ctor_get(v___x_3647_, 0);
lean_inc(v_node_3651_);
lean_inc_ref(v_f_3631_);
v___x_3652_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3631_, v_node_3651_, v_b_3635_, v___y_3636_);
v___y_3644_ = v___x_3652_;
goto v___jp_3643_;
}
default: 
{
v_a_3639_ = v_b_3635_;
goto v___jp_3638_;
}
}
}
else
{
lean_object* v___x_3653_; 
lean_dec_ref(v_f_3631_);
v___x_3653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3653_, 0, v_b_3635_);
return v___x_3653_;
}
v___jp_3638_:
{
size_t v___x_3640_; size_t v___x_3641_; 
v___x_3640_ = ((size_t)1ULL);
v___x_3641_ = lean_usize_add(v_i_3633_, v___x_3640_);
v_i_3633_ = v___x_3641_;
v_b_3635_ = v_a_3639_;
goto _start;
}
v___jp_3643_:
{
if (lean_obj_tag(v___y_3644_) == 0)
{
lean_object* v_a_3645_; 
v_a_3645_ = lean_ctor_get(v___y_3644_, 0);
lean_inc(v_a_3645_);
lean_dec_ref(v___y_3644_);
v_a_3639_ = v_a_3645_;
goto v___jp_3638_;
}
else
{
lean_dec_ref(v_f_3631_);
return v___y_3644_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_3654_, lean_object* v_as_3655_, lean_object* v_i_3656_, lean_object* v_stop_3657_, lean_object* v_b_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_){
_start:
{
size_t v_i_boxed_3661_; size_t v_stop_boxed_3662_; lean_object* v_res_3663_; 
v_i_boxed_3661_ = lean_unbox_usize(v_i_3656_);
lean_dec(v_i_3656_);
v_stop_boxed_3662_ = lean_unbox_usize(v_stop_3657_);
lean_dec(v_stop_3657_);
v_res_3663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3654_, v_as_3655_, v_i_boxed_3661_, v_stop_boxed_3662_, v_b_3658_, v___y_3659_);
lean_dec_ref(v___y_3659_);
lean_dec_ref(v_as_3655_);
return v_res_3663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_3664_, lean_object* v_x_3665_, lean_object* v_x_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_){
_start:
{
lean_object* v_res_3669_; 
v_res_3669_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3664_, v_x_3665_, v_x_3666_, v___y_3667_);
lean_dec_ref(v___y_3667_);
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(lean_object* v_map_3670_, lean_object* v_f_3671_, lean_object* v___y_3672_){
_start:
{
lean_object* v___f_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; 
v___f_3674_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3674_, 0, v_f_3671_);
v___x_3675_ = lean_box(0);
v___x_3676_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v___f_3674_, v_map_3670_, v___x_3675_, v___y_3672_);
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___boxed(lean_object* v_map_3677_, lean_object* v_f_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_){
_start:
{
lean_object* v_res_3681_; 
v_res_3681_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(v_map_3677_, v_f_3678_, v___y_3679_);
lean_dec_ref(v___y_3679_);
return v_res_3681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange(lean_object* v_p_3682_, lean_object* v_a_3683_){
_start:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___f_3687_; lean_object* v___x_3688_; 
v___x_3685_ = l_Lean_Server_statefulRequestHandlers;
v___x_3686_ = lean_st_ref_get(v___x_3685_);
v___f_3687_ = lean_alloc_closure((void*)(l_Lean_Server_handleOnDidChange___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3687_, 0, v_p_3682_);
v___x_3688_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(v___x_3686_, v___f_3687_, v_a_3683_);
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___boxed(lean_object* v_p_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_){
_start:
{
lean_object* v_res_3692_; 
v_res_3692_ = l_Lean_Server_handleOnDidChange(v_p_3689_, v_a_3690_);
lean_dec_ref(v_a_3690_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0(lean_object* v_00_u03b2_3693_, lean_object* v_map_3694_, lean_object* v_f_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v___x_3698_; 
v___x_3698_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(v_map_3694_, v_f_3695_, v___y_3696_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___boxed(lean_object* v_00_u03b2_3699_, lean_object* v_map_3700_, lean_object* v_f_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
lean_object* v_res_3704_; 
v_res_3704_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0(v_00_u03b2_3699_, v_map_3700_, v_f_3701_, v___y_3702_);
lean_dec_ref(v___y_3702_);
return v_res_3704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg(lean_object* v_map_3705_, lean_object* v_f_3706_, lean_object* v_init_3707_, lean_object* v___y_3708_){
_start:
{
lean_object* v___x_3710_; 
v___x_3710_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3706_, v_map_3705_, v_init_3707_, v___y_3708_);
return v___x_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg___boxed(lean_object* v_map_3711_, lean_object* v_f_3712_, lean_object* v_init_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_){
_start:
{
lean_object* v_res_3716_; 
v_res_3716_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg(v_map_3711_, v_f_3712_, v_init_3713_, v___y_3714_);
lean_dec_ref(v___y_3714_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0(lean_object* v_00_u03c3_3717_, lean_object* v_00_u03b2_3718_, lean_object* v_map_3719_, lean_object* v_f_3720_, lean_object* v_init_3721_, lean_object* v___y_3722_){
_start:
{
lean_object* v___x_3724_; 
v___x_3724_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3720_, v_map_3719_, v_init_3721_, v___y_3722_);
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3725_, lean_object* v_00_u03b2_3726_, lean_object* v_map_3727_, lean_object* v_f_3728_, lean_object* v_init_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_){
_start:
{
lean_object* v_res_3732_; 
v_res_3732_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0(v_00_u03c3_3725_, v_00_u03b2_3726_, v_map_3727_, v_f_3728_, v_init_3729_, v___y_3730_);
lean_dec_ref(v___y_3730_);
return v_res_3732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3733_, lean_object* v_00_u03b1_3734_, lean_object* v_00_u03b2_3735_, lean_object* v_f_3736_, lean_object* v_x_3737_, lean_object* v_x_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v___x_3741_; 
v___x_3741_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3736_, v_x_3737_, v_x_3738_, v___y_3739_);
return v___x_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3742_, lean_object* v_00_u03b1_3743_, lean_object* v_00_u03b2_3744_, lean_object* v_f_3745_, lean_object* v_x_3746_, lean_object* v_x_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
lean_object* v_res_3750_; 
v_res_3750_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1(v_00_u03c3_3742_, v_00_u03b1_3743_, v_00_u03b2_3744_, v_f_3745_, v_x_3746_, v_x_3747_, v___y_3748_);
lean_dec_ref(v___y_3748_);
return v_res_3750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3751_, lean_object* v_00_u03b2_3752_, lean_object* v_00_u03c3_3753_, lean_object* v_f_3754_, lean_object* v_as_3755_, size_t v_i_3756_, size_t v_stop_3757_, lean_object* v_b_3758_, lean_object* v___y_3759_){
_start:
{
lean_object* v___x_3761_; 
v___x_3761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3754_, v_as_3755_, v_i_3756_, v_stop_3757_, v_b_3758_, v___y_3759_);
return v___x_3761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3762_, lean_object* v_00_u03b2_3763_, lean_object* v_00_u03c3_3764_, lean_object* v_f_3765_, lean_object* v_as_3766_, lean_object* v_i_3767_, lean_object* v_stop_3768_, lean_object* v_b_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
size_t v_i_boxed_3772_; size_t v_stop_boxed_3773_; lean_object* v_res_3774_; 
v_i_boxed_3772_ = lean_unbox_usize(v_i_3767_);
lean_dec(v_i_3767_);
v_stop_boxed_3773_ = lean_unbox_usize(v_stop_3768_);
lean_dec(v_stop_3768_);
v_res_3774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3762_, v_00_u03b2_3763_, v_00_u03c3_3764_, v_f_3765_, v_as_3766_, v_i_boxed_3772_, v_stop_boxed_3773_, v_b_3769_, v___y_3770_);
lean_dec_ref(v___y_3770_);
lean_dec_ref(v_as_3766_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3775_, lean_object* v_00_u03b1_3776_, lean_object* v_00_u03b2_3777_, lean_object* v_f_3778_, lean_object* v_keys_3779_, lean_object* v_vals_3780_, lean_object* v_heq_3781_, lean_object* v_i_3782_, lean_object* v_acc_3783_, lean_object* v___y_3784_){
_start:
{
lean_object* v___x_3786_; 
v___x_3786_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3778_, v_keys_3779_, v_vals_3780_, v_i_3782_, v_acc_3783_, v___y_3784_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3787_, lean_object* v_00_u03b1_3788_, lean_object* v_00_u03b2_3789_, lean_object* v_f_3790_, lean_object* v_keys_3791_, lean_object* v_vals_3792_, lean_object* v_heq_3793_, lean_object* v_i_3794_, lean_object* v_acc_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_){
_start:
{
lean_object* v_res_3798_; 
v_res_3798_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3787_, v_00_u03b1_3788_, v_00_u03b2_3789_, v_f_3790_, v_keys_3791_, v_vals_3792_, v_heq_3793_, v_i_3794_, v_acc_3795_, v___y_3796_);
lean_dec_ref(v___y_3796_);
lean_dec_ref(v_vals_3792_);
lean_dec_ref(v_keys_3791_);
return v_res_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest(lean_object* v_method_3801_, lean_object* v_params_3802_, lean_object* v_a_3803_){
_start:
{
uint8_t v___x_3805_; 
v___x_3805_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_3801_);
if (v___x_3805_ == 0)
{
lean_object* v___x_3806_; lean_object* v_a_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3822_; 
v___x_3806_ = l_Lean_Server_lookupLspRequestHandler(v_method_3801_);
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3809_ = v___x_3806_;
v_isShared_3810_ = v_isSharedCheck_3822_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_a_3807_);
lean_dec(v___x_3806_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3822_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
if (lean_obj_tag(v_a_3807_) == 0)
{
lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3817_; 
lean_dec(v_params_3802_);
v___x_3811_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__0));
v___x_3812_ = lean_string_append(v___x_3811_, v_method_3801_);
v___x_3813_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__1));
v___x_3814_ = lean_string_append(v___x_3812_, v___x_3813_);
v___x_3815_ = l_Lean_Server_RequestError_internalError(v___x_3814_);
if (v_isShared_3810_ == 0)
{
lean_ctor_set_tag(v___x_3809_, 1);
lean_ctor_set(v___x_3809_, 0, v___x_3815_);
v___x_3817_ = v___x_3809_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3815_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
else
{
lean_object* v_val_3819_; lean_object* v_handle_3820_; lean_object* v___x_3821_; 
lean_del_object(v___x_3809_);
v_val_3819_ = lean_ctor_get(v_a_3807_, 0);
lean_inc(v_val_3819_);
lean_dec_ref(v_a_3807_);
v_handle_3820_ = lean_ctor_get(v_val_3819_, 1);
lean_inc_ref(v_handle_3820_);
lean_dec(v_val_3819_);
lean_inc_ref(v_a_3803_);
v___x_3821_ = lean_apply_3(v_handle_3820_, v_params_3802_, v_a_3803_, lean_box(0));
return v___x_3821_;
}
}
}
else
{
lean_object* v___x_3823_; 
v___x_3823_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_3801_);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; 
lean_dec(v_params_3802_);
v___x_3824_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__0));
v___x_3825_ = lean_string_append(v___x_3824_, v_method_3801_);
v___x_3826_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__1));
v___x_3827_ = lean_string_append(v___x_3825_, v___x_3826_);
v___x_3828_ = l_Lean_Server_RequestError_internalError(v___x_3827_);
v___x_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3829_, 0, v___x_3828_);
return v___x_3829_;
}
else
{
lean_object* v_val_3830_; lean_object* v_handle_3831_; lean_object* v___x_3832_; 
v_val_3830_ = lean_ctor_get(v___x_3823_, 0);
lean_inc(v_val_3830_);
lean_dec_ref(v___x_3823_);
v_handle_3831_ = lean_ctor_get(v_val_3830_, 2);
lean_inc_ref(v_handle_3831_);
lean_dec(v_val_3830_);
lean_inc_ref(v_a_3803_);
v___x_3832_ = lean_apply_3(v_handle_3831_, v_params_3802_, v_a_3803_, lean_box(0));
return v___x_3832_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest___boxed(lean_object* v_method_3833_, lean_object* v_params_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l_Lean_Server_handleLspRequest(v_method_3833_, v_params_3834_, v_a_3835_);
lean_dec_ref(v_a_3835_);
lean_dec_ref(v_method_3833_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_routeLspRequest(lean_object* v_method_3838_, lean_object* v_params_3839_){
_start:
{
uint8_t v___x_3841_; 
v___x_3841_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_3838_);
if (v___x_3841_ == 0)
{
lean_object* v___x_3842_; lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3858_; 
v___x_3842_ = l_Lean_Server_lookupLspRequestHandler(v_method_3838_);
v_a_3843_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3845_ = v___x_3842_;
v_isShared_3846_ = v_isSharedCheck_3858_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3842_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3858_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
if (lean_obj_tag(v_a_3843_) == 0)
{
lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3850_; 
lean_dec(v_params_3839_);
v___x_3847_ = l_Lean_Server_RequestError_methodNotFound(v_method_3838_);
v___x_3848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3847_);
if (v_isShared_3846_ == 0)
{
lean_ctor_set(v___x_3845_, 0, v___x_3848_);
v___x_3850_ = v___x_3845_;
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
else
{
lean_object* v_val_3852_; lean_object* v_fileSource_3853_; lean_object* v___x_3854_; lean_object* v___x_3856_; 
v_val_3852_ = lean_ctor_get(v_a_3843_, 0);
lean_inc(v_val_3852_);
lean_dec_ref(v_a_3843_);
v_fileSource_3853_ = lean_ctor_get(v_val_3852_, 0);
lean_inc_ref(v_fileSource_3853_);
lean_dec(v_val_3852_);
v___x_3854_ = lean_apply_1(v_fileSource_3853_, v_params_3839_);
if (v_isShared_3846_ == 0)
{
lean_ctor_set(v___x_3845_, 0, v___x_3854_);
v___x_3856_ = v___x_3845_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v___x_3854_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
}
}
else
{
lean_object* v___x_3859_; 
v___x_3859_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_3838_);
if (lean_obj_tag(v___x_3859_) == 0)
{
lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
lean_dec(v_params_3839_);
v___x_3860_ = l_Lean_Server_RequestError_methodNotFound(v_method_3838_);
v___x_3861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3860_);
v___x_3862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3861_);
return v___x_3862_;
}
else
{
lean_object* v_val_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3872_; 
v_val_3863_ = lean_ctor_get(v___x_3859_, 0);
v_isSharedCheck_3872_ = !lean_is_exclusive(v___x_3859_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3865_ = v___x_3859_;
v_isShared_3866_ = v_isSharedCheck_3872_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_val_3863_);
lean_dec(v___x_3859_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3872_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v_fileSource_3867_; lean_object* v___x_3868_; lean_object* v___x_3870_; 
v_fileSource_3867_ = lean_ctor_get(v_val_3863_, 0);
lean_inc_ref(v_fileSource_3867_);
lean_dec(v_val_3863_);
v___x_3868_ = lean_apply_1(v_fileSource_3867_, v_params_3839_);
if (v_isShared_3866_ == 0)
{
lean_ctor_set_tag(v___x_3865_, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3868_);
v___x_3870_ = v___x_3865_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___x_3868_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_routeLspRequest___boxed(lean_object* v_method_3873_, lean_object* v_params_3874_, lean_object* v_a_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l_Lean_Server_routeLspRequest(v_method_3873_, v_params_3874_);
lean_dec_ref(v_method_3873_);
return v_res_3876_;
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
