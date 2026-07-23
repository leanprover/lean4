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
uint8_t l_Lean_initializing();
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
extern lean_object* l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
lean_object* l_Lean_Language_Snapshot_transform(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Language_SnapshotTree_transform___boxed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Mutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AsyncList_waitFind_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_foldInfo___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_Range_includes(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTree_transform___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__4___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__4___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2___lam__0___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__3___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__3___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__3___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1(lean_object*);
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
v_findTask_1215_ = l_Lean_AsyncList_waitFind_x3f___redArg(v_p_1208_, v_cmdSnaps_1214_);
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
v_findTask_1249_ = l_Lean_AsyncList_waitFind_x3f___redArg(v_p_1242_, v_cmdSnaps_1248_);
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
v___x_1422_ = lean_unsigned_to_nat(420u);
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
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__4(lean_object* v_t_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v___f_1460_; lean_object* v___x_1461_; 
v___f_1460_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__4___closed__0));
v___x_1461_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_1458_, v___f_1460_, v_a_1459_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__4___boxed(lean_object* v_t_1462_, lean_object* v_a_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__4(v_t_1462_, v_a_1463_);
lean_dec_ref(v_a_1463_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2___lam__0(lean_object* v_s_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v_toSnapshot_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1478_; 
v_toSnapshot_1469_ = lean_ctor_get(v_s_1467_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_s_1467_);
if (v_isSharedCheck_1478_ == 0)
{
lean_object* v_unused_1479_; 
v_unused_1479_ = lean_ctor_get(v_s_1467_, 1);
lean_dec(v_unused_1479_);
v___x_1471_ = v_s_1467_;
v_isShared_1472_ = v_isSharedCheck_1478_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_toSnapshot_1469_);
lean_dec(v_s_1467_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1478_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1476_; 
v___x_1473_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_1469_, v___y_1468_);
v___x_1474_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2___lam__0___closed__0));
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 1, v___x_1474_);
lean_ctor_set(v___x_1471_, 0, v___x_1473_);
v___x_1476_ = v___x_1471_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1473_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v___x_1474_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2___lam__0___boxed(lean_object* v_s_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2___lam__0(v_s_1480_, v___y_1481_);
lean_dec_ref(v___y_1481_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2(lean_object* v_t_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v___f_1486_; lean_object* v___x_1487_; 
v___f_1486_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2___closed__0));
v___x_1487_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_1484_, v___f_1486_, v_a_1485_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2___boxed(lean_object* v_t_1488_, lean_object* v_a_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2(v_t_1488_, v_a_1489_);
lean_dec_ref(v_a_1489_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__1___lam__0(lean_object* v_s_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_toSnapshotTreeM_1493_; lean_object* v___x_1494_; 
v_toSnapshotTreeM_1493_ = lean_ctor_get(v_s_1491_, 1);
lean_inc_ref(v_toSnapshotTreeM_1493_);
lean_dec_ref(v_s_1491_);
lean_inc_ref(v___y_1492_);
v___x_1494_ = lean_apply_1(v_toSnapshotTreeM_1493_, v___y_1492_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__1___lam__0___boxed(lean_object* v_s_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__1___lam__0(v_s_1495_, v___y_1496_);
lean_dec_ref(v___y_1496_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__1(lean_object* v_t_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v___f_1501_; lean_object* v___x_1502_; 
v___f_1501_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__1___closed__0));
v___x_1502_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_1499_, v___f_1501_, v_a_1500_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__1___boxed(lean_object* v_t_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__1(v_t_1503_, v_a_1504_);
lean_dec_ref(v_a_1504_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__3___lam__0(lean_object* v_s_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1508_ = l_Lean_Language_Snapshot_transform(v_s_1506_, v___y_1507_);
v___x_1509_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2___lam__0___closed__0));
v___x_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1508_);
lean_ctor_set(v___x_1510_, 1, v___x_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__3___lam__0___boxed(lean_object* v_s_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__3___lam__0(v_s_1511_, v___y_1512_);
lean_dec_ref(v___y_1512_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__3(lean_object* v_t_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v___f_1517_; lean_object* v___x_1518_; 
v___f_1517_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__3___closed__0));
v___x_1518_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_1515_, v___f_1517_, v_a_1516_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__3___boxed(lean_object* v_t_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__3(v_t_1519_, v_a_1520_);
lean_dec_ref(v_a_1520_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1(lean_object* v_a_1522_){
_start:
{
lean_object* v_toSnapshot_1523_; lean_object* v_elabSnap_1524_; lean_object* v_resultSnap_1525_; lean_object* v_infoTreeSnap_1526_; lean_object* v_reportSnap_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v_toSnapshot_1523_ = lean_ctor_get(v_a_1522_, 0);
lean_inc_ref(v_toSnapshot_1523_);
v_elabSnap_1524_ = lean_ctor_get(v_a_1522_, 1);
lean_inc_ref(v_elabSnap_1524_);
v_resultSnap_1525_ = lean_ctor_get(v_a_1522_, 2);
lean_inc_ref(v_resultSnap_1525_);
v_infoTreeSnap_1526_ = lean_ctor_get(v_a_1522_, 3);
lean_inc_ref(v_infoTreeSnap_1526_);
v_reportSnap_1527_ = lean_ctor_get(v_a_1522_, 4);
lean_inc_ref(v_reportSnap_1527_);
lean_dec_ref(v_a_1522_);
v___x_1528_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1529_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_1523_, v___x_1528_);
v___x_1530_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__1(v_elabSnap_1524_, v___x_1528_);
v___x_1531_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2(v_resultSnap_1525_, v___x_1528_);
v___x_1532_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__3(v_infoTreeSnap_1526_, v___x_1528_);
v___x_1533_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__4(v_reportSnap_1527_, v___x_1528_);
v___x_1534_ = lean_unsigned_to_nat(4u);
v___x_1535_ = lean_mk_empty_array_with_capacity(v___x_1534_);
v___x_1536_ = lean_array_push(v___x_1535_, v___x_1530_);
v___x_1537_ = lean_array_push(v___x_1536_, v___x_1531_);
v___x_1538_ = lean_array_push(v___x_1537_, v___x_1532_);
v___x_1539_ = lean_array_push(v___x_1538_, v___x_1533_);
v___x_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1529_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
return v___x_1540_;
}
}
static lean_object* _init_l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___closed__0(void){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = lean_box(0);
v___x_1542_ = lean_task_pure(v___x_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lam__2(lean_object* v_doc_1543_, lean_object* v_hoverPos_1544_, uint8_t v_includeStop_1545_, lean_object* v_x_1546_){
_start:
{
if (lean_obj_tag(v_x_1546_) == 0)
{
lean_object* v___x_1547_; 
lean_dec(v_hoverPos_1544_);
lean_dec_ref(v_doc_1543_);
v___x_1547_ = lean_obj_once(&l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___closed__0, &l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___closed__0_once, _init_l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___closed__0);
return v___x_1547_;
}
else
{
lean_object* v_toEditableDocumentCore_1548_; lean_object* v_meta_1549_; lean_object* v_val_1550_; lean_object* v_text_1551_; lean_object* v_stx_1552_; lean_object* v_elabSnap_1553_; lean_object* v___f_1554_; lean_object* v___f_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v_toEditableDocumentCore_1548_ = lean_ctor_get(v_doc_1543_, 0);
lean_inc_ref(v_toEditableDocumentCore_1548_);
lean_dec_ref(v_doc_1543_);
v_meta_1549_ = lean_ctor_get(v_toEditableDocumentCore_1548_, 0);
lean_inc_ref(v_meta_1549_);
lean_dec_ref(v_toEditableDocumentCore_1548_);
v_val_1550_ = lean_ctor_get(v_x_1546_, 0);
lean_inc(v_val_1550_);
lean_dec_ref_known(v_x_1546_, 1);
v_text_1551_ = lean_ctor_get(v_meta_1549_, 3);
lean_inc_ref(v_text_1551_);
lean_dec_ref(v_meta_1549_);
v_stx_1552_ = lean_ctor_get(v_val_1550_, 1);
lean_inc_n(v_stx_1552_, 2);
v_elabSnap_1553_ = lean_ctor_get(v_val_1550_, 3);
lean_inc_ref_n(v_elabSnap_1553_, 2);
lean_dec(v_val_1550_);
v___f_1554_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_findCmdDataAtPos___lam__0), 2, 1);
lean_closure_set(v___f_1554_, 0, v_stx_1552_);
v___f_1555_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_findCmdDataAtPos___lam__1), 4, 3);
lean_closure_set(v___f_1555_, 0, v_elabSnap_1553_);
lean_closure_set(v___f_1555_, 1, v___f_1554_);
lean_closure_set(v___f_1555_, 2, v_stx_1552_);
v___x_1556_ = l_Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1(v_elabSnap_1553_);
v___x_1557_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos(v_text_1551_, v___x_1556_, v_hoverPos_1544_, v_includeStop_1545_);
v___x_1558_ = l_Lean_Server_ServerTask_bindCheap___redArg(v___x_1557_, v___f_1555_);
return v___x_1558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___boxed(lean_object* v_doc_1559_, lean_object* v_hoverPos_1560_, lean_object* v_includeStop_1561_, lean_object* v_x_1562_){
_start:
{
uint8_t v_includeStop_boxed_1563_; lean_object* v_res_1564_; 
v_includeStop_boxed_1563_ = lean_unbox(v_includeStop_1561_);
v_res_1564_ = l_Lean_Server_RequestM_findCmdDataAtPos___lam__2(v_doc_1559_, v_hoverPos_1560_, v_includeStop_boxed_1563_, v_x_1562_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos(lean_object* v_doc_1565_, lean_object* v_hoverPos_1566_, uint8_t v_includeStop_1567_){
_start:
{
lean_object* v___x_1568_; lean_object* v___f_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1568_ = lean_box(v_includeStop_1567_);
lean_inc(v_hoverPos_1566_);
lean_inc_ref(v_doc_1565_);
v___f_1569_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1569_, 0, v_doc_1565_);
lean_closure_set(v___f_1569_, 1, v_hoverPos_1566_);
lean_closure_set(v___f_1569_, 2, v___x_1568_);
v___x_1570_ = l_Lean_Server_RequestM_findCmdParsedSnap(v_doc_1565_, v_hoverPos_1566_);
v___x_1571_ = l_Lean_Server_ServerTask_bindCheap___redArg(v___x_1570_, v___f_1569_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___boxed(lean_object* v_doc_1572_, lean_object* v_hoverPos_1573_, lean_object* v_includeStop_1574_){
_start:
{
uint8_t v_includeStop_boxed_1575_; lean_object* v_res_1576_; 
v_includeStop_boxed_1575_ = lean_unbox(v_includeStop_1574_);
v_res_1576_ = l_Lean_Server_RequestM_findCmdDataAtPos(v_doc_1572_, v_hoverPos_1573_, v_includeStop_boxed_1575_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findInfoTreeAtPos___lam__0(lean_object* v_x_1577_){
_start:
{
if (lean_obj_tag(v_x_1577_) == 0)
{
lean_object* v___x_1578_; 
v___x_1578_ = lean_box(0);
return v___x_1578_;
}
else
{
lean_object* v_val_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1587_; 
v_val_1579_ = lean_ctor_get(v_x_1577_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_x_1577_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1581_ = v_x_1577_;
v_isShared_1582_ = v_isSharedCheck_1587_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_val_1579_);
lean_dec(v_x_1577_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1587_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v_snd_1583_; lean_object* v___x_1585_; 
v_snd_1583_ = lean_ctor_get(v_val_1579_, 1);
lean_inc(v_snd_1583_);
lean_dec(v_val_1579_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 0, v_snd_1583_);
v___x_1585_ = v___x_1581_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_snd_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findInfoTreeAtPos(lean_object* v_doc_1589_, lean_object* v_hoverPos_1590_, uint8_t v_includeStop_1591_){
_start:
{
lean_object* v___f_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___f_1592_ = ((lean_object*)(l_Lean_Server_RequestM_findInfoTreeAtPos___closed__0));
v___x_1593_ = l_Lean_Server_RequestM_findCmdDataAtPos(v_doc_1589_, v_hoverPos_1590_, v_includeStop_1591_);
v___x_1594_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_1592_, v___x_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findInfoTreeAtPos___boxed(lean_object* v_doc_1595_, lean_object* v_hoverPos_1596_, lean_object* v_includeStop_1597_){
_start:
{
uint8_t v_includeStop_boxed_1598_; lean_object* v_res_1599_; 
v_includeStop_boxed_1598_ = lean_unbox(v_includeStop_1597_);
v_res_1599_ = l_Lean_Server_RequestM_findInfoTreeAtPos(v_doc_1595_, v_hoverPos_1596_, v_includeStop_boxed_1598_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___redArg(lean_object* v_snap_1600_, lean_object* v_c_1601_, lean_object* v_a_1602_){
_start:
{
lean_object* v_doc_1604_; lean_object* v_toEditableDocumentCore_1605_; lean_object* v_meta_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v_doc_1604_ = lean_ctor_get(v_a_1602_, 1);
v_toEditableDocumentCore_1605_ = lean_ctor_get(v_doc_1604_, 0);
v_meta_1606_ = lean_ctor_get(v_toEditableDocumentCore_1605_, 0);
lean_inc_ref(v_a_1602_);
v___x_1607_ = lean_apply_1(v_c_1601_, v_a_1602_);
v___x_1608_ = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(v_snap_1600_, v_meta_1606_, v___x_1607_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1621_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1611_ = v___x_1608_;
v_isShared_1612_ = v_isSharedCheck_1621_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1608_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1621_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
if (lean_obj_tag(v_a_1609_) == 0)
{
lean_object* v_a_1613_; lean_object* v___x_1615_; 
v_a_1613_ = lean_ctor_get(v_a_1609_, 0);
lean_inc(v_a_1613_);
lean_dec_ref_known(v_a_1609_, 1);
if (v_isShared_1612_ == 0)
{
lean_ctor_set_tag(v___x_1611_, 1);
lean_ctor_set(v___x_1611_, 0, v_a_1613_);
v___x_1615_ = v___x_1611_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1613_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; 
v_a_1617_ = lean_ctor_get(v_a_1609_, 0);
lean_inc(v_a_1617_);
lean_dec_ref_known(v_a_1609_, 1);
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 0, v_a_1617_);
v___x_1619_ = v___x_1611_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1617_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1623_; lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
v_a_1622_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1622_);
lean_dec_ref_known(v___x_1608_, 1);
v___x_1623_ = l_Lean_Server_RequestError_ofException(v_a_1622_);
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1623_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1623_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
lean_ctor_set_tag(v___x_1626_, 1);
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___redArg___boxed(lean_object* v_snap_1632_, lean_object* v_c_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_Server_RequestM_runCommandElabM___redArg(v_snap_1632_, v_c_1633_, v_a_1634_);
lean_dec_ref(v_a_1634_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM(lean_object* v_00_u03b1_1637_, lean_object* v_snap_1638_, lean_object* v_c_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_Server_RequestM_runCommandElabM___redArg(v_snap_1638_, v_c_1639_, v_a_1640_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___boxed(lean_object* v_00_u03b1_1643_, lean_object* v_snap_1644_, lean_object* v_c_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Lean_Server_RequestM_runCommandElabM(v_00_u03b1_1643_, v_snap_1644_, v_c_1645_, v_a_1646_);
lean_dec_ref(v_a_1646_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___redArg(lean_object* v_snap_1649_, lean_object* v_c_1650_, lean_object* v_a_1651_){
_start:
{
lean_object* v_doc_1653_; lean_object* v_toEditableDocumentCore_1654_; lean_object* v_meta_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v_doc_1653_ = lean_ctor_get(v_a_1651_, 1);
v_toEditableDocumentCore_1654_ = lean_ctor_get(v_doc_1653_, 0);
v_meta_1655_ = lean_ctor_get(v_toEditableDocumentCore_1654_, 0);
lean_inc_ref(v_a_1651_);
v___x_1656_ = lean_apply_1(v_c_1650_, v_a_1651_);
v___x_1657_ = l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(v_snap_1649_, v_meta_1655_, v___x_1656_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1670_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1660_ = v___x_1657_;
v_isShared_1661_ = v_isSharedCheck_1670_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1670_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
if (lean_obj_tag(v_a_1658_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1664_; 
v_a_1662_ = lean_ctor_get(v_a_1658_, 0);
lean_inc(v_a_1662_);
lean_dec_ref_known(v_a_1658_, 1);
if (v_isShared_1661_ == 0)
{
lean_ctor_set_tag(v___x_1660_, 1);
lean_ctor_set(v___x_1660_, 0, v_a_1662_);
v___x_1664_ = v___x_1660_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1662_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; 
v_a_1666_ = lean_ctor_get(v_a_1658_, 0);
lean_inc(v_a_1666_);
lean_dec_ref_known(v_a_1658_, 1);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v_a_1666_);
v___x_1668_ = v___x_1660_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1666_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
else
{
lean_object* v_a_1671_; lean_object* v___x_1672_; lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
v_a_1671_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1671_);
lean_dec_ref_known(v___x_1657_, 1);
v___x_1672_ = l_Lean_Server_RequestError_ofException(v_a_1671_);
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1672_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1672_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
lean_ctor_set_tag(v___x_1675_, 1);
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___redArg___boxed(lean_object* v_snap_1681_, lean_object* v_c_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Lean_Server_RequestM_runCoreM___redArg(v_snap_1681_, v_c_1682_, v_a_1683_);
lean_dec_ref(v_a_1683_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM(lean_object* v_00_u03b1_1686_, lean_object* v_snap_1687_, lean_object* v_c_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Lean_Server_RequestM_runCoreM___redArg(v_snap_1687_, v_c_1688_, v_a_1689_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___boxed(lean_object* v_00_u03b1_1692_, lean_object* v_snap_1693_, lean_object* v_c_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_Server_RequestM_runCoreM(v_00_u03b1_1692_, v_snap_1693_, v_c_1694_, v_a_1695_);
lean_dec_ref(v_a_1695_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___redArg(lean_object* v_snap_1698_, lean_object* v_c_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_doc_1702_; lean_object* v_toEditableDocumentCore_1703_; lean_object* v_meta_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v_doc_1702_ = lean_ctor_get(v_a_1700_, 1);
v_toEditableDocumentCore_1703_ = lean_ctor_get(v_doc_1702_, 0);
v_meta_1704_ = lean_ctor_get(v_toEditableDocumentCore_1703_, 0);
lean_inc_ref(v_a_1700_);
v___x_1705_ = lean_apply_1(v_c_1699_, v_a_1700_);
v___x_1706_ = l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg(v_snap_1698_, v_meta_1704_, v___x_1705_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1719_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1709_ = v___x_1706_;
v_isShared_1710_ = v_isSharedCheck_1719_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1706_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1719_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
if (lean_obj_tag(v_a_1707_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1713_; 
v_a_1711_ = lean_ctor_get(v_a_1707_, 0);
lean_inc(v_a_1711_);
lean_dec_ref_known(v_a_1707_, 1);
if (v_isShared_1710_ == 0)
{
lean_ctor_set_tag(v___x_1709_, 1);
lean_ctor_set(v___x_1709_, 0, v_a_1711_);
v___x_1713_ = v___x_1709_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1711_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; 
v_a_1715_ = lean_ctor_get(v_a_1707_, 0);
lean_inc(v_a_1715_);
lean_dec_ref_known(v_a_1707_, 1);
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v_a_1715_);
v___x_1717_ = v___x_1709_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1715_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
else
{
lean_object* v_a_1720_; lean_object* v___x_1721_; lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
v_a_1720_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_a_1720_);
lean_dec_ref_known(v___x_1706_, 1);
v___x_1721_ = l_Lean_Server_RequestError_ofException(v_a_1720_);
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1721_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1721_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
lean_ctor_set_tag(v___x_1724_, 1);
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___redArg___boxed(lean_object* v_snap_1730_, lean_object* v_c_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Lean_Server_RequestM_runTermElabM___redArg(v_snap_1730_, v_c_1731_, v_a_1732_);
lean_dec_ref(v_a_1732_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM(lean_object* v_00_u03b1_1735_, lean_object* v_snap_1736_, lean_object* v_c_1737_, lean_object* v_a_1738_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_Server_RequestM_runTermElabM___redArg(v_snap_1736_, v_c_1737_, v_a_1738_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___boxed(lean_object* v_00_u03b1_1741_, lean_object* v_snap_1742_, lean_object* v_c_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_Server_RequestM_runTermElabM(v_00_u03b1_1741_, v_snap_1742_, v_c_1743_, v_a_1744_);
lean_dec_ref(v_a_1744_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage(lean_object* v_id_1753_, lean_object* v_r_1754_){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___y_1758_; 
v___x_1755_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__0));
v___x_1756_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__1));
switch(lean_obj_tag(v_id_1753_))
{
case 0:
{
lean_object* v_s_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
v_s_1772_ = lean_ctor_get(v_id_1753_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v_id_1753_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v_id_1753_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_s_1772_);
lean_dec(v_id_1753_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
lean_ctor_set_tag(v___x_1774_, 3);
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_s_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
v___y_1758_ = v___x_1777_;
goto v___jp_1757_;
}
}
}
case 1:
{
lean_object* v_n_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
v_n_1780_ = lean_ctor_get(v_id_1753_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v_id_1753_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v_id_1753_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_n_1780_);
lean_dec(v_id_1753_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
lean_ctor_set_tag(v___x_1782_, 2);
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_n_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
v___y_1758_ = v___x_1785_;
goto v___jp_1757_;
}
}
}
default: 
{
lean_object* v___x_1788_; 
v___x_1788_ = lean_box(0);
v___y_1758_ = v___x_1788_;
goto v___jp_1757_;
}
}
v___jp_1757_:
{
lean_object* v_serialized_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v_serialized_1759_ = lean_ctor_get(v_r_1754_, 1);
v___x_1760_ = l_Lean_Json_compress(v___y_1758_);
v___x_1761_ = lean_string_append(v___x_1756_, v___x_1760_);
lean_dec_ref(v___x_1760_);
v___x_1762_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__2));
v___x_1763_ = lean_string_append(v___x_1761_, v___x_1762_);
v___x_1764_ = lean_string_append(v___x_1755_, v___x_1763_);
lean_dec_ref(v___x_1763_);
v___x_1765_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__3));
v___x_1766_ = lean_string_append(v___x_1764_, v___x_1765_);
v___x_1767_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__4));
v___x_1768_ = lean_string_append(v___x_1767_, v_serialized_1759_);
v___x_1769_ = lean_string_append(v___x_1766_, v___x_1768_);
lean_dec_ref(v___x_1768_);
v___x_1770_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__5));
v___x_1771_ = lean_string_append(v___x_1769_, v___x_1770_);
return v___x_1771_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage___boxed(lean_object* v_id_1789_, lean_object* v_r_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Lean_Server_SerializedLspResponse_toSerializedMessage(v_id_1789_, v_r_1790_);
lean_dec_ref(v_r_1790_);
return v_res_1791_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1792_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_);
v___x_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1796_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_);
v___x_1797_ = lean_st_mk_ref(v___x_1796_);
v___x_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2____boxed(lean_object* v_a_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_();
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__0(lean_object* v_inst_1801_, lean_object* v_inst_1802_, lean_object* v_j_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Lean_Server_parseRequestParams___redArg(v_inst_1801_, v_j_1803_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
lean_dec_ref(v_inst_1802_);
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1804_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1804_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1821_; 
v_a_1813_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1815_ = v___x_1804_;
v_isShared_1816_ = v_isSharedCheck_1821_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1804_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1821_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1817_; lean_object* v___x_1819_; 
v___x_1817_ = lean_apply_1(v_inst_1802_, v_a_1813_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1817_);
v___x_1819_ = v___x_1815_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__1(lean_object* v_serialize_x3f_1822_, uint8_t v_val_1823_, lean_object* v_inst_1824_, lean_object* v_r_1825_){
_start:
{
if (lean_obj_tag(v_serialize_x3f_1822_) == 1)
{
lean_object* v_val_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
lean_dec_ref(v_inst_1824_);
v_val_1826_ = lean_ctor_get(v_serialize_x3f_1822_, 0);
lean_inc(v_val_1826_);
lean_dec_ref_known(v_serialize_x3f_1822_, 1);
v___x_1827_ = lean_box(0);
v___x_1828_ = lean_apply_1(v_val_1826_, v_r_1825_);
v___x_1829_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1829_, 0, v___x_1827_);
lean_ctor_set(v___x_1829_, 1, v___x_1828_);
lean_ctor_set_uint8(v___x_1829_, sizeof(void*)*2, v_val_1823_);
return v___x_1829_;
}
else
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
lean_dec(v_serialize_x3f_1822_);
v___x_1830_ = lean_apply_1(v_inst_1824_, v_r_1825_);
lean_inc(v___x_1830_);
v___x_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
v___x_1832_ = l_Lean_Json_compress(v___x_1830_);
v___x_1833_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1833_, 0, v___x_1831_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
lean_ctor_set_uint8(v___x_1833_, sizeof(void*)*2, v_val_1823_);
return v___x_1833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__1___boxed(lean_object* v_serialize_x3f_1834_, lean_object* v_val_1835_, lean_object* v_inst_1836_, lean_object* v_r_1837_){
_start:
{
uint8_t v_val_1655__boxed_1838_; lean_object* v_res_1839_; 
v_val_1655__boxed_1838_ = lean_unbox(v_val_1835_);
v_res_1839_ = l_Lean_Server_registerLspRequestHandler___redArg___lam__1(v_serialize_x3f_1834_, v_val_1655__boxed_1838_, v_inst_1836_, v_r_1837_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__2(lean_object* v_inst_1840_, lean_object* v_handler_1841_, lean_object* v___f_1842_, lean_object* v_j_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_1840_, v_j_1843_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1848_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref_known(v___x_1846_, 1);
lean_inc_ref(v___y_1844_);
v___x_1848_ = lean_apply_3(v_handler_1841_, v_a_1847_, v___y_1844_, lean_box(0));
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1858_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1851_ = v___x_1848_;
v_isShared_1852_ = v_isSharedCheck_1858_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1848_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1858_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1853_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_1853_, 0, lean_box(0));
lean_closure_set(v___x_1853_, 1, lean_box(0));
lean_closure_set(v___x_1853_, 2, lean_box(0));
lean_closure_set(v___x_1853_, 3, v___f_1842_);
v___x_1854_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___x_1853_, v_a_1849_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v___x_1854_);
v___x_1856_ = v___x_1851_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec_ref(v___f_1842_);
v_a_1859_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1848_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1848_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
lean_dec_ref(v___f_1842_);
lean_dec_ref(v_handler_1841_);
v_a_1867_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1846_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1846_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__2___boxed(lean_object* v_inst_1875_, lean_object* v_handler_1876_, lean_object* v___f_1877_, lean_object* v_j_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_Server_registerLspRequestHandler___redArg___lam__2(v_inst_1875_, v_handler_1876_, v___f_1877_, v_j_1878_, v___y_1879_);
lean_dec_ref(v___y_1879_);
return v_res_1881_;
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3(void){
_start:
{
lean_object* v___x_1885_; lean_object* v___f_1886_; 
v___x_1885_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___f_1886_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1886_, 0, v___x_1885_);
return v___f_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg(lean_object* v_method_1888_, lean_object* v_inst_1889_, lean_object* v_inst_1890_, lean_object* v_inst_1891_, lean_object* v_handler_1892_, lean_object* v_serialize_x3f_1893_){
_start:
{
uint8_t v___x_1895_; 
v___x_1895_ = l_Lean_initializing();
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
lean_dec(v_serialize_x3f_1893_);
lean_dec_ref(v_handler_1892_);
lean_dec_ref(v_inst_1891_);
lean_dec_ref(v_inst_1890_);
lean_dec_ref(v_inst_1889_);
v___x_1896_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__0));
v___x_1897_ = lean_string_append(v___x_1896_, v_method_1888_);
lean_dec_ref(v_method_1888_);
v___x_1898_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__1));
v___x_1899_ = lean_string_append(v___x_1897_, v___x_1898_);
v___x_1900_ = lean_mk_io_user_error(v___x_1899_);
v___x_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
return v___x_1901_;
}
else
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___f_1905_; uint8_t v___x_1906_; 
v___x_1902_ = l_Lean_Server_requestHandlers;
v___x_1903_ = lean_st_ref_get(v___x_1902_);
v___x_1904_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___f_1905_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
lean_inc_ref(v_method_1888_);
v___x_1906_ = l_Lean_PersistentHashMap_contains___redArg(v___f_1905_, v___x_1904_, v___x_1903_, v_method_1888_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; lean_object* v___f_1908_; lean_object* v___x_1909_; lean_object* v___f_1910_; lean_object* v___f_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1907_ = lean_st_ref_take(v___x_1902_);
lean_inc_ref(v_inst_1889_);
v___f_1908_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1908_, 0, v_inst_1889_);
lean_closure_set(v___f_1908_, 1, v_inst_1890_);
v___x_1909_ = lean_box(v___x_1895_);
v___f_1910_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1910_, 0, v_serialize_x3f_1893_);
lean_closure_set(v___f_1910_, 1, v___x_1909_);
lean_closure_set(v___f_1910_, 2, v_inst_1891_);
v___f_1911_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1911_, 0, v_inst_1889_);
lean_closure_set(v___f_1911_, 1, v_handler_1892_);
lean_closure_set(v___f_1911_, 2, v___f_1910_);
v___x_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___f_1908_);
lean_ctor_set(v___x_1912_, 1, v___f_1911_);
v___x_1913_ = l_Lean_PersistentHashMap_insert___redArg(v___f_1905_, v___x_1904_, v___x_1907_, v_method_1888_, v___x_1912_);
v___x_1914_ = lean_st_ref_set(v___x_1902_, v___x_1913_);
v___x_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
return v___x_1915_;
}
else
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
lean_dec(v_serialize_x3f_1893_);
lean_dec_ref(v_handler_1892_);
lean_dec_ref(v_inst_1891_);
lean_dec_ref(v_inst_1890_);
lean_dec_ref(v_inst_1889_);
v___x_1916_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__0));
v___x_1917_ = lean_string_append(v___x_1916_, v_method_1888_);
lean_dec_ref(v_method_1888_);
v___x_1918_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__4));
v___x_1919_ = lean_string_append(v___x_1917_, v___x_1918_);
v___x_1920_ = lean_mk_io_user_error(v___x_1919_);
v___x_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
return v___x_1921_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___boxed(lean_object* v_method_1922_, lean_object* v_inst_1923_, lean_object* v_inst_1924_, lean_object* v_inst_1925_, lean_object* v_handler_1926_, lean_object* v_serialize_x3f_1927_, lean_object* v_a_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Lean_Server_registerLspRequestHandler___redArg(v_method_1922_, v_inst_1923_, v_inst_1924_, v_inst_1925_, v_handler_1926_, v_serialize_x3f_1927_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler(lean_object* v_method_1930_, lean_object* v_paramType_1931_, lean_object* v_inst_1932_, lean_object* v_inst_1933_, lean_object* v_respType_1934_, lean_object* v_inst_1935_, lean_object* v_handler_1936_, lean_object* v_serialize_x3f_1937_){
_start:
{
lean_object* v___x_1939_; 
v___x_1939_ = l_Lean_Server_registerLspRequestHandler___redArg(v_method_1930_, v_inst_1932_, v_inst_1933_, v_inst_1935_, v_handler_1936_, v_serialize_x3f_1937_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___boxed(lean_object* v_method_1940_, lean_object* v_paramType_1941_, lean_object* v_inst_1942_, lean_object* v_inst_1943_, lean_object* v_respType_1944_, lean_object* v_inst_1945_, lean_object* v_handler_1946_, lean_object* v_serialize_x3f_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_Server_registerLspRequestHandler(v_method_1940_, v_paramType_1941_, v_inst_1942_, v_inst_1943_, v_respType_1944_, v_inst_1945_, v_handler_1946_, v_serialize_x3f_1947_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1950_, lean_object* v_vals_1951_, lean_object* v_i_1952_, lean_object* v_k_1953_){
_start:
{
lean_object* v___x_1954_; uint8_t v___x_1955_; 
v___x_1954_ = lean_array_get_size(v_keys_1950_);
v___x_1955_ = lean_nat_dec_lt(v_i_1952_, v___x_1954_);
if (v___x_1955_ == 0)
{
lean_object* v___x_1956_; 
lean_dec(v_i_1952_);
v___x_1956_ = lean_box(0);
return v___x_1956_;
}
else
{
lean_object* v_k_x27_1957_; uint8_t v___x_1958_; 
v_k_x27_1957_ = lean_array_fget_borrowed(v_keys_1950_, v_i_1952_);
v___x_1958_ = lean_string_dec_eq(v_k_1953_, v_k_x27_1957_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = lean_unsigned_to_nat(1u);
v___x_1960_ = lean_nat_add(v_i_1952_, v___x_1959_);
lean_dec(v_i_1952_);
v_i_1952_ = v___x_1960_;
goto _start;
}
else
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = lean_array_fget_borrowed(v_vals_1951_, v_i_1952_);
lean_dec(v_i_1952_);
lean_inc(v___x_1962_);
v___x_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
return v___x_1963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1964_, lean_object* v_vals_1965_, lean_object* v_i_1966_, lean_object* v_k_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(v_keys_1964_, v_vals_1965_, v_i_1966_, v_k_1967_);
lean_dec_ref(v_k_1967_);
lean_dec_ref(v_vals_1965_);
lean_dec_ref(v_keys_1964_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(lean_object* v_x_1969_, size_t v_x_1970_, lean_object* v_x_1971_){
_start:
{
if (lean_obj_tag(v_x_1969_) == 0)
{
lean_object* v_es_1972_; lean_object* v___x_1973_; size_t v___x_1974_; size_t v___x_1975_; lean_object* v_j_1976_; lean_object* v___x_1977_; 
v_es_1972_ = lean_ctor_get(v_x_1969_, 0);
v___x_1973_ = lean_box(2);
v___x_1974_ = ((size_t)31ULL);
v___x_1975_ = lean_usize_land(v_x_1970_, v___x_1974_);
v_j_1976_ = lean_usize_to_nat(v___x_1975_);
v___x_1977_ = lean_array_get_borrowed(v___x_1973_, v_es_1972_, v_j_1976_);
lean_dec(v_j_1976_);
switch(lean_obj_tag(v___x_1977_))
{
case 0:
{
lean_object* v_key_1978_; lean_object* v_val_1979_; uint8_t v___x_1980_; 
v_key_1978_ = lean_ctor_get(v___x_1977_, 0);
v_val_1979_ = lean_ctor_get(v___x_1977_, 1);
v___x_1980_ = lean_string_dec_eq(v_x_1971_, v_key_1978_);
if (v___x_1980_ == 0)
{
lean_object* v___x_1981_; 
v___x_1981_ = lean_box(0);
return v___x_1981_;
}
else
{
lean_object* v___x_1982_; 
lean_inc(v_val_1979_);
v___x_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1982_, 0, v_val_1979_);
return v___x_1982_;
}
}
case 1:
{
lean_object* v_node_1983_; size_t v___x_1984_; size_t v___x_1985_; 
v_node_1983_ = lean_ctor_get(v___x_1977_, 0);
v___x_1984_ = ((size_t)5ULL);
v___x_1985_ = lean_usize_shift_right(v_x_1970_, v___x_1984_);
v_x_1969_ = v_node_1983_;
v_x_1970_ = v___x_1985_;
goto _start;
}
default: 
{
lean_object* v___x_1987_; 
v___x_1987_ = lean_box(0);
return v___x_1987_;
}
}
}
else
{
lean_object* v_ks_1988_; lean_object* v_vs_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v_ks_1988_ = lean_ctor_get(v_x_1969_, 0);
v_vs_1989_ = lean_ctor_get(v_x_1969_, 1);
v___x_1990_ = lean_unsigned_to_nat(0u);
v___x_1991_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(v_ks_1988_, v_vs_1989_, v___x_1990_, v_x_1971_);
return v___x_1991_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___boxed(lean_object* v_x_1992_, lean_object* v_x_1993_, lean_object* v_x_1994_){
_start:
{
size_t v_x_263__boxed_1995_; lean_object* v_res_1996_; 
v_x_263__boxed_1995_ = lean_unbox_usize(v_x_1993_);
lean_dec(v_x_1993_);
v_res_1996_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_1992_, v_x_263__boxed_1995_, v_x_1994_);
lean_dec_ref(v_x_1994_);
lean_dec_ref(v_x_1992_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(lean_object* v_x_1997_, lean_object* v_x_1998_){
_start:
{
uint64_t v___x_1999_; size_t v___x_2000_; lean_object* v___x_2001_; 
v___x_1999_ = lean_string_hash(v_x_1998_);
v___x_2000_ = lean_uint64_to_usize(v___x_1999_);
v___x_2001_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_1997_, v___x_2000_, v_x_1998_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg___boxed(lean_object* v_x_2002_, lean_object* v_x_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v_x_2002_, v_x_2003_);
lean_dec_ref(v_x_2003_);
lean_dec_ref(v_x_2002_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupLspRequestHandler(lean_object* v_method_2005_){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2007_ = l_Lean_Server_requestHandlers;
v___x_2008_ = lean_st_ref_get(v___x_2007_);
v___x_2009_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v___x_2008_, v_method_2005_);
lean_dec(v___x_2008_);
v___x_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupLspRequestHandler___boxed(lean_object* v_method_2011_, lean_object* v_a_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Lean_Server_lookupLspRequestHandler(v_method_2011_);
lean_dec_ref(v_method_2011_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0(lean_object* v_00_u03b2_2014_, lean_object* v_x_2015_, lean_object* v_x_2016_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v_x_2015_, v_x_2016_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___boxed(lean_object* v_00_u03b2_2018_, lean_object* v_x_2019_, lean_object* v_x_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0(v_00_u03b2_2018_, v_x_2019_, v_x_2020_);
lean_dec_ref(v_x_2020_);
lean_dec_ref(v_x_2019_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0(lean_object* v_00_u03b2_2022_, lean_object* v_x_2023_, size_t v_x_2024_, lean_object* v_x_2025_){
_start:
{
lean_object* v___x_2026_; 
v___x_2026_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_2023_, v_x_2024_, v_x_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2027_, lean_object* v_x_2028_, lean_object* v_x_2029_, lean_object* v_x_2030_){
_start:
{
size_t v_x_341__boxed_2031_; lean_object* v_res_2032_; 
v_x_341__boxed_2031_ = lean_unbox_usize(v_x_2029_);
lean_dec(v_x_2029_);
v_res_2032_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0(v_00_u03b2_2027_, v_x_2028_, v_x_341__boxed_2031_, v_x_2030_);
lean_dec_ref(v_x_2030_);
lean_dec_ref(v_x_2028_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2033_, lean_object* v_keys_2034_, lean_object* v_vals_2035_, lean_object* v_heq_2036_, lean_object* v_i_2037_, lean_object* v_k_2038_){
_start:
{
lean_object* v___x_2039_; 
v___x_2039_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(v_keys_2034_, v_vals_2035_, v_i_2037_, v_k_2038_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2040_, lean_object* v_keys_2041_, lean_object* v_vals_2042_, lean_object* v_heq_2043_, lean_object* v_i_2044_, lean_object* v_k_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1(v_00_u03b2_2040_, v_keys_2041_, v_vals_2042_, v_heq_2043_, v_i_2044_, v_k_2045_);
lean_dec_ref(v_k_2045_);
lean_dec_ref(v_vals_2042_);
lean_dec_ref(v_keys_2041_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__0(lean_object* v_inst_2050_, lean_object* v_method_2051_, lean_object* v_x_2052_){
_start:
{
lean_object* v_response_2054_; 
if (lean_obj_tag(v_x_2052_) == 0)
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec_ref(v_inst_2050_);
v_a_2078_ = lean_ctor_get(v_x_2052_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v_x_2052_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v_x_2052_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v_x_2052_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
else
{
lean_object* v_a_2086_; lean_object* v_response_x3f_2087_; 
v_a_2086_ = lean_ctor_get(v_x_2052_, 0);
lean_inc(v_a_2086_);
lean_dec_ref_known(v_x_2052_, 1);
v_response_x3f_2087_ = lean_ctor_get(v_a_2086_, 0);
if (lean_obj_tag(v_response_x3f_2087_) == 0)
{
lean_object* v_serialized_2088_; lean_object* v___x_2089_; 
v_serialized_2088_ = lean_ctor_get(v_a_2086_, 1);
lean_inc_ref(v_serialized_2088_);
lean_dec(v_a_2086_);
v___x_2089_ = l_Lean_Json_parse(v_serialized_2088_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2103_; 
lean_dec_ref(v_inst_2050_);
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2092_ = v___x_2089_;
v_isShared_2093_ = v_isSharedCheck_2103_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2089_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2103_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2094_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__2));
v___x_2095_ = lean_string_append(v___x_2094_, v_method_2051_);
v___x_2096_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1));
v___x_2097_ = lean_string_append(v___x_2095_, v___x_2096_);
v___x_2098_ = lean_string_append(v___x_2097_, v_a_2090_);
lean_dec(v_a_2090_);
v___x_2099_ = l_Lean_Server_RequestError_internalError(v___x_2098_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v___x_2099_);
v___x_2101_ = v___x_2092_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
else
{
lean_object* v_a_2104_; 
v_a_2104_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2104_);
lean_dec_ref_known(v___x_2089_, 1);
v_response_2054_ = v_a_2104_;
goto v___jp_2053_;
}
}
else
{
lean_object* v_val_2105_; 
lean_inc_ref(v_response_x3f_2087_);
lean_dec(v_a_2086_);
v_val_2105_ = lean_ctor_get(v_response_x3f_2087_, 0);
lean_inc(v_val_2105_);
lean_dec_ref_known(v_response_x3f_2087_, 1);
v_response_2054_ = v_val_2105_;
goto v___jp_2053_;
}
}
v___jp_2053_:
{
lean_object* v___x_2055_; 
v___x_2055_ = lean_apply_1(v_inst_2050_, v_response_2054_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2069_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2069_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2069_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2067_; 
v___x_2060_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__0));
v___x_2061_ = lean_string_append(v___x_2060_, v_method_2051_);
v___x_2062_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1));
v___x_2063_ = lean_string_append(v___x_2061_, v___x_2062_);
v___x_2064_ = lean_string_append(v___x_2063_, v_a_2056_);
lean_dec(v_a_2056_);
v___x_2065_ = l_Lean_Server_RequestError_internalError(v___x_2064_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v___x_2065_);
v___x_2067_ = v___x_2058_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2065_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
else
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
v_a_2070_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_2055_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2055_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__0___boxed(lean_object* v_inst_2106_, lean_object* v_method_2107_, lean_object* v_x_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__0(v_inst_2106_, v_method_2107_, v_x_2108_);
lean_dec_ref(v_method_2107_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__1(lean_object* v_inst_2110_, uint8_t v_val_2111_, lean_object* v_r_2112_){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2113_ = lean_apply_1(v_inst_2110_, v_r_2112_);
lean_inc(v___x_2113_);
v___x_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
v___x_2115_ = l_Lean_Json_compress(v___x_2113_);
v___x_2116_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2116_, 0, v___x_2114_);
lean_ctor_set(v___x_2116_, 1, v___x_2115_);
lean_ctor_set_uint8(v___x_2116_, sizeof(void*)*2, v_val_2111_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__1___boxed(lean_object* v_inst_2117_, lean_object* v_val_2118_, lean_object* v_r_2119_){
_start:
{
uint8_t v_val_2493__boxed_2120_; lean_object* v_res_2121_; 
v_val_2493__boxed_2120_ = lean_unbox(v_val_2118_);
v_res_2121_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__1(v_inst_2117_, v_val_2493__boxed_2120_, v_r_2119_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__2(lean_object* v_handle_2122_, lean_object* v_inst_2123_, lean_object* v___f_2124_, lean_object* v_handler_2125_, lean_object* v___f_2126_, lean_object* v_j_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v___x_2130_; 
lean_inc_ref(v___y_2128_);
lean_inc(v_j_2127_);
v___x_2130_ = lean_apply_3(v_handle_2122_, v_j_2127_, v___y_2128_, lean_box(0));
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2132_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v___x_2132_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_2123_, v_j_2127_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2132_, 1);
v___x_2134_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2124_, v_a_2131_);
lean_inc_ref(v___y_2128_);
v___x_2135_ = lean_apply_4(v_handler_2125_, v_a_2133_, v___x_2134_, v___y_2128_, lean_box(0));
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2145_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2145_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2145_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2143_; 
v___x_2140_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_2140_, 0, lean_box(0));
lean_closure_set(v___x_2140_, 1, lean_box(0));
lean_closure_set(v___x_2140_, 2, lean_box(0));
lean_closure_set(v___x_2140_, 3, v___f_2126_);
v___x_2141_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___x_2140_, v_a_2136_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2141_);
v___x_2143_ = v___x_2138_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec_ref(v___f_2126_);
v_a_2146_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2135_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2135_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
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
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec(v_a_2131_);
lean_dec_ref(v___f_2126_);
lean_dec_ref(v_handler_2125_);
lean_dec_ref(v___f_2124_);
v_a_2154_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2132_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2132_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
else
{
lean_dec(v_j_2127_);
lean_dec_ref(v___f_2126_);
lean_dec_ref(v_handler_2125_);
lean_dec_ref(v___f_2124_);
lean_dec_ref(v_inst_2123_);
return v___x_2130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__2___boxed(lean_object* v_handle_2162_, lean_object* v_inst_2163_, lean_object* v___f_2164_, lean_object* v_handler_2165_, lean_object* v___f_2166_, lean_object* v_j_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__2(v_handle_2162_, v_inst_2163_, v___f_2164_, v_handler_2165_, v___f_2166_, v_j_2167_, v___y_2168_);
lean_dec_ref(v___y_2168_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg(lean_object* v_method_2173_, lean_object* v_inst_2174_, lean_object* v_inst_2175_, lean_object* v_inst_2176_, lean_object* v_handler_2177_){
_start:
{
uint8_t v___x_2179_; 
v___x_2179_ = l_Lean_initializing();
if (v___x_2179_ == 0)
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
lean_dec_ref(v_handler_2177_);
lean_dec_ref(v_inst_2176_);
lean_dec_ref(v_inst_2175_);
lean_dec_ref(v_inst_2174_);
v___x_2180_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__0));
v___x_2181_ = lean_string_append(v___x_2180_, v_method_2173_);
lean_dec_ref(v_method_2173_);
v___x_2182_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__1));
v___x_2183_ = lean_string_append(v___x_2181_, v___x_2182_);
v___x_2184_ = lean_mk_io_user_error(v___x_2183_);
v___x_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
return v___x_2185_;
}
else
{
lean_object* v___x_2186_; lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2222_; 
v___x_2186_ = l_Lean_Server_lookupLspRequestHandler(v_method_2173_);
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2189_ = v___x_2186_;
v_isShared_2190_ = v_isSharedCheck_2222_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2186_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2222_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
if (lean_obj_tag(v_a_2187_) == 1)
{
lean_object* v_val_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v_fileSource_2194_; lean_object* v_handle_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2213_; 
v_val_2191_ = lean_ctor_get(v_a_2187_, 0);
lean_inc(v_val_2191_);
lean_dec_ref_known(v_a_2187_, 1);
v___x_2192_ = l_Lean_Server_requestHandlers;
v___x_2193_ = lean_st_ref_take(v___x_2192_);
v_fileSource_2194_ = lean_ctor_get(v_val_2191_, 0);
v_handle_2195_ = lean_ctor_get(v_val_2191_, 1);
v_isSharedCheck_2213_ = !lean_is_exclusive(v_val_2191_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2197_ = v_val_2191_;
v_isShared_2198_ = v_isSharedCheck_2213_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_handle_2195_);
lean_inc(v_fileSource_2194_);
lean_dec(v_val_2191_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2213_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___f_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___f_2202_; lean_object* v___f_2203_; lean_object* v___f_2204_; lean_object* v___x_2206_; 
lean_inc_ref(v_method_2173_);
v___f_2199_ = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2199_, 0, v_inst_2175_);
lean_closure_set(v___f_2199_, 1, v_method_2173_);
v___x_2200_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___x_2201_ = lean_box(v___x_2179_);
v___f_2202_ = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2202_, 0, v_inst_2176_);
lean_closure_set(v___f_2202_, 1, v___x_2201_);
v___f_2203_ = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2203_, 0, v_handle_2195_);
lean_closure_set(v___f_2203_, 1, v_inst_2174_);
lean_closure_set(v___f_2203_, 2, v___f_2199_);
lean_closure_set(v___f_2203_, 3, v_handler_2177_);
lean_closure_set(v___f_2203_, 4, v___f_2202_);
v___f_2204_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 1, v___f_2203_);
v___x_2206_ = v___x_2197_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_fileSource_2194_);
lean_ctor_set(v_reuseFailAlloc_2212_, 1, v___f_2203_);
v___x_2206_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2207_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2204_, v___x_2200_, v___x_2193_, v_method_2173_, v___x_2206_);
v___x_2208_ = lean_st_ref_set(v___x_2192_, v___x_2207_);
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 0, v___x_2208_);
v___x_2210_ = v___x_2189_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
else
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2220_; 
lean_dec(v_a_2187_);
lean_dec_ref(v_handler_2177_);
lean_dec_ref(v_inst_2176_);
lean_dec_ref(v_inst_2175_);
lean_dec_ref(v_inst_2174_);
v___x_2214_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__0));
v___x_2215_ = lean_string_append(v___x_2214_, v_method_2173_);
lean_dec_ref(v_method_2173_);
v___x_2216_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__1));
v___x_2217_ = lean_string_append(v___x_2215_, v___x_2216_);
v___x_2218_ = lean_mk_io_user_error(v___x_2217_);
if (v_isShared_2190_ == 0)
{
lean_ctor_set_tag(v___x_2189_, 1);
lean_ctor_set(v___x_2189_, 0, v___x_2218_);
v___x_2220_ = v___x_2189_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2218_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___boxed(lean_object* v_method_2223_, lean_object* v_inst_2224_, lean_object* v_inst_2225_, lean_object* v_inst_2226_, lean_object* v_handler_2227_, lean_object* v_a_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_Lean_Server_chainLspRequestHandler___redArg(v_method_2223_, v_inst_2224_, v_inst_2225_, v_inst_2226_, v_handler_2227_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler(lean_object* v_method_2230_, lean_object* v_paramType_2231_, lean_object* v_inst_2232_, lean_object* v_respType_2233_, lean_object* v_inst_2234_, lean_object* v_inst_2235_, lean_object* v_handler_2236_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l_Lean_Server_chainLspRequestHandler___redArg(v_method_2230_, v_inst_2232_, v_inst_2234_, v_inst_2235_, v_handler_2236_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___boxed(lean_object* v_method_2239_, lean_object* v_paramType_2240_, lean_object* v_inst_2241_, lean_object* v_respType_2242_, lean_object* v_inst_2243_, lean_object* v_inst_2244_, lean_object* v_handler_2245_, lean_object* v_a_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_Server_chainLspRequestHandler(v_method_2239_, v_paramType_2240_, v_inst_2241_, v_respType_2242_, v_inst_2243_, v_inst_2244_, v_handler_2245_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorIdx(lean_object* v_x_2248_){
_start:
{
if (lean_obj_tag(v_x_2248_) == 0)
{
lean_object* v___x_2249_; 
v___x_2249_ = lean_unsigned_to_nat(0u);
return v___x_2249_;
}
else
{
lean_object* v___x_2250_; 
v___x_2250_ = lean_unsigned_to_nat(1u);
return v___x_2250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorIdx___boxed(lean_object* v_x_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_Server_RequestHandlerCompleteness_ctorIdx(v_x_2251_);
lean_dec(v_x_2251_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(lean_object* v_t_2253_, lean_object* v_k_2254_){
_start:
{
if (lean_obj_tag(v_t_2253_) == 0)
{
return v_k_2254_;
}
else
{
lean_object* v_refreshMethod_2255_; lean_object* v_refreshIntervalMs_2256_; lean_object* v___x_2257_; 
v_refreshMethod_2255_ = lean_ctor_get(v_t_2253_, 0);
lean_inc_ref(v_refreshMethod_2255_);
v_refreshIntervalMs_2256_ = lean_ctor_get(v_t_2253_, 1);
lean_inc(v_refreshIntervalMs_2256_);
lean_dec_ref_known(v_t_2253_, 2);
v___x_2257_ = lean_apply_2(v_k_2254_, v_refreshMethod_2255_, v_refreshIntervalMs_2256_);
return v___x_2257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim(lean_object* v_motive_2258_, lean_object* v_ctorIdx_2259_, lean_object* v_t_2260_, lean_object* v_h_2261_, lean_object* v_k_2262_){
_start:
{
lean_object* v___x_2263_; 
v___x_2263_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_2260_, v_k_2262_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim___boxed(lean_object* v_motive_2264_, lean_object* v_ctorIdx_2265_, lean_object* v_t_2266_, lean_object* v_h_2267_, lean_object* v_k_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim(v_motive_2264_, v_ctorIdx_2265_, v_t_2266_, v_h_2267_, v_k_2268_);
lean_dec(v_ctorIdx_2265_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_complete_elim___redArg(lean_object* v_t_2270_, lean_object* v_complete_2271_){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_2270_, v_complete_2271_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_complete_elim(lean_object* v_motive_2273_, lean_object* v_t_2274_, lean_object* v_h_2275_, lean_object* v_complete_2276_){
_start:
{
lean_object* v___x_2277_; 
v___x_2277_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_2274_, v_complete_2276_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_partial_elim___redArg(lean_object* v_t_2278_, lean_object* v_partial_2279_){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_2278_, v_partial_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_partial_elim(lean_object* v_motive_2281_, lean_object* v_t_2282_, lean_object* v_h_2283_, lean_object* v_partial_2284_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_2282_, v_partial_2284_);
return v___x_2285_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2286_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2287_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_);
v___x_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2290_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_);
v___x_2291_ = lean_st_mk_ref(v___x_2290_);
v___x_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2____boxed(lean_object* v_a_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_();
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(lean_object* v_method_2296_, lean_object* v_state_2297_, lean_object* v_inst_2298_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_state_2297_, v_inst_2298_);
if (lean_obj_tag(v___x_2300_) == 1)
{
lean_object* v_val_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2308_; 
v_val_2301_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2303_ = v___x_2300_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_val_2301_);
lean_dec(v___x_2300_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2304_ == 0)
{
lean_ctor_set_tag(v___x_2303_, 0);
v___x_2306_ = v___x_2303_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_val_2301_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
else
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
lean_dec(v___x_2300_);
v___x_2309_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0));
v___x_2310_ = lean_string_append(v___x_2309_, v_method_2296_);
v___x_2311_ = l_Lean_Server_RequestError_internalError(v___x_2310_);
v___x_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
return v___x_2312_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___boxed(lean_object* v_method_2313_, lean_object* v_state_2314_, lean_object* v_inst_2315_, lean_object* v_a_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_2313_, v_state_2314_, v_inst_2315_);
lean_dec(v_inst_2315_);
lean_dec(v_state_2314_);
lean_dec_ref(v_method_2313_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(lean_object* v_method_2318_, lean_object* v_state_2319_, lean_object* v_stateType_2320_, lean_object* v_inst_2321_, lean_object* v_a_2322_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_2318_, v_state_2319_, v_inst_2321_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___boxed(lean_object* v_method_2325_, lean_object* v_state_2326_, lean_object* v_stateType_2327_, lean_object* v_inst_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_2325_, v_state_2326_, v_stateType_2327_, v_inst_2328_, v_a_2329_);
lean_dec_ref(v_a_2329_);
lean_dec(v_inst_2328_);
lean_dec(v_state_2326_);
lean_dec_ref(v_method_2325_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(lean_object* v_method_2332_, lean_object* v_state_2333_, lean_object* v_inst_2334_){
_start:
{
lean_object* v___x_2336_; 
v___x_2336_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_state_2333_, v_inst_2334_);
if (lean_obj_tag(v___x_2336_) == 1)
{
lean_object* v_val_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
v_val_2337_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2336_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_val_2337_);
lean_dec(v___x_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
lean_ctor_set_tag(v___x_2339_, 0);
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_val_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
else
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
lean_dec(v___x_2336_);
v___x_2345_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0));
v___x_2346_ = lean_string_append(v___x_2345_, v_method_2332_);
v___x_2347_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2346_);
v___x_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2347_);
return v___x_2348_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg___boxed(lean_object* v_method_2349_, lean_object* v_state_2350_, lean_object* v_inst_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(v_method_2349_, v_state_2350_, v_inst_2351_);
lean_dec(v_inst_2351_);
lean_dec(v_state_2350_);
lean_dec_ref(v_method_2349_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21(lean_object* v_method_2354_, lean_object* v_state_2355_, lean_object* v_stateType_2356_, lean_object* v_inst_2357_){
_start:
{
lean_object* v___x_2359_; 
v___x_2359_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(v_method_2354_, v_state_2355_, v_inst_2357_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___boxed(lean_object* v_method_2360_, lean_object* v_state_2361_, lean_object* v_stateType_2362_, lean_object* v_inst_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21(v_method_2360_, v_state_2361_, v_stateType_2362_, v_inst_2363_);
lean_dec(v_inst_2363_);
lean_dec(v_state_2361_);
lean_dec_ref(v_method_2360_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1(lean_object* v_inst_2366_, lean_object* v_method_2367_, lean_object* v_inst_2368_, lean_object* v_handler_2369_, lean_object* v_inst_2370_, lean_object* v_param_2371_, lean_object* v_state_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v___x_2375_; 
v___x_2375_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_2366_, v_param_2371_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v_a_2376_; lean_object* v___x_2377_; 
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_a_2376_);
lean_dec_ref_known(v___x_2375_, 1);
v___x_2377_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_2367_, v_state_2372_, v_inst_2368_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v_a_2378_; lean_object* v___x_2379_; 
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
lean_inc(v_a_2378_);
lean_dec_ref_known(v___x_2377_, 1);
lean_inc_ref(v___y_2373_);
v___x_2379_ = lean_apply_4(v_handler_2369_, v_a_2376_, v_a_2378_, v___y_2373_, lean_box(0));
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2403_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2382_ = v___x_2379_;
v_isShared_2383_ = v_isSharedCheck_2403_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2379_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2403_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v_fst_2384_; lean_object* v_snd_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2402_; 
v_fst_2384_ = lean_ctor_get(v_a_2380_, 0);
v_snd_2385_ = lean_ctor_get(v_a_2380_, 1);
v_isSharedCheck_2402_ = !lean_is_exclusive(v_a_2380_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2387_ = v_a_2380_;
v_isShared_2388_ = v_isSharedCheck_2402_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_snd_2385_);
lean_inc(v_fst_2384_);
lean_dec(v_a_2380_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2402_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v_response_2389_; uint8_t v_isComplete_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2396_; 
v_response_2389_ = lean_ctor_get(v_fst_2384_, 0);
lean_inc(v_response_2389_);
v_isComplete_2390_ = lean_ctor_get_uint8(v_fst_2384_, sizeof(void*)*1);
lean_dec(v_fst_2384_);
v___x_2391_ = lean_apply_1(v_inst_2370_, v_response_2389_);
lean_inc(v___x_2391_);
v___x_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2391_);
v___x_2393_ = l_Lean_Json_compress(v___x_2391_);
v___x_2394_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2394_, 0, v___x_2392_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
lean_ctor_set_uint8(v___x_2394_, sizeof(void*)*2, v_isComplete_2390_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 0, v_inst_2368_);
v___x_2396_ = v___x_2387_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_inst_2368_);
lean_ctor_set(v_reuseFailAlloc_2401_, 1, v_snd_2385_);
v___x_2396_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
lean_object* v___x_2397_; lean_object* v___x_2399_; 
v___x_2397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2394_);
lean_ctor_set(v___x_2397_, 1, v___x_2396_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 0, v___x_2397_);
v___x_2399_ = v___x_2382_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v___x_2397_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
lean_dec_ref(v_inst_2370_);
lean_dec(v_inst_2368_);
v_a_2404_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2379_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2379_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_dec(v_a_2376_);
lean_dec_ref(v_inst_2370_);
lean_dec_ref(v_handler_2369_);
lean_dec(v_inst_2368_);
v_a_2412_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2377_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2377_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
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
else
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2427_; 
lean_dec_ref(v_inst_2370_);
lean_dec_ref(v_handler_2369_);
lean_dec(v_inst_2368_);
v_a_2420_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2422_ = v___x_2375_;
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2375_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2425_; 
if (v_isShared_2423_ == 0)
{
v___x_2425_ = v___x_2422_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_a_2420_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1___boxed(lean_object* v_inst_2428_, lean_object* v_method_2429_, lean_object* v_inst_2430_, lean_object* v_handler_2431_, lean_object* v_inst_2432_, lean_object* v_param_2433_, lean_object* v_state_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1(v_inst_2428_, v_method_2429_, v_inst_2430_, v_handler_2431_, v_inst_2432_, v_param_2433_, v_state_2434_, v___y_2435_);
lean_dec_ref(v___y_2435_);
lean_dec(v_state_2434_);
lean_dec_ref(v_method_2429_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0(lean_object* v_method_2438_, lean_object* v_inst_2439_, lean_object* v_onDidChange_2440_, lean_object* v_param_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v___x_2445_; 
v___x_2445_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_2438_, v___y_2442_, v_inst_2439_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v___x_2447_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_a_2446_);
lean_dec_ref_known(v___x_2445_, 1);
lean_inc_ref(v___y_2443_);
v___x_2447_ = lean_apply_4(v_onDidChange_2440_, v_param_2441_, v_a_2446_, v___y_2443_, lean_box(0));
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2466_; 
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2450_ = v___x_2447_;
v_isShared_2451_ = v_isSharedCheck_2466_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2447_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2466_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v_snd_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2464_; 
v_snd_2452_ = lean_ctor_get(v_a_2448_, 1);
v_isSharedCheck_2464_ = !lean_is_exclusive(v_a_2448_);
if (v_isSharedCheck_2464_ == 0)
{
lean_object* v_unused_2465_; 
v_unused_2465_ = lean_ctor_get(v_a_2448_, 0);
lean_dec(v_unused_2465_);
v___x_2454_ = v_a_2448_;
v_isShared_2455_ = v_isSharedCheck_2464_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_snd_2452_);
lean_dec(v_a_2448_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2464_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 0, v_inst_2439_);
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_inst_2439_);
lean_ctor_set(v_reuseFailAlloc_2463_, 1, v_snd_2452_);
v___x_2457_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2461_; 
v___x_2458_ = lean_box(0);
v___x_2459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2458_);
lean_ctor_set(v___x_2459_, 1, v___x_2457_);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 0, v___x_2459_);
v___x_2461_ = v___x_2450_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2459_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec(v_inst_2439_);
v_a_2467_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2447_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2447_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
else
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
lean_dec_ref(v_param_2441_);
lean_dec_ref(v_onDidChange_2440_);
lean_dec(v_inst_2439_);
v_a_2475_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v___x_2445_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2445_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2475_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object* v_method_2483_, lean_object* v_inst_2484_, lean_object* v_onDidChange_2485_, lean_object* v_param_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0(v_method_2483_, v_inst_2484_, v_onDidChange_2485_, v_param_2486_, v___y_2487_, v___y_2488_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v_method_2483_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2(lean_object* v___x_2491_, lean_object* v_x_2492_){
_start:
{
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2___boxed(lean_object* v___x_2493_, lean_object* v_x_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2(v___x_2493_, v_x_2494_);
lean_dec_ref(v_x_2494_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3(lean_object* v___x_2496_, lean_object* v_x_2497_){
_start:
{
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3___boxed(lean_object* v___x_2498_, lean_object* v_x_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3(v___x_2498_, v_x_2499_);
lean_dec_ref(v_x_2499_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4(lean_object* v_val_2501_, lean_object* v___f_2502_, lean_object* v_param_2503_, lean_object* v_x_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = lean_st_ref_get(v_val_2501_);
lean_inc_ref(v___y_2505_);
v___x_2508_ = lean_apply_4(v___f_2502_, v_param_2503_, v___x_2507_, v___y_2505_, lean_box(0));
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2519_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2511_ = v___x_2508_;
v_isShared_2512_ = v_isSharedCheck_2519_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2519_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v_fst_2513_; lean_object* v_snd_2514_; lean_object* v___x_2515_; lean_object* v___x_2517_; 
v_fst_2513_ = lean_ctor_get(v_a_2509_, 0);
lean_inc(v_fst_2513_);
v_snd_2514_ = lean_ctor_get(v_a_2509_, 1);
lean_inc(v_snd_2514_);
lean_dec(v_a_2509_);
v___x_2515_ = lean_st_ref_set(v_val_2501_, v_snd_2514_);
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 0, v_fst_2513_);
v___x_2517_ = v___x_2511_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_fst_2513_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
v_a_2520_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2508_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2508_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4___boxed(lean_object* v_val_2528_, lean_object* v___f_2529_, lean_object* v_param_2530_, lean_object* v_x_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4(v_val_2528_, v___f_2529_, v_param_2530_, v_x_2531_, v___y_2532_);
lean_dec_ref(v___y_2532_);
lean_dec(v_val_2528_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5(lean_object* v___f_2535_, lean_object* v___f_2536_, lean_object* v_lastTask_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v___x_2541_; lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2551_; 
v___x_2541_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_lastTask_2537_, v___f_2535_, v___y_2539_);
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2544_ = v___x_2541_;
v_isShared_2545_ = v_isSharedCheck_2551_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2541_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2551_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2549_; 
lean_inc(v_a_2542_);
v___x_2546_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2536_, v_a_2542_);
v___x_2547_ = lean_st_ref_set(v___y_2538_, v___x_2546_);
if (v_isShared_2545_ == 0)
{
v___x_2549_ = v___x_2544_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2542_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5___boxed(lean_object* v___f_2552_, lean_object* v___f_2553_, lean_object* v_lastTask_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5(v___f_2552_, v___f_2553_, v_lastTask_2554_, v___y_2555_, v___y_2556_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6(lean_object* v_val_2559_, lean_object* v___f_2560_, lean_object* v___f_2561_, lean_object* v___f_2562_, lean_object* v___x_2563_, lean_object* v___f_2564_, lean_object* v___f_2565_, lean_object* v_val_2566_, lean_object* v_param_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v___f_2570_; lean_object* v___f_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_6446__overap_2574_; lean_object* v___x_2575_; 
v___f_2570_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2570_, 0, v_val_2559_);
lean_closure_set(v___f_2570_, 1, v___f_2560_);
lean_closure_set(v___f_2570_, 2, v_param_2567_);
v___f_2571_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5___boxed), 6, 2);
lean_closure_set(v___f_2571_, 0, v___f_2570_);
lean_closure_set(v___f_2571_, 1, v___f_2561_);
v___x_2572_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_2572_, 0, lean_box(0));
lean_closure_set(v___x_2572_, 1, lean_box(0));
lean_closure_set(v___x_2572_, 2, lean_box(0));
lean_closure_set(v___x_2572_, 3, v___f_2562_);
lean_inc_ref(v___x_2563_);
v___x_2573_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2573_, 0, lean_box(0));
lean_closure_set(v___x_2573_, 1, lean_box(0));
lean_closure_set(v___x_2573_, 2, v___x_2563_);
lean_closure_set(v___x_2573_, 3, lean_box(0));
lean_closure_set(v___x_2573_, 4, lean_box(0));
lean_closure_set(v___x_2573_, 5, v___x_2572_);
lean_closure_set(v___x_2573_, 6, v___f_2571_);
v___x_6446__overap_2574_ = l_Std_Mutex_atomically___redArg(v___x_2563_, v___f_2564_, v___f_2565_, v_val_2566_, v___x_2573_);
lean_inc_ref(v___y_2568_);
v___x_2575_ = lean_apply_2(v___x_6446__overap_2574_, v___y_2568_, lean_box(0));
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6___boxed(lean_object* v_val_2576_, lean_object* v___f_2577_, lean_object* v___f_2578_, lean_object* v___f_2579_, lean_object* v___x_2580_, lean_object* v___f_2581_, lean_object* v___f_2582_, lean_object* v_val_2583_, lean_object* v_param_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6(v_val_2576_, v___f_2577_, v___f_2578_, v___f_2579_, v___x_2580_, v___f_2581_, v___f_2582_, v_val_2583_, v_param_2584_, v___y_2585_);
lean_dec_ref(v___y_2585_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7(lean_object* v_val_2588_, lean_object* v___f_2589_, lean_object* v_param_2590_, lean_object* v_x_2591_, lean_object* v___y_2592_){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2594_ = lean_st_ref_get(v_val_2588_);
lean_inc_ref(v___y_2592_);
v___x_2595_ = lean_apply_4(v___f_2589_, v_param_2590_, v___x_2594_, v___y_2592_, lean_box(0));
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2605_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2598_ = v___x_2595_;
v_isShared_2599_ = v_isSharedCheck_2605_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2595_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2605_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v_snd_2600_; lean_object* v___x_2601_; lean_object* v___x_2603_; 
v_snd_2600_ = lean_ctor_get(v_a_2596_, 1);
lean_inc(v_snd_2600_);
lean_dec(v_a_2596_);
v___x_2601_ = lean_st_ref_set(v_val_2588_, v_snd_2600_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v___x_2601_);
v___x_2603_ = v___x_2598_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2601_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
v_a_2606_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2595_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2595_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7___boxed(lean_object* v_val_2614_, lean_object* v___f_2615_, lean_object* v_param_2616_, lean_object* v_x_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7(v_val_2614_, v___f_2615_, v_param_2616_, v_x_2617_, v___y_2618_);
lean_dec_ref(v___y_2618_);
lean_dec(v_val_2614_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8(lean_object* v___f_2621_, lean_object* v___f_2622_, lean_object* v_lastTask_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
lean_object* v___x_2627_; lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2637_; 
v___x_2627_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_lastTask_2623_, v___f_2621_, v___y_2625_);
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2630_ = v___x_2627_;
v_isShared_2631_ = v_isSharedCheck_2637_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2627_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2637_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2635_; 
v___x_2632_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2622_, v_a_2628_);
v___x_2633_ = lean_st_ref_set(v___y_2624_, v___x_2632_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 0, v___x_2633_);
v___x_2635_ = v___x_2630_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2633_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8___boxed(lean_object* v___f_2638_, lean_object* v___f_2639_, lean_object* v_lastTask_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
lean_object* v_res_2644_; 
v_res_2644_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8(v___f_2638_, v___f_2639_, v_lastTask_2640_, v___y_2641_, v___y_2642_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9(lean_object* v_val_2645_, lean_object* v___f_2646_, lean_object* v___f_2647_, lean_object* v___f_2648_, lean_object* v___x_2649_, lean_object* v___f_2650_, lean_object* v___f_2651_, lean_object* v_val_2652_, lean_object* v_param_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v___f_2656_; lean_object* v___f_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_6497__overap_2660_; lean_object* v___x_2661_; 
v___f_2656_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7___boxed), 6, 3);
lean_closure_set(v___f_2656_, 0, v_val_2645_);
lean_closure_set(v___f_2656_, 1, v___f_2646_);
lean_closure_set(v___f_2656_, 2, v_param_2653_);
v___f_2657_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8___boxed), 6, 2);
lean_closure_set(v___f_2657_, 0, v___f_2656_);
lean_closure_set(v___f_2657_, 1, v___f_2647_);
v___x_2658_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_2658_, 0, lean_box(0));
lean_closure_set(v___x_2658_, 1, lean_box(0));
lean_closure_set(v___x_2658_, 2, lean_box(0));
lean_closure_set(v___x_2658_, 3, v___f_2648_);
lean_inc_ref(v___x_2649_);
v___x_2659_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2659_, 0, lean_box(0));
lean_closure_set(v___x_2659_, 1, lean_box(0));
lean_closure_set(v___x_2659_, 2, v___x_2649_);
lean_closure_set(v___x_2659_, 3, lean_box(0));
lean_closure_set(v___x_2659_, 4, lean_box(0));
lean_closure_set(v___x_2659_, 5, v___x_2658_);
lean_closure_set(v___x_2659_, 6, v___f_2657_);
v___x_6497__overap_2660_ = l_Std_Mutex_atomically___redArg(v___x_2649_, v___f_2650_, v___f_2651_, v_val_2652_, v___x_2659_);
lean_inc_ref(v___y_2654_);
v___x_2661_ = lean_apply_2(v___x_6497__overap_2660_, v___y_2654_, lean_box(0));
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9___boxed(lean_object* v_val_2662_, lean_object* v___f_2663_, lean_object* v___f_2664_, lean_object* v___f_2665_, lean_object* v___x_2666_, lean_object* v___f_2667_, lean_object* v___f_2668_, lean_object* v_val_2669_, lean_object* v_param_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9(v_val_2662_, v___f_2663_, v___f_2664_, v___f_2665_, v___x_2666_, v___f_2667_, v___f_2668_, v_val_2669_, v_param_2670_, v___y_2671_);
lean_dec_ref(v___y_2671_);
return v_res_2673_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0(void){
_start:
{
lean_object* v___x_2674_; 
v___x_2674_ = l_instMonadEIO(lean_box(0));
return v___x_2674_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1(void){
_start:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2675_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0);
v___x_2676_ = l_ReaderT_instMonad___redArg(v___x_2675_);
return v___x_2676_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3(void){
_start:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2678_ = lean_box(0);
v___x_2679_ = lean_task_pure(v___x_2678_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(lean_object* v_method_2705_, lean_object* v_completeness_2706_, lean_object* v_inst_2707_, lean_object* v_inst_2708_, lean_object* v_inst_2709_, lean_object* v_inst_2710_, lean_object* v_initState_2711_, lean_object* v_handler_2712_, lean_object* v_onDidChange_2713_){
_start:
{
lean_object* v___x_2715_; uint8_t v___x_2716_; 
v___x_2715_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1);
v___x_2716_ = l_Lean_initializing();
if (v___x_2716_ == 0)
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
lean_dec_ref(v_onDidChange_2713_);
lean_dec_ref(v_handler_2712_);
lean_dec(v_initState_2711_);
lean_dec(v_inst_2710_);
lean_dec_ref(v_inst_2709_);
lean_dec_ref(v_inst_2708_);
lean_dec_ref(v_inst_2707_);
lean_dec(v_completeness_2706_);
v___x_2717_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2));
v___x_2718_ = lean_string_append(v___x_2717_, v_method_2705_);
lean_dec_ref(v_method_2705_);
v___x_2719_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__1));
v___x_2720_ = lean_string_append(v___x_2718_, v___x_2719_);
v___x_2721_ = lean_mk_io_user_error(v___x_2720_);
v___x_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
return v___x_2722_;
}
else
{
lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___f_2729_; lean_object* v___f_2730_; lean_object* v___f_2731_; lean_object* v___f_2732_; lean_object* v___f_2733_; lean_object* v___f_2734_; lean_object* v___x_2735_; lean_object* v___f_2736_; lean_object* v___f_2737_; lean_object* v___f_2738_; lean_object* v___f_2739_; lean_object* v___f_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2723_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3);
v___x_2724_ = l_Std_Mutex_new___redArg(v___x_2723_);
lean_inc_n(v_inst_2710_, 2);
v___x_2725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2725_, 0, v_inst_2710_);
lean_ctor_set(v___x_2725_, 1, v_initState_2711_);
lean_inc_ref(v___x_2725_);
v___x_2726_ = lean_st_mk_ref(v___x_2725_);
v___x_2727_ = l_Lean_Server_statefulRequestHandlers;
v___x_2728_ = lean_st_ref_take(v___x_2727_);
v___f_2729_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__7));
lean_inc_ref(v_inst_2707_);
v___f_2730_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2730_, 0, v_inst_2707_);
lean_closure_set(v___f_2730_, 1, v_inst_2708_);
lean_inc_ref_n(v_method_2705_, 2);
v___f_2731_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1___boxed), 9, 5);
lean_closure_set(v___f_2731_, 0, v_inst_2707_);
lean_closure_set(v___f_2731_, 1, v_method_2705_);
lean_closure_set(v___f_2731_, 2, v_inst_2710_);
lean_closure_set(v___f_2731_, 3, v_handler_2712_);
lean_closure_set(v___f_2731_, 4, v_inst_2709_);
v___f_2732_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0___boxed), 7, 3);
lean_closure_set(v___f_2732_, 0, v_method_2705_);
lean_closure_set(v___f_2732_, 1, v_inst_2710_);
lean_closure_set(v___f_2732_, 2, v_onDidChange_2713_);
v___f_2733_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__9));
v___f_2734_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__13));
v___x_2735_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___f_2736_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__14));
v___f_2737_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15));
lean_inc_ref_n(v___x_2724_, 2);
lean_inc_ref(v___f_2731_);
lean_inc_n(v___x_2726_, 2);
v___f_2738_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6___boxed), 11, 8);
lean_closure_set(v___f_2738_, 0, v___x_2726_);
lean_closure_set(v___f_2738_, 1, v___f_2731_);
lean_closure_set(v___f_2738_, 2, v___f_2736_);
lean_closure_set(v___f_2738_, 3, v___f_2734_);
lean_closure_set(v___f_2738_, 4, v___x_2715_);
lean_closure_set(v___f_2738_, 5, v___f_2729_);
lean_closure_set(v___f_2738_, 6, v___f_2733_);
lean_closure_set(v___f_2738_, 7, v___x_2724_);
lean_inc_ref(v___f_2732_);
v___f_2739_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9___boxed), 11, 8);
lean_closure_set(v___f_2739_, 0, v___x_2726_);
lean_closure_set(v___f_2739_, 1, v___f_2732_);
lean_closure_set(v___f_2739_, 2, v___f_2737_);
lean_closure_set(v___f_2739_, 3, v___f_2734_);
lean_closure_set(v___f_2739_, 4, v___x_2715_);
lean_closure_set(v___f_2739_, 5, v___f_2729_);
lean_closure_set(v___f_2739_, 6, v___f_2733_);
lean_closure_set(v___f_2739_, 7, v___x_2724_);
v___f_2740_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
v___x_2741_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2741_, 0, v___f_2730_);
lean_ctor_set(v___x_2741_, 1, v___f_2731_);
lean_ctor_set(v___x_2741_, 2, v___f_2738_);
lean_ctor_set(v___x_2741_, 3, v___f_2732_);
lean_ctor_set(v___x_2741_, 4, v___f_2739_);
lean_ctor_set(v___x_2741_, 5, v___x_2724_);
lean_ctor_set(v___x_2741_, 6, v___x_2725_);
lean_ctor_set(v___x_2741_, 7, v___x_2726_);
lean_ctor_set(v___x_2741_, 8, v_completeness_2706_);
v___x_2742_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2740_, v___x_2735_, v___x_2728_, v_method_2705_, v___x_2741_);
v___x_2743_ = lean_st_ref_set(v___x_2727_, v___x_2742_);
v___x_2744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2743_);
return v___x_2744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2745_, lean_object* v_completeness_2746_, lean_object* v_inst_2747_, lean_object* v_inst_2748_, lean_object* v_inst_2749_, lean_object* v_inst_2750_, lean_object* v_initState_2751_, lean_object* v_handler_2752_, lean_object* v_onDidChange_2753_, lean_object* v_a_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2745_, v_completeness_2746_, v_inst_2747_, v_inst_2748_, v_inst_2749_, v_inst_2750_, v_initState_2751_, v_handler_2752_, v_onDidChange_2753_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(lean_object* v_method_2756_, lean_object* v_completeness_2757_, lean_object* v_paramType_2758_, lean_object* v_inst_2759_, lean_object* v_inst_2760_, lean_object* v_respType_2761_, lean_object* v_inst_2762_, lean_object* v_stateType_2763_, lean_object* v_inst_2764_, lean_object* v_initState_2765_, lean_object* v_handler_2766_, lean_object* v_onDidChange_2767_){
_start:
{
lean_object* v___x_2769_; 
v___x_2769_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2756_, v_completeness_2757_, v_inst_2759_, v_inst_2760_, v_inst_2762_, v_inst_2764_, v_initState_2765_, v_handler_2766_, v_onDidChange_2767_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___boxed(lean_object* v_method_2770_, lean_object* v_completeness_2771_, lean_object* v_paramType_2772_, lean_object* v_inst_2773_, lean_object* v_inst_2774_, lean_object* v_respType_2775_, lean_object* v_inst_2776_, lean_object* v_stateType_2777_, lean_object* v_inst_2778_, lean_object* v_initState_2779_, lean_object* v_handler_2780_, lean_object* v_onDidChange_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(v_method_2770_, v_completeness_2771_, v_paramType_2772_, v_inst_2773_, v_inst_2774_, v_respType_2775_, v_inst_2776_, v_stateType_2777_, v_inst_2778_, v_initState_2779_, v_handler_2780_, v_onDidChange_2781_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(lean_object* v_method_2784_, lean_object* v_completeness_2785_, lean_object* v_inst_2786_, lean_object* v_inst_2787_, lean_object* v_inst_2788_, lean_object* v_inst_2789_, lean_object* v_initState_2790_, lean_object* v_handler_2791_, lean_object* v_onDidChange_2792_){
_start:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___f_2797_; uint8_t v___x_2798_; 
v___x_2794_ = l_Lean_Server_requestHandlers;
v___x_2795_ = lean_st_ref_get(v___x_2794_);
v___x_2796_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___f_2797_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
lean_inc_ref(v_method_2784_);
v___x_2798_ = l_Lean_PersistentHashMap_contains___redArg(v___f_2797_, v___x_2796_, v___x_2795_, v_method_2784_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2799_; 
v___x_2799_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2784_, v_completeness_2785_, v_inst_2786_, v_inst_2787_, v_inst_2788_, v_inst_2789_, v_initState_2790_, v_handler_2791_, v_onDidChange_2792_);
return v___x_2799_;
}
else
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
lean_dec_ref(v_onDidChange_2792_);
lean_dec_ref(v_handler_2791_);
lean_dec(v_initState_2790_);
lean_dec(v_inst_2789_);
lean_dec_ref(v_inst_2788_);
lean_dec_ref(v_inst_2787_);
lean_dec_ref(v_inst_2786_);
lean_dec(v_completeness_2785_);
v___x_2800_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2));
v___x_2801_ = lean_string_append(v___x_2800_, v_method_2784_);
lean_dec_ref(v_method_2784_);
v___x_2802_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__4));
v___x_2803_ = lean_string_append(v___x_2801_, v___x_2802_);
v___x_2804_ = lean_mk_io_user_error(v___x_2803_);
v___x_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
return v___x_2805_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2806_, lean_object* v_completeness_2807_, lean_object* v_inst_2808_, lean_object* v_inst_2809_, lean_object* v_inst_2810_, lean_object* v_inst_2811_, lean_object* v_initState_2812_, lean_object* v_handler_2813_, lean_object* v_onDidChange_2814_, lean_object* v_a_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2806_, v_completeness_2807_, v_inst_2808_, v_inst_2809_, v_inst_2810_, v_inst_2811_, v_initState_2812_, v_handler_2813_, v_onDidChange_2814_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler(lean_object* v_method_2817_, lean_object* v_completeness_2818_, lean_object* v_paramType_2819_, lean_object* v_inst_2820_, lean_object* v_inst_2821_, lean_object* v_respType_2822_, lean_object* v_inst_2823_, lean_object* v_stateType_2824_, lean_object* v_inst_2825_, lean_object* v_initState_2826_, lean_object* v_handler_2827_, lean_object* v_onDidChange_2828_){
_start:
{
lean_object* v___x_2830_; 
v___x_2830_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2817_, v_completeness_2818_, v_inst_2820_, v_inst_2821_, v_inst_2823_, v_inst_2825_, v_initState_2826_, v_handler_2827_, v_onDidChange_2828_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___boxed(lean_object* v_method_2831_, lean_object* v_completeness_2832_, lean_object* v_paramType_2833_, lean_object* v_inst_2834_, lean_object* v_inst_2835_, lean_object* v_respType_2836_, lean_object* v_inst_2837_, lean_object* v_stateType_2838_, lean_object* v_inst_2839_, lean_object* v_initState_2840_, lean_object* v_handler_2841_, lean_object* v_onDidChange_2842_, lean_object* v_a_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler(v_method_2831_, v_completeness_2832_, v_paramType_2833_, v_inst_2834_, v_inst_2835_, v_respType_2836_, v_inst_2837_, v_stateType_2838_, v_inst_2839_, v_initState_2840_, v_handler_2841_, v_onDidChange_2842_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0(lean_object* v_handler_2845_, lean_object* v_p_2846_, lean_object* v_s_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v___x_2850_; 
lean_inc_ref(v___y_2848_);
v___x_2850_ = lean_apply_4(v_handler_2845_, v_p_2846_, v_s_2847_, v___y_2848_, lean_box(0));
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2869_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2853_ = v___x_2850_;
v_isShared_2854_ = v_isSharedCheck_2869_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2850_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2869_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v_fst_2855_; lean_object* v_snd_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2868_; 
v_fst_2855_ = lean_ctor_get(v_a_2851_, 0);
v_snd_2856_ = lean_ctor_get(v_a_2851_, 1);
v_isSharedCheck_2868_ = !lean_is_exclusive(v_a_2851_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2858_ = v_a_2851_;
v_isShared_2859_ = v_isSharedCheck_2868_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_snd_2856_);
lean_inc(v_fst_2855_);
lean_dec(v_a_2851_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2868_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
uint8_t v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2863_; 
v___x_2860_ = 1;
v___x_2861_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2861_, 0, v_fst_2855_);
lean_ctor_set_uint8(v___x_2861_, sizeof(void*)*1, v___x_2860_);
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 0, v___x_2861_);
v___x_2863_ = v___x_2858_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v___x_2861_);
lean_ctor_set(v_reuseFailAlloc_2867_, 1, v_snd_2856_);
v___x_2863_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
lean_object* v___x_2865_; 
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 0, v___x_2863_);
v___x_2865_ = v___x_2853_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v___x_2863_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
v_a_2870_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2850_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2850_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2870_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object* v_handler_2878_, lean_object* v_p_2879_, lean_object* v_s_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0(v_handler_2878_, v_p_2879_, v_s_2880_, v___y_2881_);
lean_dec_ref(v___y_2881_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(lean_object* v_method_2884_, lean_object* v_inst_2885_, lean_object* v_inst_2886_, lean_object* v_inst_2887_, lean_object* v_inst_2888_, lean_object* v_initState_2889_, lean_object* v_handler_2890_, lean_object* v_onDidChange_2891_){
_start:
{
lean_object* v_handler_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v_handler_2893_ = lean_alloc_closure((void*)(l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v_handler_2893_, 0, v_handler_2890_);
v___x_2894_ = lean_box(0);
v___x_2895_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2884_, v___x_2894_, v_inst_2885_, v_inst_2886_, v_inst_2887_, v_inst_2888_, v_initState_2889_, v_handler_2893_, v_onDidChange_2891_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2896_, lean_object* v_inst_2897_, lean_object* v_inst_2898_, lean_object* v_inst_2899_, lean_object* v_inst_2900_, lean_object* v_initState_2901_, lean_object* v_handler_2902_, lean_object* v_onDidChange_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(v_method_2896_, v_inst_2897_, v_inst_2898_, v_inst_2899_, v_inst_2900_, v_initState_2901_, v_handler_2902_, v_onDidChange_2903_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler(lean_object* v_method_2906_, lean_object* v_paramType_2907_, lean_object* v_inst_2908_, lean_object* v_inst_2909_, lean_object* v_respType_2910_, lean_object* v_inst_2911_, lean_object* v_stateType_2912_, lean_object* v_inst_2913_, lean_object* v_initState_2914_, lean_object* v_handler_2915_, lean_object* v_onDidChange_2916_){
_start:
{
lean_object* v___x_2918_; 
v___x_2918_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(v_method_2906_, v_inst_2908_, v_inst_2909_, v_inst_2911_, v_inst_2913_, v_initState_2914_, v_handler_2915_, v_onDidChange_2916_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___boxed(lean_object* v_method_2919_, lean_object* v_paramType_2920_, lean_object* v_inst_2921_, lean_object* v_inst_2922_, lean_object* v_respType_2923_, lean_object* v_inst_2924_, lean_object* v_stateType_2925_, lean_object* v_inst_2926_, lean_object* v_initState_2927_, lean_object* v_handler_2928_, lean_object* v_onDidChange_2929_, lean_object* v_a_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler(v_method_2919_, v_paramType_2920_, v_inst_2921_, v_inst_2922_, v_respType_2923_, v_inst_2924_, v_stateType_2925_, v_inst_2926_, v_initState_2927_, v_handler_2928_, v_onDidChange_2929_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(lean_object* v_method_2932_, lean_object* v_refreshMethod_2933_, lean_object* v_refreshIntervalMs_2934_, lean_object* v_inst_2935_, lean_object* v_inst_2936_, lean_object* v_inst_2937_, lean_object* v_inst_2938_, lean_object* v_initState_2939_, lean_object* v_handler_2940_, lean_object* v_onDidChange_2941_){
_start:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2943_, 0, v_refreshMethod_2933_);
lean_ctor_set(v___x_2943_, 1, v_refreshIntervalMs_2934_);
v___x_2944_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2932_, v___x_2943_, v_inst_2935_, v_inst_2936_, v_inst_2937_, v_inst_2938_, v_initState_2939_, v_handler_2940_, v_onDidChange_2941_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2945_, lean_object* v_refreshMethod_2946_, lean_object* v_refreshIntervalMs_2947_, lean_object* v_inst_2948_, lean_object* v_inst_2949_, lean_object* v_inst_2950_, lean_object* v_inst_2951_, lean_object* v_initState_2952_, lean_object* v_handler_2953_, lean_object* v_onDidChange_2954_, lean_object* v_a_2955_){
_start:
{
lean_object* v_res_2956_; 
v_res_2956_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(v_method_2945_, v_refreshMethod_2946_, v_refreshIntervalMs_2947_, v_inst_2948_, v_inst_2949_, v_inst_2950_, v_inst_2951_, v_initState_2952_, v_handler_2953_, v_onDidChange_2954_);
return v_res_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler(lean_object* v_method_2957_, lean_object* v_refreshMethod_2958_, lean_object* v_refreshIntervalMs_2959_, lean_object* v_paramType_2960_, lean_object* v_inst_2961_, lean_object* v_inst_2962_, lean_object* v_respType_2963_, lean_object* v_inst_2964_, lean_object* v_stateType_2965_, lean_object* v_inst_2966_, lean_object* v_initState_2967_, lean_object* v_handler_2968_, lean_object* v_onDidChange_2969_){
_start:
{
lean_object* v___x_2971_; 
v___x_2971_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(v_method_2957_, v_refreshMethod_2958_, v_refreshIntervalMs_2959_, v_inst_2961_, v_inst_2962_, v_inst_2964_, v_inst_2966_, v_initState_2967_, v_handler_2968_, v_onDidChange_2969_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___boxed(lean_object* v_method_2972_, lean_object* v_refreshMethod_2973_, lean_object* v_refreshIntervalMs_2974_, lean_object* v_paramType_2975_, lean_object* v_inst_2976_, lean_object* v_inst_2977_, lean_object* v_respType_2978_, lean_object* v_inst_2979_, lean_object* v_stateType_2980_, lean_object* v_inst_2981_, lean_object* v_initState_2982_, lean_object* v_handler_2983_, lean_object* v_onDidChange_2984_, lean_object* v_a_2985_){
_start:
{
lean_object* v_res_2986_; 
v_res_2986_ = l_Lean_Server_registerPartialStatefulLspRequestHandler(v_method_2972_, v_refreshMethod_2973_, v_refreshIntervalMs_2974_, v_paramType_2975_, v_inst_2976_, v_inst_2977_, v_respType_2978_, v_inst_2979_, v_stateType_2980_, v_inst_2981_, v_initState_2982_, v_handler_2983_, v_onDidChange_2984_);
return v_res_2986_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2987_, lean_object* v_i_2988_, lean_object* v_k_2989_){
_start:
{
lean_object* v___x_2990_; uint8_t v___x_2991_; 
v___x_2990_ = lean_array_get_size(v_keys_2987_);
v___x_2991_ = lean_nat_dec_lt(v_i_2988_, v___x_2990_);
if (v___x_2991_ == 0)
{
lean_dec(v_i_2988_);
return v___x_2991_;
}
else
{
lean_object* v_k_x27_2992_; uint8_t v___x_2993_; 
v_k_x27_2992_ = lean_array_fget_borrowed(v_keys_2987_, v_i_2988_);
v___x_2993_ = lean_string_dec_eq(v_k_2989_, v_k_x27_2992_);
if (v___x_2993_ == 0)
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2994_ = lean_unsigned_to_nat(1u);
v___x_2995_ = lean_nat_add(v_i_2988_, v___x_2994_);
lean_dec(v_i_2988_);
v_i_2988_ = v___x_2995_;
goto _start;
}
else
{
lean_dec(v_i_2988_);
return v___x_2993_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2997_, lean_object* v_i_2998_, lean_object* v_k_2999_){
_start:
{
uint8_t v_res_3000_; lean_object* v_r_3001_; 
v_res_3000_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_keys_2997_, v_i_2998_, v_k_2999_);
lean_dec_ref(v_k_2999_);
lean_dec_ref(v_keys_2997_);
v_r_3001_ = lean_box(v_res_3000_);
return v_r_3001_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(lean_object* v_x_3002_, size_t v_x_3003_, lean_object* v_x_3004_){
_start:
{
if (lean_obj_tag(v_x_3002_) == 0)
{
lean_object* v_es_3005_; lean_object* v___x_3006_; size_t v___x_3007_; size_t v___x_3008_; lean_object* v_j_3009_; lean_object* v___x_3010_; 
v_es_3005_ = lean_ctor_get(v_x_3002_, 0);
v___x_3006_ = lean_box(2);
v___x_3007_ = ((size_t)31ULL);
v___x_3008_ = lean_usize_land(v_x_3003_, v___x_3007_);
v_j_3009_ = lean_usize_to_nat(v___x_3008_);
v___x_3010_ = lean_array_get_borrowed(v___x_3006_, v_es_3005_, v_j_3009_);
lean_dec(v_j_3009_);
switch(lean_obj_tag(v___x_3010_))
{
case 0:
{
lean_object* v_key_3011_; uint8_t v___x_3012_; 
v_key_3011_ = lean_ctor_get(v___x_3010_, 0);
v___x_3012_ = lean_string_dec_eq(v_x_3004_, v_key_3011_);
return v___x_3012_;
}
case 1:
{
lean_object* v_node_3013_; size_t v___x_3014_; size_t v___x_3015_; 
v_node_3013_ = lean_ctor_get(v___x_3010_, 0);
v___x_3014_ = ((size_t)5ULL);
v___x_3015_ = lean_usize_shift_right(v_x_3003_, v___x_3014_);
v_x_3002_ = v_node_3013_;
v_x_3003_ = v___x_3015_;
goto _start;
}
default: 
{
uint8_t v___x_3017_; 
v___x_3017_ = 0;
return v___x_3017_;
}
}
}
else
{
lean_object* v_ks_3018_; lean_object* v___x_3019_; uint8_t v___x_3020_; 
v_ks_3018_ = lean_ctor_get(v_x_3002_, 0);
v___x_3019_ = lean_unsigned_to_nat(0u);
v___x_3020_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_ks_3018_, v___x_3019_, v_x_3004_);
return v___x_3020_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg___boxed(lean_object* v_x_3021_, lean_object* v_x_3022_, lean_object* v_x_3023_){
_start:
{
size_t v_x_214__boxed_3024_; uint8_t v_res_3025_; lean_object* v_r_3026_; 
v_x_214__boxed_3024_ = lean_unbox_usize(v_x_3022_);
lean_dec(v_x_3022_);
v_res_3025_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_3021_, v_x_214__boxed_3024_, v_x_3023_);
lean_dec_ref(v_x_3023_);
lean_dec_ref(v_x_3021_);
v_r_3026_ = lean_box(v_res_3025_);
return v_r_3026_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(lean_object* v_x_3027_, lean_object* v_x_3028_){
_start:
{
uint64_t v___x_3029_; size_t v___x_3030_; uint8_t v___x_3031_; 
v___x_3029_ = lean_string_hash(v_x_3028_);
v___x_3030_ = lean_uint64_to_usize(v___x_3029_);
v___x_3031_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_3027_, v___x_3030_, v_x_3028_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg___boxed(lean_object* v_x_3032_, lean_object* v_x_3033_){
_start:
{
uint8_t v_res_3034_; lean_object* v_r_3035_; 
v_res_3034_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v_x_3032_, v_x_3033_);
lean_dec_ref(v_x_3033_);
lean_dec_ref(v_x_3032_);
v_r_3035_ = lean_box(v_res_3034_);
return v_r_3035_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_isStatefulLspRequestMethod(lean_object* v_method_3036_){
_start:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; uint8_t v___x_3040_; 
v___x_3038_ = l_Lean_Server_statefulRequestHandlers;
v___x_3039_ = lean_st_ref_get(v___x_3038_);
v___x_3040_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v___x_3039_, v_method_3036_);
lean_dec(v___x_3039_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_isStatefulLspRequestMethod___boxed(lean_object* v_method_3041_, lean_object* v_a_3042_){
_start:
{
uint8_t v_res_3043_; lean_object* v_r_3044_; 
v_res_3043_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_3041_);
lean_dec_ref(v_method_3041_);
v_r_3044_ = lean_box(v_res_3043_);
return v_r_3044_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0(lean_object* v_00_u03b2_3045_, lean_object* v_x_3046_, lean_object* v_x_3047_){
_start:
{
uint8_t v___x_3048_; 
v___x_3048_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v_x_3046_, v_x_3047_);
return v___x_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___boxed(lean_object* v_00_u03b2_3049_, lean_object* v_x_3050_, lean_object* v_x_3051_){
_start:
{
uint8_t v_res_3052_; lean_object* v_r_3053_; 
v_res_3052_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0(v_00_u03b2_3049_, v_x_3050_, v_x_3051_);
lean_dec_ref(v_x_3051_);
lean_dec_ref(v_x_3050_);
v_r_3053_ = lean_box(v_res_3052_);
return v_r_3053_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0(lean_object* v_00_u03b2_3054_, lean_object* v_x_3055_, size_t v_x_3056_, lean_object* v_x_3057_){
_start:
{
uint8_t v___x_3058_; 
v___x_3058_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_3055_, v_x_3056_, v_x_3057_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3059_, lean_object* v_x_3060_, lean_object* v_x_3061_, lean_object* v_x_3062_){
_start:
{
size_t v_x_284__boxed_3063_; uint8_t v_res_3064_; lean_object* v_r_3065_; 
v_x_284__boxed_3063_ = lean_unbox_usize(v_x_3061_);
lean_dec(v_x_3061_);
v_res_3064_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0(v_00_u03b2_3059_, v_x_3060_, v_x_284__boxed_3063_, v_x_3062_);
lean_dec_ref(v_x_3062_);
lean_dec_ref(v_x_3060_);
v_r_3065_ = lean_box(v_res_3064_);
return v_r_3065_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3066_, lean_object* v_keys_3067_, lean_object* v_vals_3068_, lean_object* v_heq_3069_, lean_object* v_i_3070_, lean_object* v_k_3071_){
_start:
{
uint8_t v___x_3072_; 
v___x_3072_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_keys_3067_, v_i_3070_, v_k_3071_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3073_, lean_object* v_keys_3074_, lean_object* v_vals_3075_, lean_object* v_heq_3076_, lean_object* v_i_3077_, lean_object* v_k_3078_){
_start:
{
uint8_t v_res_3079_; lean_object* v_r_3080_; 
v_res_3079_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1(v_00_u03b2_3073_, v_keys_3074_, v_vals_3075_, v_heq_3076_, v_i_3077_, v_k_3078_);
lean_dec_ref(v_k_3078_);
lean_dec_ref(v_vals_3075_);
lean_dec_ref(v_keys_3074_);
v_r_3080_ = lean_box(v_res_3079_);
return v_r_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupStatefulLspRequestHandler(lean_object* v_method_3081_){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3083_ = l_Lean_Server_statefulRequestHandlers;
v___x_3084_ = lean_st_ref_get(v___x_3083_);
v___x_3085_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v___x_3084_, v_method_3081_);
lean_dec(v___x_3084_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupStatefulLspRequestHandler___boxed(lean_object* v_method_3086_, lean_object* v_a_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_3086_);
lean_dec_ref(v_method_3086_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(lean_object* v_as_3089_, size_t v_i_3090_, size_t v_stop_3091_, lean_object* v_b_3092_){
_start:
{
lean_object* v___y_3094_; uint8_t v___x_3098_; 
v___x_3098_ = lean_usize_dec_eq(v_i_3090_, v_stop_3091_);
if (v___x_3098_ == 0)
{
lean_object* v___x_3099_; lean_object* v_snd_3100_; lean_object* v_completeness_3101_; 
v___x_3099_ = lean_array_uget(v_as_3089_, v_i_3090_);
v_snd_3100_ = lean_ctor_get(v___x_3099_, 1);
v_completeness_3101_ = lean_ctor_get(v_snd_3100_, 8);
lean_inc(v_completeness_3101_);
if (lean_obj_tag(v_completeness_3101_) == 1)
{
lean_object* v_fst_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3119_; 
v_fst_3102_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3119_ == 0)
{
lean_object* v_unused_3120_; 
v_unused_3120_ = lean_ctor_get(v___x_3099_, 1);
lean_dec(v_unused_3120_);
v___x_3104_ = v___x_3099_;
v_isShared_3105_ = v_isSharedCheck_3119_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_fst_3102_);
lean_dec(v___x_3099_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3119_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v_refreshMethod_3106_; lean_object* v_refreshIntervalMs_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3118_; 
v_refreshMethod_3106_ = lean_ctor_get(v_completeness_3101_, 0);
v_refreshIntervalMs_3107_ = lean_ctor_get(v_completeness_3101_, 1);
v_isSharedCheck_3118_ = !lean_is_exclusive(v_completeness_3101_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3109_ = v_completeness_3101_;
v_isShared_3110_ = v_isSharedCheck_3118_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_refreshIntervalMs_3107_);
lean_inc(v_refreshMethod_3106_);
lean_dec(v_completeness_3101_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3118_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3112_; 
if (v_isShared_3105_ == 0)
{
lean_ctor_set(v___x_3104_, 1, v_refreshIntervalMs_3107_);
lean_ctor_set(v___x_3104_, 0, v_refreshMethod_3106_);
v___x_3112_ = v___x_3104_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_refreshMethod_3106_);
lean_ctor_set(v_reuseFailAlloc_3117_, 1, v_refreshIntervalMs_3107_);
v___x_3112_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
lean_object* v___x_3114_; 
if (v_isShared_3110_ == 0)
{
lean_ctor_set_tag(v___x_3109_, 0);
lean_ctor_set(v___x_3109_, 1, v___x_3112_);
lean_ctor_set(v___x_3109_, 0, v_fst_3102_);
v___x_3114_ = v___x_3109_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_fst_3102_);
lean_ctor_set(v_reuseFailAlloc_3116_, 1, v___x_3112_);
v___x_3114_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
lean_object* v___x_3115_; 
v___x_3115_ = lean_array_push(v_b_3092_, v___x_3114_);
v___y_3094_ = v___x_3115_;
goto v___jp_3093_;
}
}
}
}
}
else
{
lean_dec(v_completeness_3101_);
lean_dec(v___x_3099_);
v___y_3094_ = v_b_3092_;
goto v___jp_3093_;
}
}
else
{
return v_b_3092_;
}
v___jp_3093_:
{
size_t v___x_3095_; size_t v___x_3096_; 
v___x_3095_ = ((size_t)1ULL);
v___x_3096_ = lean_usize_add(v_i_3090_, v___x_3095_);
v_i_3090_ = v___x_3096_;
v_b_3092_ = v___y_3094_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2___boxed(lean_object* v_as_3121_, lean_object* v_i_3122_, lean_object* v_stop_3123_, lean_object* v_b_3124_){
_start:
{
size_t v_i_boxed_3125_; size_t v_stop_boxed_3126_; lean_object* v_res_3127_; 
v_i_boxed_3125_ = lean_unbox_usize(v_i_3122_);
lean_dec(v_i_3122_);
v_stop_boxed_3126_ = lean_unbox_usize(v_stop_3123_);
lean_dec(v_stop_3123_);
v_res_3127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_3121_, v_i_boxed_3125_, v_stop_boxed_3126_, v_b_3124_);
lean_dec_ref(v_as_3121_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(lean_object* v_as_3130_, lean_object* v_start_3131_, lean_object* v_stop_3132_){
_start:
{
lean_object* v___x_3133_; uint8_t v___x_3134_; 
v___x_3133_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___closed__0));
v___x_3134_ = lean_nat_dec_lt(v_start_3131_, v_stop_3132_);
if (v___x_3134_ == 0)
{
return v___x_3133_;
}
else
{
lean_object* v___x_3135_; uint8_t v___x_3136_; 
v___x_3135_ = lean_array_get_size(v_as_3130_);
v___x_3136_ = lean_nat_dec_le(v_stop_3132_, v___x_3135_);
if (v___x_3136_ == 0)
{
uint8_t v___x_3137_; 
v___x_3137_ = lean_nat_dec_lt(v_start_3131_, v___x_3135_);
if (v___x_3137_ == 0)
{
return v___x_3133_;
}
else
{
size_t v___x_3138_; size_t v___x_3139_; lean_object* v___x_3140_; 
v___x_3138_ = lean_usize_of_nat(v_start_3131_);
v___x_3139_ = lean_usize_of_nat(v___x_3135_);
v___x_3140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_3130_, v___x_3138_, v___x_3139_, v___x_3133_);
return v___x_3140_;
}
}
else
{
size_t v___x_3141_; size_t v___x_3142_; lean_object* v___x_3143_; 
v___x_3141_ = lean_usize_of_nat(v_start_3131_);
v___x_3142_ = lean_usize_of_nat(v_stop_3132_);
v___x_3143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_3130_, v___x_3141_, v___x_3142_, v___x_3133_);
return v___x_3143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___boxed(lean_object* v_as_3144_, lean_object* v_start_3145_, lean_object* v_stop_3146_){
_start:
{
lean_object* v_res_3147_; 
v_res_3147_ = l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(v_as_3144_, v_start_3145_, v_stop_3146_);
lean_dec(v_stop_3146_);
lean_dec(v_start_3145_);
lean_dec_ref(v_as_3144_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_f_3148_, lean_object* v_keys_3149_, lean_object* v_vals_3150_, lean_object* v_i_3151_, lean_object* v_acc_3152_){
_start:
{
lean_object* v___x_3153_; uint8_t v___x_3154_; 
v___x_3153_ = lean_array_get_size(v_keys_3149_);
v___x_3154_ = lean_nat_dec_lt(v_i_3151_, v___x_3153_);
if (v___x_3154_ == 0)
{
lean_dec(v_i_3151_);
lean_dec(v_f_3148_);
return v_acc_3152_;
}
else
{
lean_object* v_k_3155_; lean_object* v_v_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v_k_3155_ = lean_array_fget_borrowed(v_keys_3149_, v_i_3151_);
v_v_3156_ = lean_array_fget_borrowed(v_vals_3150_, v_i_3151_);
lean_inc(v_f_3148_);
lean_inc(v_v_3156_);
lean_inc(v_k_3155_);
v___x_3157_ = lean_apply_3(v_f_3148_, v_acc_3152_, v_k_3155_, v_v_3156_);
v___x_3158_ = lean_unsigned_to_nat(1u);
v___x_3159_ = lean_nat_add(v_i_3151_, v___x_3158_);
lean_dec(v_i_3151_);
v_i_3151_ = v___x_3159_;
v_acc_3152_ = v___x_3157_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_f_3161_, lean_object* v_keys_3162_, lean_object* v_vals_3163_, lean_object* v_i_3164_, lean_object* v_acc_3165_){
_start:
{
lean_object* v_res_3166_; 
v_res_3166_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_3161_, v_keys_3162_, v_vals_3163_, v_i_3164_, v_acc_3165_);
lean_dec_ref(v_vals_3163_);
lean_dec_ref(v_keys_3162_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_3167_, lean_object* v_x_3168_, lean_object* v_x_3169_){
_start:
{
if (lean_obj_tag(v_x_3168_) == 0)
{
lean_object* v_es_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; uint8_t v___x_3173_; 
v_es_3170_ = lean_ctor_get(v_x_3168_, 0);
v___x_3171_ = lean_unsigned_to_nat(0u);
v___x_3172_ = lean_array_get_size(v_es_3170_);
v___x_3173_ = lean_nat_dec_lt(v___x_3171_, v___x_3172_);
if (v___x_3173_ == 0)
{
lean_dec(v_f_3167_);
return v_x_3169_;
}
else
{
uint8_t v___x_3174_; 
v___x_3174_ = lean_nat_dec_le(v___x_3172_, v___x_3172_);
if (v___x_3174_ == 0)
{
if (v___x_3173_ == 0)
{
lean_dec(v_f_3167_);
return v_x_3169_;
}
else
{
size_t v___x_3175_; size_t v___x_3176_; lean_object* v___x_3177_; 
v___x_3175_ = ((size_t)0ULL);
v___x_3176_ = lean_usize_of_nat(v___x_3172_);
v___x_3177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_3167_, v_es_3170_, v___x_3175_, v___x_3176_, v_x_3169_);
return v___x_3177_;
}
}
else
{
size_t v___x_3178_; size_t v___x_3179_; lean_object* v___x_3180_; 
v___x_3178_ = ((size_t)0ULL);
v___x_3179_ = lean_usize_of_nat(v___x_3172_);
v___x_3180_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_3167_, v_es_3170_, v___x_3178_, v___x_3179_, v_x_3169_);
return v___x_3180_;
}
}
}
else
{
lean_object* v_ks_3181_; lean_object* v_vs_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v_ks_3181_ = lean_ctor_get(v_x_3168_, 0);
v_vs_3182_ = lean_ctor_get(v_x_3168_, 1);
v___x_3183_ = lean_unsigned_to_nat(0u);
v___x_3184_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_3167_, v_ks_3181_, v_vs_3182_, v___x_3183_, v_x_3169_);
return v___x_3184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_f_3185_, lean_object* v_as_3186_, size_t v_i_3187_, size_t v_stop_3188_, lean_object* v_b_3189_){
_start:
{
lean_object* v___y_3191_; uint8_t v___x_3195_; 
v___x_3195_ = lean_usize_dec_eq(v_i_3187_, v_stop_3188_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; 
v___x_3196_ = lean_array_uget_borrowed(v_as_3186_, v_i_3187_);
switch(lean_obj_tag(v___x_3196_))
{
case 0:
{
lean_object* v_key_3197_; lean_object* v_val_3198_; lean_object* v___x_3199_; 
v_key_3197_ = lean_ctor_get(v___x_3196_, 0);
v_val_3198_ = lean_ctor_get(v___x_3196_, 1);
lean_inc(v_f_3185_);
lean_inc(v_val_3198_);
lean_inc(v_key_3197_);
v___x_3199_ = lean_apply_3(v_f_3185_, v_b_3189_, v_key_3197_, v_val_3198_);
v___y_3191_ = v___x_3199_;
goto v___jp_3190_;
}
case 1:
{
lean_object* v_node_3200_; lean_object* v___x_3201_; 
v_node_3200_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_f_3185_);
v___x_3201_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3185_, v_node_3200_, v_b_3189_);
v___y_3191_ = v___x_3201_;
goto v___jp_3190_;
}
default: 
{
v___y_3191_ = v_b_3189_;
goto v___jp_3190_;
}
}
}
else
{
lean_dec(v_f_3185_);
return v_b_3189_;
}
v___jp_3190_:
{
size_t v___x_3192_; size_t v___x_3193_; 
v___x_3192_ = ((size_t)1ULL);
v___x_3193_ = lean_usize_add(v_i_3187_, v___x_3192_);
v_i_3187_ = v___x_3193_;
v_b_3189_ = v___y_3191_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_f_3202_, lean_object* v_as_3203_, lean_object* v_i_3204_, lean_object* v_stop_3205_, lean_object* v_b_3206_){
_start:
{
size_t v_i_boxed_3207_; size_t v_stop_boxed_3208_; lean_object* v_res_3209_; 
v_i_boxed_3207_ = lean_unbox_usize(v_i_3204_);
lean_dec(v_i_3204_);
v_stop_boxed_3208_ = lean_unbox_usize(v_stop_3205_);
lean_dec(v_stop_3205_);
v_res_3209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_3202_, v_as_3203_, v_i_boxed_3207_, v_stop_boxed_3208_, v_b_3206_);
lean_dec_ref(v_as_3203_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_3210_, lean_object* v_x_3211_, lean_object* v_x_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3210_, v_x_3211_, v_x_3212_);
lean_dec_ref(v_x_3211_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___lam__0(lean_object* v_f_3214_, lean_object* v_x1_3215_, lean_object* v_x2_3216_, lean_object* v_x3_3217_){
_start:
{
lean_object* v___x_3218_; 
v___x_3218_ = lean_apply_3(v_f_3214_, v_x1_3215_, v_x2_3216_, v_x3_3217_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(lean_object* v_map_3219_, lean_object* v_f_3220_, lean_object* v_init_3221_){
_start:
{
lean_object* v___f_3222_; lean_object* v___x_3223_; 
v___f_3222_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3222_, 0, v_f_3220_);
v___x_3223_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v___f_3222_, v_map_3219_, v_init_3221_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___boxed(lean_object* v_map_3224_, lean_object* v_f_3225_, lean_object* v_init_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_map_3224_, v_f_3225_, v_init_3226_);
lean_dec_ref(v_map_3224_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___lam__0(lean_object* v_ps_3228_, lean_object* v_k_3229_, lean_object* v_v_3230_){
_start:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3231_, 0, v_k_3229_);
lean_ctor_set(v___x_3231_, 1, v_v_3230_);
v___x_3232_ = lean_array_push(v_ps_3228_, v___x_3231_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(lean_object* v_m_3236_){
_start:
{
lean_object* v___f_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___f_3237_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__0));
v___x_3238_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__1));
v___x_3239_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_m_3236_, v___f_3237_, v___x_3238_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___boxed(lean_object* v_m_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v_m_3240_);
lean_dec_ref(v_m_3240_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_partialLspRequestHandlerMethods(){
_start:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3243_ = l_Lean_Server_statefulRequestHandlers;
v___x_3244_ = lean_st_ref_get(v___x_3243_);
v___x_3245_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v___x_3244_);
lean_dec(v___x_3244_);
v___x_3246_ = lean_unsigned_to_nat(0u);
v___x_3247_ = lean_array_get_size(v___x_3245_);
v___x_3248_ = l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(v___x_3245_, v___x_3246_, v___x_3247_);
lean_dec_ref(v___x_3245_);
v___x_3249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3248_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_partialLspRequestHandlerMethods___boxed(lean_object* v_a_3250_){
_start:
{
lean_object* v_res_3251_; 
v_res_3251_ = l_Lean_Server_partialLspRequestHandlerMethods();
return v_res_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0(lean_object* v_00_u03b2_3252_, lean_object* v_m_3253_){
_start:
{
lean_object* v___x_3254_; 
v___x_3254_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v_m_3253_);
return v___x_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___boxed(lean_object* v_00_u03b2_3255_, lean_object* v_m_3256_){
_start:
{
lean_object* v_res_3257_; 
v_res_3257_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0(v_00_u03b2_3255_, v_m_3256_);
lean_dec_ref(v_m_3256_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0(lean_object* v_00_u03c3_3258_, lean_object* v_00_u03b2_3259_, lean_object* v_map_3260_, lean_object* v_f_3261_, lean_object* v_init_3262_){
_start:
{
lean_object* v___x_3263_; 
v___x_3263_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_map_3260_, v_f_3261_, v_init_3262_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3264_, lean_object* v_00_u03b2_3265_, lean_object* v_map_3266_, lean_object* v_f_3267_, lean_object* v_init_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0(v_00_u03c3_3264_, v_00_u03b2_3265_, v_map_3266_, v_f_3267_, v_init_3268_);
lean_dec_ref(v_map_3266_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg(lean_object* v_map_3270_, lean_object* v_f_3271_, lean_object* v_init_3272_){
_start:
{
lean_object* v___x_3273_; 
v___x_3273_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3271_, v_map_3270_, v_init_3272_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_3274_, lean_object* v_f_3275_, lean_object* v_init_3276_){
_start:
{
lean_object* v_res_3277_; 
v_res_3277_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg(v_map_3274_, v_f_3275_, v_init_3276_);
lean_dec_ref(v_map_3274_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3278_, lean_object* v_00_u03b2_3279_, lean_object* v_map_3280_, lean_object* v_f_3281_, lean_object* v_init_3282_){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3281_, v_map_3280_, v_init_3282_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3284_, lean_object* v_00_u03b2_3285_, lean_object* v_map_3286_, lean_object* v_f_3287_, lean_object* v_init_3288_){
_start:
{
lean_object* v_res_3289_; 
v_res_3289_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1(v_00_u03c3_3284_, v_00_u03b2_3285_, v_map_3286_, v_f_3287_, v_init_3288_);
lean_dec_ref(v_map_3286_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3290_, lean_object* v_00_u03b1_3291_, lean_object* v_00_u03b2_3292_, lean_object* v_f_3293_, lean_object* v_x_3294_, lean_object* v_x_3295_){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3293_, v_x_3294_, v_x_3295_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3297_, lean_object* v_00_u03b1_3298_, lean_object* v_00_u03b2_3299_, lean_object* v_f_3300_, lean_object* v_x_3301_, lean_object* v_x_3302_){
_start:
{
lean_object* v_res_3303_; 
v_res_3303_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3297_, v_00_u03b1_3298_, v_00_u03b2_3299_, v_f_3300_, v_x_3301_, v_x_3302_);
lean_dec_ref(v_x_3301_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_3304_, lean_object* v_00_u03b2_3305_, lean_object* v_00_u03c3_3306_, lean_object* v_f_3307_, lean_object* v_as_3308_, size_t v_i_3309_, size_t v_stop_3310_, lean_object* v_b_3311_){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_3307_, v_as_3308_, v_i_3309_, v_stop_3310_, v_b_3311_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_3313_, lean_object* v_00_u03b2_3314_, lean_object* v_00_u03c3_3315_, lean_object* v_f_3316_, lean_object* v_as_3317_, lean_object* v_i_3318_, lean_object* v_stop_3319_, lean_object* v_b_3320_){
_start:
{
size_t v_i_boxed_3321_; size_t v_stop_boxed_3322_; lean_object* v_res_3323_; 
v_i_boxed_3321_ = lean_unbox_usize(v_i_3318_);
lean_dec(v_i_3318_);
v_stop_boxed_3322_ = lean_unbox_usize(v_stop_3319_);
lean_dec(v_stop_3319_);
v_res_3323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_3313_, v_00_u03b2_3314_, v_00_u03c3_3315_, v_f_3316_, v_as_3317_, v_i_boxed_3321_, v_stop_boxed_3322_, v_b_3320_);
lean_dec_ref(v_as_3317_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03c3_3324_, lean_object* v_00_u03b1_3325_, lean_object* v_00_u03b2_3326_, lean_object* v_f_3327_, lean_object* v_keys_3328_, lean_object* v_vals_3329_, lean_object* v_heq_3330_, lean_object* v_i_3331_, lean_object* v_acc_3332_){
_start:
{
lean_object* v___x_3333_; 
v___x_3333_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_3327_, v_keys_3328_, v_vals_3329_, v_i_3331_, v_acc_3332_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03c3_3334_, lean_object* v_00_u03b1_3335_, lean_object* v_00_u03b2_3336_, lean_object* v_f_3337_, lean_object* v_keys_3338_, lean_object* v_vals_3339_, lean_object* v_heq_3340_, lean_object* v_i_3341_, lean_object* v_acc_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6(v_00_u03c3_3334_, v_00_u03b1_3335_, v_00_u03b2_3336_, v_f_3337_, v_keys_3338_, v_vals_3339_, v_heq_3340_, v_i_3341_, v_acc_3342_);
lean_dec_ref(v_vals_3339_);
lean_dec_ref(v_keys_3338_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0(lean_object* v_inst_3344_, lean_object* v_pureOnDidChange_3345_, lean_object* v_method_3346_, lean_object* v_onDidChange_3347_, lean_object* v_p_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; 
lean_inc(v_inst_3344_);
v___x_3352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3352_, 0, v_inst_3344_);
lean_ctor_set(v___x_3352_, 1, v___y_3349_);
lean_inc_ref(v___y_3350_);
lean_inc_ref(v_p_3348_);
v___x_3353_ = lean_apply_4(v_pureOnDidChange_3345_, v_p_3348_, v___x_3352_, v___y_3350_, lean_box(0));
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v_a_3354_; lean_object* v_snd_3355_; lean_object* v___x_3356_; 
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
lean_inc(v_a_3354_);
lean_dec_ref_known(v___x_3353_, 1);
v_snd_3355_ = lean_ctor_get(v_a_3354_, 1);
lean_inc(v_snd_3355_);
lean_dec(v_a_3354_);
v___x_3356_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_3346_, v_snd_3355_, v_inst_3344_);
lean_dec(v_inst_3344_);
lean_dec(v_snd_3355_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; lean_object* v___x_3358_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_a_3357_);
lean_dec_ref_known(v___x_3356_, 1);
lean_inc_ref(v___y_3350_);
v___x_3358_ = lean_apply_4(v_onDidChange_3347_, v_p_3348_, v_a_3357_, v___y_3350_, lean_box(0));
if (lean_obj_tag(v___x_3358_) == 0)
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3376_; 
v_a_3359_ = lean_ctor_get(v___x_3358_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3361_ = v___x_3358_;
v_isShared_3362_ = v_isSharedCheck_3376_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3358_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3376_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v_snd_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3374_; 
v_snd_3363_ = lean_ctor_get(v_a_3359_, 1);
v_isSharedCheck_3374_ = !lean_is_exclusive(v_a_3359_);
if (v_isSharedCheck_3374_ == 0)
{
lean_object* v_unused_3375_; 
v_unused_3375_ = lean_ctor_get(v_a_3359_, 0);
lean_dec(v_unused_3375_);
v___x_3365_ = v_a_3359_;
v_isShared_3366_ = v_isSharedCheck_3374_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_snd_3363_);
lean_dec(v_a_3359_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3374_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3367_; lean_object* v___x_3369_; 
v___x_3367_ = lean_box(0);
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 0, v___x_3367_);
v___x_3369_ = v___x_3365_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3367_);
lean_ctor_set(v_reuseFailAlloc_3373_, 1, v_snd_3363_);
v___x_3369_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
lean_object* v___x_3371_; 
if (v_isShared_3362_ == 0)
{
lean_ctor_set(v___x_3361_, 0, v___x_3369_);
v___x_3371_ = v___x_3361_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3369_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
}
}
else
{
return v___x_3358_;
}
}
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
lean_dec_ref(v_p_3348_);
lean_dec_ref(v_onDidChange_3347_);
v_a_3377_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v___x_3356_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3356_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
else
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3392_; 
lean_dec_ref(v_p_3348_);
lean_dec_ref(v_onDidChange_3347_);
lean_dec(v_inst_3344_);
v_a_3385_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3387_ = v___x_3353_;
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3353_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3390_; 
if (v_isShared_3388_ == 0)
{
v___x_3390_ = v___x_3387_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_a_3385_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object* v_inst_3393_, lean_object* v_pureOnDidChange_3394_, lean_object* v_method_3395_, lean_object* v_onDidChange_3396_, lean_object* v_p_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0(v_inst_3393_, v_pureOnDidChange_3394_, v_method_3395_, v_onDidChange_3396_, v_p_3397_, v___y_3398_, v___y_3399_);
lean_dec_ref(v___y_3399_);
lean_dec_ref(v_method_3395_);
return v_res_3401_;
}
}
static lean_object* _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3403_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__0));
v___x_3404_ = l_Lean_Server_RequestError_internalError(v___x_3403_);
return v___x_3404_;
}
}
static lean_object* _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3406_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__2));
v___x_3407_ = l_Lean_Server_RequestError_internalError(v___x_3406_);
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1(lean_object* v_inst_3408_, lean_object* v_inst_3409_, lean_object* v_pureHandle_3410_, lean_object* v_inst_3411_, lean_object* v_method_3412_, lean_object* v_handler_3413_, lean_object* v_p_3414_, lean_object* v_s_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
lean_inc(v_p_3414_);
v___x_3418_ = lean_apply_1(v_inst_3408_, v_p_3414_);
lean_inc(v_inst_3409_);
v___x_3419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3419_, 0, v_inst_3409_);
lean_ctor_set(v___x_3419_, 1, v_s_3415_);
lean_inc_ref(v___y_3416_);
v___x_3420_ = lean_apply_4(v_pureHandle_3410_, v___x_3418_, v___x_3419_, v___y_3416_, lean_box(0));
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3455_; 
v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3423_ = v___x_3420_;
v_isShared_3424_ = v_isSharedCheck_3455_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v___x_3420_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3455_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v_fst_3425_; lean_object* v_snd_3426_; lean_object* v_response_x3f_3427_; lean_object* v_serialized_3428_; uint8_t v_isComplete_3429_; lean_object* v_a_3431_; 
v_fst_3425_ = lean_ctor_get(v_a_3421_, 0);
lean_inc(v_fst_3425_);
v_snd_3426_ = lean_ctor_get(v_a_3421_, 1);
lean_inc(v_snd_3426_);
lean_dec(v_a_3421_);
v_response_x3f_3427_ = lean_ctor_get(v_fst_3425_, 0);
lean_inc(v_response_x3f_3427_);
v_serialized_3428_ = lean_ctor_get(v_fst_3425_, 1);
lean_inc_ref(v_serialized_3428_);
v_isComplete_3429_ = lean_ctor_get_uint8(v_fst_3425_, sizeof(void*)*2);
lean_dec(v_fst_3425_);
if (lean_obj_tag(v_response_x3f_3427_) == 0)
{
lean_object* v___x_3450_; 
v___x_3450_ = l_Lean_Json_parse(v_serialized_3428_);
if (lean_obj_tag(v___x_3450_) == 1)
{
lean_object* v_a_3451_; 
v_a_3451_ = lean_ctor_get(v___x_3450_, 0);
lean_inc(v_a_3451_);
lean_dec_ref_known(v___x_3450_, 1);
v_a_3431_ = v_a_3451_;
goto v___jp_3430_;
}
else
{
lean_object* v___x_3452_; lean_object* v___x_3453_; 
lean_dec_ref(v___x_3450_);
lean_dec(v_snd_3426_);
lean_del_object(v___x_3423_);
lean_dec(v_p_3414_);
lean_dec_ref(v_handler_3413_);
lean_dec_ref(v_inst_3411_);
lean_dec(v_inst_3409_);
v___x_3452_ = lean_obj_once(&l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3, &l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3_once, _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3);
v___x_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3452_);
return v___x_3453_;
}
}
else
{
lean_object* v_val_3454_; 
lean_dec_ref(v_serialized_3428_);
v_val_3454_ = lean_ctor_get(v_response_x3f_3427_, 0);
lean_inc(v_val_3454_);
lean_dec_ref_known(v_response_x3f_3427_, 1);
v_a_3431_ = v_val_3454_;
goto v___jp_3430_;
}
v___jp_3430_:
{
lean_object* v___x_3432_; 
v___x_3432_ = lean_apply_1(v_inst_3411_, v_a_3431_);
if (lean_obj_tag(v___x_3432_) == 1)
{
lean_object* v_a_3433_; lean_object* v___x_3434_; 
lean_del_object(v___x_3423_);
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
lean_inc(v_a_3433_);
lean_dec_ref_known(v___x_3432_, 1);
v___x_3434_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_3412_, v_snd_3426_, v_inst_3409_);
lean_dec(v_inst_3409_);
lean_dec(v_snd_3426_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_a_3435_);
lean_dec_ref_known(v___x_3434_, 1);
v___x_3436_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3436_, 0, v_a_3433_);
lean_ctor_set_uint8(v___x_3436_, sizeof(void*)*1, v_isComplete_3429_);
lean_inc_ref(v___y_3416_);
v___x_3437_ = lean_apply_5(v_handler_3413_, v_p_3414_, v___x_3436_, v_a_3435_, v___y_3416_, lean_box(0));
return v___x_3437_;
}
else
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
lean_dec(v_a_3433_);
lean_dec(v_p_3414_);
lean_dec_ref(v_handler_3413_);
v_a_3438_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3440_ = v___x_3434_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___x_3434_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3438_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
}
else
{
lean_object* v___x_3446_; lean_object* v___x_3448_; 
lean_dec_ref(v___x_3432_);
lean_dec(v_snd_3426_);
lean_dec(v_p_3414_);
lean_dec_ref(v_handler_3413_);
lean_dec(v_inst_3409_);
v___x_3446_ = lean_obj_once(&l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1, &l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1_once, _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1);
if (v_isShared_3424_ == 0)
{
lean_ctor_set_tag(v___x_3423_, 1);
lean_ctor_set(v___x_3423_, 0, v___x_3446_);
v___x_3448_ = v___x_3423_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3446_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
}
}
else
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3463_; 
lean_dec(v_p_3414_);
lean_dec_ref(v_handler_3413_);
lean_dec_ref(v_inst_3411_);
lean_dec(v_inst_3409_);
v_a_3456_ = lean_ctor_get(v___x_3420_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3458_ = v___x_3420_;
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3420_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3459_ == 0)
{
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3456_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___boxed(lean_object* v_inst_3464_, lean_object* v_inst_3465_, lean_object* v_pureHandle_3466_, lean_object* v_inst_3467_, lean_object* v_method_3468_, lean_object* v_handler_3469_, lean_object* v_p_3470_, lean_object* v_s_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_){
_start:
{
lean_object* v_res_3474_; 
v_res_3474_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1(v_inst_3464_, v_inst_3465_, v_pureHandle_3466_, v_inst_3467_, v_method_3468_, v_handler_3469_, v_p_3470_, v_s_3471_, v___y_3472_);
lean_dec_ref(v___y_3472_);
lean_dec_ref(v_method_3468_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg(lean_object* v_method_3476_, lean_object* v_inst_3477_, lean_object* v_inst_3478_, lean_object* v_inst_3479_, lean_object* v_inst_3480_, lean_object* v_inst_3481_, lean_object* v_inst_3482_, lean_object* v_handler_3483_, lean_object* v_onDidChange_3484_){
_start:
{
uint8_t v___x_3486_; 
v___x_3486_ = l_Lean_initializing();
if (v___x_3486_ == 0)
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
lean_dec_ref(v_onDidChange_3484_);
lean_dec_ref(v_handler_3483_);
lean_dec(v_inst_3482_);
lean_dec_ref(v_inst_3481_);
lean_dec_ref(v_inst_3480_);
lean_dec_ref(v_inst_3479_);
lean_dec_ref(v_inst_3478_);
lean_dec_ref(v_inst_3477_);
v___x_3487_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0));
v___x_3488_ = lean_string_append(v___x_3487_, v_method_3476_);
lean_dec_ref(v_method_3476_);
v___x_3489_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__1));
v___x_3490_ = lean_string_append(v___x_3488_, v___x_3489_);
v___x_3491_ = lean_mk_io_user_error(v___x_3490_);
v___x_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3491_);
return v___x_3492_;
}
else
{
lean_object* v___x_3493_; 
v___x_3493_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_3476_);
if (lean_obj_tag(v___x_3493_) == 1)
{
lean_object* v_val_3494_; lean_object* v_pureHandle_3495_; lean_object* v_pureOnDidChange_3496_; lean_object* v_initState_3497_; lean_object* v_completeness_3498_; lean_object* v___x_3499_; 
v_val_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_val_3494_);
lean_dec_ref_known(v___x_3493_, 1);
v_pureHandle_3495_ = lean_ctor_get(v_val_3494_, 1);
lean_inc_ref(v_pureHandle_3495_);
v_pureOnDidChange_3496_ = lean_ctor_get(v_val_3494_, 3);
lean_inc_ref(v_pureOnDidChange_3496_);
v_initState_3497_ = lean_ctor_get(v_val_3494_, 6);
lean_inc(v_initState_3497_);
v_completeness_3498_ = lean_ctor_get(v_val_3494_, 8);
lean_inc(v_completeness_3498_);
lean_dec(v_val_3494_);
v___x_3499_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(v_method_3476_, v_initState_3497_, v_inst_3482_);
lean_dec(v_initState_3497_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_a_3500_; lean_object* v___f_3501_; lean_object* v___f_3502_; lean_object* v___x_3503_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_a_3500_);
lean_dec_ref_known(v___x_3499_, 1);
lean_inc_ref_n(v_method_3476_, 2);
lean_inc_n(v_inst_3482_, 2);
v___f_3501_ = lean_alloc_closure((void*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_3501_, 0, v_inst_3482_);
lean_closure_set(v___f_3501_, 1, v_pureOnDidChange_3496_);
lean_closure_set(v___f_3501_, 2, v_method_3476_);
lean_closure_set(v___f_3501_, 3, v_onDidChange_3484_);
v___f_3502_ = lean_alloc_closure((void*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___boxed), 10, 6);
lean_closure_set(v___f_3502_, 0, v_inst_3478_);
lean_closure_set(v___f_3502_, 1, v_inst_3482_);
lean_closure_set(v___f_3502_, 2, v_pureHandle_3495_);
lean_closure_set(v___f_3502_, 3, v_inst_3480_);
lean_closure_set(v___f_3502_, 4, v_method_3476_);
lean_closure_set(v___f_3502_, 5, v_handler_3483_);
v___x_3503_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_3476_, v_completeness_3498_, v_inst_3477_, v_inst_3479_, v_inst_3481_, v_inst_3482_, v_a_3500_, v___f_3502_, v___f_3501_);
return v___x_3503_;
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3511_; 
lean_dec(v_completeness_3498_);
lean_dec_ref(v_pureOnDidChange_3496_);
lean_dec_ref(v_pureHandle_3495_);
lean_dec_ref(v_onDidChange_3484_);
lean_dec_ref(v_handler_3483_);
lean_dec(v_inst_3482_);
lean_dec_ref(v_inst_3481_);
lean_dec_ref(v_inst_3480_);
lean_dec_ref(v_inst_3479_);
lean_dec_ref(v_inst_3478_);
lean_dec_ref(v_inst_3477_);
lean_dec_ref(v_method_3476_);
v_a_3504_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3506_ = v___x_3499_;
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3499_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3509_; 
if (v_isShared_3507_ == 0)
{
v___x_3509_ = v___x_3506_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3504_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
}
else
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
lean_dec(v___x_3493_);
lean_dec_ref(v_onDidChange_3484_);
lean_dec_ref(v_handler_3483_);
lean_dec(v_inst_3482_);
lean_dec_ref(v_inst_3481_);
lean_dec_ref(v_inst_3480_);
lean_dec_ref(v_inst_3479_);
lean_dec_ref(v_inst_3478_);
lean_dec_ref(v_inst_3477_);
v___x_3512_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0));
v___x_3513_ = lean_string_append(v___x_3512_, v_method_3476_);
lean_dec_ref(v_method_3476_);
v___x_3514_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__1));
v___x_3515_ = lean_string_append(v___x_3513_, v___x_3514_);
v___x_3516_ = lean_mk_io_user_error(v___x_3515_);
v___x_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3516_);
return v___x_3517_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_3518_, lean_object* v_inst_3519_, lean_object* v_inst_3520_, lean_object* v_inst_3521_, lean_object* v_inst_3522_, lean_object* v_inst_3523_, lean_object* v_inst_3524_, lean_object* v_handler_3525_, lean_object* v_onDidChange_3526_, lean_object* v_a_3527_){
_start:
{
lean_object* v_res_3528_; 
v_res_3528_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg(v_method_3518_, v_inst_3519_, v_inst_3520_, v_inst_3521_, v_inst_3522_, v_inst_3523_, v_inst_3524_, v_handler_3525_, v_onDidChange_3526_);
return v_res_3528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler(lean_object* v_method_3529_, lean_object* v_paramType_3530_, lean_object* v_inst_3531_, lean_object* v_inst_3532_, lean_object* v_inst_3533_, lean_object* v_respType_3534_, lean_object* v_inst_3535_, lean_object* v_inst_3536_, lean_object* v_stateType_3537_, lean_object* v_inst_3538_, lean_object* v_handler_3539_, lean_object* v_onDidChange_3540_){
_start:
{
lean_object* v___x_3542_; 
v___x_3542_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg(v_method_3529_, v_inst_3531_, v_inst_3532_, v_inst_3533_, v_inst_3535_, v_inst_3536_, v_inst_3538_, v_handler_3539_, v_onDidChange_3540_);
return v___x_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___boxed(lean_object* v_method_3543_, lean_object* v_paramType_3544_, lean_object* v_inst_3545_, lean_object* v_inst_3546_, lean_object* v_inst_3547_, lean_object* v_respType_3548_, lean_object* v_inst_3549_, lean_object* v_inst_3550_, lean_object* v_stateType_3551_, lean_object* v_inst_3552_, lean_object* v_handler_3553_, lean_object* v_onDidChange_3554_, lean_object* v_a_3555_){
_start:
{
lean_object* v_res_3556_; 
v_res_3556_ = l_Lean_Server_chainStatefulLspRequestHandler(v_method_3543_, v_paramType_3544_, v_inst_3545_, v_inst_3546_, v_inst_3547_, v_respType_3548_, v_inst_3549_, v_inst_3550_, v_stateType_3551_, v_inst_3552_, v_handler_3553_, v_onDidChange_3554_);
return v_res_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___lam__0(lean_object* v_p_3557_, lean_object* v_x_3558_, lean_object* v_handler_3559_, lean_object* v___y_3560_){
_start:
{
lean_object* v_onDidChange_3562_; lean_object* v___x_3563_; 
v_onDidChange_3562_ = lean_ctor_get(v_handler_3559_, 4);
lean_inc_ref(v_onDidChange_3562_);
lean_dec_ref(v_handler_3559_);
lean_inc_ref(v___y_3560_);
v___x_3563_ = lean_apply_3(v_onDidChange_3562_, v_p_3557_, v___y_3560_, lean_box(0));
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___lam__0___boxed(lean_object* v_p_3564_, lean_object* v_x_3565_, lean_object* v_handler_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l_Lean_Server_handleOnDidChange___lam__0(v_p_3564_, v_x_3565_, v_handler_3566_, v___y_3567_);
lean_dec_ref(v___y_3567_);
lean_dec_ref(v_x_3565_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0(lean_object* v_f_3570_, lean_object* v_x_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
lean_object* v___x_3576_; 
lean_inc_ref(v___y_3574_);
v___x_3576_ = lean_apply_4(v_f_3570_, v___y_3572_, v___y_3573_, v___y_3574_, lean_box(0));
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0___boxed(lean_object* v_f_3577_, lean_object* v_x_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_){
_start:
{
lean_object* v_res_3583_; 
v_res_3583_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0(v_f_3577_, v_x_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
lean_dec_ref(v___y_3581_);
return v_res_3583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_3584_, lean_object* v_keys_3585_, lean_object* v_vals_3586_, lean_object* v_i_3587_, lean_object* v_acc_3588_, lean_object* v___y_3589_){
_start:
{
lean_object* v___x_3591_; uint8_t v___x_3592_; 
v___x_3591_ = lean_array_get_size(v_keys_3585_);
v___x_3592_ = lean_nat_dec_lt(v_i_3587_, v___x_3591_);
if (v___x_3592_ == 0)
{
lean_object* v___x_3593_; 
lean_dec(v_i_3587_);
lean_dec_ref(v_f_3584_);
v___x_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3593_, 0, v_acc_3588_);
return v___x_3593_;
}
else
{
lean_object* v_k_3594_; lean_object* v_v_3595_; lean_object* v___x_3596_; 
v_k_3594_ = lean_array_fget_borrowed(v_keys_3585_, v_i_3587_);
v_v_3595_ = lean_array_fget_borrowed(v_vals_3586_, v_i_3587_);
lean_inc_ref(v_f_3584_);
lean_inc_ref(v___y_3589_);
lean_inc(v_v_3595_);
lean_inc(v_k_3594_);
v___x_3596_ = lean_apply_5(v_f_3584_, v_acc_3588_, v_k_3594_, v_v_3595_, v___y_3589_, lean_box(0));
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v_a_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
lean_inc(v_a_3597_);
lean_dec_ref_known(v___x_3596_, 1);
v___x_3598_ = lean_unsigned_to_nat(1u);
v___x_3599_ = lean_nat_add(v_i_3587_, v___x_3598_);
lean_dec(v_i_3587_);
v_i_3587_ = v___x_3599_;
v_acc_3588_ = v_a_3597_;
goto _start;
}
else
{
lean_dec(v_i_3587_);
lean_dec_ref(v_f_3584_);
return v___x_3596_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_3601_, lean_object* v_keys_3602_, lean_object* v_vals_3603_, lean_object* v_i_3604_, lean_object* v_acc_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
lean_object* v_res_3608_; 
v_res_3608_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3601_, v_keys_3602_, v_vals_3603_, v_i_3604_, v_acc_3605_, v___y_3606_);
lean_dec_ref(v___y_3606_);
lean_dec_ref(v_vals_3603_);
lean_dec_ref(v_keys_3602_);
return v_res_3608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(lean_object* v_f_3609_, lean_object* v_x_3610_, lean_object* v_x_3611_, lean_object* v___y_3612_){
_start:
{
if (lean_obj_tag(v_x_3610_) == 0)
{
lean_object* v_es_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3634_; 
v_es_3614_ = lean_ctor_get(v_x_3610_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v_x_3610_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3616_ = v_x_3610_;
v_isShared_3617_ = v_isSharedCheck_3634_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_es_3614_);
lean_dec(v_x_3610_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3634_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; uint8_t v___x_3620_; 
v___x_3618_ = lean_unsigned_to_nat(0u);
v___x_3619_ = lean_array_get_size(v_es_3614_);
v___x_3620_ = lean_nat_dec_lt(v___x_3618_, v___x_3619_);
if (v___x_3620_ == 0)
{
lean_object* v___x_3622_; 
lean_dec_ref(v_es_3614_);
lean_dec_ref(v_f_3609_);
if (v_isShared_3617_ == 0)
{
lean_ctor_set(v___x_3616_, 0, v_x_3611_);
v___x_3622_ = v___x_3616_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_x_3611_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
else
{
uint8_t v___x_3624_; 
v___x_3624_ = lean_nat_dec_le(v___x_3619_, v___x_3619_);
if (v___x_3624_ == 0)
{
if (v___x_3620_ == 0)
{
lean_object* v___x_3626_; 
lean_dec_ref(v_es_3614_);
lean_dec_ref(v_f_3609_);
if (v_isShared_3617_ == 0)
{
lean_ctor_set(v___x_3616_, 0, v_x_3611_);
v___x_3626_ = v___x_3616_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_x_3611_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
else
{
size_t v___x_3628_; size_t v___x_3629_; lean_object* v___x_3630_; 
lean_del_object(v___x_3616_);
v___x_3628_ = ((size_t)0ULL);
v___x_3629_ = lean_usize_of_nat(v___x_3619_);
v___x_3630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3609_, v_es_3614_, v___x_3628_, v___x_3629_, v_x_3611_, v___y_3612_);
lean_dec_ref(v_es_3614_);
return v___x_3630_;
}
}
else
{
size_t v___x_3631_; size_t v___x_3632_; lean_object* v___x_3633_; 
lean_del_object(v___x_3616_);
v___x_3631_ = ((size_t)0ULL);
v___x_3632_ = lean_usize_of_nat(v___x_3619_);
v___x_3633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3609_, v_es_3614_, v___x_3631_, v___x_3632_, v_x_3611_, v___y_3612_);
lean_dec_ref(v_es_3614_);
return v___x_3633_;
}
}
}
}
else
{
lean_object* v_ks_3635_; lean_object* v_vs_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v_ks_3635_ = lean_ctor_get(v_x_3610_, 0);
lean_inc_ref(v_ks_3635_);
v_vs_3636_ = lean_ctor_get(v_x_3610_, 1);
lean_inc_ref(v_vs_3636_);
lean_dec_ref_known(v_x_3610_, 2);
v___x_3637_ = lean_unsigned_to_nat(0u);
v___x_3638_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3609_, v_ks_3635_, v_vs_3636_, v___x_3637_, v_x_3611_, v___y_3612_);
lean_dec_ref(v_vs_3636_);
lean_dec_ref(v_ks_3635_);
return v___x_3638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_3639_, lean_object* v_as_3640_, size_t v_i_3641_, size_t v_stop_3642_, lean_object* v_b_3643_, lean_object* v___y_3644_){
_start:
{
lean_object* v_a_3647_; lean_object* v___y_3652_; uint8_t v___x_3654_; 
v___x_3654_ = lean_usize_dec_eq(v_i_3641_, v_stop_3642_);
if (v___x_3654_ == 0)
{
lean_object* v___x_3655_; 
v___x_3655_ = lean_array_uget_borrowed(v_as_3640_, v_i_3641_);
switch(lean_obj_tag(v___x_3655_))
{
case 0:
{
lean_object* v_key_3656_; lean_object* v_val_3657_; lean_object* v___x_3658_; 
v_key_3656_ = lean_ctor_get(v___x_3655_, 0);
v_val_3657_ = lean_ctor_get(v___x_3655_, 1);
lean_inc_ref(v_f_3639_);
lean_inc_ref(v___y_3644_);
lean_inc(v_val_3657_);
lean_inc(v_key_3656_);
v___x_3658_ = lean_apply_5(v_f_3639_, v_b_3643_, v_key_3656_, v_val_3657_, v___y_3644_, lean_box(0));
v___y_3652_ = v___x_3658_;
goto v___jp_3651_;
}
case 1:
{
lean_object* v_node_3659_; lean_object* v___x_3660_; 
v_node_3659_ = lean_ctor_get(v___x_3655_, 0);
lean_inc(v_node_3659_);
lean_inc_ref(v_f_3639_);
v___x_3660_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3639_, v_node_3659_, v_b_3643_, v___y_3644_);
v___y_3652_ = v___x_3660_;
goto v___jp_3651_;
}
default: 
{
v_a_3647_ = v_b_3643_;
goto v___jp_3646_;
}
}
}
else
{
lean_object* v___x_3661_; 
lean_dec_ref(v_f_3639_);
v___x_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3661_, 0, v_b_3643_);
return v___x_3661_;
}
v___jp_3646_:
{
size_t v___x_3648_; size_t v___x_3649_; 
v___x_3648_ = ((size_t)1ULL);
v___x_3649_ = lean_usize_add(v_i_3641_, v___x_3648_);
v_i_3641_ = v___x_3649_;
v_b_3643_ = v_a_3647_;
goto _start;
}
v___jp_3651_:
{
if (lean_obj_tag(v___y_3652_) == 0)
{
lean_object* v_a_3653_; 
v_a_3653_ = lean_ctor_get(v___y_3652_, 0);
lean_inc(v_a_3653_);
lean_dec_ref_known(v___y_3652_, 1);
v_a_3647_ = v_a_3653_;
goto v___jp_3646_;
}
else
{
lean_dec_ref(v_f_3639_);
return v___y_3652_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_3662_, lean_object* v_as_3663_, lean_object* v_i_3664_, lean_object* v_stop_3665_, lean_object* v_b_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_){
_start:
{
size_t v_i_boxed_3669_; size_t v_stop_boxed_3670_; lean_object* v_res_3671_; 
v_i_boxed_3669_ = lean_unbox_usize(v_i_3664_);
lean_dec(v_i_3664_);
v_stop_boxed_3670_ = lean_unbox_usize(v_stop_3665_);
lean_dec(v_stop_3665_);
v_res_3671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3662_, v_as_3663_, v_i_boxed_3669_, v_stop_boxed_3670_, v_b_3666_, v___y_3667_);
lean_dec_ref(v___y_3667_);
lean_dec_ref(v_as_3663_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_3672_, lean_object* v_x_3673_, lean_object* v_x_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_){
_start:
{
lean_object* v_res_3677_; 
v_res_3677_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3672_, v_x_3673_, v_x_3674_, v___y_3675_);
lean_dec_ref(v___y_3675_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(lean_object* v_map_3678_, lean_object* v_f_3679_, lean_object* v___y_3680_){
_start:
{
lean_object* v___f_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; 
v___f_3682_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3682_, 0, v_f_3679_);
v___x_3683_ = lean_box(0);
v___x_3684_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v___f_3682_, v_map_3678_, v___x_3683_, v___y_3680_);
return v___x_3684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___boxed(lean_object* v_map_3685_, lean_object* v_f_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(v_map_3685_, v_f_3686_, v___y_3687_);
lean_dec_ref(v___y_3687_);
return v_res_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange(lean_object* v_p_3690_, lean_object* v_a_3691_){
_start:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___f_3695_; lean_object* v___x_3696_; 
v___x_3693_ = l_Lean_Server_statefulRequestHandlers;
v___x_3694_ = lean_st_ref_get(v___x_3693_);
v___f_3695_ = lean_alloc_closure((void*)(l_Lean_Server_handleOnDidChange___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3695_, 0, v_p_3690_);
v___x_3696_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(v___x_3694_, v___f_3695_, v_a_3691_);
return v___x_3696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___boxed(lean_object* v_p_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_){
_start:
{
lean_object* v_res_3700_; 
v_res_3700_ = l_Lean_Server_handleOnDidChange(v_p_3697_, v_a_3698_);
lean_dec_ref(v_a_3698_);
return v_res_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0(lean_object* v_00_u03b2_3701_, lean_object* v_map_3702_, lean_object* v_f_3703_, lean_object* v___y_3704_){
_start:
{
lean_object* v___x_3706_; 
v___x_3706_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(v_map_3702_, v_f_3703_, v___y_3704_);
return v___x_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___boxed(lean_object* v_00_u03b2_3707_, lean_object* v_map_3708_, lean_object* v_f_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_){
_start:
{
lean_object* v_res_3712_; 
v_res_3712_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0(v_00_u03b2_3707_, v_map_3708_, v_f_3709_, v___y_3710_);
lean_dec_ref(v___y_3710_);
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg(lean_object* v_map_3713_, lean_object* v_f_3714_, lean_object* v_init_3715_, lean_object* v___y_3716_){
_start:
{
lean_object* v___x_3718_; 
v___x_3718_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3714_, v_map_3713_, v_init_3715_, v___y_3716_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg___boxed(lean_object* v_map_3719_, lean_object* v_f_3720_, lean_object* v_init_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_){
_start:
{
lean_object* v_res_3724_; 
v_res_3724_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg(v_map_3719_, v_f_3720_, v_init_3721_, v___y_3722_);
lean_dec_ref(v___y_3722_);
return v_res_3724_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0(lean_object* v_00_u03c3_3725_, lean_object* v_00_u03b2_3726_, lean_object* v_map_3727_, lean_object* v_f_3728_, lean_object* v_init_3729_, lean_object* v___y_3730_){
_start:
{
lean_object* v___x_3732_; 
v___x_3732_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3728_, v_map_3727_, v_init_3729_, v___y_3730_);
return v___x_3732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3733_, lean_object* v_00_u03b2_3734_, lean_object* v_map_3735_, lean_object* v_f_3736_, lean_object* v_init_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0(v_00_u03c3_3733_, v_00_u03b2_3734_, v_map_3735_, v_f_3736_, v_init_3737_, v___y_3738_);
lean_dec_ref(v___y_3738_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3741_, lean_object* v_00_u03b1_3742_, lean_object* v_00_u03b2_3743_, lean_object* v_f_3744_, lean_object* v_x_3745_, lean_object* v_x_3746_, lean_object* v___y_3747_){
_start:
{
lean_object* v___x_3749_; 
v___x_3749_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3744_, v_x_3745_, v_x_3746_, v___y_3747_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3750_, lean_object* v_00_u03b1_3751_, lean_object* v_00_u03b2_3752_, lean_object* v_f_3753_, lean_object* v_x_3754_, lean_object* v_x_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
lean_object* v_res_3758_; 
v_res_3758_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1(v_00_u03c3_3750_, v_00_u03b1_3751_, v_00_u03b2_3752_, v_f_3753_, v_x_3754_, v_x_3755_, v___y_3756_);
lean_dec_ref(v___y_3756_);
return v_res_3758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3759_, lean_object* v_00_u03b2_3760_, lean_object* v_00_u03c3_3761_, lean_object* v_f_3762_, lean_object* v_as_3763_, size_t v_i_3764_, size_t v_stop_3765_, lean_object* v_b_3766_, lean_object* v___y_3767_){
_start:
{
lean_object* v___x_3769_; 
v___x_3769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3762_, v_as_3763_, v_i_3764_, v_stop_3765_, v_b_3766_, v___y_3767_);
return v___x_3769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3770_, lean_object* v_00_u03b2_3771_, lean_object* v_00_u03c3_3772_, lean_object* v_f_3773_, lean_object* v_as_3774_, lean_object* v_i_3775_, lean_object* v_stop_3776_, lean_object* v_b_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_){
_start:
{
size_t v_i_boxed_3780_; size_t v_stop_boxed_3781_; lean_object* v_res_3782_; 
v_i_boxed_3780_ = lean_unbox_usize(v_i_3775_);
lean_dec(v_i_3775_);
v_stop_boxed_3781_ = lean_unbox_usize(v_stop_3776_);
lean_dec(v_stop_3776_);
v_res_3782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3770_, v_00_u03b2_3771_, v_00_u03c3_3772_, v_f_3773_, v_as_3774_, v_i_boxed_3780_, v_stop_boxed_3781_, v_b_3777_, v___y_3778_);
lean_dec_ref(v___y_3778_);
lean_dec_ref(v_as_3774_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3783_, lean_object* v_00_u03b1_3784_, lean_object* v_00_u03b2_3785_, lean_object* v_f_3786_, lean_object* v_keys_3787_, lean_object* v_vals_3788_, lean_object* v_heq_3789_, lean_object* v_i_3790_, lean_object* v_acc_3791_, lean_object* v___y_3792_){
_start:
{
lean_object* v___x_3794_; 
v___x_3794_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3786_, v_keys_3787_, v_vals_3788_, v_i_3790_, v_acc_3791_, v___y_3792_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3795_, lean_object* v_00_u03b1_3796_, lean_object* v_00_u03b2_3797_, lean_object* v_f_3798_, lean_object* v_keys_3799_, lean_object* v_vals_3800_, lean_object* v_heq_3801_, lean_object* v_i_3802_, lean_object* v_acc_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
lean_object* v_res_3806_; 
v_res_3806_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3795_, v_00_u03b1_3796_, v_00_u03b2_3797_, v_f_3798_, v_keys_3799_, v_vals_3800_, v_heq_3801_, v_i_3802_, v_acc_3803_, v___y_3804_);
lean_dec_ref(v___y_3804_);
lean_dec_ref(v_vals_3800_);
lean_dec_ref(v_keys_3799_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest(lean_object* v_method_3809_, lean_object* v_params_3810_, lean_object* v_a_3811_){
_start:
{
uint8_t v___x_3813_; 
v___x_3813_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_3809_);
if (v___x_3813_ == 0)
{
lean_object* v___x_3814_; lean_object* v_a_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3830_; 
v___x_3814_ = l_Lean_Server_lookupLspRequestHandler(v_method_3809_);
v_a_3815_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3817_ = v___x_3814_;
v_isShared_3818_ = v_isSharedCheck_3830_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_a_3815_);
lean_dec(v___x_3814_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3830_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
if (lean_obj_tag(v_a_3815_) == 0)
{
lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3825_; 
lean_dec(v_params_3810_);
v___x_3819_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__0));
v___x_3820_ = lean_string_append(v___x_3819_, v_method_3809_);
v___x_3821_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__1));
v___x_3822_ = lean_string_append(v___x_3820_, v___x_3821_);
v___x_3823_ = l_Lean_Server_RequestError_internalError(v___x_3822_);
if (v_isShared_3818_ == 0)
{
lean_ctor_set_tag(v___x_3817_, 1);
lean_ctor_set(v___x_3817_, 0, v___x_3823_);
v___x_3825_ = v___x_3817_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v___x_3823_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
else
{
lean_object* v_val_3827_; lean_object* v_handle_3828_; lean_object* v___x_3829_; 
lean_del_object(v___x_3817_);
v_val_3827_ = lean_ctor_get(v_a_3815_, 0);
lean_inc(v_val_3827_);
lean_dec_ref_known(v_a_3815_, 1);
v_handle_3828_ = lean_ctor_get(v_val_3827_, 1);
lean_inc_ref(v_handle_3828_);
lean_dec(v_val_3827_);
lean_inc_ref(v_a_3811_);
v___x_3829_ = lean_apply_3(v_handle_3828_, v_params_3810_, v_a_3811_, lean_box(0));
return v___x_3829_;
}
}
}
else
{
lean_object* v___x_3831_; 
v___x_3831_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_3809_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; 
lean_dec(v_params_3810_);
v___x_3832_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__0));
v___x_3833_ = lean_string_append(v___x_3832_, v_method_3809_);
v___x_3834_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__1));
v___x_3835_ = lean_string_append(v___x_3833_, v___x_3834_);
v___x_3836_ = l_Lean_Server_RequestError_internalError(v___x_3835_);
v___x_3837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3837_, 0, v___x_3836_);
return v___x_3837_;
}
else
{
lean_object* v_val_3838_; lean_object* v_handle_3839_; lean_object* v___x_3840_; 
v_val_3838_ = lean_ctor_get(v___x_3831_, 0);
lean_inc(v_val_3838_);
lean_dec_ref_known(v___x_3831_, 1);
v_handle_3839_ = lean_ctor_get(v_val_3838_, 2);
lean_inc_ref(v_handle_3839_);
lean_dec(v_val_3838_);
lean_inc_ref(v_a_3811_);
v___x_3840_ = lean_apply_3(v_handle_3839_, v_params_3810_, v_a_3811_, lean_box(0));
return v___x_3840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest___boxed(lean_object* v_method_3841_, lean_object* v_params_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_){
_start:
{
lean_object* v_res_3845_; 
v_res_3845_ = l_Lean_Server_handleLspRequest(v_method_3841_, v_params_3842_, v_a_3843_);
lean_dec_ref(v_a_3843_);
lean_dec_ref(v_method_3841_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_routeLspRequest(lean_object* v_method_3846_, lean_object* v_params_3847_){
_start:
{
uint8_t v___x_3849_; 
v___x_3849_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_3846_);
if (v___x_3849_ == 0)
{
lean_object* v___x_3850_; lean_object* v_a_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3866_; 
v___x_3850_ = l_Lean_Server_lookupLspRequestHandler(v_method_3846_);
v_a_3851_ = lean_ctor_get(v___x_3850_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3850_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3853_ = v___x_3850_;
v_isShared_3854_ = v_isSharedCheck_3866_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_a_3851_);
lean_dec(v___x_3850_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3866_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
if (lean_obj_tag(v_a_3851_) == 0)
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3858_; 
lean_dec(v_params_3847_);
v___x_3855_ = l_Lean_Server_RequestError_methodNotFound(v_method_3846_);
v___x_3856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3856_, 0, v___x_3855_);
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 0, v___x_3856_);
v___x_3858_ = v___x_3853_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v___x_3856_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
else
{
lean_object* v_val_3860_; lean_object* v_fileSource_3861_; lean_object* v___x_3862_; lean_object* v___x_3864_; 
v_val_3860_ = lean_ctor_get(v_a_3851_, 0);
lean_inc(v_val_3860_);
lean_dec_ref_known(v_a_3851_, 1);
v_fileSource_3861_ = lean_ctor_get(v_val_3860_, 0);
lean_inc_ref(v_fileSource_3861_);
lean_dec(v_val_3860_);
v___x_3862_ = lean_apply_1(v_fileSource_3861_, v_params_3847_);
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 0, v___x_3862_);
v___x_3864_ = v___x_3853_;
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
else
{
lean_object* v___x_3867_; 
v___x_3867_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_3846_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
lean_dec(v_params_3847_);
v___x_3868_ = l_Lean_Server_RequestError_methodNotFound(v_method_3846_);
v___x_3869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3868_);
v___x_3870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3869_);
return v___x_3870_;
}
else
{
lean_object* v_val_3871_; lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3880_; 
v_val_3871_ = lean_ctor_get(v___x_3867_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3873_ = v___x_3867_;
v_isShared_3874_ = v_isSharedCheck_3880_;
goto v_resetjp_3872_;
}
else
{
lean_inc(v_val_3871_);
lean_dec(v___x_3867_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3880_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
lean_object* v_fileSource_3875_; lean_object* v___x_3876_; lean_object* v___x_3878_; 
v_fileSource_3875_ = lean_ctor_get(v_val_3871_, 0);
lean_inc_ref(v_fileSource_3875_);
lean_dec(v_val_3871_);
v___x_3876_ = lean_apply_1(v_fileSource_3875_, v_params_3847_);
if (v_isShared_3874_ == 0)
{
lean_ctor_set_tag(v___x_3873_, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3876_);
v___x_3878_ = v___x_3873_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v___x_3876_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_routeLspRequest___boxed(lean_object* v_method_3881_, lean_object* v_params_3882_, lean_object* v_a_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l_Lean_Server_routeLspRequest(v_method_3881_, v_params_3882_);
lean_dec_ref(v_method_3881_);
return v_res_3884_;
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
