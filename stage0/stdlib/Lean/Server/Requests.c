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
uint8_t lean_bool_not(uint8_t);
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
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_Range_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Lean_Server_ServerTask_bindCheap___redArg(lean_object*, lean_object*);
lean_object* l_instMonadFinallyEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_tryFinally___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
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
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_registerLspRequestHandler___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerLspRequestHandler___redArg___closed__0 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Server_registerLspRequestHandler___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerLspRequestHandler___redArg___closed__1;
static const lean_string_object l_Lean_Server_registerLspRequestHandler___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Failed to register LSP request handler for '"};
static const lean_object* l_Lean_Server_registerLspRequestHandler___redArg___closed__2 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___redArg___closed__2_value;
static const lean_string_object l_Lean_Server_registerLspRequestHandler___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "': already registered"};
static const lean_object* l_Lean_Server_registerLspRequestHandler___redArg___closed__3 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___redArg___closed__3_value;
static const lean_string_object l_Lean_Server_registerLspRequestHandler___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "': only possible during initialization"};
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
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__1(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftBaseIOEIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__4 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3_value),((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__4_value)} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__5 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__5_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__5_value),((lean_object*)&l_Lean_Server_instMonadLiftEIOExceptionRequestM___closed__0_value)} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__6 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__6_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadFinallyEIO___aux__1___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__7 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__7_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_tryFinally___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__7_value)} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__8 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__8_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__9 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__9_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3_value),((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__9_value)} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__10 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__10_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__10_value),((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__4_value)} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__11 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__11_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__11_value),((lean_object*)&l_Lean_Server_instMonadLiftEIOExceptionRequestM___closed__0_value)} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__12 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__12_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__13 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__13_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__14 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__14_value;
static const lean_string_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "Failed to register stateful LSP request handler for '"};
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
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__2(lean_object* v_head_123_, lean_object* v_f_124_, lean_object* v___f_125_, lean_object* v_tail_126_, lean_object* v_x_127_){
_start:
{
lean_object* v_snd_128_; 
v_snd_128_ = lean_ctor_get(v_x_127_, 1);
if (lean_obj_tag(v_snd_128_) == 1)
{
lean_object* v_fst_129_; uint8_t v_foldChildren_130_; uint8_t v___x_131_; 
lean_inc_ref(v_snd_128_);
v_fst_129_ = lean_ctor_get(v_x_127_, 0);
lean_inc(v_fst_129_);
lean_dec_ref(v_x_127_);
v_foldChildren_130_ = lean_ctor_get_uint8(v_snd_128_, 0);
lean_dec_ref_known(v_snd_128_, 0);
v___x_131_ = lean_bool_not(v_foldChildren_130_);
if (v___x_131_ == 0)
{
lean_object* v_task_132_; lean_object* v___f_133_; lean_object* v_subtreeTask_134_; lean_object* v___x_135_; 
lean_dec(v_tail_126_);
v_task_132_ = lean_ctor_get(v_head_123_, 3);
lean_inc_ref(v_task_132_);
lean_dec_ref(v_head_123_);
v___f_133_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_133_, 0, v_f_124_);
lean_closure_set(v___f_133_, 1, v_fst_129_);
v_subtreeTask_134_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_task_132_, v___f_133_);
v___x_135_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_subtreeTask_134_, v___f_125_);
return v___x_135_;
}
else
{
lean_object* v___x_136_; 
lean_dec_ref(v___f_125_);
lean_dec_ref(v_head_123_);
v___x_136_ = l___private_Lean_Server_Requests_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(v_f_124_, v_fst_129_, v_tail_126_);
return v___x_136_;
}
}
else
{
lean_object* v_fst_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_147_; 
lean_dec(v_tail_126_);
lean_dec_ref(v___f_125_);
lean_dec_ref(v_f_124_);
lean_dec_ref(v_head_123_);
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
lean_closure_set(v___f_159_, 0, v_head_156_);
lean_closure_set(v___f_159_, 1, v_f_149_);
lean_closure_set(v___f_159_, 2, v___f_158_);
lean_closure_set(v___f_159_, 3, v_tail_157_);
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
uint8_t v___x_426__boxed_219_; lean_object* v_res_220_; 
v___x_426__boxed_219_ = lean_unbox(v___x_216_);
v_res_220_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0(v___x_426__boxed_219_, v___x_217_, v_tree_218_);
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
lean_object* v_val_236_; uint8_t v___x_237_; uint8_t v___x_238_; 
v_val_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_val_236_);
lean_dec_ref_known(v___x_235_, 1);
v___x_237_ = l_Lean_FileMap_rangeContainsHoverPos(v_text_225_, v_val_236_, v_hoverPos_226_, v_includeStop_227_);
lean_dec(v_val_236_);
v___x_238_ = lean_bool_not(v___x_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___f_240_; lean_object* v___x_241_; 
v___x_239_ = lean_box(v___x_234_);
v___f_240_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0___boxed), 3, 2);
lean_closure_set(v___f_240_, 0, v___x_239_);
lean_closure_set(v___f_240_, 1, v___x_228_);
v___x_241_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_240_, v_task_232_);
return v___x_241_;
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
lean_dec_ref(v_task_232_);
v___x_242_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0));
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_228_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = lean_task_pure(v___x_243_);
return v___x_244_;
}
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
lean_dec(v___x_235_);
lean_dec_ref(v_task_232_);
v___x_245_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1));
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_228_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
v___x_247_ = lean_task_pure(v___x_246_);
return v___x_247_;
}
}
else
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec(v_stx_x3f_231_);
lean_dec_ref(v_snap_229_);
v___x_248_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0));
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_228_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = lean_task_pure(v___x_249_);
return v___x_250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___boxed(lean_object* v_text_251_, lean_object* v_hoverPos_252_, lean_object* v_includeStop_253_, lean_object* v___x_254_, lean_object* v_snap_255_, lean_object* v_x_256_){
_start:
{
uint8_t v_includeStop_boxed_257_; lean_object* v_res_258_; 
v_includeStop_boxed_257_ = lean_unbox(v_includeStop_253_);
v_res_258_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1(v_text_251_, v_hoverPos_252_, v_includeStop_boxed_257_, v___x_254_, v_snap_255_, v_x_256_);
lean_dec(v_x_256_);
lean_dec(v_hoverPos_252_);
lean_dec_ref(v_text_251_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos(lean_object* v_text_259_, lean_object* v_tree_260_, lean_object* v_hoverPos_261_, uint8_t v_includeStop_262_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___f_265_; lean_object* v___x_266_; 
v___x_263_ = lean_box(0);
v___x_264_ = lean_box(v_includeStop_262_);
v___f_265_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___boxed), 6, 4);
lean_closure_set(v___f_265_, 0, v_text_259_);
lean_closure_set(v___f_265_, 1, v_hoverPos_261_);
lean_closure_set(v___f_265_, 2, v___x_264_);
lean_closure_set(v___f_265_, 3, v___x_263_);
v___x_266_ = l_Lean_Language_SnapshotTree_foldSnaps___redArg(v_tree_260_, v___x_263_, v___f_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___boxed(lean_object* v_text_267_, lean_object* v_tree_268_, lean_object* v_hoverPos_269_, lean_object* v_includeStop_270_){
_start:
{
uint8_t v_includeStop_boxed_271_; lean_object* v_res_272_; 
v_includeStop_boxed_271_ = lean_unbox(v_includeStop_270_);
v_res_272_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos(v_text_267_, v_tree_268_, v_hoverPos_269_, v_includeStop_boxed_271_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0(lean_object* v_requestedRange_273_, uint8_t v___x_274_, lean_object* v_f_275_, lean_object* v_ctx_276_, lean_object* v_i_277_, lean_object* v_acc_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Lean_Elab_Info_range_x3f(v_i_277_);
if (lean_obj_tag(v___x_279_) == 1)
{
lean_object* v_val_280_; uint8_t v___x_281_; uint8_t v___x_282_; 
v_val_280_ = lean_ctor_get(v___x_279_, 0);
lean_inc(v_val_280_);
lean_dec_ref_known(v___x_279_, 1);
v___x_281_ = l_Lean_Syntax_Range_overlaps(v_val_280_, v_requestedRange_273_, v___x_274_, v___x_274_);
lean_dec(v_val_280_);
v___x_282_ = lean_bool_not(v___x_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; 
v___x_283_ = lean_apply_3(v_f_275_, v_ctx_276_, v_i_277_, v_acc_278_);
return v___x_283_;
}
else
{
lean_dec_ref(v_i_277_);
lean_dec_ref(v_ctx_276_);
lean_dec(v_f_275_);
return v_acc_278_;
}
}
else
{
lean_dec(v___x_279_);
lean_dec_ref(v_i_277_);
lean_dec_ref(v_ctx_276_);
lean_dec(v_f_275_);
return v_acc_278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0___boxed(lean_object* v_requestedRange_284_, lean_object* v___x_285_, lean_object* v_f_286_, lean_object* v_ctx_287_, lean_object* v_i_288_, lean_object* v_acc_289_){
_start:
{
uint8_t v___x_553__boxed_290_; lean_object* v_res_291_; 
v___x_553__boxed_290_ = lean_unbox(v___x_285_);
v_res_291_ = l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0(v_requestedRange_284_, v___x_553__boxed_290_, v_f_286_, v_ctx_287_, v_i_288_, v_acc_289_);
lean_dec_ref(v_requestedRange_284_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1(lean_object* v___f_292_, lean_object* v_acc_293_, uint8_t v___x_294_, lean_object* v_tree_295_){
_start:
{
lean_object* v_element_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_311_; 
v_element_296_ = lean_ctor_get(v_tree_295_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v_tree_295_);
if (v_isSharedCheck_311_ == 0)
{
lean_object* v_unused_312_; 
v_unused_312_ = lean_ctor_get(v_tree_295_, 1);
lean_dec(v_unused_312_);
v___x_298_ = v_tree_295_;
v_isShared_299_ = v_isSharedCheck_311_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_element_296_);
lean_dec(v_tree_295_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_311_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v_infoTree_x3f_300_; 
v_infoTree_x3f_300_ = lean_ctor_get(v_element_296_, 2);
lean_inc(v_infoTree_x3f_300_);
lean_dec_ref(v_element_296_);
if (lean_obj_tag(v_infoTree_x3f_300_) == 1)
{
lean_object* v_val_301_; lean_object* v_acc_302_; lean_object* v___x_303_; lean_object* v___x_305_; 
v_val_301_ = lean_ctor_get(v_infoTree_x3f_300_, 0);
lean_inc(v_val_301_);
lean_dec_ref_known(v_infoTree_x3f_300_, 1);
v_acc_302_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_292_, v_acc_293_, v_val_301_);
v___x_303_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_303_, 0, v___x_294_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 1, v___x_303_);
lean_ctor_set(v___x_298_, 0, v_acc_302_);
v___x_305_ = v___x_298_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_acc_302_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v___x_303_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
else
{
lean_object* v___x_307_; lean_object* v___x_309_; 
lean_dec(v_infoTree_x3f_300_);
lean_dec(v___f_292_);
v___x_307_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_307_, 0, v___x_294_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 1, v___x_307_);
lean_ctor_set(v___x_298_, 0, v_acc_293_);
v___x_309_ = v___x_298_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_acc_293_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1___boxed(lean_object* v___f_313_, lean_object* v_acc_314_, lean_object* v___x_315_, lean_object* v_tree_316_){
_start:
{
uint8_t v___x_567__boxed_317_; lean_object* v_res_318_; 
v___x_567__boxed_317_ = lean_unbox(v___x_315_);
v_res_318_ = l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1(v___f_313_, v_acc_314_, v___x_567__boxed_317_, v_tree_316_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__2(lean_object* v_requestedRange_319_, lean_object* v_f_320_, lean_object* v_snap_321_, lean_object* v_acc_322_){
_start:
{
lean_object* v_stx_x3f_323_; 
v_stx_x3f_323_ = lean_ctor_get(v_snap_321_, 0);
lean_inc(v_stx_x3f_323_);
if (lean_obj_tag(v_stx_x3f_323_) == 1)
{
lean_object* v_task_324_; lean_object* v_val_325_; uint8_t v___x_326_; lean_object* v___x_327_; 
v_task_324_ = lean_ctor_get(v_snap_321_, 3);
lean_inc_ref(v_task_324_);
lean_dec_ref(v_snap_321_);
v_val_325_ = lean_ctor_get(v_stx_x3f_323_, 0);
lean_inc(v_val_325_);
lean_dec_ref_known(v_stx_x3f_323_, 1);
v___x_326_ = 1;
v___x_327_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_val_325_, v___x_326_);
lean_dec(v_val_325_);
if (lean_obj_tag(v___x_327_) == 1)
{
lean_object* v_val_328_; uint8_t v___x_329_; uint8_t v___x_330_; 
v_val_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_val_328_);
lean_dec_ref_known(v___x_327_, 1);
v___x_329_ = l_Lean_Syntax_Range_overlaps(v_val_328_, v_requestedRange_319_, v___x_326_, v___x_326_);
lean_dec(v_val_328_);
v___x_330_ = lean_bool_not(v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___f_332_; lean_object* v___x_333_; lean_object* v___f_334_; lean_object* v___x_335_; 
v___x_331_ = lean_box(v___x_326_);
v___f_332_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_332_, 0, v_requestedRange_319_);
lean_closure_set(v___f_332_, 1, v___x_331_);
lean_closure_set(v___f_332_, 2, v_f_320_);
v___x_333_ = lean_box(v___x_326_);
v___f_334_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_334_, 0, v___f_332_);
lean_closure_set(v___f_334_, 1, v_acc_322_);
lean_closure_set(v___f_334_, 2, v___x_333_);
v___x_335_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_334_, v_task_324_);
return v___x_335_;
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec_ref(v_task_324_);
lean_dec(v_f_320_);
lean_dec_ref(v_requestedRange_319_);
v___x_336_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0));
v___x_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_337_, 0, v_acc_322_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = lean_task_pure(v___x_337_);
return v___x_338_;
}
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
lean_dec(v___x_327_);
lean_dec_ref(v_task_324_);
lean_dec(v_f_320_);
lean_dec_ref(v_requestedRange_319_);
v___x_339_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1));
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v_acc_322_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
v___x_341_ = lean_task_pure(v___x_340_);
return v___x_341_;
}
}
else
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
lean_dec(v_stx_x3f_323_);
lean_dec_ref(v_snap_321_);
lean_dec(v_f_320_);
lean_dec_ref(v_requestedRange_319_);
v___x_342_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0));
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v_acc_322_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = lean_task_pure(v___x_343_);
return v___x_344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg(lean_object* v_tree_345_, lean_object* v_requestedRange_346_, lean_object* v_init_347_, lean_object* v_f_348_){
_start:
{
lean_object* v___f_349_; lean_object* v___x_350_; 
v___f_349_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__2), 4, 2);
lean_closure_set(v___f_349_, 0, v_requestedRange_346_);
lean_closure_set(v___f_349_, 1, v_f_348_);
v___x_350_ = l_Lean_Language_SnapshotTree_foldSnaps___redArg(v_tree_345_, v_init_347_, v___f_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange(lean_object* v_00_u03b1_351_, lean_object* v_tree_352_, lean_object* v_requestedRange_353_, lean_object* v_init_354_, lean_object* v_f_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_Language_SnapshotTree_foldInfosInRange___redArg(v_tree_352_, v_requestedRange_353_, v_init_354_, v_f_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0(lean_object* v_log_357_, uint8_t v___x_358_, lean_object* v_tree_359_){
_start:
{
lean_object* v_element_360_; lean_object* v_diagnostics_361_; lean_object* v_msgLog_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_371_; 
v_element_360_ = lean_ctor_get(v_tree_359_, 0);
lean_inc_ref(v_element_360_);
lean_dec_ref(v_tree_359_);
v_diagnostics_361_ = lean_ctor_get(v_element_360_, 1);
lean_inc_ref(v_diagnostics_361_);
lean_dec_ref(v_element_360_);
v_msgLog_362_ = lean_ctor_get(v_diagnostics_361_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v_diagnostics_361_);
if (v_isSharedCheck_371_ == 0)
{
lean_object* v_unused_372_; 
v_unused_372_ = lean_ctor_get(v_diagnostics_361_, 1);
lean_dec(v_unused_372_);
v___x_364_ = v_diagnostics_361_;
v_isShared_365_ = v_isSharedCheck_371_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_msgLog_362_);
lean_dec(v_diagnostics_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_371_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_366_ = l_Lean_MessageLog_append(v_log_357_, v_msgLog_362_);
v___x_367_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_367_, 0, v___x_358_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 1, v___x_367_);
lean_ctor_set(v___x_364_, 0, v___x_366_);
v___x_369_ = v___x_364_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v___x_367_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0___boxed(lean_object* v_log_373_, lean_object* v___x_374_, lean_object* v_tree_375_){
_start:
{
uint8_t v___x_384__boxed_376_; lean_object* v_res_377_; 
v___x_384__boxed_376_ = lean_unbox(v___x_374_);
v_res_377_ = l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0(v_log_373_, v___x_384__boxed_376_, v_tree_375_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1(lean_object* v_requestedRange_378_, lean_object* v_snap_379_, lean_object* v_log_380_){
_start:
{
lean_object* v_stx_x3f_381_; 
v_stx_x3f_381_ = lean_ctor_get(v_snap_379_, 0);
lean_inc(v_stx_x3f_381_);
if (lean_obj_tag(v_stx_x3f_381_) == 1)
{
lean_object* v_task_382_; lean_object* v_val_383_; uint8_t v___x_384_; lean_object* v___x_385_; 
v_task_382_ = lean_ctor_get(v_snap_379_, 3);
lean_inc_ref(v_task_382_);
lean_dec_ref(v_snap_379_);
v_val_383_ = lean_ctor_get(v_stx_x3f_381_, 0);
lean_inc(v_val_383_);
lean_dec_ref_known(v_stx_x3f_381_, 1);
v___x_384_ = 1;
v___x_385_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_val_383_, v___x_384_);
lean_dec(v_val_383_);
if (lean_obj_tag(v___x_385_) == 1)
{
lean_object* v_val_386_; uint8_t v___x_387_; uint8_t v___x_388_; 
v_val_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_val_386_);
lean_dec_ref_known(v___x_385_, 1);
v___x_387_ = l_Lean_Syntax_Range_overlaps(v_val_386_, v_requestedRange_378_, v___x_384_, v___x_384_);
lean_dec(v_val_386_);
v___x_388_ = lean_bool_not(v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v___f_390_; lean_object* v___x_391_; 
v___x_389_ = lean_box(v___x_384_);
v___f_390_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0___boxed), 3, 2);
lean_closure_set(v___f_390_, 0, v_log_380_);
lean_closure_set(v___f_390_, 1, v___x_389_);
v___x_391_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_390_, v_task_382_);
return v___x_391_;
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec_ref(v_task_382_);
v___x_392_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0));
v___x_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_393_, 0, v_log_380_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
v___x_394_ = lean_task_pure(v___x_393_);
return v___x_394_;
}
}
else
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
lean_dec(v___x_385_);
lean_dec_ref(v_task_382_);
v___x_395_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1));
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v_log_380_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
v___x_397_ = lean_task_pure(v___x_396_);
return v___x_397_;
}
}
else
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
lean_dec(v_stx_x3f_381_);
lean_dec_ref(v_snap_379_);
v___x_398_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1));
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v_log_380_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = lean_task_pure(v___x_399_);
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1___boxed(lean_object* v_requestedRange_401_, lean_object* v_snap_402_, lean_object* v_log_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1(v_requestedRange_401_, v_snap_402_, v_log_403_);
lean_dec_ref(v_requestedRange_401_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange(lean_object* v_tree_405_, lean_object* v_requestedRange_406_){
_start:
{
lean_object* v___f_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___f_407_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1___boxed), 3, 1);
lean_closure_set(v___f_407_, 0, v_requestedRange_406_);
v___x_408_ = l_Lean_MessageLog_empty;
v___x_409_ = l_Lean_Language_SnapshotTree_foldSnaps___redArg(v_tree_405_, v___x_408_, v___f_407_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_methodNotFound(lean_object* v_method_423_){
_start:
{
uint8_t v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_424_ = 2;
v___x_425_ = ((lean_object*)(l_Lean_Server_RequestError_methodNotFound___closed__0));
v___x_426_ = lean_string_append(v___x_425_, v_method_423_);
v___x_427_ = ((lean_object*)(l_Lean_Server_RequestError_methodNotFound___closed__1));
v___x_428_ = lean_string_append(v___x_426_, v___x_427_);
v___x_429_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set_uint8(v___x_429_, sizeof(void*)*1, v___x_424_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_methodNotFound___boxed(lean_object* v_method_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_Server_RequestError_methodNotFound(v_method_430_);
lean_dec_ref(v_method_430_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_invalidParams(lean_object* v_message_432_){
_start:
{
uint8_t v___x_433_; lean_object* v___x_434_; 
v___x_433_ = 3;
v___x_434_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_434_, 0, v_message_432_);
lean_ctor_set_uint8(v___x_434_, sizeof(void*)*1, v___x_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_internalError(lean_object* v_message_435_){
_start:
{
uint8_t v___x_436_; lean_object* v___x_437_; 
v___x_436_ = 4;
v___x_437_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_437_, 0, v_message_435_);
lean_ctor_set_uint8(v___x_437_, sizeof(void*)*1, v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_ofException(lean_object* v_e_447_){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_449_ = l_Lean_Exception_toMessageData(v_e_447_);
v___x_450_ = l_Lean_MessageData_toString(v___x_449_);
v___x_451_ = l_Lean_Server_RequestError_internalError(v___x_450_);
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_ofException___boxed(lean_object* v_e_453_, lean_object* v_a_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_Server_RequestError_ofException(v_e_453_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_ofIoError(lean_object* v_e_456_){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_io_error_to_string(v_e_456_);
v___x_458_ = l_Lean_Server_RequestError_internalError(v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_toLspResponseError(lean_object* v_id_459_, lean_object* v_e_460_){
_start:
{
uint8_t v_code_461_; lean_object* v_message_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v_code_461_ = lean_ctor_get_uint8(v_e_460_, sizeof(void*)*1);
v_message_462_ = lean_ctor_get(v_e_460_, 0);
v___x_463_ = lean_box(0);
lean_inc_ref(v_message_462_);
v___x_464_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_464_, 0, v_id_459_);
lean_ctor_set(v___x_464_, 1, v_message_462_);
lean_ctor_set(v___x_464_, 2, v___x_463_);
lean_ctor_set_uint8(v___x_464_, sizeof(void*)*3, v_code_461_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_toLspResponseError___boxed(lean_object* v_id_465_, lean_object* v_e_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_Server_RequestError_toLspResponseError(v_id_465_, v_e_466_);
lean_dec_ref(v_e_466_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___redArg(lean_object* v_inst_470_, lean_object* v_params_471_){
_start:
{
lean_object* v___x_472_; 
lean_inc(v_params_471_);
v___x_472_ = lean_apply_1(v_inst_470_, v_params_471_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_488_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_488_ == 0)
{
v___x_475_ = v___x_472_;
v_isShared_476_ = v_isSharedCheck_488_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_488_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
uint8_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_477_ = 3;
v___x_478_ = ((lean_object*)(l_Lean_Server_parseRequestParams___redArg___closed__0));
v___x_479_ = l_Lean_Json_compress(v_params_471_);
v___x_480_ = lean_string_append(v___x_478_, v___x_479_);
lean_dec_ref(v___x_479_);
v___x_481_ = ((lean_object*)(l_Lean_Server_parseRequestParams___redArg___closed__1));
v___x_482_ = lean_string_append(v___x_480_, v___x_481_);
v___x_483_ = lean_string_append(v___x_482_, v_a_473_);
lean_dec(v_a_473_);
v___x_484_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_484_, 0, v___x_483_);
lean_ctor_set_uint8(v___x_484_, sizeof(void*)*1, v___x_477_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v___x_484_);
v___x_486_ = v___x_475_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
else
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
lean_dec(v_params_471_);
v_a_489_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_496_ == 0)
{
v___x_491_ = v___x_472_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_472_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_489_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams(lean_object* v_paramType_497_, lean_object* v_inst_498_, lean_object* v_params_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Lean_Server_parseRequestParams___redArg(v_inst_498_, v_params_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___redArg(lean_object* v_x_501_){
_start:
{
if (lean_obj_tag(v_x_501_) == 0)
{
lean_object* v___x_502_; 
v___x_502_ = lean_unsigned_to_nat(0u);
return v___x_502_;
}
else
{
lean_object* v___x_503_; 
v___x_503_ = lean_unsigned_to_nat(1u);
return v___x_503_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___redArg___boxed(lean_object* v_x_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_Server_ServerRequestResponse_ctorIdx___redArg(v_x_504_);
lean_dec_ref(v_x_504_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx(lean_object* v_00_u03b1_506_, lean_object* v_x_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Lean_Server_ServerRequestResponse_ctorIdx___redArg(v_x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___boxed(lean_object* v_00_u03b1_509_, lean_object* v_x_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_Server_ServerRequestResponse_ctorIdx(v_00_u03b1_509_, v_x_510_);
lean_dec_ref(v_x_510_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorElim___redArg(lean_object* v_t_512_, lean_object* v_k_513_){
_start:
{
if (lean_obj_tag(v_t_512_) == 0)
{
lean_object* v_response_514_; lean_object* v___x_515_; 
v_response_514_ = lean_ctor_get(v_t_512_, 0);
lean_inc(v_response_514_);
lean_dec_ref_known(v_t_512_, 1);
v___x_515_ = lean_apply_1(v_k_513_, v_response_514_);
return v___x_515_;
}
else
{
uint8_t v_code_516_; lean_object* v_message_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v_code_516_ = lean_ctor_get_uint8(v_t_512_, sizeof(void*)*1);
v_message_517_ = lean_ctor_get(v_t_512_, 0);
lean_inc_ref(v_message_517_);
lean_dec_ref_known(v_t_512_, 1);
v___x_518_ = lean_box(v_code_516_);
v___x_519_ = lean_apply_2(v_k_513_, v___x_518_, v_message_517_);
return v___x_519_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorElim(lean_object* v_00_u03b1_520_, lean_object* v_motive_521_, lean_object* v_ctorIdx_522_, lean_object* v_t_523_, lean_object* v_h_524_, lean_object* v_k_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_523_, v_k_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorElim___boxed(lean_object* v_00_u03b1_527_, lean_object* v_motive_528_, lean_object* v_ctorIdx_529_, lean_object* v_t_530_, lean_object* v_h_531_, lean_object* v_k_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_Server_ServerRequestResponse_ctorElim(v_00_u03b1_527_, v_motive_528_, v_ctorIdx_529_, v_t_530_, v_h_531_, v_k_532_);
lean_dec(v_ctorIdx_529_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_success_elim___redArg(lean_object* v_t_534_, lean_object* v_success_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_534_, v_success_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_success_elim(lean_object* v_00_u03b1_537_, lean_object* v_motive_538_, lean_object* v_t_539_, lean_object* v_h_540_, lean_object* v_success_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_539_, v_success_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_failure_elim___redArg(lean_object* v_t_543_, lean_object* v_failure_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_543_, v_failure_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_failure_elim(lean_object* v_00_u03b1_546_, lean_object* v_motive_547_, lean_object* v_t_548_, lean_object* v_h_549_, lean_object* v_failure_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_548_, v_failure_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse_default(lean_object* v_00_u03b1_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = ((lean_object*)(l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0));
return v___x_556_;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedServerRequestResponse___closed__0(void){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Lean_Server_instInhabitedServerRequestResponse_default(lean_box(0));
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse(lean_object* v_a_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = lean_obj_once(&l_Lean_Server_instInhabitedServerRequestResponse___closed__0, &l_Lean_Server_instInhabitedServerRequestResponse___closed__0_once, _init_l_Lean_Server_instInhabitedServerRequestResponse___closed__0);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run___redArg(lean_object* v_act_560_, lean_object* v_rc_561_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = lean_apply_2(v_act_560_, v_rc_561_, lean_box(0));
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run___redArg___boxed(lean_object* v_act_564_, lean_object* v_rc_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_Server_RequestM_run___redArg(v_act_564_, v_rc_565_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run(lean_object* v_00_u03b1_568_, lean_object* v_act_569_, lean_object* v_rc_570_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = lean_apply_2(v_act_569_, v_rc_570_, lean_box(0));
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run___boxed(lean_object* v_00_u03b1_573_, lean_object* v_act_574_, lean_object* v_rc_575_, lean_object* v_a_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_Server_RequestM_run(v_00_u03b1_573_, v_act_574_, v_rc_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestTask_pure___redArg(lean_object* v_a_578_){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_579_, 0, v_a_578_);
v___x_580_ = lean_task_pure(v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestTask_pure(lean_object* v_00_u03b1_581_, lean_object* v_a_582_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_583_, 0, v_a_582_);
v___x_584_ = lean_task_pure(v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM___lam__0(lean_object* v_00_u03b1_585_, lean_object* v_x_586_, lean_object* v___y_587_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = lean_apply_1(v_x_586_, lean_box(0));
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_589_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_589_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_606_; 
v_a_598_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_606_ == 0)
{
v___x_600_ = v___x_589_;
v_isShared_601_ = v_isSharedCheck_606_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_589_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_606_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_602_ = l_Lean_Server_RequestError_ofIoError(v_a_598_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_602_);
v___x_604_ = v___x_600_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_602_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM___lam__0___boxed(lean_object* v_00_u03b1_607_, lean_object* v_x_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_Server_instMonadLiftIORequestM___lam__0(v_00_u03b1_607_, v_x_608_, v___y_609_);
lean_dec_ref(v___y_609_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0(lean_object* v_00_u03b1_614_, lean_object* v_x_615_, lean_object* v___y_616_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = lean_apply_1(v_x_615_, lean_box(0));
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___x_618_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_618_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_628_; lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
v_a_627_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_a_627_);
lean_dec_ref_known(v___x_618_, 1);
v___x_628_ = l_Lean_Server_RequestError_ofException(v_a_627_);
v_a_629_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_628_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_628_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
lean_ctor_set_tag(v___x_631_, 1);
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0___boxed(lean_object* v_00_u03b1_637_, lean_object* v_x_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0(v_00_u03b1_637_, v_x_638_, v___y_639_);
lean_dec_ref(v___y_639_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0(lean_object* v_00_u03b1_644_, lean_object* v_x_645_, lean_object* v___y_646_){
_start:
{
lean_object* v_cancelTk_648_; lean_object* v___x_649_; 
v_cancelTk_648_ = lean_ctor_get(v___y_646_, 4);
lean_inc_ref(v_cancelTk_648_);
v___x_649_ = lean_apply_2(v_x_645_, v_cancelTk_648_, lean_box(0));
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_662_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_662_ == 0)
{
v___x_652_ = v___x_649_;
v_isShared_653_ = v_isSharedCheck_662_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_649_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_662_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
if (lean_obj_tag(v_a_650_) == 0)
{
lean_object* v___x_654_; lean_object* v___x_656_; 
lean_dec_ref_known(v_a_650_, 1);
v___x_654_ = ((lean_object*)(l_Lean_Server_RequestError_requestCancelled));
if (v_isShared_653_ == 0)
{
lean_ctor_set_tag(v___x_652_, 1);
lean_ctor_set(v___x_652_, 0, v___x_654_);
v___x_656_ = v___x_652_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; 
v_a_658_ = lean_ctor_get(v_a_650_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v_a_650_, 1);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v_a_658_);
v___x_660_ = v___x_652_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_658_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_671_; 
v_a_663_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_671_ == 0)
{
v___x_665_ = v___x_649_;
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_649_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_667_ = l_Lean_Server_RequestError_ofIoError(v_a_663_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_667_);
v___x_669_ = v___x_665_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0___boxed(lean_object* v_00_u03b1_672_, lean_object* v_x_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0(v_00_u03b1_672_, v_x_673_, v___y_674_);
lean_dec_ref(v___y_674_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO___redArg(lean_object* v_x_679_, lean_object* v_ctx_680_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = lean_apply_2(v_x_679_, v_ctx_680_, lean_box(0));
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_682_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_682_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_700_; 
v_a_691_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_700_ == 0)
{
v___x_693_ = v___x_682_;
v_isShared_694_ = v_isSharedCheck_700_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_682_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_700_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v_message_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
v_message_695_ = lean_ctor_get(v_a_691_, 0);
lean_inc_ref(v_message_695_);
lean_dec(v_a_691_);
v___x_696_ = lean_mk_io_user_error(v_message_695_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_696_);
v___x_698_ = v___x_693_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO___redArg___boxed(lean_object* v_x_701_, lean_object* v_ctx_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_Server_RequestM_runInIO___redArg(v_x_701_, v_ctx_702_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO(lean_object* v_00_u03b1_705_, lean_object* v_x_706_, lean_object* v_ctx_707_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_Lean_Server_RequestM_runInIO___redArg(v_x_706_, v_ctx_707_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO___boxed(lean_object* v_00_u03b1_710_, lean_object* v_x_711_, lean_object* v_ctx_712_, lean_object* v_a_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_Server_RequestM_runInIO(v_00_u03b1_710_, v_x_711_, v_ctx_712_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___redArg___lam__0(lean_object* v_toPure_715_, lean_object* v_rc_716_){
_start:
{
lean_object* v_doc_717_; lean_object* v___x_718_; 
v_doc_717_ = lean_ctor_get(v_rc_716_, 1);
lean_inc_ref(v_doc_717_);
lean_dec_ref(v_rc_716_);
v___x_718_ = lean_apply_2(v_toPure_715_, lean_box(0), v_doc_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___redArg(lean_object* v_inst_719_, lean_object* v_inst_720_){
_start:
{
lean_object* v_toApplicative_721_; lean_object* v_toBind_722_; lean_object* v_toPure_723_; lean_object* v___f_724_; lean_object* v___x_725_; 
v_toApplicative_721_ = lean_ctor_get(v_inst_719_, 0);
lean_inc_ref(v_toApplicative_721_);
v_toBind_722_ = lean_ctor_get(v_inst_719_, 1);
lean_inc(v_toBind_722_);
lean_dec_ref(v_inst_719_);
v_toPure_723_ = lean_ctor_get(v_toApplicative_721_, 1);
lean_inc(v_toPure_723_);
lean_dec_ref(v_toApplicative_721_);
v___f_724_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_readDoc___redArg___lam__0), 2, 1);
lean_closure_set(v___f_724_, 0, v_toPure_723_);
v___x_725_ = lean_apply_4(v_toBind_722_, lean_box(0), lean_box(0), v_inst_720_, v___f_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc(lean_object* v_m_726_, lean_object* v_inst_727_, lean_object* v_inst_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_Server_RequestM_readDoc___redArg(v_inst_727_, v_inst_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg___lam__0(lean_object* v_t_730_, lean_object* v_a_731_){
_start:
{
lean_object* v___x_733_; 
lean_inc_ref(v_a_731_);
v___x_733_ = lean_apply_2(v_t_730_, v_a_731_, lean_box(0));
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg___lam__0___boxed(lean_object* v_t_734_, lean_object* v_a_735_, lean_object* v___y_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_Server_RequestM_asTask___redArg___lam__0(v_t_734_, v_a_735_);
lean_dec_ref(v_a_735_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg(lean_object* v_t_738_, lean_object* v_a_739_){
_start:
{
lean_object* v___f_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
lean_inc_ref(v_a_739_);
v___f_741_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_asTask___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_741_, 0, v_t_738_);
lean_closure_set(v___f_741_, 1, v_a_739_);
v___x_742_ = l_Lean_Server_ServerTask_EIO_asTask___redArg(v___f_741_);
v___x_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg___boxed(lean_object* v_t_744_, lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_Server_RequestM_asTask___redArg(v_t_744_, v_a_745_);
lean_dec_ref(v_a_745_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask(lean_object* v_00_u03b1_748_, lean_object* v_t_749_, lean_object* v_a_750_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_Server_RequestM_asTask___redArg(v_t_749_, v_a_750_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___boxed(lean_object* v_00_u03b1_753_, lean_object* v_t_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_Server_RequestM_asTask(v_00_u03b1_753_, v_t_754_, v_a_755_);
lean_dec_ref(v_a_755_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask___redArg(lean_object* v_t_758_, lean_object* v_a_759_){
_start:
{
lean_object* v___x_761_; 
lean_inc_ref(v_a_759_);
v___x_761_ = lean_apply_2(v_t_758_, v_a_759_, lean_box(0));
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_771_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_771_ == 0)
{
v___x_764_ = v___x_761_;
v_isShared_765_ = v_isSharedCheck_771_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_771_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_769_; 
v___x_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_766_, 0, v_a_762_);
v___x_767_ = lean_task_pure(v___x_766_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v___x_767_);
v___x_769_ = v___x_764_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
v_a_772_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_761_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_761_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask___redArg___boxed(lean_object* v_t_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_Server_RequestM_pureTask___redArg(v_t_780_, v_a_781_);
lean_dec_ref(v_a_781_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask(lean_object* v_00_u03b1_784_, lean_object* v_t_785_, lean_object* v_a_786_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_Server_RequestM_pureTask___redArg(v_t_785_, v_a_786_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask___boxed(lean_object* v_00_u03b1_789_, lean_object* v_t_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Lean_Server_RequestM_pureTask(v_00_u03b1_789_, v_t_790_, v_a_791_);
lean_dec_ref(v_a_791_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0(lean_object* v_f_794_, lean_object* v_a_795_, lean_object* v_x_796_){
_start:
{
lean_object* v___x_798_; 
lean_inc_ref(v_a_795_);
v___x_798_ = lean_apply_3(v_f_794_, v_x_796_, v_a_795_, lean_box(0));
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0___boxed(lean_object* v_f_799_, lean_object* v_a_800_, lean_object* v_x_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0(v_f_799_, v_a_800_, v_x_801_);
lean_dec_ref(v_a_800_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg(lean_object* v_t_804_, lean_object* v_f_805_, lean_object* v_a_806_){
_start:
{
lean_object* v___f_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
lean_inc_ref(v_a_806_);
v___f_808_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_808_, 0, v_f_805_);
lean_closure_set(v___f_808_, 1, v_a_806_);
v___x_809_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(v___f_808_, v_t_804_);
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg___boxed(lean_object* v_t_811_, lean_object* v_f_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_t_811_, v_f_812_, v_a_813_);
lean_dec_ref(v_a_813_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap(lean_object* v_00_u03b1_816_, lean_object* v_00_u03b2_817_, lean_object* v_t_818_, lean_object* v_f_819_, lean_object* v_a_820_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_t_818_, v_f_819_, v_a_820_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___boxed(lean_object* v_00_u03b1_823_, lean_object* v_00_u03b2_824_, lean_object* v_t_825_, lean_object* v_f_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_Server_RequestM_mapTaskCheap(v_00_u03b1_823_, v_00_u03b2_824_, v_t_825_, v_f_826_, v_a_827_);
lean_dec_ref(v_a_827_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly___redArg(lean_object* v_t_830_, lean_object* v_f_831_, lean_object* v_a_832_){
_start:
{
lean_object* v___f_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
lean_inc_ref(v_a_832_);
v___f_834_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_834_, 0, v_f_831_);
lean_closure_set(v___f_834_, 1, v_a_832_);
v___x_835_ = l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(v___f_834_, v_t_830_);
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly___redArg___boxed(lean_object* v_t_837_, lean_object* v_f_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_t_837_, v_f_838_, v_a_839_);
lean_dec_ref(v_a_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly(lean_object* v_00_u03b1_842_, lean_object* v_00_u03b2_843_, lean_object* v_t_844_, lean_object* v_f_845_, lean_object* v_a_846_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_t_844_, v_f_845_, v_a_846_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly___boxed(lean_object* v_00_u03b1_849_, lean_object* v_00_u03b2_850_, lean_object* v_t_851_, lean_object* v_f_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_Server_RequestM_mapTaskCostly(v_00_u03b1_849_, v_00_u03b2_850_, v_t_851_, v_f_852_, v_a_853_);
lean_dec_ref(v_a_853_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0(lean_object* v_f_856_, lean_object* v_a_857_, lean_object* v_x_858_){
_start:
{
lean_object* v___x_860_; 
lean_inc_ref(v_a_857_);
v___x_860_ = lean_apply_3(v_f_856_, v_x_858_, v_a_857_, lean_box(0));
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0___boxed(lean_object* v_f_861_, lean_object* v_a_862_, lean_object* v_x_863_, lean_object* v___y_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0(v_f_861_, v_a_862_, v_x_863_);
lean_dec_ref(v_a_862_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg(lean_object* v_t_866_, lean_object* v_f_867_, lean_object* v_a_868_){
_start:
{
lean_object* v___f_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
lean_inc_ref(v_a_868_);
v___f_870_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_870_, 0, v_f_867_);
lean_closure_set(v___f_870_, 1, v_a_868_);
v___x_871_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(v_t_866_, v___f_870_);
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg___boxed(lean_object* v_t_873_, lean_object* v_f_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lean_Server_RequestM_bindTaskCheap___redArg(v_t_873_, v_f_874_, v_a_875_);
lean_dec_ref(v_a_875_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap(lean_object* v_00_u03b1_878_, lean_object* v_00_u03b2_879_, lean_object* v_t_880_, lean_object* v_f_881_, lean_object* v_a_882_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_Server_RequestM_bindTaskCheap___redArg(v_t_880_, v_f_881_, v_a_882_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___boxed(lean_object* v_00_u03b1_885_, lean_object* v_00_u03b2_886_, lean_object* v_t_887_, lean_object* v_f_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_Server_RequestM_bindTaskCheap(v_00_u03b1_885_, v_00_u03b2_886_, v_t_887_, v_f_888_, v_a_889_);
lean_dec_ref(v_a_889_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly___redArg(lean_object* v_t_892_, lean_object* v_f_893_, lean_object* v_a_894_){
_start:
{
lean_object* v___f_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
lean_inc_ref(v_a_894_);
v___f_896_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_896_, 0, v_f_893_);
lean_closure_set(v___f_896_, 1, v_a_894_);
v___x_897_ = l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(v_t_892_, v___f_896_);
v___x_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly___redArg___boxed(lean_object* v_t_899_, lean_object* v_f_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_t_899_, v_f_900_, v_a_901_);
lean_dec_ref(v_a_901_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly(lean_object* v_00_u03b1_904_, lean_object* v_00_u03b2_905_, lean_object* v_t_906_, lean_object* v_f_907_, lean_object* v_a_908_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_t_906_, v_f_907_, v_a_908_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly___boxed(lean_object* v_00_u03b1_911_, lean_object* v_00_u03b2_912_, lean_object* v_t_913_, lean_object* v_f_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_Server_RequestM_bindTaskCostly(v_00_u03b1_911_, v_00_u03b2_912_, v_t_913_, v_f_914_, v_a_915_);
lean_dec_ref(v_a_915_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0(lean_object* v_f_918_, lean_object* v_x_919_, lean_object* v___y_920_){
_start:
{
if (lean_obj_tag(v_x_919_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec_ref(v_f_918_);
v_a_922_ = lean_ctor_get(v_x_919_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v_x_919_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v_x_919_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v_x_919_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
lean_ctor_set_tag(v___x_924_, 1);
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_931_; 
v_a_930_ = lean_ctor_get(v_x_919_, 0);
lean_inc(v_a_930_);
lean_dec_ref_known(v_x_919_, 1);
lean_inc_ref(v___y_920_);
v___x_931_ = lean_apply_3(v_f_918_, v_a_930_, v___y_920_, lean_box(0));
return v___x_931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0___boxed(lean_object* v_f_932_, lean_object* v_x_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0(v_f_932_, v_x_933_, v___y_934_);
lean_dec_ref(v___y_934_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg(lean_object* v_t_937_, lean_object* v_f_938_, lean_object* v_a_939_){
_start:
{
lean_object* v___f_941_; lean_object* v___x_942_; 
v___f_941_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_941_, 0, v_f_938_);
v___x_942_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_t_937_, v___f_941_, v_a_939_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___boxed(lean_object* v_t_943_, lean_object* v_f_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_Server_RequestM_mapRequestTaskCheap___redArg(v_t_943_, v_f_944_, v_a_945_);
lean_dec_ref(v_a_945_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap(lean_object* v_00_u03b1_948_, lean_object* v_00_u03b2_949_, lean_object* v_t_950_, lean_object* v_f_951_, lean_object* v_a_952_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_Server_RequestM_mapRequestTaskCheap___redArg(v_t_950_, v_f_951_, v_a_952_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___boxed(lean_object* v_00_u03b1_955_, lean_object* v_00_u03b2_956_, lean_object* v_t_957_, lean_object* v_f_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_Server_RequestM_mapRequestTaskCheap(v_00_u03b1_955_, v_00_u03b2_956_, v_t_957_, v_f_958_, v_a_959_);
lean_dec_ref(v_a_959_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(lean_object* v_t_962_, lean_object* v_f_963_, lean_object* v_a_964_){
_start:
{
lean_object* v___f_966_; lean_object* v___x_967_; 
v___f_966_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_966_, 0, v_f_963_);
v___x_967_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_t_962_, v___f_966_, v_a_964_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly___redArg___boxed(lean_object* v_t_968_, lean_object* v_f_969_, lean_object* v_a_970_, lean_object* v_a_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(v_t_968_, v_f_969_, v_a_970_);
lean_dec_ref(v_a_970_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly(lean_object* v_00_u03b1_973_, lean_object* v_00_u03b2_974_, lean_object* v_t_975_, lean_object* v_f_976_, lean_object* v_a_977_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(v_t_975_, v_f_976_, v_a_977_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly___boxed(lean_object* v_00_u03b1_980_, lean_object* v_00_u03b2_981_, lean_object* v_t_982_, lean_object* v_f_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_Server_RequestM_mapRequestTaskCostly(v_00_u03b1_980_, v_00_u03b2_981_, v_t_982_, v_f_983_, v_a_984_);
lean_dec_ref(v_a_984_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0(lean_object* v_f_987_, lean_object* v_x_988_, lean_object* v___y_989_){
_start:
{
if (lean_obj_tag(v_x_988_) == 0)
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec_ref(v_f_987_);
v_a_991_ = lean_ctor_get(v_x_988_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v_x_988_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v_x_988_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v_x_988_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
lean_ctor_set_tag(v___x_993_, 1);
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
else
{
lean_object* v_a_999_; lean_object* v___x_1000_; 
v_a_999_ = lean_ctor_get(v_x_988_, 0);
lean_inc(v_a_999_);
lean_dec_ref_known(v_x_988_, 1);
lean_inc_ref(v___y_989_);
v___x_1000_ = lean_apply_3(v_f_987_, v_a_999_, v___y_989_, lean_box(0));
return v___x_1000_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0___boxed(lean_object* v_f_1001_, lean_object* v_x_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0(v_f_1001_, v_x_1002_, v___y_1003_);
lean_dec_ref(v___y_1003_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg(lean_object* v_t_1006_, lean_object* v_f_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v___f_1010_; lean_object* v___x_1011_; 
v___f_1010_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1010_, 0, v_f_1007_);
v___x_1011_ = l_Lean_Server_RequestM_bindTaskCheap___redArg(v_t_1006_, v___f_1010_, v_a_1008_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___boxed(lean_object* v_t_1012_, lean_object* v_f_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_Server_RequestM_bindRequestTaskCheap___redArg(v_t_1012_, v_f_1013_, v_a_1014_);
lean_dec_ref(v_a_1014_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap(lean_object* v_00_u03b1_1017_, lean_object* v_00_u03b2_1018_, lean_object* v_t_1019_, lean_object* v_f_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_Server_RequestM_bindRequestTaskCheap___redArg(v_t_1019_, v_f_1020_, v_a_1021_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___boxed(lean_object* v_00_u03b1_1024_, lean_object* v_00_u03b2_1025_, lean_object* v_t_1026_, lean_object* v_f_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Lean_Server_RequestM_bindRequestTaskCheap(v_00_u03b1_1024_, v_00_u03b2_1025_, v_t_1026_, v_f_1027_, v_a_1028_);
lean_dec_ref(v_a_1028_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly___redArg(lean_object* v_t_1031_, lean_object* v_f_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v___f_1035_; lean_object* v___x_1036_; 
v___f_1035_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1035_, 0, v_f_1032_);
v___x_1036_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_t_1031_, v___f_1035_, v_a_1033_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly___redArg___boxed(lean_object* v_t_1037_, lean_object* v_f_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_Server_RequestM_bindRequestTaskCostly___redArg(v_t_1037_, v_f_1038_, v_a_1039_);
lean_dec_ref(v_a_1039_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly(lean_object* v_00_u03b1_1042_, lean_object* v_00_u03b2_1043_, lean_object* v_t_1044_, lean_object* v_f_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_Lean_Server_RequestM_bindRequestTaskCostly___redArg(v_t_1044_, v_f_1045_, v_a_1046_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly___boxed(lean_object* v_00_u03b1_1049_, lean_object* v_00_u03b2_1050_, lean_object* v_t_1051_, lean_object* v_f_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_Server_RequestM_bindRequestTaskCostly(v_00_u03b1_1049_, v_00_u03b2_1050_, v_t_1051_, v_f_1052_, v_a_1053_);
lean_dec_ref(v_a_1053_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___redArg(lean_object* v_inst_1056_, lean_object* v_params_1057_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_Server_parseRequestParams___redArg(v_inst_1056_, v_params_1057_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1059_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1059_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
lean_ctor_set_tag(v___x_1062_, 1);
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
v_a_1068_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1059_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1059_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
lean_ctor_set_tag(v___x_1070_, 0);
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___redArg___boxed(lean_object* v_inst_1076_, lean_object* v_params_1077_, lean_object* v_a_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_1076_, v_params_1077_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams(lean_object* v_paramType_1080_, lean_object* v_inst_1081_, lean_object* v_params_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_1081_, v_params_1082_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___boxed(lean_object* v_paramType_1086_, lean_object* v_inst_1087_, lean_object* v_params_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_Server_RequestM_parseRequestParams(v_paramType_1086_, v_inst_1087_, v_params_1088_, v_a_1089_);
lean_dec_ref(v_a_1089_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_checkCancelled(lean_object* v_a_1092_){
_start:
{
lean_object* v_cancelTk_1094_; uint8_t v___x_1095_; 
v_cancelTk_1094_ = lean_ctor_get(v_a_1092_, 4);
v___x_1095_ = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_cancelTk_1094_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = lean_box(0);
v___x_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
return v___x_1097_;
}
else
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = ((lean_object*)(l_Lean_Server_RequestError_requestCancelled));
v___x_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
return v___x_1099_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_checkCancelled___boxed(lean_object* v_a_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_Server_RequestM_checkCancelled(v_a_1100_);
lean_dec_ref(v_a_1100_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0(lean_object* v_inst_1104_, lean_object* v_x_1105_){
_start:
{
if (lean_obj_tag(v_x_1105_) == 0)
{
lean_object* v_response_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1124_; 
v_response_1106_ = lean_ctor_get(v_x_1105_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_x_1105_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1108_ = v_x_1105_;
v_isShared_1109_ = v_isSharedCheck_1124_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_response_1106_);
lean_dec(v_x_1105_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1124_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1110_; 
lean_inc(v_response_1106_);
v___x_1110_ = lean_apply_1(v_inst_1104_, v_response_1106_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; uint8_t v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
lean_del_object(v___x_1108_);
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1111_);
lean_dec_ref_known(v___x_1110_, 1);
v___x_1112_ = 0;
v___x_1113_ = ((lean_object*)(l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0___closed__0));
v___x_1114_ = l_Lean_Json_compress(v_response_1106_);
v___x_1115_ = lean_string_append(v___x_1113_, v___x_1114_);
lean_dec_ref(v___x_1114_);
v___x_1116_ = ((lean_object*)(l_Lean_Server_parseRequestParams___redArg___closed__1));
v___x_1117_ = lean_string_append(v___x_1115_, v___x_1116_);
v___x_1118_ = lean_string_append(v___x_1117_, v_a_1111_);
lean_dec(v_a_1111_);
v___x_1119_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
lean_ctor_set_uint8(v___x_1119_, sizeof(void*)*1, v___x_1112_);
return v___x_1119_;
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; 
lean_dec(v_response_1106_);
v_a_1120_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1120_);
lean_dec_ref_known(v___x_1110_, 1);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v_a_1120_);
v___x_1122_ = v___x_1108_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
else
{
uint8_t v_code_1125_; lean_object* v_message_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_dec_ref(v_inst_1104_);
v_code_1125_ = lean_ctor_get_uint8(v_x_1105_, sizeof(void*)*1);
v_message_1126_ = lean_ctor_get(v_x_1105_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_x_1105_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v_x_1105_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_message_1126_);
lean_dec(v_x_1105_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_message_1126_);
lean_ctor_set_uint8(v_reuseFailAlloc_1132_, sizeof(void*)*1, v_code_1125_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___redArg(lean_object* v_inst_1134_, lean_object* v_inst_1135_, lean_object* v_method_1136_, lean_object* v_param_1137_, lean_object* v_a_1138_){
_start:
{
lean_object* v_serverRequestEmitter_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___f_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v_serverRequestEmitter_1140_ = lean_ctor_get(v_a_1138_, 5);
v___x_1141_ = lean_apply_1(v_inst_1134_, v_param_1137_);
lean_inc_ref(v_serverRequestEmitter_1140_);
v___x_1142_ = lean_apply_3(v_serverRequestEmitter_1140_, v_method_1136_, v___x_1141_, lean_box(0));
v___f_1143_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1143_, 0, v_inst_1135_);
v___x_1144_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_1143_, v___x_1142_);
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___redArg___boxed(lean_object* v_inst_1146_, lean_object* v_inst_1147_, lean_object* v_method_1148_, lean_object* v_param_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_Server_RequestM_sendServerRequest___redArg(v_inst_1146_, v_inst_1147_, v_method_1148_, v_param_1149_, v_a_1150_);
lean_dec_ref(v_a_1150_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest(lean_object* v_paramType_1153_, lean_object* v_inst_1154_, lean_object* v_responseType_1155_, lean_object* v_inst_1156_, lean_object* v_inst_1157_, lean_object* v_method_1158_, lean_object* v_param_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_Server_RequestM_sendServerRequest___redArg(v_inst_1154_, v_inst_1156_, v_method_1158_, v_param_1159_, v_a_1160_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___boxed(lean_object* v_paramType_1163_, lean_object* v_inst_1164_, lean_object* v_responseType_1165_, lean_object* v_inst_1166_, lean_object* v_inst_1167_, lean_object* v_method_1168_, lean_object* v_param_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_Server_RequestM_sendServerRequest(v_paramType_1163_, v_inst_1164_, v_responseType_1165_, v_inst_1166_, v_inst_1167_, v_method_1168_, v_param_1169_, v_a_1170_);
lean_dec_ref(v_a_1170_);
lean_dec(v_inst_1167_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux___redArg(lean_object* v_notFoundX_1173_, lean_object* v_x_1174_, lean_object* v_x_1175_, lean_object* v_a_1176_){
_start:
{
if (lean_obj_tag(v_x_1175_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1186_; 
lean_dec_ref(v_x_1174_);
lean_dec_ref(v_notFoundX_1173_);
v_a_1178_ = lean_ctor_get(v_x_1175_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_x_1175_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1180_ = v_x_1175_;
v_isShared_1181_ = v_isSharedCheck_1186_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v_x_1175_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1186_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1182_; lean_object* v___x_1184_; 
v___x_1182_ = l_Lean_Server_RequestError_ofIoError(v_a_1178_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set_tag(v___x_1180_, 1);
lean_ctor_set(v___x_1180_, 0, v___x_1182_);
v___x_1184_ = v___x_1180_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
else
{
lean_object* v_a_1187_; 
v_a_1187_ = lean_ctor_get(v_x_1175_, 0);
lean_inc(v_a_1187_);
lean_dec_ref_known(v_x_1175_, 1);
if (lean_obj_tag(v_a_1187_) == 0)
{
lean_object* v___x_1188_; 
lean_dec_ref(v_x_1174_);
lean_inc_ref(v_a_1176_);
v___x_1188_ = lean_apply_2(v_notFoundX_1173_, v_a_1176_, lean_box(0));
return v___x_1188_;
}
else
{
lean_object* v_val_1189_; lean_object* v___x_1190_; 
lean_dec_ref(v_notFoundX_1173_);
v_val_1189_ = lean_ctor_get(v_a_1187_, 0);
lean_inc(v_val_1189_);
lean_dec_ref_known(v_a_1187_, 1);
lean_inc_ref(v_a_1176_);
v___x_1190_ = lean_apply_3(v_x_1174_, v_val_1189_, v_a_1176_, lean_box(0));
return v___x_1190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux___redArg___boxed(lean_object* v_notFoundX_1191_, lean_object* v_x_1192_, lean_object* v_x_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_Server_RequestM_waitFindSnapAux___redArg(v_notFoundX_1191_, v_x_1192_, v_x_1193_, v_a_1194_);
lean_dec_ref(v_a_1194_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux(lean_object* v_00_u03b1_1197_, lean_object* v_notFoundX_1198_, lean_object* v_x_1199_, lean_object* v_x_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_Server_RequestM_waitFindSnapAux___redArg(v_notFoundX_1198_, v_x_1199_, v_x_1200_, v_a_1201_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux___boxed(lean_object* v_00_u03b1_1204_, lean_object* v_notFoundX_1205_, lean_object* v_x_1206_, lean_object* v_x_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_Server_RequestM_waitFindSnapAux(v_00_u03b1_1204_, v_notFoundX_1205_, v_x_1206_, v_x_1207_, v_a_1208_);
lean_dec_ref(v_a_1208_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___redArg(lean_object* v_doc_1211_, lean_object* v_p_1212_, lean_object* v_notFoundX_1213_, lean_object* v_x_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v_toEditableDocumentCore_1217_; lean_object* v_cmdSnaps_1218_; lean_object* v_findTask_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v_toEditableDocumentCore_1217_ = lean_ctor_get(v_doc_1211_, 0);
lean_inc_ref(v_toEditableDocumentCore_1217_);
lean_dec_ref(v_doc_1211_);
v_cmdSnaps_1218_ = lean_ctor_get(v_toEditableDocumentCore_1217_, 2);
lean_inc(v_cmdSnaps_1218_);
lean_dec_ref(v_toEditableDocumentCore_1217_);
v_findTask_1219_ = l_Lean_AsyncList_waitFind_x3f___redArg(v_p_1212_, v_cmdSnaps_1218_);
v___x_1220_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_waitFindSnapAux___boxed), 6, 3);
lean_closure_set(v___x_1220_, 0, lean_box(0));
lean_closure_set(v___x_1220_, 1, v_notFoundX_1213_);
lean_closure_set(v___x_1220_, 2, v_x_1214_);
v___x_1221_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_findTask_1219_, v___x_1220_, v_a_1215_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___redArg___boxed(lean_object* v_doc_1222_, lean_object* v_p_1223_, lean_object* v_notFoundX_1224_, lean_object* v_x_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_doc_1222_, v_p_1223_, v_notFoundX_1224_, v_x_1225_, v_a_1226_);
lean_dec_ref(v_a_1226_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap(lean_object* v_00_u03b2_1229_, lean_object* v_doc_1230_, lean_object* v_p_1231_, lean_object* v_notFoundX_1232_, lean_object* v_x_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_doc_1230_, v_p_1231_, v_notFoundX_1232_, v_x_1233_, v_a_1234_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___boxed(lean_object* v_00_u03b2_1237_, lean_object* v_doc_1238_, lean_object* v_p_1239_, lean_object* v_notFoundX_1240_, lean_object* v_x_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_Server_RequestM_withWaitFindSnap(v_00_u03b2_1237_, v_doc_1238_, v_p_1239_, v_notFoundX_1240_, v_x_1241_, v_a_1242_);
lean_dec_ref(v_a_1242_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___redArg(lean_object* v_doc_1245_, lean_object* v_p_1246_, lean_object* v_notFoundX_1247_, lean_object* v_x_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v_toEditableDocumentCore_1251_; lean_object* v_cmdSnaps_1252_; lean_object* v_findTask_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v_toEditableDocumentCore_1251_ = lean_ctor_get(v_doc_1245_, 0);
lean_inc_ref(v_toEditableDocumentCore_1251_);
lean_dec_ref(v_doc_1245_);
v_cmdSnaps_1252_ = lean_ctor_get(v_toEditableDocumentCore_1251_, 2);
lean_inc(v_cmdSnaps_1252_);
lean_dec_ref(v_toEditableDocumentCore_1251_);
v_findTask_1253_ = l_Lean_AsyncList_waitFind_x3f___redArg(v_p_1246_, v_cmdSnaps_1252_);
v___x_1254_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_waitFindSnapAux___boxed), 6, 3);
lean_closure_set(v___x_1254_, 0, lean_box(0));
lean_closure_set(v___x_1254_, 1, v_notFoundX_1247_);
lean_closure_set(v___x_1254_, 2, v_x_1248_);
v___x_1255_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_findTask_1253_, v___x_1254_, v_a_1249_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___redArg___boxed(lean_object* v_doc_1256_, lean_object* v_p_1257_, lean_object* v_notFoundX_1258_, lean_object* v_x_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_Server_RequestM_bindWaitFindSnap___redArg(v_doc_1256_, v_p_1257_, v_notFoundX_1258_, v_x_1259_, v_a_1260_);
lean_dec_ref(v_a_1260_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap(lean_object* v_00_u03b2_1263_, lean_object* v_doc_1264_, lean_object* v_p_1265_, lean_object* v_notFoundX_1266_, lean_object* v_x_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Lean_Server_RequestM_bindWaitFindSnap___redArg(v_doc_1264_, v_p_1265_, v_notFoundX_1266_, v_x_1267_, v_a_1268_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___boxed(lean_object* v_00_u03b2_1271_, lean_object* v_doc_1272_, lean_object* v_p_1273_, lean_object* v_notFoundX_1274_, lean_object* v_x_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_Server_RequestM_bindWaitFindSnap(v_00_u03b2_1271_, v_doc_1272_, v_p_1273_, v_notFoundX_1274_, v_x_1275_, v_a_1276_);
lean_dec_ref(v_a_1276_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(lean_object* v___y_1279_){
_start:
{
lean_object* v_doc_1281_; lean_object* v___x_1282_; 
v_doc_1281_ = lean_ctor_get(v___y_1279_, 1);
lean_inc_ref(v_doc_1281_);
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v_doc_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0___boxed(lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(v___y_1283_);
lean_dec_ref(v___y_1283_);
return v_res_1285_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0(lean_object* v___x_1286_, lean_object* v_s_1287_){
_start:
{
lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1288_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_s_1287_);
v___x_1289_ = lean_nat_dec_le(v___x_1286_, v___x_1288_);
lean_dec(v___x_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0___boxed(lean_object* v___x_1290_, lean_object* v_s_1291_){
_start:
{
uint8_t v_res_1292_; lean_object* v_r_1293_; 
v_res_1292_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0(v___x_1290_, v_s_1291_);
lean_dec_ref(v_s_1291_);
lean_dec(v___x_1290_);
v_r_1293_ = lean_box(v_res_1292_);
return v_r_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1(lean_object* v___x_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1294_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1___boxed(lean_object* v___x_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1(v___x_1298_, v___y_1299_);
lean_dec_ref(v___y_1299_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg(lean_object* v_lspPos_1306_, lean_object* v_f_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v___x_1310_; lean_object* v_a_1311_; lean_object* v_toEditableDocumentCore_1312_; lean_object* v_meta_1313_; lean_object* v_text_1314_; lean_object* v_line_1315_; lean_object* v_character_1316_; lean_object* v___x_1317_; lean_object* v___f_1318_; uint8_t v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___f_1332_; lean_object* v___x_1333_; 
v___x_1310_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(v_a_1308_);
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1311_);
lean_dec_ref(v___x_1310_);
v_toEditableDocumentCore_1312_ = lean_ctor_get(v_a_1311_, 0);
v_meta_1313_ = lean_ctor_get(v_toEditableDocumentCore_1312_, 0);
v_text_1314_ = lean_ctor_get(v_meta_1313_, 3);
v_line_1315_ = lean_ctor_get(v_lspPos_1306_, 0);
lean_inc(v_line_1315_);
v_character_1316_ = lean_ctor_get(v_lspPos_1306_, 1);
lean_inc(v_character_1316_);
v___x_1317_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1314_, v_lspPos_1306_);
v___f_1318_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1318_, 0, v___x_1317_);
v___x_1319_ = 3;
v___x_1320_ = ((lean_object*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__0));
v___x_1321_ = ((lean_object*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__1));
v___x_1322_ = l_Nat_reprFast(v_line_1315_);
v___x_1323_ = lean_string_append(v___x_1321_, v___x_1322_);
lean_dec_ref(v___x_1322_);
v___x_1324_ = ((lean_object*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__2));
v___x_1325_ = lean_string_append(v___x_1323_, v___x_1324_);
v___x_1326_ = l_Nat_reprFast(v_character_1316_);
v___x_1327_ = lean_string_append(v___x_1325_, v___x_1326_);
lean_dec_ref(v___x_1326_);
v___x_1328_ = ((lean_object*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__3));
v___x_1329_ = lean_string_append(v___x_1327_, v___x_1328_);
v___x_1330_ = lean_string_append(v___x_1320_, v___x_1329_);
lean_dec_ref(v___x_1329_);
v___x_1331_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
lean_ctor_set_uint8(v___x_1331_, sizeof(void*)*1, v___x_1319_);
v___f_1332_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1332_, 0, v___x_1331_);
v___x_1333_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_a_1311_, v___f_1318_, v___f_1332_, v_f_1307_, v_a_1308_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___boxed(lean_object* v_lspPos_1334_, lean_object* v_f_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg(v_lspPos_1334_, v_f_1335_, v_a_1336_);
lean_dec_ref(v_a_1336_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos(lean_object* v_00_u03b1_1339_, lean_object* v_lspPos_1340_, lean_object* v_f_1341_, lean_object* v_a_1342_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg(v_lspPos_1340_, v_f_1341_, v_a_1342_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___boxed(lean_object* v_00_u03b1_1345_, lean_object* v_lspPos_1346_, lean_object* v_f_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos(v_00_u03b1_1345_, v_lspPos_1346_, v_f_1347_, v_a_1348_);
lean_dec_ref(v_a_1348_);
return v_res_1350_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_isAfterHoverPos(lean_object* v_hoverPos_1351_, lean_object* v_cmdParsed_1352_){
_start:
{
lean_object* v_stx_1353_; uint8_t v___x_1354_; lean_object* v___x_1355_; 
v_stx_1353_ = lean_ctor_get(v_cmdParsed_1352_, 1);
v___x_1354_ = 1;
v___x_1355_ = l_Lean_Syntax_getPos_x3f(v_stx_1353_, v___x_1354_);
if (lean_obj_tag(v___x_1355_) == 1)
{
lean_object* v_val_1356_; uint8_t v___x_1357_; 
v_val_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_val_1356_);
lean_dec_ref_known(v___x_1355_, 1);
v___x_1357_ = lean_nat_dec_lt(v_hoverPos_1351_, v_val_1356_);
lean_dec(v_val_1356_);
return v___x_1357_;
}
else
{
uint8_t v___x_1358_; 
lean_dec(v___x_1355_);
v___x_1358_ = 0;
return v___x_1358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_isAfterHoverPos___boxed(lean_object* v_hoverPos_1359_, lean_object* v_cmdParsed_1360_){
_start:
{
uint8_t v_res_1361_; lean_object* v_r_1362_; 
v_res_1361_ = l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_isAfterHoverPos(v_hoverPos_1359_, v_cmdParsed_1360_);
lean_dec_ref(v_cmdParsed_1360_);
lean_dec(v_hoverPos_1359_);
v_r_1362_ = lean_box(v_res_1361_);
return v_r_1362_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_containsHoverPos(lean_object* v_doc_1363_, lean_object* v_hoverPos_1364_, lean_object* v_cmdParsed_1365_){
_start:
{
lean_object* v_stx_1366_; uint8_t v___x_1367_; lean_object* v___x_1368_; 
v_stx_1366_ = lean_ctor_get(v_cmdParsed_1365_, 1);
v___x_1367_ = 1;
v___x_1368_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_1366_, v___x_1367_);
if (lean_obj_tag(v___x_1368_) == 1)
{
lean_object* v_toEditableDocumentCore_1369_; lean_object* v_meta_1370_; lean_object* v_val_1371_; lean_object* v_text_1372_; uint8_t v___x_1373_; uint8_t v___x_1374_; 
v_toEditableDocumentCore_1369_ = lean_ctor_get(v_doc_1363_, 0);
v_meta_1370_ = lean_ctor_get(v_toEditableDocumentCore_1369_, 0);
v_val_1371_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_val_1371_);
lean_dec_ref_known(v___x_1368_, 1);
v_text_1372_ = lean_ctor_get(v_meta_1370_, 3);
v___x_1373_ = 0;
v___x_1374_ = l_Lean_FileMap_rangeContainsHoverPos(v_text_1372_, v_val_1371_, v_hoverPos_1364_, v___x_1373_);
lean_dec(v_val_1371_);
return v___x_1374_;
}
else
{
uint8_t v___x_1375_; 
lean_dec(v___x_1368_);
v___x_1375_ = 0;
return v___x_1375_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_containsHoverPos___boxed(lean_object* v_doc_1376_, lean_object* v_hoverPos_1377_, lean_object* v_cmdParsed_1378_){
_start:
{
uint8_t v_res_1379_; lean_object* v_r_1380_; 
v_res_1379_ = l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_containsHoverPos(v_doc_1376_, v_hoverPos_1377_, v_cmdParsed_1378_);
lean_dec_ref(v_cmdParsed_1378_);
lean_dec(v_hoverPos_1377_);
lean_dec_ref(v_doc_1376_);
v_r_1380_ = lean_box(v_res_1379_);
return v_r_1380_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0(void){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = lean_box(0);
v___x_1382_ = lean_task_pure(v___x_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go(lean_object* v_doc_1383_, lean_object* v_hoverPos_1384_, lean_object* v_cmdParsed_1385_){
_start:
{
uint8_t v___x_1386_; 
v___x_1386_ = l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_containsHoverPos(v_doc_1383_, v_hoverPos_1384_, v_cmdParsed_1385_);
if (v___x_1386_ == 0)
{
uint8_t v___x_1387_; 
v___x_1387_ = l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_isAfterHoverPos(v_hoverPos_1384_, v_cmdParsed_1385_);
if (v___x_1387_ == 0)
{
lean_object* v_nextCmdSnap_x3f_1388_; 
v_nextCmdSnap_x3f_1388_ = lean_ctor_get(v_cmdParsed_1385_, 4);
lean_inc(v_nextCmdSnap_x3f_1388_);
lean_dec_ref(v_cmdParsed_1385_);
if (lean_obj_tag(v_nextCmdSnap_x3f_1388_) == 0)
{
lean_object* v___x_1389_; 
lean_dec(v_hoverPos_1384_);
lean_dec_ref(v_doc_1383_);
v___x_1389_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0, &l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0);
return v___x_1389_;
}
else
{
lean_object* v_val_1390_; lean_object* v_task_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v_val_1390_ = lean_ctor_get(v_nextCmdSnap_x3f_1388_, 0);
lean_inc(v_val_1390_);
lean_dec_ref_known(v_nextCmdSnap_x3f_1388_, 1);
v_task_1391_ = lean_ctor_get(v_val_1390_, 3);
lean_inc_ref(v_task_1391_);
lean_dec(v_val_1390_);
v___x_1392_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go), 3, 2);
lean_closure_set(v___x_1392_, 0, v_doc_1383_);
lean_closure_set(v___x_1392_, 1, v_hoverPos_1384_);
v___x_1393_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_task_1391_, v___x_1392_);
return v___x_1393_;
}
}
else
{
lean_object* v___x_1394_; 
lean_dec_ref(v_cmdParsed_1385_);
lean_dec(v_hoverPos_1384_);
lean_dec_ref(v_doc_1383_);
v___x_1394_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0, &l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0);
return v___x_1394_;
}
}
else
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
lean_dec(v_hoverPos_1384_);
lean_dec_ref(v_doc_1383_);
v___x_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1395_, 0, v_cmdParsed_1385_);
v___x_1396_ = lean_task_pure(v___x_1395_);
return v___x_1396_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdParsedSnap___lam__0(lean_object* v_doc_1397_, lean_object* v_hoverPos_1398_, lean_object* v_headerProcessed_1399_){
_start:
{
lean_object* v_result_x3f_1400_; 
v_result_x3f_1400_ = lean_ctor_get(v_headerProcessed_1399_, 2);
lean_inc(v_result_x3f_1400_);
lean_dec_ref(v_headerProcessed_1399_);
if (lean_obj_tag(v_result_x3f_1400_) == 1)
{
lean_object* v_val_1401_; lean_object* v_firstCmdSnap_1402_; lean_object* v_task_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v_val_1401_ = lean_ctor_get(v_result_x3f_1400_, 0);
lean_inc(v_val_1401_);
lean_dec_ref_known(v_result_x3f_1400_, 1);
v_firstCmdSnap_1402_ = lean_ctor_get(v_val_1401_, 1);
lean_inc_ref(v_firstCmdSnap_1402_);
lean_dec(v_val_1401_);
v_task_1403_ = lean_ctor_get(v_firstCmdSnap_1402_, 3);
lean_inc_ref(v_task_1403_);
lean_dec_ref(v_firstCmdSnap_1402_);
v___x_1404_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go), 3, 2);
lean_closure_set(v___x_1404_, 0, v_doc_1397_);
lean_closure_set(v___x_1404_, 1, v_hoverPos_1398_);
v___x_1405_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_task_1403_, v___x_1404_);
return v___x_1405_;
}
else
{
lean_object* v___x_1406_; 
lean_dec(v_result_x3f_1400_);
lean_dec(v_hoverPos_1398_);
lean_dec_ref(v_doc_1397_);
v___x_1406_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0, &l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0);
return v___x_1406_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdParsedSnap(lean_object* v_doc_1407_, lean_object* v_hoverPos_1408_){
_start:
{
lean_object* v_toEditableDocumentCore_1409_; lean_object* v_initSnap_1410_; lean_object* v_result_x3f_1411_; 
v_toEditableDocumentCore_1409_ = lean_ctor_get(v_doc_1407_, 0);
v_initSnap_1410_ = lean_ctor_get(v_toEditableDocumentCore_1409_, 1);
v_result_x3f_1411_ = lean_ctor_get(v_initSnap_1410_, 4);
if (lean_obj_tag(v_result_x3f_1411_) == 1)
{
lean_object* v_val_1412_; lean_object* v_processedSnap_1413_; lean_object* v_task_1414_; lean_object* v___f_1415_; lean_object* v___x_1416_; 
v_val_1412_ = lean_ctor_get(v_result_x3f_1411_, 0);
v_processedSnap_1413_ = lean_ctor_get(v_val_1412_, 1);
v_task_1414_ = lean_ctor_get(v_processedSnap_1413_, 3);
lean_inc_ref(v_task_1414_);
v___f_1415_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_findCmdParsedSnap___lam__0), 3, 2);
lean_closure_set(v___f_1415_, 0, v_doc_1407_);
lean_closure_set(v___f_1415_, 1, v_hoverPos_1408_);
v___x_1416_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_task_1414_, v___f_1415_);
return v___x_1416_;
}
else
{
lean_object* v___x_1417_; 
lean_dec(v_hoverPos_1408_);
lean_dec_ref(v_doc_1407_);
v___x_1417_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0, &l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_RequestM_findCmdParsedSnap_go___closed__0);
return v___x_1417_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__0(lean_object* v_msg_1418_){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = lean_box(0);
v___x_1420_ = lean_panic_fn_borrowed(v___x_1419_, v_msg_1418_);
return v___x_1420_;
}
}
static lean_object* _init_l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1424_ = ((lean_object*)(l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__2));
v___x_1425_ = lean_unsigned_to_nat(8u);
v___x_1426_ = lean_unsigned_to_nat(420u);
v___x_1427_ = ((lean_object*)(l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__1));
v___x_1428_ = ((lean_object*)(l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__0));
v___x_1429_ = l_mkPanicMessageWithDecl(v___x_1428_, v___x_1427_, v___x_1426_, v___x_1425_, v___x_1424_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lam__0(lean_object* v_stx_1430_, lean_object* v_s_1431_){
_start:
{
lean_object* v_infoTree_x3f_1432_; 
v_infoTree_x3f_1432_ = lean_ctor_get(v_s_1431_, 2);
lean_inc(v_infoTree_x3f_1432_);
lean_dec_ref(v_s_1431_);
if (lean_obj_tag(v_infoTree_x3f_1432_) == 0)
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
lean_dec(v_stx_1430_);
v___x_1433_ = lean_obj_once(&l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__3, &l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__3_once, _init_l_Lean_Server_RequestM_findCmdDataAtPos___lam__0___closed__3);
v___x_1434_ = l_panic___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__0(v___x_1433_);
return v___x_1434_;
}
else
{
lean_object* v_val_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1443_; 
v_val_1435_ = lean_ctor_get(v_infoTree_x3f_1432_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_infoTree_x3f_1432_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1437_ = v_infoTree_x3f_1432_;
v_isShared_1438_ = v_isSharedCheck_1443_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_val_1435_);
lean_dec(v_infoTree_x3f_1432_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1443_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1439_; lean_object* v___x_1441_; 
v___x_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1439_, 0, v_stx_1430_);
lean_ctor_set(v___x_1439_, 1, v_val_1435_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 0, v___x_1439_);
v___x_1441_ = v___x_1437_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1439_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lam__1(lean_object* v_elabSnap_1444_, lean_object* v___f_1445_, lean_object* v_stx_1446_, lean_object* v_x_1447_){
_start:
{
if (lean_obj_tag(v_x_1447_) == 0)
{
lean_object* v_infoTreeSnap_1448_; lean_object* v_task_1449_; lean_object* v___x_1450_; 
lean_dec(v_stx_1446_);
v_infoTreeSnap_1448_ = lean_ctor_get(v_elabSnap_1444_, 3);
lean_inc_ref(v_infoTreeSnap_1448_);
lean_dec_ref(v_elabSnap_1444_);
v_task_1449_ = lean_ctor_get(v_infoTreeSnap_1448_, 3);
lean_inc_ref(v_task_1449_);
lean_dec_ref(v_infoTreeSnap_1448_);
v___x_1450_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_1445_, v_task_1449_);
return v___x_1450_;
}
else
{
lean_object* v_val_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1460_; 
lean_dec_ref(v___f_1445_);
lean_dec_ref(v_elabSnap_1444_);
v_val_1451_ = lean_ctor_get(v_x_1447_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_x_1447_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1453_ = v_x_1447_;
v_isShared_1454_ = v_isSharedCheck_1460_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_val_1451_);
lean_dec(v_x_1447_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1460_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; lean_object* v___x_1457_; 
v___x_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1455_, 0, v_stx_1446_);
lean_ctor_set(v___x_1455_, 1, v_val_1451_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1455_);
v___x_1457_ = v___x_1453_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1455_);
v___x_1457_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1458_; 
v___x_1458_ = lean_task_pure(v___x_1457_);
return v___x_1458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__4(lean_object* v_t_1462_, lean_object* v_a_1463_){
_start:
{
lean_object* v___f_1464_; lean_object* v___x_1465_; 
v___f_1464_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__4___closed__0));
v___x_1465_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_1462_, v___f_1464_, v_a_1463_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__4___boxed(lean_object* v_t_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__4(v_t_1466_, v_a_1467_);
lean_dec_ref(v_a_1467_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2___lam__0(lean_object* v_s_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_toSnapshot_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1482_; 
v_toSnapshot_1473_ = lean_ctor_get(v_s_1471_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_s_1471_);
if (v_isSharedCheck_1482_ == 0)
{
lean_object* v_unused_1483_; 
v_unused_1483_ = lean_ctor_get(v_s_1471_, 1);
lean_dec(v_unused_1483_);
v___x_1475_ = v_s_1471_;
v_isShared_1476_ = v_isSharedCheck_1482_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_toSnapshot_1473_);
lean_dec(v_s_1471_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1482_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1480_; 
v___x_1477_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_1473_, v___y_1472_);
v___x_1478_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2___lam__0___closed__0));
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 1, v___x_1478_);
lean_ctor_set(v___x_1475_, 0, v___x_1477_);
v___x_1480_ = v___x_1475_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1477_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2___lam__0___boxed(lean_object* v_s_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2___lam__0(v_s_1484_, v___y_1485_);
lean_dec_ref(v___y_1485_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2(lean_object* v_t_1488_, lean_object* v_a_1489_){
_start:
{
lean_object* v___f_1490_; lean_object* v___x_1491_; 
v___f_1490_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2___closed__0));
v___x_1491_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_1488_, v___f_1490_, v_a_1489_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2___boxed(lean_object* v_t_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2(v_t_1492_, v_a_1493_);
lean_dec_ref(v_a_1493_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__1___lam__0(lean_object* v_s_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v_toSnapshotTreeM_1497_; lean_object* v___x_1498_; 
v_toSnapshotTreeM_1497_ = lean_ctor_get(v_s_1495_, 1);
lean_inc_ref(v_toSnapshotTreeM_1497_);
lean_dec_ref(v_s_1495_);
lean_inc_ref(v___y_1496_);
v___x_1498_ = lean_apply_1(v_toSnapshotTreeM_1497_, v___y_1496_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__1___lam__0___boxed(lean_object* v_s_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__1___lam__0(v_s_1499_, v___y_1500_);
lean_dec_ref(v___y_1500_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__1(lean_object* v_t_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v___f_1505_; lean_object* v___x_1506_; 
v___f_1505_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__1___closed__0));
v___x_1506_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_1503_, v___f_1505_, v_a_1504_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__1___boxed(lean_object* v_t_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__1(v_t_1507_, v_a_1508_);
lean_dec_ref(v_a_1508_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__3___lam__0(lean_object* v_s_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1512_ = l_Lean_Language_Snapshot_transform(v_s_1510_, v___y_1511_);
v___x_1513_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2___lam__0___closed__0));
v___x_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1512_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__3___lam__0___boxed(lean_object* v_s_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__3___lam__0(v_s_1515_, v___y_1516_);
lean_dec_ref(v___y_1516_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__3(lean_object* v_t_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v___f_1521_; lean_object* v___x_1522_; 
v___f_1521_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__3___closed__0));
v___x_1522_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_1519_, v___f_1521_, v_a_1520_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__3___boxed(lean_object* v_t_1523_, lean_object* v_a_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__3(v_t_1523_, v_a_1524_);
lean_dec_ref(v_a_1524_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1(lean_object* v_a_1526_){
_start:
{
lean_object* v_toSnapshot_1527_; lean_object* v_elabSnap_1528_; lean_object* v_resultSnap_1529_; lean_object* v_infoTreeSnap_1530_; lean_object* v_reportSnap_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v_toSnapshot_1527_ = lean_ctor_get(v_a_1526_, 0);
lean_inc_ref(v_toSnapshot_1527_);
v_elabSnap_1528_ = lean_ctor_get(v_a_1526_, 1);
lean_inc_ref(v_elabSnap_1528_);
v_resultSnap_1529_ = lean_ctor_get(v_a_1526_, 2);
lean_inc_ref(v_resultSnap_1529_);
v_infoTreeSnap_1530_ = lean_ctor_get(v_a_1526_, 3);
lean_inc_ref(v_infoTreeSnap_1530_);
v_reportSnap_1531_ = lean_ctor_get(v_a_1526_, 4);
lean_inc_ref(v_reportSnap_1531_);
lean_dec_ref(v_a_1526_);
v___x_1532_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1533_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_1527_, v___x_1532_);
v___x_1534_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__1(v_elabSnap_1528_, v___x_1532_);
v___x_1535_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__2(v_resultSnap_1529_, v___x_1532_);
v___x_1536_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__3(v_infoTreeSnap_1530_, v___x_1532_);
v___x_1537_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1_spec__4(v_reportSnap_1531_, v___x_1532_);
v___x_1538_ = lean_unsigned_to_nat(4u);
v___x_1539_ = lean_mk_empty_array_with_capacity(v___x_1538_);
v___x_1540_ = lean_array_push(v___x_1539_, v___x_1534_);
v___x_1541_ = lean_array_push(v___x_1540_, v___x_1535_);
v___x_1542_ = lean_array_push(v___x_1541_, v___x_1536_);
v___x_1543_ = lean_array_push(v___x_1542_, v___x_1537_);
v___x_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1533_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
return v___x_1544_;
}
}
static lean_object* _init_l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___closed__0(void){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = lean_box(0);
v___x_1546_ = lean_task_pure(v___x_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lam__2(lean_object* v_doc_1547_, lean_object* v_hoverPos_1548_, uint8_t v_includeStop_1549_, lean_object* v_x_1550_){
_start:
{
if (lean_obj_tag(v_x_1550_) == 0)
{
lean_object* v___x_1551_; 
lean_dec(v_hoverPos_1548_);
lean_dec_ref(v_doc_1547_);
v___x_1551_ = lean_obj_once(&l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___closed__0, &l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___closed__0_once, _init_l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___closed__0);
return v___x_1551_;
}
else
{
lean_object* v_toEditableDocumentCore_1552_; lean_object* v_meta_1553_; lean_object* v_val_1554_; lean_object* v_text_1555_; lean_object* v_stx_1556_; lean_object* v_elabSnap_1557_; lean_object* v___f_1558_; lean_object* v___f_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v_toEditableDocumentCore_1552_ = lean_ctor_get(v_doc_1547_, 0);
lean_inc_ref(v_toEditableDocumentCore_1552_);
lean_dec_ref(v_doc_1547_);
v_meta_1553_ = lean_ctor_get(v_toEditableDocumentCore_1552_, 0);
lean_inc_ref(v_meta_1553_);
lean_dec_ref(v_toEditableDocumentCore_1552_);
v_val_1554_ = lean_ctor_get(v_x_1550_, 0);
lean_inc(v_val_1554_);
lean_dec_ref_known(v_x_1550_, 1);
v_text_1555_ = lean_ctor_get(v_meta_1553_, 3);
lean_inc_ref(v_text_1555_);
lean_dec_ref(v_meta_1553_);
v_stx_1556_ = lean_ctor_get(v_val_1554_, 1);
lean_inc_n(v_stx_1556_, 2);
v_elabSnap_1557_ = lean_ctor_get(v_val_1554_, 3);
lean_inc_ref_n(v_elabSnap_1557_, 2);
lean_dec(v_val_1554_);
v___f_1558_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_findCmdDataAtPos___lam__0), 2, 1);
lean_closure_set(v___f_1558_, 0, v_stx_1556_);
v___f_1559_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_findCmdDataAtPos___lam__1), 4, 3);
lean_closure_set(v___f_1559_, 0, v_elabSnap_1557_);
lean_closure_set(v___f_1559_, 1, v___f_1558_);
lean_closure_set(v___f_1559_, 2, v_stx_1556_);
v___x_1560_ = l_Lean_Language_toSnapshotTree___at___00Lean_Server_RequestM_findCmdDataAtPos_spec__1(v_elabSnap_1557_);
v___x_1561_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos(v_text_1555_, v___x_1560_, v_hoverPos_1548_, v_includeStop_1549_);
v___x_1562_ = l_Lean_Server_ServerTask_bindCheap___redArg(v___x_1561_, v___f_1559_);
return v___x_1562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___boxed(lean_object* v_doc_1563_, lean_object* v_hoverPos_1564_, lean_object* v_includeStop_1565_, lean_object* v_x_1566_){
_start:
{
uint8_t v_includeStop_boxed_1567_; lean_object* v_res_1568_; 
v_includeStop_boxed_1567_ = lean_unbox(v_includeStop_1565_);
v_res_1568_ = l_Lean_Server_RequestM_findCmdDataAtPos___lam__2(v_doc_1563_, v_hoverPos_1564_, v_includeStop_boxed_1567_, v_x_1566_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos(lean_object* v_doc_1569_, lean_object* v_hoverPos_1570_, uint8_t v_includeStop_1571_){
_start:
{
lean_object* v___x_1572_; lean_object* v___f_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1572_ = lean_box(v_includeStop_1571_);
lean_inc(v_hoverPos_1570_);
lean_inc_ref(v_doc_1569_);
v___f_1573_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_findCmdDataAtPos___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1573_, 0, v_doc_1569_);
lean_closure_set(v___f_1573_, 1, v_hoverPos_1570_);
lean_closure_set(v___f_1573_, 2, v___x_1572_);
v___x_1574_ = l_Lean_Server_RequestM_findCmdParsedSnap(v_doc_1569_, v_hoverPos_1570_);
v___x_1575_ = l_Lean_Server_ServerTask_bindCheap___redArg(v___x_1574_, v___f_1573_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findCmdDataAtPos___boxed(lean_object* v_doc_1576_, lean_object* v_hoverPos_1577_, lean_object* v_includeStop_1578_){
_start:
{
uint8_t v_includeStop_boxed_1579_; lean_object* v_res_1580_; 
v_includeStop_boxed_1579_ = lean_unbox(v_includeStop_1578_);
v_res_1580_ = l_Lean_Server_RequestM_findCmdDataAtPos(v_doc_1576_, v_hoverPos_1577_, v_includeStop_boxed_1579_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findInfoTreeAtPos___lam__0(lean_object* v_x_1581_){
_start:
{
if (lean_obj_tag(v_x_1581_) == 0)
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_box(0);
return v___x_1582_;
}
else
{
lean_object* v_val_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1591_; 
v_val_1583_ = lean_ctor_get(v_x_1581_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_x_1581_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1585_ = v_x_1581_;
v_isShared_1586_ = v_isSharedCheck_1591_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_val_1583_);
lean_dec(v_x_1581_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1591_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v_snd_1587_; lean_object* v___x_1589_; 
v_snd_1587_ = lean_ctor_get(v_val_1583_, 1);
lean_inc(v_snd_1587_);
lean_dec(v_val_1583_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 0, v_snd_1587_);
v___x_1589_ = v___x_1585_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_snd_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findInfoTreeAtPos(lean_object* v_doc_1593_, lean_object* v_hoverPos_1594_, uint8_t v_includeStop_1595_){
_start:
{
lean_object* v___f_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___f_1596_ = ((lean_object*)(l_Lean_Server_RequestM_findInfoTreeAtPos___closed__0));
v___x_1597_ = l_Lean_Server_RequestM_findCmdDataAtPos(v_doc_1593_, v_hoverPos_1594_, v_includeStop_1595_);
v___x_1598_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_1596_, v___x_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_findInfoTreeAtPos___boxed(lean_object* v_doc_1599_, lean_object* v_hoverPos_1600_, lean_object* v_includeStop_1601_){
_start:
{
uint8_t v_includeStop_boxed_1602_; lean_object* v_res_1603_; 
v_includeStop_boxed_1602_ = lean_unbox(v_includeStop_1601_);
v_res_1603_ = l_Lean_Server_RequestM_findInfoTreeAtPos(v_doc_1599_, v_hoverPos_1600_, v_includeStop_boxed_1602_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___redArg(lean_object* v_snap_1604_, lean_object* v_c_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v_doc_1608_; lean_object* v_toEditableDocumentCore_1609_; lean_object* v_meta_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v_doc_1608_ = lean_ctor_get(v_a_1606_, 1);
v_toEditableDocumentCore_1609_ = lean_ctor_get(v_doc_1608_, 0);
v_meta_1610_ = lean_ctor_get(v_toEditableDocumentCore_1609_, 0);
lean_inc_ref(v_a_1606_);
v___x_1611_ = lean_apply_1(v_c_1605_, v_a_1606_);
v___x_1612_ = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(v_snap_1604_, v_meta_1610_, v___x_1611_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1625_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1615_ = v___x_1612_;
v_isShared_1616_ = v_isSharedCheck_1625_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1612_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1625_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
if (lean_obj_tag(v_a_1613_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1619_; 
v_a_1617_ = lean_ctor_get(v_a_1613_, 0);
lean_inc(v_a_1617_);
lean_dec_ref_known(v_a_1613_, 1);
if (v_isShared_1616_ == 0)
{
lean_ctor_set_tag(v___x_1615_, 1);
lean_ctor_set(v___x_1615_, 0, v_a_1617_);
v___x_1619_ = v___x_1615_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1617_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; 
v_a_1621_ = lean_ctor_get(v_a_1613_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v_a_1613_, 1);
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 0, v_a_1621_);
v___x_1623_ = v___x_1615_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1627_; lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
v_a_1626_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v___x_1612_, 1);
v___x_1627_ = l_Lean_Server_RequestError_ofException(v_a_1626_);
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1627_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1627_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
lean_ctor_set_tag(v___x_1630_, 1);
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
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
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___redArg___boxed(lean_object* v_snap_1636_, lean_object* v_c_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Lean_Server_RequestM_runCommandElabM___redArg(v_snap_1636_, v_c_1637_, v_a_1638_);
lean_dec_ref(v_a_1638_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM(lean_object* v_00_u03b1_1641_, lean_object* v_snap_1642_, lean_object* v_c_1643_, lean_object* v_a_1644_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_Server_RequestM_runCommandElabM___redArg(v_snap_1642_, v_c_1643_, v_a_1644_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___boxed(lean_object* v_00_u03b1_1647_, lean_object* v_snap_1648_, lean_object* v_c_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Lean_Server_RequestM_runCommandElabM(v_00_u03b1_1647_, v_snap_1648_, v_c_1649_, v_a_1650_);
lean_dec_ref(v_a_1650_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___redArg(lean_object* v_snap_1653_, lean_object* v_c_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v_doc_1657_; lean_object* v_toEditableDocumentCore_1658_; lean_object* v_meta_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v_doc_1657_ = lean_ctor_get(v_a_1655_, 1);
v_toEditableDocumentCore_1658_ = lean_ctor_get(v_doc_1657_, 0);
v_meta_1659_ = lean_ctor_get(v_toEditableDocumentCore_1658_, 0);
lean_inc_ref(v_a_1655_);
v___x_1660_ = lean_apply_1(v_c_1654_, v_a_1655_);
v___x_1661_ = l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(v_snap_1653_, v_meta_1659_, v___x_1660_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1674_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1674_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1674_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
if (lean_obj_tag(v_a_1662_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1668_; 
v_a_1666_ = lean_ctor_get(v_a_1662_, 0);
lean_inc(v_a_1666_);
lean_dec_ref_known(v_a_1662_, 1);
if (v_isShared_1665_ == 0)
{
lean_ctor_set_tag(v___x_1664_, 1);
lean_ctor_set(v___x_1664_, 0, v_a_1666_);
v___x_1668_ = v___x_1664_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1666_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; 
v_a_1670_ = lean_ctor_get(v_a_1662_, 0);
lean_inc(v_a_1670_);
lean_dec_ref_known(v_a_1662_, 1);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v_a_1670_);
v___x_1672_ = v___x_1664_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
else
{
lean_object* v_a_1675_; lean_object* v___x_1676_; lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
v_a_1675_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1675_);
lean_dec_ref_known(v___x_1661_, 1);
v___x_1676_ = l_Lean_Server_RequestError_ofException(v_a_1675_);
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1676_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1676_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
lean_ctor_set_tag(v___x_1679_, 1);
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___redArg___boxed(lean_object* v_snap_1685_, lean_object* v_c_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Lean_Server_RequestM_runCoreM___redArg(v_snap_1685_, v_c_1686_, v_a_1687_);
lean_dec_ref(v_a_1687_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM(lean_object* v_00_u03b1_1690_, lean_object* v_snap_1691_, lean_object* v_c_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_Server_RequestM_runCoreM___redArg(v_snap_1691_, v_c_1692_, v_a_1693_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___boxed(lean_object* v_00_u03b1_1696_, lean_object* v_snap_1697_, lean_object* v_c_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_Server_RequestM_runCoreM(v_00_u03b1_1696_, v_snap_1697_, v_c_1698_, v_a_1699_);
lean_dec_ref(v_a_1699_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___redArg(lean_object* v_snap_1702_, lean_object* v_c_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v_doc_1706_; lean_object* v_toEditableDocumentCore_1707_; lean_object* v_meta_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v_doc_1706_ = lean_ctor_get(v_a_1704_, 1);
v_toEditableDocumentCore_1707_ = lean_ctor_get(v_doc_1706_, 0);
v_meta_1708_ = lean_ctor_get(v_toEditableDocumentCore_1707_, 0);
lean_inc_ref(v_a_1704_);
v___x_1709_ = lean_apply_1(v_c_1703_, v_a_1704_);
v___x_1710_ = l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg(v_snap_1702_, v_meta_1708_, v___x_1709_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1723_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1713_ = v___x_1710_;
v_isShared_1714_ = v_isSharedCheck_1723_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1710_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1723_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
if (lean_obj_tag(v_a_1711_) == 0)
{
lean_object* v_a_1715_; lean_object* v___x_1717_; 
v_a_1715_ = lean_ctor_get(v_a_1711_, 0);
lean_inc(v_a_1715_);
lean_dec_ref_known(v_a_1711_, 1);
if (v_isShared_1714_ == 0)
{
lean_ctor_set_tag(v___x_1713_, 1);
lean_ctor_set(v___x_1713_, 0, v_a_1715_);
v___x_1717_ = v___x_1713_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1715_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
else
{
lean_object* v_a_1719_; lean_object* v___x_1721_; 
v_a_1719_ = lean_ctor_get(v_a_1711_, 0);
lean_inc(v_a_1719_);
lean_dec_ref_known(v_a_1711_, 1);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 0, v_a_1719_);
v___x_1721_ = v___x_1713_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1719_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1725_; lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
v_a_1724_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_a_1724_);
lean_dec_ref_known(v___x_1710_, 1);
v___x_1725_ = l_Lean_Server_RequestError_ofException(v_a_1724_);
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1725_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1725_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
lean_ctor_set_tag(v___x_1728_, 1);
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___redArg___boxed(lean_object* v_snap_1734_, lean_object* v_c_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_Server_RequestM_runTermElabM___redArg(v_snap_1734_, v_c_1735_, v_a_1736_);
lean_dec_ref(v_a_1736_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM(lean_object* v_00_u03b1_1739_, lean_object* v_snap_1740_, lean_object* v_c_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_Server_RequestM_runTermElabM___redArg(v_snap_1740_, v_c_1741_, v_a_1742_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___boxed(lean_object* v_00_u03b1_1745_, lean_object* v_snap_1746_, lean_object* v_c_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_Server_RequestM_runTermElabM(v_00_u03b1_1745_, v_snap_1746_, v_c_1747_, v_a_1748_);
lean_dec_ref(v_a_1748_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage(lean_object* v_id_1757_, lean_object* v_r_1758_){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___y_1762_; 
v___x_1759_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__0));
v___x_1760_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__1));
switch(lean_obj_tag(v_id_1757_))
{
case 0:
{
lean_object* v_s_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
v_s_1776_ = lean_ctor_get(v_id_1757_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v_id_1757_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v_id_1757_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_s_1776_);
lean_dec(v_id_1757_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
lean_ctor_set_tag(v___x_1778_, 3);
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_s_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
v___y_1762_ = v___x_1781_;
goto v___jp_1761_;
}
}
}
case 1:
{
lean_object* v_n_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
v_n_1784_ = lean_ctor_get(v_id_1757_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_id_1757_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v_id_1757_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_n_1784_);
lean_dec(v_id_1757_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
lean_ctor_set_tag(v___x_1786_, 2);
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_n_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
v___y_1762_ = v___x_1789_;
goto v___jp_1761_;
}
}
}
default: 
{
lean_object* v___x_1792_; 
v___x_1792_ = lean_box(0);
v___y_1762_ = v___x_1792_;
goto v___jp_1761_;
}
}
v___jp_1761_:
{
lean_object* v_serialized_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v_serialized_1763_ = lean_ctor_get(v_r_1758_, 1);
v___x_1764_ = l_Lean_Json_compress(v___y_1762_);
v___x_1765_ = lean_string_append(v___x_1760_, v___x_1764_);
lean_dec_ref(v___x_1764_);
v___x_1766_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__2));
v___x_1767_ = lean_string_append(v___x_1765_, v___x_1766_);
v___x_1768_ = lean_string_append(v___x_1759_, v___x_1767_);
lean_dec_ref(v___x_1767_);
v___x_1769_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__3));
v___x_1770_ = lean_string_append(v___x_1768_, v___x_1769_);
v___x_1771_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__4));
v___x_1772_ = lean_string_append(v___x_1771_, v_serialized_1763_);
v___x_1773_ = lean_string_append(v___x_1770_, v___x_1772_);
lean_dec_ref(v___x_1772_);
v___x_1774_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__5));
v___x_1775_ = lean_string_append(v___x_1773_, v___x_1774_);
return v___x_1775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage___boxed(lean_object* v_id_1793_, lean_object* v_r_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Lean_Server_SerializedLspResponse_toSerializedMessage(v_id_1793_, v_r_1794_);
lean_dec_ref(v_r_1794_);
return v_res_1795_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1796_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_);
v___x_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1800_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_);
v___x_1801_ = lean_st_mk_ref(v___x_1800_);
v___x_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2____boxed(lean_object* v_a_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_();
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__0(lean_object* v_inst_1805_, lean_object* v_inst_1806_, lean_object* v_j_1807_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Lean_Server_parseRequestParams___redArg(v_inst_1805_, v_j_1807_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
lean_dec_ref(v_inst_1806_);
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1808_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1808_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1825_; 
v_a_1817_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1819_ = v___x_1808_;
v_isShared_1820_ = v_isSharedCheck_1825_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1808_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1825_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1821_; lean_object* v___x_1823_; 
v___x_1821_ = lean_apply_1(v_inst_1806_, v_a_1817_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___x_1821_);
v___x_1823_ = v___x_1819_;
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__1(lean_object* v_serialize_x3f_1826_, lean_object* v_inst_1827_, lean_object* v_r_1828_){
_start:
{
if (lean_obj_tag(v_serialize_x3f_1826_) == 1)
{
lean_object* v_val_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; uint8_t v___x_1832_; lean_object* v___x_1833_; 
lean_dec_ref(v_inst_1827_);
v_val_1829_ = lean_ctor_get(v_serialize_x3f_1826_, 0);
lean_inc(v_val_1829_);
lean_dec_ref_known(v_serialize_x3f_1826_, 1);
v___x_1830_ = lean_box(0);
v___x_1831_ = lean_apply_1(v_val_1829_, v_r_1828_);
v___x_1832_ = 1;
v___x_1833_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1833_, 0, v___x_1830_);
lean_ctor_set(v___x_1833_, 1, v___x_1831_);
lean_ctor_set_uint8(v___x_1833_, sizeof(void*)*2, v___x_1832_);
return v___x_1833_;
}
else
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; lean_object* v___x_1838_; 
lean_dec(v_serialize_x3f_1826_);
v___x_1834_ = lean_apply_1(v_inst_1827_, v_r_1828_);
lean_inc(v___x_1834_);
v___x_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
v___x_1836_ = l_Lean_Json_compress(v___x_1834_);
v___x_1837_ = 1;
v___x_1838_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1838_, 0, v___x_1835_);
lean_ctor_set(v___x_1838_, 1, v___x_1836_);
lean_ctor_set_uint8(v___x_1838_, sizeof(void*)*2, v___x_1837_);
return v___x_1838_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__2(lean_object* v_inst_1839_, lean_object* v_handler_1840_, lean_object* v___f_1841_, lean_object* v_j_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_1839_, v_j_1842_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1847_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1846_);
lean_dec_ref_known(v___x_1845_, 1);
lean_inc_ref(v___y_1843_);
v___x_1847_ = lean_apply_3(v_handler_1840_, v_a_1846_, v___y_1843_, lean_box(0));
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1857_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1850_ = v___x_1847_;
v_isShared_1851_ = v_isSharedCheck_1857_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1847_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1857_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1855_; 
v___x_1852_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_1852_, 0, lean_box(0));
lean_closure_set(v___x_1852_, 1, lean_box(0));
lean_closure_set(v___x_1852_, 2, lean_box(0));
lean_closure_set(v___x_1852_, 3, v___f_1841_);
v___x_1853_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___x_1852_, v_a_1848_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1853_);
v___x_1855_ = v___x_1850_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
else
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
lean_dec_ref(v___f_1841_);
v_a_1858_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1847_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1847_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1858_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_dec_ref(v___f_1841_);
lean_dec_ref(v_handler_1840_);
v_a_1866_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1845_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1845_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__2___boxed(lean_object* v_inst_1874_, lean_object* v_handler_1875_, lean_object* v___f_1876_, lean_object* v_j_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Lean_Server_registerLspRequestHandler___redArg___lam__2(v_inst_1874_, v_handler_1875_, v___f_1876_, v_j_1877_, v___y_1878_);
lean_dec_ref(v___y_1878_);
return v_res_1880_;
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__1(void){
_start:
{
lean_object* v___x_1882_; lean_object* v___f_1883_; 
v___x_1882_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___f_1883_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1883_, 0, v___x_1882_);
return v___f_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg(lean_object* v_method_1887_, lean_object* v_inst_1888_, lean_object* v_inst_1889_, lean_object* v_inst_1890_, lean_object* v_handler_1891_, lean_object* v_serialize_x3f_1892_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Lean_initializing();
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1932_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1897_ = v___x_1894_;
v_isShared_1898_ = v_isSharedCheck_1932_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1894_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1932_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
uint8_t v___x_1899_; uint8_t v___x_1900_; 
v___x_1899_ = lean_unbox(v_a_1895_);
lean_dec(v_a_1895_);
v___x_1900_ = lean_bool_not(v___x_1899_);
if (v___x_1900_ == 0)
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___f_1904_; uint8_t v___x_1905_; 
v___x_1901_ = l_Lean_Server_requestHandlers;
v___x_1902_ = lean_st_ref_get(v___x_1901_);
v___x_1903_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__0));
v___f_1904_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__1, &l_Lean_Server_registerLspRequestHandler___redArg___closed__1_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__1);
lean_inc_ref(v_method_1887_);
v___x_1905_ = l_Lean_PersistentHashMap_contains___redArg(v___f_1904_, v___x_1903_, v___x_1902_, v_method_1887_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; lean_object* v___f_1907_; lean_object* v___f_1908_; lean_object* v___f_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1914_; 
v___x_1906_ = lean_st_ref_take(v___x_1901_);
lean_inc_ref(v_inst_1888_);
v___f_1907_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1907_, 0, v_inst_1888_);
lean_closure_set(v___f_1907_, 1, v_inst_1889_);
v___f_1908_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1908_, 0, v_serialize_x3f_1892_);
lean_closure_set(v___f_1908_, 1, v_inst_1890_);
v___f_1909_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1909_, 0, v_inst_1888_);
lean_closure_set(v___f_1909_, 1, v_handler_1891_);
lean_closure_set(v___f_1909_, 2, v___f_1908_);
v___x_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___f_1907_);
lean_ctor_set(v___x_1910_, 1, v___f_1909_);
v___x_1911_ = l_Lean_PersistentHashMap_insert___redArg(v___f_1904_, v___x_1903_, v___x_1906_, v_method_1887_, v___x_1910_);
v___x_1912_ = lean_st_ref_set(v___x_1901_, v___x_1911_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v___x_1912_);
v___x_1914_ = v___x_1897_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1912_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
else
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1922_; 
lean_dec(v_serialize_x3f_1892_);
lean_dec_ref(v_handler_1891_);
lean_dec_ref(v_inst_1890_);
lean_dec_ref(v_inst_1889_);
lean_dec_ref(v_inst_1888_);
v___x_1916_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___x_1917_ = lean_string_append(v___x_1916_, v_method_1887_);
lean_dec_ref(v_method_1887_);
v___x_1918_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__3));
v___x_1919_ = lean_string_append(v___x_1917_, v___x_1918_);
v___x_1920_ = lean_mk_io_user_error(v___x_1919_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set_tag(v___x_1897_, 1);
lean_ctor_set(v___x_1897_, 0, v___x_1920_);
v___x_1922_ = v___x_1897_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1920_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
else
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1930_; 
lean_dec(v_serialize_x3f_1892_);
lean_dec_ref(v_handler_1891_);
lean_dec_ref(v_inst_1890_);
lean_dec_ref(v_inst_1889_);
lean_dec_ref(v_inst_1888_);
v___x_1924_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___x_1925_ = lean_string_append(v___x_1924_, v_method_1887_);
lean_dec_ref(v_method_1887_);
v___x_1926_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__4));
v___x_1927_ = lean_string_append(v___x_1925_, v___x_1926_);
v___x_1928_ = lean_mk_io_user_error(v___x_1927_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set_tag(v___x_1897_, 1);
lean_ctor_set(v___x_1897_, 0, v___x_1928_);
v___x_1930_ = v___x_1897_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec(v_serialize_x3f_1892_);
lean_dec_ref(v_handler_1891_);
lean_dec_ref(v_inst_1890_);
lean_dec_ref(v_inst_1889_);
lean_dec_ref(v_inst_1888_);
lean_dec_ref(v_method_1887_);
v_a_1933_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1894_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1894_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___boxed(lean_object* v_method_1941_, lean_object* v_inst_1942_, lean_object* v_inst_1943_, lean_object* v_inst_1944_, lean_object* v_handler_1945_, lean_object* v_serialize_x3f_1946_, lean_object* v_a_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_Server_registerLspRequestHandler___redArg(v_method_1941_, v_inst_1942_, v_inst_1943_, v_inst_1944_, v_handler_1945_, v_serialize_x3f_1946_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler(lean_object* v_method_1949_, lean_object* v_paramType_1950_, lean_object* v_inst_1951_, lean_object* v_inst_1952_, lean_object* v_respType_1953_, lean_object* v_inst_1954_, lean_object* v_handler_1955_, lean_object* v_serialize_x3f_1956_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_Lean_Server_registerLspRequestHandler___redArg(v_method_1949_, v_inst_1951_, v_inst_1952_, v_inst_1954_, v_handler_1955_, v_serialize_x3f_1956_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___boxed(lean_object* v_method_1959_, lean_object* v_paramType_1960_, lean_object* v_inst_1961_, lean_object* v_inst_1962_, lean_object* v_respType_1963_, lean_object* v_inst_1964_, lean_object* v_handler_1965_, lean_object* v_serialize_x3f_1966_, lean_object* v_a_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_Server_registerLspRequestHandler(v_method_1959_, v_paramType_1960_, v_inst_1961_, v_inst_1962_, v_respType_1963_, v_inst_1964_, v_handler_1965_, v_serialize_x3f_1966_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1969_, lean_object* v_vals_1970_, lean_object* v_i_1971_, lean_object* v_k_1972_){
_start:
{
lean_object* v___x_1973_; uint8_t v___x_1974_; 
v___x_1973_ = lean_array_get_size(v_keys_1969_);
v___x_1974_ = lean_nat_dec_lt(v_i_1971_, v___x_1973_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; 
lean_dec(v_i_1971_);
v___x_1975_ = lean_box(0);
return v___x_1975_;
}
else
{
lean_object* v_k_x27_1976_; uint8_t v___x_1977_; 
v_k_x27_1976_ = lean_array_fget_borrowed(v_keys_1969_, v_i_1971_);
v___x_1977_ = lean_string_dec_eq(v_k_1972_, v_k_x27_1976_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = lean_unsigned_to_nat(1u);
v___x_1979_ = lean_nat_add(v_i_1971_, v___x_1978_);
lean_dec(v_i_1971_);
v_i_1971_ = v___x_1979_;
goto _start;
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = lean_array_fget_borrowed(v_vals_1970_, v_i_1971_);
lean_dec(v_i_1971_);
lean_inc(v___x_1981_);
v___x_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
return v___x_1982_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1983_, lean_object* v_vals_1984_, lean_object* v_i_1985_, lean_object* v_k_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(v_keys_1983_, v_vals_1984_, v_i_1985_, v_k_1986_);
lean_dec_ref(v_k_1986_);
lean_dec_ref(v_vals_1984_);
lean_dec_ref(v_keys_1983_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(lean_object* v_x_1988_, size_t v_x_1989_, lean_object* v_x_1990_){
_start:
{
if (lean_obj_tag(v_x_1988_) == 0)
{
lean_object* v_es_1991_; lean_object* v___x_1992_; size_t v___x_1993_; size_t v___x_1994_; lean_object* v_j_1995_; lean_object* v___x_1996_; 
v_es_1991_ = lean_ctor_get(v_x_1988_, 0);
v___x_1992_ = lean_box(2);
v___x_1993_ = ((size_t)31ULL);
v___x_1994_ = lean_usize_land(v_x_1989_, v___x_1993_);
v_j_1995_ = lean_usize_to_nat(v___x_1994_);
v___x_1996_ = lean_array_get_borrowed(v___x_1992_, v_es_1991_, v_j_1995_);
lean_dec(v_j_1995_);
switch(lean_obj_tag(v___x_1996_))
{
case 0:
{
lean_object* v_key_1997_; lean_object* v_val_1998_; uint8_t v___x_1999_; 
v_key_1997_ = lean_ctor_get(v___x_1996_, 0);
v_val_1998_ = lean_ctor_get(v___x_1996_, 1);
v___x_1999_ = lean_string_dec_eq(v_x_1990_, v_key_1997_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; 
v___x_2000_ = lean_box(0);
return v___x_2000_;
}
else
{
lean_object* v___x_2001_; 
lean_inc(v_val_1998_);
v___x_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2001_, 0, v_val_1998_);
return v___x_2001_;
}
}
case 1:
{
lean_object* v_node_2002_; size_t v___x_2003_; size_t v___x_2004_; 
v_node_2002_ = lean_ctor_get(v___x_1996_, 0);
v___x_2003_ = ((size_t)5ULL);
v___x_2004_ = lean_usize_shift_right(v_x_1989_, v___x_2003_);
v_x_1988_ = v_node_2002_;
v_x_1989_ = v___x_2004_;
goto _start;
}
default: 
{
lean_object* v___x_2006_; 
v___x_2006_ = lean_box(0);
return v___x_2006_;
}
}
}
else
{
lean_object* v_ks_2007_; lean_object* v_vs_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v_ks_2007_ = lean_ctor_get(v_x_1988_, 0);
v_vs_2008_ = lean_ctor_get(v_x_1988_, 1);
v___x_2009_ = lean_unsigned_to_nat(0u);
v___x_2010_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(v_ks_2007_, v_vs_2008_, v___x_2009_, v_x_1990_);
return v___x_2010_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___boxed(lean_object* v_x_2011_, lean_object* v_x_2012_, lean_object* v_x_2013_){
_start:
{
size_t v_x_263__boxed_2014_; lean_object* v_res_2015_; 
v_x_263__boxed_2014_ = lean_unbox_usize(v_x_2012_);
lean_dec(v_x_2012_);
v_res_2015_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_2011_, v_x_263__boxed_2014_, v_x_2013_);
lean_dec_ref(v_x_2013_);
lean_dec_ref(v_x_2011_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(lean_object* v_x_2016_, lean_object* v_x_2017_){
_start:
{
uint64_t v___x_2018_; size_t v___x_2019_; lean_object* v___x_2020_; 
v___x_2018_ = lean_string_hash(v_x_2017_);
v___x_2019_ = lean_uint64_to_usize(v___x_2018_);
v___x_2020_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_2016_, v___x_2019_, v_x_2017_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg___boxed(lean_object* v_x_2021_, lean_object* v_x_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v_x_2021_, v_x_2022_);
lean_dec_ref(v_x_2022_);
lean_dec_ref(v_x_2021_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupLspRequestHandler(lean_object* v_method_2024_){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2026_ = l_Lean_Server_requestHandlers;
v___x_2027_ = lean_st_ref_get(v___x_2026_);
v___x_2028_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v___x_2027_, v_method_2024_);
lean_dec(v___x_2027_);
v___x_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2028_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupLspRequestHandler___boxed(lean_object* v_method_2030_, lean_object* v_a_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Lean_Server_lookupLspRequestHandler(v_method_2030_);
lean_dec_ref(v_method_2030_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0(lean_object* v_00_u03b2_2033_, lean_object* v_x_2034_, lean_object* v_x_2035_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v_x_2034_, v_x_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___boxed(lean_object* v_00_u03b2_2037_, lean_object* v_x_2038_, lean_object* v_x_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0(v_00_u03b2_2037_, v_x_2038_, v_x_2039_);
lean_dec_ref(v_x_2039_);
lean_dec_ref(v_x_2038_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0(lean_object* v_00_u03b2_2041_, lean_object* v_x_2042_, size_t v_x_2043_, lean_object* v_x_2044_){
_start:
{
lean_object* v___x_2045_; 
v___x_2045_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_2042_, v_x_2043_, v_x_2044_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2046_, lean_object* v_x_2047_, lean_object* v_x_2048_, lean_object* v_x_2049_){
_start:
{
size_t v_x_341__boxed_2050_; lean_object* v_res_2051_; 
v_x_341__boxed_2050_ = lean_unbox_usize(v_x_2048_);
lean_dec(v_x_2048_);
v_res_2051_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0(v_00_u03b2_2046_, v_x_2047_, v_x_341__boxed_2050_, v_x_2049_);
lean_dec_ref(v_x_2049_);
lean_dec_ref(v_x_2047_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2052_, lean_object* v_keys_2053_, lean_object* v_vals_2054_, lean_object* v_heq_2055_, lean_object* v_i_2056_, lean_object* v_k_2057_){
_start:
{
lean_object* v___x_2058_; 
v___x_2058_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(v_keys_2053_, v_vals_2054_, v_i_2056_, v_k_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2059_, lean_object* v_keys_2060_, lean_object* v_vals_2061_, lean_object* v_heq_2062_, lean_object* v_i_2063_, lean_object* v_k_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1(v_00_u03b2_2059_, v_keys_2060_, v_vals_2061_, v_heq_2062_, v_i_2063_, v_k_2064_);
lean_dec_ref(v_k_2064_);
lean_dec_ref(v_vals_2061_);
lean_dec_ref(v_keys_2060_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__0(lean_object* v_inst_2069_, lean_object* v_method_2070_, lean_object* v_x_2071_){
_start:
{
lean_object* v_response_2073_; 
if (lean_obj_tag(v_x_2071_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec_ref(v_inst_2069_);
v_a_2097_ = lean_ctor_get(v_x_2071_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v_x_2071_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v_x_2071_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v_x_2071_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v_response_x3f_2106_; 
v_a_2105_ = lean_ctor_get(v_x_2071_, 0);
lean_inc(v_a_2105_);
lean_dec_ref_known(v_x_2071_, 1);
v_response_x3f_2106_ = lean_ctor_get(v_a_2105_, 0);
if (lean_obj_tag(v_response_x3f_2106_) == 0)
{
lean_object* v_serialized_2107_; lean_object* v___x_2108_; 
v_serialized_2107_ = lean_ctor_get(v_a_2105_, 1);
lean_inc_ref(v_serialized_2107_);
lean_dec(v_a_2105_);
v___x_2108_ = l_Lean_Json_parse(v_serialized_2107_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2122_; 
lean_dec_ref(v_inst_2069_);
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2111_ = v___x_2108_;
v_isShared_2112_ = v_isSharedCheck_2122_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2108_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2122_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2120_; 
v___x_2113_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__2));
v___x_2114_ = lean_string_append(v___x_2113_, v_method_2070_);
v___x_2115_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1));
v___x_2116_ = lean_string_append(v___x_2114_, v___x_2115_);
v___x_2117_ = lean_string_append(v___x_2116_, v_a_2109_);
lean_dec(v_a_2109_);
v___x_2118_ = l_Lean_Server_RequestError_internalError(v___x_2117_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v___x_2118_);
v___x_2120_ = v___x_2111_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2118_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
else
{
lean_object* v_a_2123_; 
v_a_2123_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2108_, 1);
v_response_2073_ = v_a_2123_;
goto v___jp_2072_;
}
}
else
{
lean_object* v_val_2124_; 
lean_inc_ref(v_response_x3f_2106_);
lean_dec(v_a_2105_);
v_val_2124_ = lean_ctor_get(v_response_x3f_2106_, 0);
lean_inc(v_val_2124_);
lean_dec_ref_known(v_response_x3f_2106_, 1);
v_response_2073_ = v_val_2124_;
goto v___jp_2072_;
}
}
v___jp_2072_:
{
lean_object* v___x_2074_; 
v___x_2074_ = lean_apply_1(v_inst_2069_, v_response_2073_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2088_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2077_ = v___x_2074_;
v_isShared_2078_ = v_isSharedCheck_2088_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2074_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2088_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2086_; 
v___x_2079_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__0));
v___x_2080_ = lean_string_append(v___x_2079_, v_method_2070_);
v___x_2081_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1));
v___x_2082_ = lean_string_append(v___x_2080_, v___x_2081_);
v___x_2083_ = lean_string_append(v___x_2082_, v_a_2075_);
lean_dec(v_a_2075_);
v___x_2084_ = l_Lean_Server_RequestError_internalError(v___x_2083_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v___x_2084_);
v___x_2086_ = v___x_2077_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
v_a_2089_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2074_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2074_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__0___boxed(lean_object* v_inst_2125_, lean_object* v_method_2126_, lean_object* v_x_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__0(v_inst_2125_, v_method_2126_, v_x_2127_);
lean_dec_ref(v_method_2126_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__1(lean_object* v_inst_2129_, lean_object* v_r_2130_){
_start:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; lean_object* v___x_2135_; 
v___x_2131_ = lean_apply_1(v_inst_2129_, v_r_2130_);
lean_inc(v___x_2131_);
v___x_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
v___x_2133_ = l_Lean_Json_compress(v___x_2131_);
v___x_2134_ = 1;
v___x_2135_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2135_, 0, v___x_2132_);
lean_ctor_set(v___x_2135_, 1, v___x_2133_);
lean_ctor_set_uint8(v___x_2135_, sizeof(void*)*2, v___x_2134_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__2(lean_object* v_handle_2136_, lean_object* v_inst_2137_, lean_object* v___f_2138_, lean_object* v_handler_2139_, lean_object* v___f_2140_, lean_object* v_j_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v___x_2144_; 
lean_inc_ref(v___y_2142_);
lean_inc(v_j_2141_);
v___x_2144_ = lean_apply_3(v_handle_2136_, v_j_2141_, v___y_2142_, lean_box(0));
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2146_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v___x_2146_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_2137_, v_j_2141_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2146_, 1);
v___x_2148_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2138_, v_a_2145_);
lean_inc_ref(v___y_2142_);
v___x_2149_ = lean_apply_4(v_handler_2139_, v_a_2147_, v___x_2148_, v___y_2142_, lean_box(0));
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2159_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2152_ = v___x_2149_;
v_isShared_2153_ = v_isSharedCheck_2159_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2149_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2159_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2157_; 
v___x_2154_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_2154_, 0, lean_box(0));
lean_closure_set(v___x_2154_, 1, lean_box(0));
lean_closure_set(v___x_2154_, 2, lean_box(0));
lean_closure_set(v___x_2154_, 3, v___f_2140_);
v___x_2155_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___x_2154_, v_a_2150_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2155_);
v___x_2157_ = v___x_2152_;
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
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_dec_ref(v___f_2140_);
v_a_2160_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2149_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2149_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
else
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
lean_dec(v_a_2145_);
lean_dec_ref(v___f_2140_);
lean_dec_ref(v_handler_2139_);
lean_dec_ref(v___f_2138_);
v_a_2168_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2146_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2146_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
else
{
lean_dec(v_j_2141_);
lean_dec_ref(v___f_2140_);
lean_dec_ref(v_handler_2139_);
lean_dec_ref(v___f_2138_);
lean_dec_ref(v_inst_2137_);
return v___x_2144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__2___boxed(lean_object* v_handle_2176_, lean_object* v_inst_2177_, lean_object* v___f_2178_, lean_object* v_handler_2179_, lean_object* v___f_2180_, lean_object* v_j_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__2(v_handle_2176_, v_inst_2177_, v___f_2178_, v_handler_2179_, v___f_2180_, v_j_2181_, v___y_2182_);
lean_dec_ref(v___y_2182_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg(lean_object* v_method_2187_, lean_object* v_inst_2188_, lean_object* v_inst_2189_, lean_object* v_inst_2190_, lean_object* v_handler_2191_){
_start:
{
lean_object* v___x_2193_; 
v___x_2193_ = l_Lean_initializing();
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2244_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2196_ = v___x_2193_;
v_isShared_2197_ = v_isSharedCheck_2244_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2193_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2244_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
uint8_t v___x_2198_; uint8_t v___x_2199_; 
v___x_2198_ = lean_unbox(v_a_2194_);
lean_dec(v_a_2194_);
v___x_2199_ = lean_bool_not(v___x_2198_);
if (v___x_2199_ == 0)
{
lean_object* v___x_2200_; lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2235_; 
lean_del_object(v___x_2196_);
v___x_2200_ = l_Lean_Server_lookupLspRequestHandler(v_method_2187_);
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2203_ = v___x_2200_;
v_isShared_2204_ = v_isSharedCheck_2235_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2200_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2235_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
if (lean_obj_tag(v_a_2201_) == 1)
{
lean_object* v_val_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v_fileSource_2208_; lean_object* v_handle_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2226_; 
v_val_2205_ = lean_ctor_get(v_a_2201_, 0);
lean_inc(v_val_2205_);
lean_dec_ref_known(v_a_2201_, 1);
v___x_2206_ = l_Lean_Server_requestHandlers;
v___x_2207_ = lean_st_ref_take(v___x_2206_);
v_fileSource_2208_ = lean_ctor_get(v_val_2205_, 0);
v_handle_2209_ = lean_ctor_get(v_val_2205_, 1);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_val_2205_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2211_ = v_val_2205_;
v_isShared_2212_ = v_isSharedCheck_2226_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_handle_2209_);
lean_inc(v_fileSource_2208_);
lean_dec(v_val_2205_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2226_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___f_2213_; lean_object* v___f_2214_; lean_object* v___x_2215_; lean_object* v___f_2216_; lean_object* v___f_2217_; lean_object* v___x_2219_; 
lean_inc_ref(v_method_2187_);
v___f_2213_ = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2213_, 0, v_inst_2189_);
lean_closure_set(v___f_2213_, 1, v_method_2187_);
v___f_2214_ = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2214_, 0, v_inst_2190_);
v___x_2215_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__0));
v___f_2216_ = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2216_, 0, v_handle_2209_);
lean_closure_set(v___f_2216_, 1, v_inst_2188_);
lean_closure_set(v___f_2216_, 2, v___f_2213_);
lean_closure_set(v___f_2216_, 3, v_handler_2191_);
lean_closure_set(v___f_2216_, 4, v___f_2214_);
v___f_2217_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__1, &l_Lean_Server_registerLspRequestHandler___redArg___closed__1_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__1);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 1, v___f_2216_);
v___x_2219_ = v___x_2211_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_fileSource_2208_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v___f_2216_);
v___x_2219_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2223_; 
v___x_2220_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2217_, v___x_2215_, v___x_2207_, v_method_2187_, v___x_2219_);
v___x_2221_ = lean_st_ref_set(v___x_2206_, v___x_2220_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 0, v___x_2221_);
v___x_2223_ = v___x_2203_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2221_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
else
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2233_; 
lean_dec(v_a_2201_);
lean_dec_ref(v_handler_2191_);
lean_dec_ref(v_inst_2190_);
lean_dec_ref(v_inst_2189_);
lean_dec_ref(v_inst_2188_);
v___x_2227_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__0));
v___x_2228_ = lean_string_append(v___x_2227_, v_method_2187_);
lean_dec_ref(v_method_2187_);
v___x_2229_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__1));
v___x_2230_ = lean_string_append(v___x_2228_, v___x_2229_);
v___x_2231_ = lean_mk_io_user_error(v___x_2230_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set_tag(v___x_2203_, 1);
lean_ctor_set(v___x_2203_, 0, v___x_2231_);
v___x_2233_ = v___x_2203_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2231_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
else
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2242_; 
lean_dec_ref(v_handler_2191_);
lean_dec_ref(v_inst_2190_);
lean_dec_ref(v_inst_2189_);
lean_dec_ref(v_inst_2188_);
v___x_2236_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__0));
v___x_2237_ = lean_string_append(v___x_2236_, v_method_2187_);
lean_dec_ref(v_method_2187_);
v___x_2238_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__4));
v___x_2239_ = lean_string_append(v___x_2237_, v___x_2238_);
v___x_2240_ = lean_mk_io_user_error(v___x_2239_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set_tag(v___x_2196_, 1);
lean_ctor_set(v___x_2196_, 0, v___x_2240_);
v___x_2242_ = v___x_2196_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
lean_dec_ref(v_handler_2191_);
lean_dec_ref(v_inst_2190_);
lean_dec_ref(v_inst_2189_);
lean_dec_ref(v_inst_2188_);
lean_dec_ref(v_method_2187_);
v_a_2245_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___x_2193_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2193_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___boxed(lean_object* v_method_2253_, lean_object* v_inst_2254_, lean_object* v_inst_2255_, lean_object* v_inst_2256_, lean_object* v_handler_2257_, lean_object* v_a_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Lean_Server_chainLspRequestHandler___redArg(v_method_2253_, v_inst_2254_, v_inst_2255_, v_inst_2256_, v_handler_2257_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler(lean_object* v_method_2260_, lean_object* v_paramType_2261_, lean_object* v_inst_2262_, lean_object* v_respType_2263_, lean_object* v_inst_2264_, lean_object* v_inst_2265_, lean_object* v_handler_2266_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Lean_Server_chainLspRequestHandler___redArg(v_method_2260_, v_inst_2262_, v_inst_2264_, v_inst_2265_, v_handler_2266_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___boxed(lean_object* v_method_2269_, lean_object* v_paramType_2270_, lean_object* v_inst_2271_, lean_object* v_respType_2272_, lean_object* v_inst_2273_, lean_object* v_inst_2274_, lean_object* v_handler_2275_, lean_object* v_a_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Lean_Server_chainLspRequestHandler(v_method_2269_, v_paramType_2270_, v_inst_2271_, v_respType_2272_, v_inst_2273_, v_inst_2274_, v_handler_2275_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorIdx(lean_object* v_x_2278_){
_start:
{
if (lean_obj_tag(v_x_2278_) == 0)
{
lean_object* v___x_2279_; 
v___x_2279_ = lean_unsigned_to_nat(0u);
return v___x_2279_;
}
else
{
lean_object* v___x_2280_; 
v___x_2280_ = lean_unsigned_to_nat(1u);
return v___x_2280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorIdx___boxed(lean_object* v_x_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_Server_RequestHandlerCompleteness_ctorIdx(v_x_2281_);
lean_dec(v_x_2281_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(lean_object* v_t_2283_, lean_object* v_k_2284_){
_start:
{
if (lean_obj_tag(v_t_2283_) == 0)
{
return v_k_2284_;
}
else
{
lean_object* v_refreshMethod_2285_; lean_object* v_refreshIntervalMs_2286_; lean_object* v___x_2287_; 
v_refreshMethod_2285_ = lean_ctor_get(v_t_2283_, 0);
lean_inc_ref(v_refreshMethod_2285_);
v_refreshIntervalMs_2286_ = lean_ctor_get(v_t_2283_, 1);
lean_inc(v_refreshIntervalMs_2286_);
lean_dec_ref_known(v_t_2283_, 2);
v___x_2287_ = lean_apply_2(v_k_2284_, v_refreshMethod_2285_, v_refreshIntervalMs_2286_);
return v___x_2287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim(lean_object* v_motive_2288_, lean_object* v_ctorIdx_2289_, lean_object* v_t_2290_, lean_object* v_h_2291_, lean_object* v_k_2292_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_2290_, v_k_2292_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim___boxed(lean_object* v_motive_2294_, lean_object* v_ctorIdx_2295_, lean_object* v_t_2296_, lean_object* v_h_2297_, lean_object* v_k_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim(v_motive_2294_, v_ctorIdx_2295_, v_t_2296_, v_h_2297_, v_k_2298_);
lean_dec(v_ctorIdx_2295_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_complete_elim___redArg(lean_object* v_t_2300_, lean_object* v_complete_2301_){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_2300_, v_complete_2301_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_complete_elim(lean_object* v_motive_2303_, lean_object* v_t_2304_, lean_object* v_h_2305_, lean_object* v_complete_2306_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_2304_, v_complete_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_partial_elim___redArg(lean_object* v_t_2308_, lean_object* v_partial_2309_){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_2308_, v_partial_2309_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_partial_elim(lean_object* v_motive_2311_, lean_object* v_t_2312_, lean_object* v_h_2313_, lean_object* v_partial_2314_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_2312_, v_partial_2314_);
return v___x_2315_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2316_; 
v___x_2316_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2316_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_);
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2320_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_);
v___x_2321_ = lean_st_mk_ref(v___x_2320_);
v___x_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2____boxed(lean_object* v_a_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_();
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(lean_object* v_method_2326_, lean_object* v_state_2327_, lean_object* v_inst_2328_){
_start:
{
lean_object* v___x_2330_; 
v___x_2330_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_state_2327_, v_inst_2328_);
if (lean_obj_tag(v___x_2330_) == 1)
{
lean_object* v_val_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
v_val_2331_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2333_ = v___x_2330_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_val_2331_);
lean_dec(v___x_2330_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
lean_ctor_set_tag(v___x_2333_, 0);
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_val_2331_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
else
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
lean_dec(v___x_2330_);
v___x_2339_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0));
v___x_2340_ = lean_string_append(v___x_2339_, v_method_2326_);
v___x_2341_ = l_Lean_Server_RequestError_internalError(v___x_2340_);
v___x_2342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2341_);
return v___x_2342_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___boxed(lean_object* v_method_2343_, lean_object* v_state_2344_, lean_object* v_inst_2345_, lean_object* v_a_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_2343_, v_state_2344_, v_inst_2345_);
lean_dec(v_inst_2345_);
lean_dec(v_state_2344_);
lean_dec_ref(v_method_2343_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(lean_object* v_method_2348_, lean_object* v_state_2349_, lean_object* v_stateType_2350_, lean_object* v_inst_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_2348_, v_state_2349_, v_inst_2351_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___boxed(lean_object* v_method_2355_, lean_object* v_state_2356_, lean_object* v_stateType_2357_, lean_object* v_inst_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_2355_, v_state_2356_, v_stateType_2357_, v_inst_2358_, v_a_2359_);
lean_dec_ref(v_a_2359_);
lean_dec(v_inst_2358_);
lean_dec(v_state_2356_);
lean_dec_ref(v_method_2355_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(lean_object* v_method_2362_, lean_object* v_state_2363_, lean_object* v_inst_2364_){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_state_2363_, v_inst_2364_);
if (lean_obj_tag(v___x_2366_) == 1)
{
lean_object* v_val_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
v_val_2367_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2366_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_val_2367_);
lean_dec(v___x_2366_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
lean_ctor_set_tag(v___x_2369_, 0);
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_val_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
else
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
lean_dec(v___x_2366_);
v___x_2375_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0));
v___x_2376_ = lean_string_append(v___x_2375_, v_method_2362_);
v___x_2377_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
v___x_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
return v___x_2378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg___boxed(lean_object* v_method_2379_, lean_object* v_state_2380_, lean_object* v_inst_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(v_method_2379_, v_state_2380_, v_inst_2381_);
lean_dec(v_inst_2381_);
lean_dec(v_state_2380_);
lean_dec_ref(v_method_2379_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21(lean_object* v_method_2384_, lean_object* v_state_2385_, lean_object* v_stateType_2386_, lean_object* v_inst_2387_){
_start:
{
lean_object* v___x_2389_; 
v___x_2389_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(v_method_2384_, v_state_2385_, v_inst_2387_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___boxed(lean_object* v_method_2390_, lean_object* v_state_2391_, lean_object* v_stateType_2392_, lean_object* v_inst_2393_, lean_object* v_a_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21(v_method_2390_, v_state_2391_, v_stateType_2392_, v_inst_2393_);
lean_dec(v_inst_2393_);
lean_dec(v_state_2391_);
lean_dec_ref(v_method_2390_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1(lean_object* v_inst_2396_, lean_object* v_method_2397_, lean_object* v_inst_2398_, lean_object* v_handler_2399_, lean_object* v_inst_2400_, lean_object* v_param_2401_, lean_object* v_state_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v___x_2405_; 
v___x_2405_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_2396_, v_param_2401_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; lean_object* v___x_2407_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_a_2406_);
lean_dec_ref_known(v___x_2405_, 1);
v___x_2407_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_2397_, v_state_2402_, v_inst_2398_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v___x_2409_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2408_);
lean_dec_ref_known(v___x_2407_, 1);
lean_inc_ref(v___y_2403_);
v___x_2409_ = lean_apply_4(v_handler_2399_, v_a_2406_, v_a_2408_, v___y_2403_, lean_box(0));
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2433_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2412_ = v___x_2409_;
v_isShared_2413_ = v_isSharedCheck_2433_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2409_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2433_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v_fst_2414_; lean_object* v_snd_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2432_; 
v_fst_2414_ = lean_ctor_get(v_a_2410_, 0);
v_snd_2415_ = lean_ctor_get(v_a_2410_, 1);
v_isSharedCheck_2432_ = !lean_is_exclusive(v_a_2410_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2417_ = v_a_2410_;
v_isShared_2418_ = v_isSharedCheck_2432_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_snd_2415_);
lean_inc(v_fst_2414_);
lean_dec(v_a_2410_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2432_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v_response_2419_; uint8_t v_isComplete_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2426_; 
v_response_2419_ = lean_ctor_get(v_fst_2414_, 0);
lean_inc(v_response_2419_);
v_isComplete_2420_ = lean_ctor_get_uint8(v_fst_2414_, sizeof(void*)*1);
lean_dec(v_fst_2414_);
v___x_2421_ = lean_apply_1(v_inst_2400_, v_response_2419_);
lean_inc(v___x_2421_);
v___x_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2421_);
v___x_2423_ = l_Lean_Json_compress(v___x_2421_);
v___x_2424_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2424_, 0, v___x_2422_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
lean_ctor_set_uint8(v___x_2424_, sizeof(void*)*2, v_isComplete_2420_);
if (v_isShared_2418_ == 0)
{
lean_ctor_set(v___x_2417_, 0, v_inst_2398_);
v___x_2426_ = v___x_2417_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_inst_2398_);
lean_ctor_set(v_reuseFailAlloc_2431_, 1, v_snd_2415_);
v___x_2426_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
lean_object* v___x_2427_; lean_object* v___x_2429_; 
v___x_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2424_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 0, v___x_2427_);
v___x_2429_ = v___x_2412_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2427_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
lean_dec_ref(v_inst_2400_);
lean_dec(v_inst_2398_);
v_a_2434_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v___x_2409_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2409_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
if (v_isShared_2437_ == 0)
{
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_a_2434_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
else
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2449_; 
lean_dec(v_a_2406_);
lean_dec_ref(v_inst_2400_);
lean_dec_ref(v_handler_2399_);
lean_dec(v_inst_2398_);
v_a_2442_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2444_ = v___x_2407_;
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2407_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2447_; 
if (v_isShared_2445_ == 0)
{
v___x_2447_ = v___x_2444_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_a_2442_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
else
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
lean_dec_ref(v_inst_2400_);
lean_dec_ref(v_handler_2399_);
lean_dec(v_inst_2398_);
v_a_2450_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2405_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2405_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1___boxed(lean_object* v_inst_2458_, lean_object* v_method_2459_, lean_object* v_inst_2460_, lean_object* v_handler_2461_, lean_object* v_inst_2462_, lean_object* v_param_2463_, lean_object* v_state_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1(v_inst_2458_, v_method_2459_, v_inst_2460_, v_handler_2461_, v_inst_2462_, v_param_2463_, v_state_2464_, v___y_2465_);
lean_dec_ref(v___y_2465_);
lean_dec(v_state_2464_);
lean_dec_ref(v_method_2459_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0(lean_object* v_method_2468_, lean_object* v_inst_2469_, lean_object* v_onDidChange_2470_, lean_object* v_param_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_2468_, v___y_2472_, v_inst_2469_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_a_2476_; lean_object* v___x_2477_; 
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_a_2476_);
lean_dec_ref_known(v___x_2475_, 1);
lean_inc_ref(v___y_2473_);
v___x_2477_ = lean_apply_4(v_onDidChange_2470_, v_param_2471_, v_a_2476_, v___y_2473_, lean_box(0));
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2496_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2480_ = v___x_2477_;
v_isShared_2481_ = v_isSharedCheck_2496_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2477_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2496_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v_snd_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2494_; 
v_snd_2482_ = lean_ctor_get(v_a_2478_, 1);
v_isSharedCheck_2494_ = !lean_is_exclusive(v_a_2478_);
if (v_isSharedCheck_2494_ == 0)
{
lean_object* v_unused_2495_; 
v_unused_2495_ = lean_ctor_get(v_a_2478_, 0);
lean_dec(v_unused_2495_);
v___x_2484_ = v_a_2478_;
v_isShared_2485_ = v_isSharedCheck_2494_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_snd_2482_);
lean_dec(v_a_2478_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2494_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 0, v_inst_2469_);
v___x_2487_ = v___x_2484_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_inst_2469_);
lean_ctor_set(v_reuseFailAlloc_2493_, 1, v_snd_2482_);
v___x_2487_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2491_; 
v___x_2488_ = lean_box(0);
v___x_2489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2488_);
lean_ctor_set(v___x_2489_, 1, v___x_2487_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v___x_2489_);
v___x_2491_ = v___x_2480_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2489_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
lean_dec(v_inst_2469_);
v_a_2497_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___x_2477_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2477_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_dec_ref(v_param_2471_);
lean_dec_ref(v_onDidChange_2470_);
lean_dec(v_inst_2469_);
v_a_2505_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2475_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2475_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object* v_method_2513_, lean_object* v_inst_2514_, lean_object* v_onDidChange_2515_, lean_object* v_param_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0(v_method_2513_, v_inst_2514_, v_onDidChange_2515_, v_param_2516_, v___y_2517_, v___y_2518_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v_method_2513_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2(lean_object* v___x_2521_, lean_object* v_x_2522_){
_start:
{
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2___boxed(lean_object* v___x_2523_, lean_object* v_x_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2(v___x_2523_, v_x_2524_);
lean_dec_ref(v_x_2524_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3(lean_object* v___x_2526_, lean_object* v_x_2527_){
_start:
{
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3___boxed(lean_object* v___x_2528_, lean_object* v_x_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3(v___x_2528_, v_x_2529_);
lean_dec_ref(v_x_2529_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4(lean_object* v_val_2531_, lean_object* v___f_2532_, lean_object* v_param_2533_, lean_object* v_x_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = lean_st_ref_get(v_val_2531_);
lean_inc_ref(v___y_2535_);
v___x_2538_ = lean_apply_4(v___f_2532_, v_param_2533_, v___x_2537_, v___y_2535_, lean_box(0));
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2549_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2541_ = v___x_2538_;
v_isShared_2542_ = v_isSharedCheck_2549_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2538_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2549_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v_fst_2543_; lean_object* v_snd_2544_; lean_object* v___x_2545_; lean_object* v___x_2547_; 
v_fst_2543_ = lean_ctor_get(v_a_2539_, 0);
lean_inc(v_fst_2543_);
v_snd_2544_ = lean_ctor_get(v_a_2539_, 1);
lean_inc(v_snd_2544_);
lean_dec(v_a_2539_);
v___x_2545_ = lean_st_ref_set(v_val_2531_, v_snd_2544_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 0, v_fst_2543_);
v___x_2547_ = v___x_2541_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_fst_2543_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
else
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2557_; 
v_a_2550_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2552_ = v___x_2538_;
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2538_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
if (v_isShared_2553_ == 0)
{
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2550_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4___boxed(lean_object* v_val_2558_, lean_object* v___f_2559_, lean_object* v_param_2560_, lean_object* v_x_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4(v_val_2558_, v___f_2559_, v_param_2560_, v_x_2561_, v___y_2562_);
lean_dec_ref(v___y_2562_);
lean_dec(v_val_2558_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5(lean_object* v___f_2565_, lean_object* v___f_2566_, lean_object* v_lastTask_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
lean_object* v___x_2571_; lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2581_; 
v___x_2571_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_lastTask_2567_, v___f_2565_, v___y_2569_);
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2574_ = v___x_2571_;
v_isShared_2575_ = v_isSharedCheck_2581_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2571_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2581_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2579_; 
lean_inc(v_a_2572_);
v___x_2576_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2566_, v_a_2572_);
v___x_2577_ = lean_st_ref_set(v___y_2568_, v___x_2576_);
if (v_isShared_2575_ == 0)
{
v___x_2579_ = v___x_2574_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2572_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5___boxed(lean_object* v___f_2582_, lean_object* v___f_2583_, lean_object* v_lastTask_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5(v___f_2582_, v___f_2583_, v_lastTask_2584_, v___y_2585_, v___y_2586_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6(lean_object* v_val_2589_, lean_object* v___f_2590_, lean_object* v___f_2591_, lean_object* v___f_2592_, lean_object* v___x_2593_, lean_object* v___f_2594_, lean_object* v___f_2595_, lean_object* v_val_2596_, lean_object* v_param_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v___f_2600_; lean_object* v___f_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_6048__overap_2604_; lean_object* v___x_2605_; 
v___f_2600_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2600_, 0, v_val_2589_);
lean_closure_set(v___f_2600_, 1, v___f_2590_);
lean_closure_set(v___f_2600_, 2, v_param_2597_);
v___f_2601_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5___boxed), 6, 2);
lean_closure_set(v___f_2601_, 0, v___f_2600_);
lean_closure_set(v___f_2601_, 1, v___f_2591_);
v___x_2602_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_2602_, 0, lean_box(0));
lean_closure_set(v___x_2602_, 1, lean_box(0));
lean_closure_set(v___x_2602_, 2, lean_box(0));
lean_closure_set(v___x_2602_, 3, v___f_2592_);
lean_inc_ref(v___x_2593_);
v___x_2603_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2603_, 0, lean_box(0));
lean_closure_set(v___x_2603_, 1, lean_box(0));
lean_closure_set(v___x_2603_, 2, v___x_2593_);
lean_closure_set(v___x_2603_, 3, lean_box(0));
lean_closure_set(v___x_2603_, 4, lean_box(0));
lean_closure_set(v___x_2603_, 5, v___x_2602_);
lean_closure_set(v___x_2603_, 6, v___f_2601_);
v___x_6048__overap_2604_ = l_Std_Mutex_atomically___redArg(v___x_2593_, v___f_2594_, v___f_2595_, v_val_2596_, v___x_2603_);
lean_inc_ref(v___y_2598_);
v___x_2605_ = lean_apply_2(v___x_6048__overap_2604_, v___y_2598_, lean_box(0));
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6___boxed(lean_object* v_val_2606_, lean_object* v___f_2607_, lean_object* v___f_2608_, lean_object* v___f_2609_, lean_object* v___x_2610_, lean_object* v___f_2611_, lean_object* v___f_2612_, lean_object* v_val_2613_, lean_object* v_param_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6(v_val_2606_, v___f_2607_, v___f_2608_, v___f_2609_, v___x_2610_, v___f_2611_, v___f_2612_, v_val_2613_, v_param_2614_, v___y_2615_);
lean_dec_ref(v___y_2615_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7(lean_object* v_val_2618_, lean_object* v___f_2619_, lean_object* v_param_2620_, lean_object* v_x_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = lean_st_ref_get(v_val_2618_);
lean_inc_ref(v___y_2622_);
v___x_2625_ = lean_apply_4(v___f_2619_, v_param_2620_, v___x_2624_, v___y_2622_, lean_box(0));
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2635_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2628_ = v___x_2625_;
v_isShared_2629_ = v_isSharedCheck_2635_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2625_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2635_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v_snd_2630_; lean_object* v___x_2631_; lean_object* v___x_2633_; 
v_snd_2630_ = lean_ctor_get(v_a_2626_, 1);
lean_inc(v_snd_2630_);
lean_dec(v_a_2626_);
v___x_2631_ = lean_st_ref_set(v_val_2618_, v_snd_2630_);
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 0, v___x_2631_);
v___x_2633_ = v___x_2628_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2631_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
else
{
lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2643_; 
v_a_2636_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2638_ = v___x_2625_;
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2625_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2641_; 
if (v_isShared_2639_ == 0)
{
v___x_2641_ = v___x_2638_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2636_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7___boxed(lean_object* v_val_2644_, lean_object* v___f_2645_, lean_object* v_param_2646_, lean_object* v_x_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7(v_val_2644_, v___f_2645_, v_param_2646_, v_x_2647_, v___y_2648_);
lean_dec_ref(v___y_2648_);
lean_dec(v_val_2644_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8(lean_object* v___f_2651_, lean_object* v___f_2652_, lean_object* v_lastTask_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v___x_2657_; lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2667_; 
v___x_2657_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_lastTask_2653_, v___f_2651_, v___y_2655_);
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2660_ = v___x_2657_;
v_isShared_2661_ = v_isSharedCheck_2667_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2657_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2667_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2665_; 
v___x_2662_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2652_, v_a_2658_);
v___x_2663_ = lean_st_ref_set(v___y_2654_, v___x_2662_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 0, v___x_2663_);
v___x_2665_ = v___x_2660_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2663_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8___boxed(lean_object* v___f_2668_, lean_object* v___f_2669_, lean_object* v_lastTask_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8(v___f_2668_, v___f_2669_, v_lastTask_2670_, v___y_2671_, v___y_2672_);
lean_dec_ref(v___y_2672_);
lean_dec(v___y_2671_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9(lean_object* v_val_2675_, lean_object* v___f_2676_, lean_object* v___f_2677_, lean_object* v___f_2678_, lean_object* v___x_2679_, lean_object* v___f_2680_, lean_object* v___f_2681_, lean_object* v_val_2682_, lean_object* v_param_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v___f_2686_; lean_object* v___f_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_6099__overap_2690_; lean_object* v___x_2691_; 
v___f_2686_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7___boxed), 6, 3);
lean_closure_set(v___f_2686_, 0, v_val_2675_);
lean_closure_set(v___f_2686_, 1, v___f_2676_);
lean_closure_set(v___f_2686_, 2, v_param_2683_);
v___f_2687_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8___boxed), 6, 2);
lean_closure_set(v___f_2687_, 0, v___f_2686_);
lean_closure_set(v___f_2687_, 1, v___f_2677_);
v___x_2688_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_2688_, 0, lean_box(0));
lean_closure_set(v___x_2688_, 1, lean_box(0));
lean_closure_set(v___x_2688_, 2, lean_box(0));
lean_closure_set(v___x_2688_, 3, v___f_2678_);
lean_inc_ref(v___x_2679_);
v___x_2689_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2689_, 0, lean_box(0));
lean_closure_set(v___x_2689_, 1, lean_box(0));
lean_closure_set(v___x_2689_, 2, v___x_2679_);
lean_closure_set(v___x_2689_, 3, lean_box(0));
lean_closure_set(v___x_2689_, 4, lean_box(0));
lean_closure_set(v___x_2689_, 5, v___x_2688_);
lean_closure_set(v___x_2689_, 6, v___f_2687_);
v___x_6099__overap_2690_ = l_Std_Mutex_atomically___redArg(v___x_2679_, v___f_2680_, v___f_2681_, v_val_2682_, v___x_2689_);
lean_inc_ref(v___y_2684_);
v___x_2691_ = lean_apply_2(v___x_6099__overap_2690_, v___y_2684_, lean_box(0));
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9___boxed(lean_object* v_val_2692_, lean_object* v___f_2693_, lean_object* v___f_2694_, lean_object* v___f_2695_, lean_object* v___x_2696_, lean_object* v___f_2697_, lean_object* v___f_2698_, lean_object* v_val_2699_, lean_object* v_param_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9(v_val_2692_, v___f_2693_, v___f_2694_, v___f_2695_, v___x_2696_, v___f_2697_, v___f_2698_, v_val_2699_, v_param_2700_, v___y_2701_);
lean_dec_ref(v___y_2701_);
return v_res_2703_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0(void){
_start:
{
lean_object* v___x_2704_; 
v___x_2704_ = l_instMonadEIO(lean_box(0));
return v___x_2704_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1(void){
_start:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2705_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0);
v___x_2706_ = l_ReaderT_instMonad___redArg(v___x_2705_);
return v___x_2706_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2(void){
_start:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2707_ = lean_box(0);
v___x_2708_ = lean_task_pure(v___x_2707_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(lean_object* v_method_2735_, lean_object* v_completeness_2736_, lean_object* v_inst_2737_, lean_object* v_inst_2738_, lean_object* v_inst_2739_, lean_object* v_inst_2740_, lean_object* v_initState_2741_, lean_object* v_handler_2742_, lean_object* v_onDidChange_2743_){
_start:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2745_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1);
v___x_2746_ = l_Lean_initializing();
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2785_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2749_ = v___x_2746_;
v_isShared_2750_ = v_isSharedCheck_2785_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2746_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2785_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
uint8_t v___x_2751_; uint8_t v___x_2752_; 
v___x_2751_ = lean_unbox(v_a_2747_);
lean_dec(v_a_2747_);
v___x_2752_ = lean_bool_not(v___x_2751_);
if (v___x_2752_ == 0)
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___f_2759_; lean_object* v___f_2760_; lean_object* v___f_2761_; lean_object* v___f_2762_; lean_object* v___f_2763_; lean_object* v___f_2764_; lean_object* v___x_2765_; lean_object* v___f_2766_; lean_object* v___f_2767_; lean_object* v___f_2768_; lean_object* v___f_2769_; lean_object* v___f_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2775_; 
v___x_2753_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2);
v___x_2754_ = l_Std_Mutex_new___redArg(v___x_2753_);
lean_inc_n(v_inst_2740_, 2);
v___x_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2755_, 0, v_inst_2740_);
lean_ctor_set(v___x_2755_, 1, v_initState_2741_);
lean_inc_ref(v___x_2755_);
v___x_2756_ = lean_st_mk_ref(v___x_2755_);
v___x_2757_ = l_Lean_Server_statefulRequestHandlers;
v___x_2758_ = lean_st_ref_take(v___x_2757_);
v___f_2759_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__6));
lean_inc_ref(v_inst_2737_);
v___f_2760_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2760_, 0, v_inst_2737_);
lean_closure_set(v___f_2760_, 1, v_inst_2738_);
lean_inc_ref_n(v_method_2735_, 2);
v___f_2761_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1___boxed), 9, 5);
lean_closure_set(v___f_2761_, 0, v_inst_2737_);
lean_closure_set(v___f_2761_, 1, v_method_2735_);
lean_closure_set(v___f_2761_, 2, v_inst_2740_);
lean_closure_set(v___f_2761_, 3, v_handler_2742_);
lean_closure_set(v___f_2761_, 4, v_inst_2739_);
v___f_2762_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0___boxed), 7, 3);
lean_closure_set(v___f_2762_, 0, v_method_2735_);
lean_closure_set(v___f_2762_, 1, v_inst_2740_);
lean_closure_set(v___f_2762_, 2, v_onDidChange_2743_);
v___f_2763_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__8));
v___f_2764_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__12));
v___x_2765_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__0));
v___f_2766_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__13));
v___f_2767_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__14));
lean_inc_ref_n(v___x_2754_, 2);
lean_inc_ref(v___f_2761_);
lean_inc_n(v___x_2756_, 2);
v___f_2768_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6___boxed), 11, 8);
lean_closure_set(v___f_2768_, 0, v___x_2756_);
lean_closure_set(v___f_2768_, 1, v___f_2761_);
lean_closure_set(v___f_2768_, 2, v___f_2766_);
lean_closure_set(v___f_2768_, 3, v___f_2764_);
lean_closure_set(v___f_2768_, 4, v___x_2745_);
lean_closure_set(v___f_2768_, 5, v___f_2759_);
lean_closure_set(v___f_2768_, 6, v___f_2763_);
lean_closure_set(v___f_2768_, 7, v___x_2754_);
lean_inc_ref(v___f_2762_);
v___f_2769_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9___boxed), 11, 8);
lean_closure_set(v___f_2769_, 0, v___x_2756_);
lean_closure_set(v___f_2769_, 1, v___f_2762_);
lean_closure_set(v___f_2769_, 2, v___f_2767_);
lean_closure_set(v___f_2769_, 3, v___f_2764_);
lean_closure_set(v___f_2769_, 4, v___x_2745_);
lean_closure_set(v___f_2769_, 5, v___f_2759_);
lean_closure_set(v___f_2769_, 6, v___f_2763_);
lean_closure_set(v___f_2769_, 7, v___x_2754_);
v___f_2770_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__1, &l_Lean_Server_registerLspRequestHandler___redArg___closed__1_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__1);
v___x_2771_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2771_, 0, v___f_2760_);
lean_ctor_set(v___x_2771_, 1, v___f_2761_);
lean_ctor_set(v___x_2771_, 2, v___f_2768_);
lean_ctor_set(v___x_2771_, 3, v___f_2762_);
lean_ctor_set(v___x_2771_, 4, v___f_2769_);
lean_ctor_set(v___x_2771_, 5, v___x_2754_);
lean_ctor_set(v___x_2771_, 6, v___x_2755_);
lean_ctor_set(v___x_2771_, 7, v___x_2756_);
lean_ctor_set(v___x_2771_, 8, v_completeness_2736_);
v___x_2772_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2770_, v___x_2765_, v___x_2758_, v_method_2735_, v___x_2771_);
v___x_2773_ = lean_st_ref_set(v___x_2757_, v___x_2772_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v___x_2773_);
v___x_2775_ = v___x_2749_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2773_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
else
{
lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2783_; 
lean_dec_ref(v_onDidChange_2743_);
lean_dec_ref(v_handler_2742_);
lean_dec(v_initState_2741_);
lean_dec(v_inst_2740_);
lean_dec_ref(v_inst_2739_);
lean_dec_ref(v_inst_2738_);
lean_dec_ref(v_inst_2737_);
lean_dec(v_completeness_2736_);
v___x_2777_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15));
v___x_2778_ = lean_string_append(v___x_2777_, v_method_2735_);
lean_dec_ref(v_method_2735_);
v___x_2779_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__4));
v___x_2780_ = lean_string_append(v___x_2778_, v___x_2779_);
v___x_2781_ = lean_mk_io_user_error(v___x_2780_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set_tag(v___x_2749_, 1);
lean_ctor_set(v___x_2749_, 0, v___x_2781_);
v___x_2783_ = v___x_2749_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2781_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
lean_dec_ref(v_onDidChange_2743_);
lean_dec_ref(v_handler_2742_);
lean_dec(v_initState_2741_);
lean_dec(v_inst_2740_);
lean_dec_ref(v_inst_2739_);
lean_dec_ref(v_inst_2738_);
lean_dec_ref(v_inst_2737_);
lean_dec(v_completeness_2736_);
lean_dec_ref(v_method_2735_);
v_a_2786_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2746_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2746_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2794_, lean_object* v_completeness_2795_, lean_object* v_inst_2796_, lean_object* v_inst_2797_, lean_object* v_inst_2798_, lean_object* v_inst_2799_, lean_object* v_initState_2800_, lean_object* v_handler_2801_, lean_object* v_onDidChange_2802_, lean_object* v_a_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2794_, v_completeness_2795_, v_inst_2796_, v_inst_2797_, v_inst_2798_, v_inst_2799_, v_initState_2800_, v_handler_2801_, v_onDidChange_2802_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(lean_object* v_method_2805_, lean_object* v_completeness_2806_, lean_object* v_paramType_2807_, lean_object* v_inst_2808_, lean_object* v_inst_2809_, lean_object* v_respType_2810_, lean_object* v_inst_2811_, lean_object* v_stateType_2812_, lean_object* v_inst_2813_, lean_object* v_initState_2814_, lean_object* v_handler_2815_, lean_object* v_onDidChange_2816_){
_start:
{
lean_object* v___x_2818_; 
v___x_2818_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2805_, v_completeness_2806_, v_inst_2808_, v_inst_2809_, v_inst_2811_, v_inst_2813_, v_initState_2814_, v_handler_2815_, v_onDidChange_2816_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___boxed(lean_object* v_method_2819_, lean_object* v_completeness_2820_, lean_object* v_paramType_2821_, lean_object* v_inst_2822_, lean_object* v_inst_2823_, lean_object* v_respType_2824_, lean_object* v_inst_2825_, lean_object* v_stateType_2826_, lean_object* v_inst_2827_, lean_object* v_initState_2828_, lean_object* v_handler_2829_, lean_object* v_onDidChange_2830_, lean_object* v_a_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(v_method_2819_, v_completeness_2820_, v_paramType_2821_, v_inst_2822_, v_inst_2823_, v_respType_2824_, v_inst_2825_, v_stateType_2826_, v_inst_2827_, v_initState_2828_, v_handler_2829_, v_onDidChange_2830_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(lean_object* v_method_2833_, lean_object* v_completeness_2834_, lean_object* v_inst_2835_, lean_object* v_inst_2836_, lean_object* v_inst_2837_, lean_object* v_inst_2838_, lean_object* v_initState_2839_, lean_object* v_handler_2840_, lean_object* v_onDidChange_2841_){
_start:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___f_2846_; uint8_t v___x_2847_; 
v___x_2843_ = l_Lean_Server_requestHandlers;
v___x_2844_ = lean_st_ref_get(v___x_2843_);
v___x_2845_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__0));
v___f_2846_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__1, &l_Lean_Server_registerLspRequestHandler___redArg___closed__1_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__1);
lean_inc_ref(v_method_2833_);
v___x_2847_ = l_Lean_PersistentHashMap_contains___redArg(v___f_2846_, v___x_2845_, v___x_2844_, v_method_2833_);
if (v___x_2847_ == 0)
{
lean_object* v___x_2848_; 
v___x_2848_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2833_, v_completeness_2834_, v_inst_2835_, v_inst_2836_, v_inst_2837_, v_inst_2838_, v_initState_2839_, v_handler_2840_, v_onDidChange_2841_);
return v___x_2848_;
}
else
{
lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
lean_dec_ref(v_onDidChange_2841_);
lean_dec_ref(v_handler_2840_);
lean_dec(v_initState_2839_);
lean_dec(v_inst_2838_);
lean_dec_ref(v_inst_2837_);
lean_dec_ref(v_inst_2836_);
lean_dec_ref(v_inst_2835_);
lean_dec(v_completeness_2834_);
v___x_2849_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15));
v___x_2850_ = lean_string_append(v___x_2849_, v_method_2833_);
lean_dec_ref(v_method_2833_);
v___x_2851_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__3));
v___x_2852_ = lean_string_append(v___x_2850_, v___x_2851_);
v___x_2853_ = lean_mk_io_user_error(v___x_2852_);
v___x_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2853_);
return v___x_2854_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2855_, lean_object* v_completeness_2856_, lean_object* v_inst_2857_, lean_object* v_inst_2858_, lean_object* v_inst_2859_, lean_object* v_inst_2860_, lean_object* v_initState_2861_, lean_object* v_handler_2862_, lean_object* v_onDidChange_2863_, lean_object* v_a_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2855_, v_completeness_2856_, v_inst_2857_, v_inst_2858_, v_inst_2859_, v_inst_2860_, v_initState_2861_, v_handler_2862_, v_onDidChange_2863_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler(lean_object* v_method_2866_, lean_object* v_completeness_2867_, lean_object* v_paramType_2868_, lean_object* v_inst_2869_, lean_object* v_inst_2870_, lean_object* v_respType_2871_, lean_object* v_inst_2872_, lean_object* v_stateType_2873_, lean_object* v_inst_2874_, lean_object* v_initState_2875_, lean_object* v_handler_2876_, lean_object* v_onDidChange_2877_){
_start:
{
lean_object* v___x_2879_; 
v___x_2879_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2866_, v_completeness_2867_, v_inst_2869_, v_inst_2870_, v_inst_2872_, v_inst_2874_, v_initState_2875_, v_handler_2876_, v_onDidChange_2877_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___boxed(lean_object* v_method_2880_, lean_object* v_completeness_2881_, lean_object* v_paramType_2882_, lean_object* v_inst_2883_, lean_object* v_inst_2884_, lean_object* v_respType_2885_, lean_object* v_inst_2886_, lean_object* v_stateType_2887_, lean_object* v_inst_2888_, lean_object* v_initState_2889_, lean_object* v_handler_2890_, lean_object* v_onDidChange_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler(v_method_2880_, v_completeness_2881_, v_paramType_2882_, v_inst_2883_, v_inst_2884_, v_respType_2885_, v_inst_2886_, v_stateType_2887_, v_inst_2888_, v_initState_2889_, v_handler_2890_, v_onDidChange_2891_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0(lean_object* v_handler_2894_, lean_object* v_p_2895_, lean_object* v_s_2896_, lean_object* v___y_2897_){
_start:
{
lean_object* v___x_2899_; 
lean_inc_ref(v___y_2897_);
v___x_2899_ = lean_apply_4(v_handler_2894_, v_p_2895_, v_s_2896_, v___y_2897_, lean_box(0));
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2918_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2902_ = v___x_2899_;
v_isShared_2903_ = v_isSharedCheck_2918_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2899_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2918_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v_fst_2904_; lean_object* v_snd_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2917_; 
v_fst_2904_ = lean_ctor_get(v_a_2900_, 0);
v_snd_2905_ = lean_ctor_get(v_a_2900_, 1);
v_isSharedCheck_2917_ = !lean_is_exclusive(v_a_2900_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2907_ = v_a_2900_;
v_isShared_2908_ = v_isSharedCheck_2917_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_snd_2905_);
lean_inc(v_fst_2904_);
lean_dec(v_a_2900_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2917_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
uint8_t v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2912_; 
v___x_2909_ = 1;
v___x_2910_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2910_, 0, v_fst_2904_);
lean_ctor_set_uint8(v___x_2910_, sizeof(void*)*1, v___x_2909_);
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 0, v___x_2910_);
v___x_2912_ = v___x_2907_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v___x_2910_);
lean_ctor_set(v_reuseFailAlloc_2916_, 1, v_snd_2905_);
v___x_2912_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2914_; 
if (v_isShared_2903_ == 0)
{
lean_ctor_set(v___x_2902_, 0, v___x_2912_);
v___x_2914_ = v___x_2902_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2912_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
}
else
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
v_a_2919_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2921_ = v___x_2899_;
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2899_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2924_; 
if (v_isShared_2922_ == 0)
{
v___x_2924_ = v___x_2921_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2919_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object* v_handler_2927_, lean_object* v_p_2928_, lean_object* v_s_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0(v_handler_2927_, v_p_2928_, v_s_2929_, v___y_2930_);
lean_dec_ref(v___y_2930_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(lean_object* v_method_2933_, lean_object* v_inst_2934_, lean_object* v_inst_2935_, lean_object* v_inst_2936_, lean_object* v_inst_2937_, lean_object* v_initState_2938_, lean_object* v_handler_2939_, lean_object* v_onDidChange_2940_){
_start:
{
lean_object* v_handler_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
v_handler_2942_ = lean_alloc_closure((void*)(l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v_handler_2942_, 0, v_handler_2939_);
v___x_2943_ = lean_box(0);
v___x_2944_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2933_, v___x_2943_, v_inst_2934_, v_inst_2935_, v_inst_2936_, v_inst_2937_, v_initState_2938_, v_handler_2942_, v_onDidChange_2940_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2945_, lean_object* v_inst_2946_, lean_object* v_inst_2947_, lean_object* v_inst_2948_, lean_object* v_inst_2949_, lean_object* v_initState_2950_, lean_object* v_handler_2951_, lean_object* v_onDidChange_2952_, lean_object* v_a_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(v_method_2945_, v_inst_2946_, v_inst_2947_, v_inst_2948_, v_inst_2949_, v_initState_2950_, v_handler_2951_, v_onDidChange_2952_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler(lean_object* v_method_2955_, lean_object* v_paramType_2956_, lean_object* v_inst_2957_, lean_object* v_inst_2958_, lean_object* v_respType_2959_, lean_object* v_inst_2960_, lean_object* v_stateType_2961_, lean_object* v_inst_2962_, lean_object* v_initState_2963_, lean_object* v_handler_2964_, lean_object* v_onDidChange_2965_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(v_method_2955_, v_inst_2957_, v_inst_2958_, v_inst_2960_, v_inst_2962_, v_initState_2963_, v_handler_2964_, v_onDidChange_2965_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___boxed(lean_object* v_method_2968_, lean_object* v_paramType_2969_, lean_object* v_inst_2970_, lean_object* v_inst_2971_, lean_object* v_respType_2972_, lean_object* v_inst_2973_, lean_object* v_stateType_2974_, lean_object* v_inst_2975_, lean_object* v_initState_2976_, lean_object* v_handler_2977_, lean_object* v_onDidChange_2978_, lean_object* v_a_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler(v_method_2968_, v_paramType_2969_, v_inst_2970_, v_inst_2971_, v_respType_2972_, v_inst_2973_, v_stateType_2974_, v_inst_2975_, v_initState_2976_, v_handler_2977_, v_onDidChange_2978_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(lean_object* v_method_2981_, lean_object* v_refreshMethod_2982_, lean_object* v_refreshIntervalMs_2983_, lean_object* v_inst_2984_, lean_object* v_inst_2985_, lean_object* v_inst_2986_, lean_object* v_inst_2987_, lean_object* v_initState_2988_, lean_object* v_handler_2989_, lean_object* v_onDidChange_2990_){
_start:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2992_, 0, v_refreshMethod_2982_);
lean_ctor_set(v___x_2992_, 1, v_refreshIntervalMs_2983_);
v___x_2993_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2981_, v___x_2992_, v_inst_2984_, v_inst_2985_, v_inst_2986_, v_inst_2987_, v_initState_2988_, v_handler_2989_, v_onDidChange_2990_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2994_, lean_object* v_refreshMethod_2995_, lean_object* v_refreshIntervalMs_2996_, lean_object* v_inst_2997_, lean_object* v_inst_2998_, lean_object* v_inst_2999_, lean_object* v_inst_3000_, lean_object* v_initState_3001_, lean_object* v_handler_3002_, lean_object* v_onDidChange_3003_, lean_object* v_a_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(v_method_2994_, v_refreshMethod_2995_, v_refreshIntervalMs_2996_, v_inst_2997_, v_inst_2998_, v_inst_2999_, v_inst_3000_, v_initState_3001_, v_handler_3002_, v_onDidChange_3003_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler(lean_object* v_method_3006_, lean_object* v_refreshMethod_3007_, lean_object* v_refreshIntervalMs_3008_, lean_object* v_paramType_3009_, lean_object* v_inst_3010_, lean_object* v_inst_3011_, lean_object* v_respType_3012_, lean_object* v_inst_3013_, lean_object* v_stateType_3014_, lean_object* v_inst_3015_, lean_object* v_initState_3016_, lean_object* v_handler_3017_, lean_object* v_onDidChange_3018_){
_start:
{
lean_object* v___x_3020_; 
v___x_3020_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(v_method_3006_, v_refreshMethod_3007_, v_refreshIntervalMs_3008_, v_inst_3010_, v_inst_3011_, v_inst_3013_, v_inst_3015_, v_initState_3016_, v_handler_3017_, v_onDidChange_3018_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___boxed(lean_object* v_method_3021_, lean_object* v_refreshMethod_3022_, lean_object* v_refreshIntervalMs_3023_, lean_object* v_paramType_3024_, lean_object* v_inst_3025_, lean_object* v_inst_3026_, lean_object* v_respType_3027_, lean_object* v_inst_3028_, lean_object* v_stateType_3029_, lean_object* v_inst_3030_, lean_object* v_initState_3031_, lean_object* v_handler_3032_, lean_object* v_onDidChange_3033_, lean_object* v_a_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l_Lean_Server_registerPartialStatefulLspRequestHandler(v_method_3021_, v_refreshMethod_3022_, v_refreshIntervalMs_3023_, v_paramType_3024_, v_inst_3025_, v_inst_3026_, v_respType_3027_, v_inst_3028_, v_stateType_3029_, v_inst_3030_, v_initState_3031_, v_handler_3032_, v_onDidChange_3033_);
return v_res_3035_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3036_, lean_object* v_i_3037_, lean_object* v_k_3038_){
_start:
{
lean_object* v___x_3039_; uint8_t v___x_3040_; 
v___x_3039_ = lean_array_get_size(v_keys_3036_);
v___x_3040_ = lean_nat_dec_lt(v_i_3037_, v___x_3039_);
if (v___x_3040_ == 0)
{
lean_dec(v_i_3037_);
return v___x_3040_;
}
else
{
lean_object* v_k_x27_3041_; uint8_t v___x_3042_; 
v_k_x27_3041_ = lean_array_fget_borrowed(v_keys_3036_, v_i_3037_);
v___x_3042_ = lean_string_dec_eq(v_k_3038_, v_k_x27_3041_);
if (v___x_3042_ == 0)
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = lean_unsigned_to_nat(1u);
v___x_3044_ = lean_nat_add(v_i_3037_, v___x_3043_);
lean_dec(v_i_3037_);
v_i_3037_ = v___x_3044_;
goto _start;
}
else
{
lean_dec(v_i_3037_);
return v___x_3042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3046_, lean_object* v_i_3047_, lean_object* v_k_3048_){
_start:
{
uint8_t v_res_3049_; lean_object* v_r_3050_; 
v_res_3049_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_keys_3046_, v_i_3047_, v_k_3048_);
lean_dec_ref(v_k_3048_);
lean_dec_ref(v_keys_3046_);
v_r_3050_ = lean_box(v_res_3049_);
return v_r_3050_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(lean_object* v_x_3051_, size_t v_x_3052_, lean_object* v_x_3053_){
_start:
{
if (lean_obj_tag(v_x_3051_) == 0)
{
lean_object* v_es_3054_; lean_object* v___x_3055_; size_t v___x_3056_; size_t v___x_3057_; lean_object* v_j_3058_; lean_object* v___x_3059_; 
v_es_3054_ = lean_ctor_get(v_x_3051_, 0);
v___x_3055_ = lean_box(2);
v___x_3056_ = ((size_t)31ULL);
v___x_3057_ = lean_usize_land(v_x_3052_, v___x_3056_);
v_j_3058_ = lean_usize_to_nat(v___x_3057_);
v___x_3059_ = lean_array_get_borrowed(v___x_3055_, v_es_3054_, v_j_3058_);
lean_dec(v_j_3058_);
switch(lean_obj_tag(v___x_3059_))
{
case 0:
{
lean_object* v_key_3060_; uint8_t v___x_3061_; 
v_key_3060_ = lean_ctor_get(v___x_3059_, 0);
v___x_3061_ = lean_string_dec_eq(v_x_3053_, v_key_3060_);
return v___x_3061_;
}
case 1:
{
lean_object* v_node_3062_; size_t v___x_3063_; size_t v___x_3064_; 
v_node_3062_ = lean_ctor_get(v___x_3059_, 0);
v___x_3063_ = ((size_t)5ULL);
v___x_3064_ = lean_usize_shift_right(v_x_3052_, v___x_3063_);
v_x_3051_ = v_node_3062_;
v_x_3052_ = v___x_3064_;
goto _start;
}
default: 
{
uint8_t v___x_3066_; 
v___x_3066_ = 0;
return v___x_3066_;
}
}
}
else
{
lean_object* v_ks_3067_; lean_object* v___x_3068_; uint8_t v___x_3069_; 
v_ks_3067_ = lean_ctor_get(v_x_3051_, 0);
v___x_3068_ = lean_unsigned_to_nat(0u);
v___x_3069_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_ks_3067_, v___x_3068_, v_x_3053_);
return v___x_3069_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg___boxed(lean_object* v_x_3070_, lean_object* v_x_3071_, lean_object* v_x_3072_){
_start:
{
size_t v_x_214__boxed_3073_; uint8_t v_res_3074_; lean_object* v_r_3075_; 
v_x_214__boxed_3073_ = lean_unbox_usize(v_x_3071_);
lean_dec(v_x_3071_);
v_res_3074_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_3070_, v_x_214__boxed_3073_, v_x_3072_);
lean_dec_ref(v_x_3072_);
lean_dec_ref(v_x_3070_);
v_r_3075_ = lean_box(v_res_3074_);
return v_r_3075_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(lean_object* v_x_3076_, lean_object* v_x_3077_){
_start:
{
uint64_t v___x_3078_; size_t v___x_3079_; uint8_t v___x_3080_; 
v___x_3078_ = lean_string_hash(v_x_3077_);
v___x_3079_ = lean_uint64_to_usize(v___x_3078_);
v___x_3080_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_3076_, v___x_3079_, v_x_3077_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg___boxed(lean_object* v_x_3081_, lean_object* v_x_3082_){
_start:
{
uint8_t v_res_3083_; lean_object* v_r_3084_; 
v_res_3083_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v_x_3081_, v_x_3082_);
lean_dec_ref(v_x_3082_);
lean_dec_ref(v_x_3081_);
v_r_3084_ = lean_box(v_res_3083_);
return v_r_3084_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_isStatefulLspRequestMethod(lean_object* v_method_3085_){
_start:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; uint8_t v___x_3089_; 
v___x_3087_ = l_Lean_Server_statefulRequestHandlers;
v___x_3088_ = lean_st_ref_get(v___x_3087_);
v___x_3089_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v___x_3088_, v_method_3085_);
lean_dec(v___x_3088_);
return v___x_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_isStatefulLspRequestMethod___boxed(lean_object* v_method_3090_, lean_object* v_a_3091_){
_start:
{
uint8_t v_res_3092_; lean_object* v_r_3093_; 
v_res_3092_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_3090_);
lean_dec_ref(v_method_3090_);
v_r_3093_ = lean_box(v_res_3092_);
return v_r_3093_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0(lean_object* v_00_u03b2_3094_, lean_object* v_x_3095_, lean_object* v_x_3096_){
_start:
{
uint8_t v___x_3097_; 
v___x_3097_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v_x_3095_, v_x_3096_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___boxed(lean_object* v_00_u03b2_3098_, lean_object* v_x_3099_, lean_object* v_x_3100_){
_start:
{
uint8_t v_res_3101_; lean_object* v_r_3102_; 
v_res_3101_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0(v_00_u03b2_3098_, v_x_3099_, v_x_3100_);
lean_dec_ref(v_x_3100_);
lean_dec_ref(v_x_3099_);
v_r_3102_ = lean_box(v_res_3101_);
return v_r_3102_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0(lean_object* v_00_u03b2_3103_, lean_object* v_x_3104_, size_t v_x_3105_, lean_object* v_x_3106_){
_start:
{
uint8_t v___x_3107_; 
v___x_3107_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_3104_, v_x_3105_, v_x_3106_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3108_, lean_object* v_x_3109_, lean_object* v_x_3110_, lean_object* v_x_3111_){
_start:
{
size_t v_x_284__boxed_3112_; uint8_t v_res_3113_; lean_object* v_r_3114_; 
v_x_284__boxed_3112_ = lean_unbox_usize(v_x_3110_);
lean_dec(v_x_3110_);
v_res_3113_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0(v_00_u03b2_3108_, v_x_3109_, v_x_284__boxed_3112_, v_x_3111_);
lean_dec_ref(v_x_3111_);
lean_dec_ref(v_x_3109_);
v_r_3114_ = lean_box(v_res_3113_);
return v_r_3114_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3115_, lean_object* v_keys_3116_, lean_object* v_vals_3117_, lean_object* v_heq_3118_, lean_object* v_i_3119_, lean_object* v_k_3120_){
_start:
{
uint8_t v___x_3121_; 
v___x_3121_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_keys_3116_, v_i_3119_, v_k_3120_);
return v___x_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3122_, lean_object* v_keys_3123_, lean_object* v_vals_3124_, lean_object* v_heq_3125_, lean_object* v_i_3126_, lean_object* v_k_3127_){
_start:
{
uint8_t v_res_3128_; lean_object* v_r_3129_; 
v_res_3128_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1(v_00_u03b2_3122_, v_keys_3123_, v_vals_3124_, v_heq_3125_, v_i_3126_, v_k_3127_);
lean_dec_ref(v_k_3127_);
lean_dec_ref(v_vals_3124_);
lean_dec_ref(v_keys_3123_);
v_r_3129_ = lean_box(v_res_3128_);
return v_r_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupStatefulLspRequestHandler(lean_object* v_method_3130_){
_start:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3132_ = l_Lean_Server_statefulRequestHandlers;
v___x_3133_ = lean_st_ref_get(v___x_3132_);
v___x_3134_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v___x_3133_, v_method_3130_);
lean_dec(v___x_3133_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupStatefulLspRequestHandler___boxed(lean_object* v_method_3135_, lean_object* v_a_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_3135_);
lean_dec_ref(v_method_3135_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(lean_object* v_as_3138_, size_t v_i_3139_, size_t v_stop_3140_, lean_object* v_b_3141_){
_start:
{
lean_object* v___y_3143_; uint8_t v___x_3147_; 
v___x_3147_ = lean_usize_dec_eq(v_i_3139_, v_stop_3140_);
if (v___x_3147_ == 0)
{
lean_object* v___x_3148_; lean_object* v_snd_3149_; lean_object* v_completeness_3150_; 
v___x_3148_ = lean_array_uget(v_as_3138_, v_i_3139_);
v_snd_3149_ = lean_ctor_get(v___x_3148_, 1);
v_completeness_3150_ = lean_ctor_get(v_snd_3149_, 8);
lean_inc(v_completeness_3150_);
if (lean_obj_tag(v_completeness_3150_) == 1)
{
lean_object* v_fst_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3168_; 
v_fst_3151_ = lean_ctor_get(v___x_3148_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3168_ == 0)
{
lean_object* v_unused_3169_; 
v_unused_3169_ = lean_ctor_get(v___x_3148_, 1);
lean_dec(v_unused_3169_);
v___x_3153_ = v___x_3148_;
v_isShared_3154_ = v_isSharedCheck_3168_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_fst_3151_);
lean_dec(v___x_3148_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3168_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v_refreshMethod_3155_; lean_object* v_refreshIntervalMs_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3167_; 
v_refreshMethod_3155_ = lean_ctor_get(v_completeness_3150_, 0);
v_refreshIntervalMs_3156_ = lean_ctor_get(v_completeness_3150_, 1);
v_isSharedCheck_3167_ = !lean_is_exclusive(v_completeness_3150_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3158_ = v_completeness_3150_;
v_isShared_3159_ = v_isSharedCheck_3167_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_refreshIntervalMs_3156_);
lean_inc(v_refreshMethod_3155_);
lean_dec(v_completeness_3150_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3167_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3154_ == 0)
{
lean_ctor_set(v___x_3153_, 1, v_refreshIntervalMs_3156_);
lean_ctor_set(v___x_3153_, 0, v_refreshMethod_3155_);
v___x_3161_ = v___x_3153_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_refreshMethod_3155_);
lean_ctor_set(v_reuseFailAlloc_3166_, 1, v_refreshIntervalMs_3156_);
v___x_3161_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
lean_object* v___x_3163_; 
if (v_isShared_3159_ == 0)
{
lean_ctor_set_tag(v___x_3158_, 0);
lean_ctor_set(v___x_3158_, 1, v___x_3161_);
lean_ctor_set(v___x_3158_, 0, v_fst_3151_);
v___x_3163_ = v___x_3158_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_fst_3151_);
lean_ctor_set(v_reuseFailAlloc_3165_, 1, v___x_3161_);
v___x_3163_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
lean_object* v___x_3164_; 
v___x_3164_ = lean_array_push(v_b_3141_, v___x_3163_);
v___y_3143_ = v___x_3164_;
goto v___jp_3142_;
}
}
}
}
}
else
{
lean_dec(v_completeness_3150_);
lean_dec(v___x_3148_);
v___y_3143_ = v_b_3141_;
goto v___jp_3142_;
}
}
else
{
return v_b_3141_;
}
v___jp_3142_:
{
size_t v___x_3144_; size_t v___x_3145_; 
v___x_3144_ = ((size_t)1ULL);
v___x_3145_ = lean_usize_add(v_i_3139_, v___x_3144_);
v_i_3139_ = v___x_3145_;
v_b_3141_ = v___y_3143_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2___boxed(lean_object* v_as_3170_, lean_object* v_i_3171_, lean_object* v_stop_3172_, lean_object* v_b_3173_){
_start:
{
size_t v_i_boxed_3174_; size_t v_stop_boxed_3175_; lean_object* v_res_3176_; 
v_i_boxed_3174_ = lean_unbox_usize(v_i_3171_);
lean_dec(v_i_3171_);
v_stop_boxed_3175_ = lean_unbox_usize(v_stop_3172_);
lean_dec(v_stop_3172_);
v_res_3176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_3170_, v_i_boxed_3174_, v_stop_boxed_3175_, v_b_3173_);
lean_dec_ref(v_as_3170_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(lean_object* v_as_3179_, lean_object* v_start_3180_, lean_object* v_stop_3181_){
_start:
{
lean_object* v___x_3182_; uint8_t v___x_3183_; 
v___x_3182_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___closed__0));
v___x_3183_ = lean_nat_dec_lt(v_start_3180_, v_stop_3181_);
if (v___x_3183_ == 0)
{
return v___x_3182_;
}
else
{
lean_object* v___x_3184_; uint8_t v___x_3185_; 
v___x_3184_ = lean_array_get_size(v_as_3179_);
v___x_3185_ = lean_nat_dec_le(v_stop_3181_, v___x_3184_);
if (v___x_3185_ == 0)
{
uint8_t v___x_3186_; 
v___x_3186_ = lean_nat_dec_lt(v_start_3180_, v___x_3184_);
if (v___x_3186_ == 0)
{
return v___x_3182_;
}
else
{
size_t v___x_3187_; size_t v___x_3188_; lean_object* v___x_3189_; 
v___x_3187_ = lean_usize_of_nat(v_start_3180_);
v___x_3188_ = lean_usize_of_nat(v___x_3184_);
v___x_3189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_3179_, v___x_3187_, v___x_3188_, v___x_3182_);
return v___x_3189_;
}
}
else
{
size_t v___x_3190_; size_t v___x_3191_; lean_object* v___x_3192_; 
v___x_3190_ = lean_usize_of_nat(v_start_3180_);
v___x_3191_ = lean_usize_of_nat(v_stop_3181_);
v___x_3192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_3179_, v___x_3190_, v___x_3191_, v___x_3182_);
return v___x_3192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___boxed(lean_object* v_as_3193_, lean_object* v_start_3194_, lean_object* v_stop_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(v_as_3193_, v_start_3194_, v_stop_3195_);
lean_dec(v_stop_3195_);
lean_dec(v_start_3194_);
lean_dec_ref(v_as_3193_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_f_3197_, lean_object* v_keys_3198_, lean_object* v_vals_3199_, lean_object* v_i_3200_, lean_object* v_acc_3201_){
_start:
{
lean_object* v___x_3202_; uint8_t v___x_3203_; 
v___x_3202_ = lean_array_get_size(v_keys_3198_);
v___x_3203_ = lean_nat_dec_lt(v_i_3200_, v___x_3202_);
if (v___x_3203_ == 0)
{
lean_dec(v_i_3200_);
lean_dec(v_f_3197_);
return v_acc_3201_;
}
else
{
lean_object* v_k_3204_; lean_object* v_v_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v_k_3204_ = lean_array_fget_borrowed(v_keys_3198_, v_i_3200_);
v_v_3205_ = lean_array_fget_borrowed(v_vals_3199_, v_i_3200_);
lean_inc(v_f_3197_);
lean_inc(v_v_3205_);
lean_inc(v_k_3204_);
v___x_3206_ = lean_apply_3(v_f_3197_, v_acc_3201_, v_k_3204_, v_v_3205_);
v___x_3207_ = lean_unsigned_to_nat(1u);
v___x_3208_ = lean_nat_add(v_i_3200_, v___x_3207_);
lean_dec(v_i_3200_);
v_i_3200_ = v___x_3208_;
v_acc_3201_ = v___x_3206_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_f_3210_, lean_object* v_keys_3211_, lean_object* v_vals_3212_, lean_object* v_i_3213_, lean_object* v_acc_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_3210_, v_keys_3211_, v_vals_3212_, v_i_3213_, v_acc_3214_);
lean_dec_ref(v_vals_3212_);
lean_dec_ref(v_keys_3211_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_3216_, lean_object* v_x_3217_, lean_object* v_x_3218_){
_start:
{
if (lean_obj_tag(v_x_3217_) == 0)
{
lean_object* v_es_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; uint8_t v___x_3222_; 
v_es_3219_ = lean_ctor_get(v_x_3217_, 0);
v___x_3220_ = lean_unsigned_to_nat(0u);
v___x_3221_ = lean_array_get_size(v_es_3219_);
v___x_3222_ = lean_nat_dec_lt(v___x_3220_, v___x_3221_);
if (v___x_3222_ == 0)
{
lean_dec(v_f_3216_);
return v_x_3218_;
}
else
{
uint8_t v___x_3223_; 
v___x_3223_ = lean_nat_dec_le(v___x_3221_, v___x_3221_);
if (v___x_3223_ == 0)
{
if (v___x_3222_ == 0)
{
lean_dec(v_f_3216_);
return v_x_3218_;
}
else
{
size_t v___x_3224_; size_t v___x_3225_; lean_object* v___x_3226_; 
v___x_3224_ = ((size_t)0ULL);
v___x_3225_ = lean_usize_of_nat(v___x_3221_);
v___x_3226_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_3216_, v_es_3219_, v___x_3224_, v___x_3225_, v_x_3218_);
return v___x_3226_;
}
}
else
{
size_t v___x_3227_; size_t v___x_3228_; lean_object* v___x_3229_; 
v___x_3227_ = ((size_t)0ULL);
v___x_3228_ = lean_usize_of_nat(v___x_3221_);
v___x_3229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_3216_, v_es_3219_, v___x_3227_, v___x_3228_, v_x_3218_);
return v___x_3229_;
}
}
}
else
{
lean_object* v_ks_3230_; lean_object* v_vs_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v_ks_3230_ = lean_ctor_get(v_x_3217_, 0);
v_vs_3231_ = lean_ctor_get(v_x_3217_, 1);
v___x_3232_ = lean_unsigned_to_nat(0u);
v___x_3233_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_3216_, v_ks_3230_, v_vs_3231_, v___x_3232_, v_x_3218_);
return v___x_3233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_f_3234_, lean_object* v_as_3235_, size_t v_i_3236_, size_t v_stop_3237_, lean_object* v_b_3238_){
_start:
{
lean_object* v___y_3240_; uint8_t v___x_3244_; 
v___x_3244_ = lean_usize_dec_eq(v_i_3236_, v_stop_3237_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3245_; 
v___x_3245_ = lean_array_uget_borrowed(v_as_3235_, v_i_3236_);
switch(lean_obj_tag(v___x_3245_))
{
case 0:
{
lean_object* v_key_3246_; lean_object* v_val_3247_; lean_object* v___x_3248_; 
v_key_3246_ = lean_ctor_get(v___x_3245_, 0);
v_val_3247_ = lean_ctor_get(v___x_3245_, 1);
lean_inc(v_f_3234_);
lean_inc(v_val_3247_);
lean_inc(v_key_3246_);
v___x_3248_ = lean_apply_3(v_f_3234_, v_b_3238_, v_key_3246_, v_val_3247_);
v___y_3240_ = v___x_3248_;
goto v___jp_3239_;
}
case 1:
{
lean_object* v_node_3249_; lean_object* v___x_3250_; 
v_node_3249_ = lean_ctor_get(v___x_3245_, 0);
lean_inc(v_f_3234_);
v___x_3250_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3234_, v_node_3249_, v_b_3238_);
v___y_3240_ = v___x_3250_;
goto v___jp_3239_;
}
default: 
{
v___y_3240_ = v_b_3238_;
goto v___jp_3239_;
}
}
}
else
{
lean_dec(v_f_3234_);
return v_b_3238_;
}
v___jp_3239_:
{
size_t v___x_3241_; size_t v___x_3242_; 
v___x_3241_ = ((size_t)1ULL);
v___x_3242_ = lean_usize_add(v_i_3236_, v___x_3241_);
v_i_3236_ = v___x_3242_;
v_b_3238_ = v___y_3240_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_f_3251_, lean_object* v_as_3252_, lean_object* v_i_3253_, lean_object* v_stop_3254_, lean_object* v_b_3255_){
_start:
{
size_t v_i_boxed_3256_; size_t v_stop_boxed_3257_; lean_object* v_res_3258_; 
v_i_boxed_3256_ = lean_unbox_usize(v_i_3253_);
lean_dec(v_i_3253_);
v_stop_boxed_3257_ = lean_unbox_usize(v_stop_3254_);
lean_dec(v_stop_3254_);
v_res_3258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_3251_, v_as_3252_, v_i_boxed_3256_, v_stop_boxed_3257_, v_b_3255_);
lean_dec_ref(v_as_3252_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_3259_, lean_object* v_x_3260_, lean_object* v_x_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3259_, v_x_3260_, v_x_3261_);
lean_dec_ref(v_x_3260_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___lam__0(lean_object* v_f_3263_, lean_object* v_x1_3264_, lean_object* v_x2_3265_, lean_object* v_x3_3266_){
_start:
{
lean_object* v___x_3267_; 
v___x_3267_ = lean_apply_3(v_f_3263_, v_x1_3264_, v_x2_3265_, v_x3_3266_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(lean_object* v_map_3268_, lean_object* v_f_3269_, lean_object* v_init_3270_){
_start:
{
lean_object* v___f_3271_; lean_object* v___x_3272_; 
v___f_3271_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3271_, 0, v_f_3269_);
v___x_3272_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v___f_3271_, v_map_3268_, v_init_3270_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___boxed(lean_object* v_map_3273_, lean_object* v_f_3274_, lean_object* v_init_3275_){
_start:
{
lean_object* v_res_3276_; 
v_res_3276_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_map_3273_, v_f_3274_, v_init_3275_);
lean_dec_ref(v_map_3273_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___lam__0(lean_object* v_ps_3277_, lean_object* v_k_3278_, lean_object* v_v_3279_){
_start:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3280_, 0, v_k_3278_);
lean_ctor_set(v___x_3280_, 1, v_v_3279_);
v___x_3281_ = lean_array_push(v_ps_3277_, v___x_3280_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(lean_object* v_m_3285_){
_start:
{
lean_object* v___f_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
v___f_3286_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__0));
v___x_3287_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__1));
v___x_3288_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_m_3285_, v___f_3286_, v___x_3287_);
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___boxed(lean_object* v_m_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v_m_3289_);
lean_dec_ref(v_m_3289_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_partialLspRequestHandlerMethods(){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3292_ = l_Lean_Server_statefulRequestHandlers;
v___x_3293_ = lean_st_ref_get(v___x_3292_);
v___x_3294_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v___x_3293_);
lean_dec(v___x_3293_);
v___x_3295_ = lean_unsigned_to_nat(0u);
v___x_3296_ = lean_array_get_size(v___x_3294_);
v___x_3297_ = l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(v___x_3294_, v___x_3295_, v___x_3296_);
lean_dec_ref(v___x_3294_);
v___x_3298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3297_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_partialLspRequestHandlerMethods___boxed(lean_object* v_a_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_Lean_Server_partialLspRequestHandlerMethods();
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0(lean_object* v_00_u03b2_3301_, lean_object* v_m_3302_){
_start:
{
lean_object* v___x_3303_; 
v___x_3303_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v_m_3302_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___boxed(lean_object* v_00_u03b2_3304_, lean_object* v_m_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0(v_00_u03b2_3304_, v_m_3305_);
lean_dec_ref(v_m_3305_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0(lean_object* v_00_u03c3_3307_, lean_object* v_00_u03b2_3308_, lean_object* v_map_3309_, lean_object* v_f_3310_, lean_object* v_init_3311_){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_map_3309_, v_f_3310_, v_init_3311_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3313_, lean_object* v_00_u03b2_3314_, lean_object* v_map_3315_, lean_object* v_f_3316_, lean_object* v_init_3317_){
_start:
{
lean_object* v_res_3318_; 
v_res_3318_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0(v_00_u03c3_3313_, v_00_u03b2_3314_, v_map_3315_, v_f_3316_, v_init_3317_);
lean_dec_ref(v_map_3315_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg(lean_object* v_map_3319_, lean_object* v_f_3320_, lean_object* v_init_3321_){
_start:
{
lean_object* v___x_3322_; 
v___x_3322_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3320_, v_map_3319_, v_init_3321_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_3323_, lean_object* v_f_3324_, lean_object* v_init_3325_){
_start:
{
lean_object* v_res_3326_; 
v_res_3326_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg(v_map_3323_, v_f_3324_, v_init_3325_);
lean_dec_ref(v_map_3323_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3327_, lean_object* v_00_u03b2_3328_, lean_object* v_map_3329_, lean_object* v_f_3330_, lean_object* v_init_3331_){
_start:
{
lean_object* v___x_3332_; 
v___x_3332_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3330_, v_map_3329_, v_init_3331_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3333_, lean_object* v_00_u03b2_3334_, lean_object* v_map_3335_, lean_object* v_f_3336_, lean_object* v_init_3337_){
_start:
{
lean_object* v_res_3338_; 
v_res_3338_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1(v_00_u03c3_3333_, v_00_u03b2_3334_, v_map_3335_, v_f_3336_, v_init_3337_);
lean_dec_ref(v_map_3335_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3339_, lean_object* v_00_u03b1_3340_, lean_object* v_00_u03b2_3341_, lean_object* v_f_3342_, lean_object* v_x_3343_, lean_object* v_x_3344_){
_start:
{
lean_object* v___x_3345_; 
v___x_3345_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3342_, v_x_3343_, v_x_3344_);
return v___x_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3346_, lean_object* v_00_u03b1_3347_, lean_object* v_00_u03b2_3348_, lean_object* v_f_3349_, lean_object* v_x_3350_, lean_object* v_x_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3346_, v_00_u03b1_3347_, v_00_u03b2_3348_, v_f_3349_, v_x_3350_, v_x_3351_);
lean_dec_ref(v_x_3350_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_3353_, lean_object* v_00_u03b2_3354_, lean_object* v_00_u03c3_3355_, lean_object* v_f_3356_, lean_object* v_as_3357_, size_t v_i_3358_, size_t v_stop_3359_, lean_object* v_b_3360_){
_start:
{
lean_object* v___x_3361_; 
v___x_3361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_3356_, v_as_3357_, v_i_3358_, v_stop_3359_, v_b_3360_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_3362_, lean_object* v_00_u03b2_3363_, lean_object* v_00_u03c3_3364_, lean_object* v_f_3365_, lean_object* v_as_3366_, lean_object* v_i_3367_, lean_object* v_stop_3368_, lean_object* v_b_3369_){
_start:
{
size_t v_i_boxed_3370_; size_t v_stop_boxed_3371_; lean_object* v_res_3372_; 
v_i_boxed_3370_ = lean_unbox_usize(v_i_3367_);
lean_dec(v_i_3367_);
v_stop_boxed_3371_ = lean_unbox_usize(v_stop_3368_);
lean_dec(v_stop_3368_);
v_res_3372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_3362_, v_00_u03b2_3363_, v_00_u03c3_3364_, v_f_3365_, v_as_3366_, v_i_boxed_3370_, v_stop_boxed_3371_, v_b_3369_);
lean_dec_ref(v_as_3366_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03c3_3373_, lean_object* v_00_u03b1_3374_, lean_object* v_00_u03b2_3375_, lean_object* v_f_3376_, lean_object* v_keys_3377_, lean_object* v_vals_3378_, lean_object* v_heq_3379_, lean_object* v_i_3380_, lean_object* v_acc_3381_){
_start:
{
lean_object* v___x_3382_; 
v___x_3382_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_3376_, v_keys_3377_, v_vals_3378_, v_i_3380_, v_acc_3381_);
return v___x_3382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03c3_3383_, lean_object* v_00_u03b1_3384_, lean_object* v_00_u03b2_3385_, lean_object* v_f_3386_, lean_object* v_keys_3387_, lean_object* v_vals_3388_, lean_object* v_heq_3389_, lean_object* v_i_3390_, lean_object* v_acc_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6(v_00_u03c3_3383_, v_00_u03b1_3384_, v_00_u03b2_3385_, v_f_3386_, v_keys_3387_, v_vals_3388_, v_heq_3389_, v_i_3390_, v_acc_3391_);
lean_dec_ref(v_vals_3388_);
lean_dec_ref(v_keys_3387_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0(lean_object* v_inst_3393_, lean_object* v_pureOnDidChange_3394_, lean_object* v_method_3395_, lean_object* v_onDidChange_3396_, lean_object* v_p_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_){
_start:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; 
lean_inc(v_inst_3393_);
v___x_3401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3401_, 0, v_inst_3393_);
lean_ctor_set(v___x_3401_, 1, v___y_3398_);
lean_inc_ref(v___y_3399_);
lean_inc_ref(v_p_3397_);
v___x_3402_ = lean_apply_4(v_pureOnDidChange_3394_, v_p_3397_, v___x_3401_, v___y_3399_, lean_box(0));
if (lean_obj_tag(v___x_3402_) == 0)
{
lean_object* v_a_3403_; lean_object* v_snd_3404_; lean_object* v___x_3405_; 
v_a_3403_ = lean_ctor_get(v___x_3402_, 0);
lean_inc(v_a_3403_);
lean_dec_ref_known(v___x_3402_, 1);
v_snd_3404_ = lean_ctor_get(v_a_3403_, 1);
lean_inc(v_snd_3404_);
lean_dec(v_a_3403_);
v___x_3405_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_3395_, v_snd_3404_, v_inst_3393_);
lean_dec(v_inst_3393_);
lean_dec(v_snd_3404_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; lean_object* v___x_3407_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
lean_dec_ref_known(v___x_3405_, 1);
lean_inc_ref(v___y_3399_);
v___x_3407_ = lean_apply_4(v_onDidChange_3396_, v_p_3397_, v_a_3406_, v___y_3399_, lean_box(0));
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3425_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3410_ = v___x_3407_;
v_isShared_3411_ = v_isSharedCheck_3425_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3407_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3425_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v_snd_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3423_; 
v_snd_3412_ = lean_ctor_get(v_a_3408_, 1);
v_isSharedCheck_3423_ = !lean_is_exclusive(v_a_3408_);
if (v_isSharedCheck_3423_ == 0)
{
lean_object* v_unused_3424_; 
v_unused_3424_ = lean_ctor_get(v_a_3408_, 0);
lean_dec(v_unused_3424_);
v___x_3414_ = v_a_3408_;
v_isShared_3415_ = v_isSharedCheck_3423_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_snd_3412_);
lean_dec(v_a_3408_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3423_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3416_; lean_object* v___x_3418_; 
v___x_3416_ = lean_box(0);
if (v_isShared_3415_ == 0)
{
lean_ctor_set(v___x_3414_, 0, v___x_3416_);
v___x_3418_ = v___x_3414_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3416_);
lean_ctor_set(v_reuseFailAlloc_3422_, 1, v_snd_3412_);
v___x_3418_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
lean_object* v___x_3420_; 
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 0, v___x_3418_);
v___x_3420_ = v___x_3410_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3418_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
}
else
{
return v___x_3407_;
}
}
else
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
lean_dec_ref(v_p_3397_);
lean_dec_ref(v_onDidChange_3396_);
v_a_3426_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3428_ = v___x_3405_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3405_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3431_; 
if (v_isShared_3429_ == 0)
{
v___x_3431_ = v___x_3428_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_a_3426_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
lean_dec_ref(v_p_3397_);
lean_dec_ref(v_onDidChange_3396_);
lean_dec(v_inst_3393_);
v_a_3434_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3402_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3402_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object* v_inst_3442_, lean_object* v_pureOnDidChange_3443_, lean_object* v_method_3444_, lean_object* v_onDidChange_3445_, lean_object* v_p_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0(v_inst_3442_, v_pureOnDidChange_3443_, v_method_3444_, v_onDidChange_3445_, v_p_3446_, v___y_3447_, v___y_3448_);
lean_dec_ref(v___y_3448_);
lean_dec_ref(v_method_3444_);
return v_res_3450_;
}
}
static lean_object* _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3452_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__0));
v___x_3453_ = l_Lean_Server_RequestError_internalError(v___x_3452_);
return v___x_3453_;
}
}
static lean_object* _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3455_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__2));
v___x_3456_ = l_Lean_Server_RequestError_internalError(v___x_3455_);
return v___x_3456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1(lean_object* v_inst_3457_, lean_object* v_inst_3458_, lean_object* v_pureHandle_3459_, lean_object* v_inst_3460_, lean_object* v_method_3461_, lean_object* v_handler_3462_, lean_object* v_p_3463_, lean_object* v_s_3464_, lean_object* v___y_3465_){
_start:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
lean_inc(v_p_3463_);
v___x_3467_ = lean_apply_1(v_inst_3457_, v_p_3463_);
lean_inc(v_inst_3458_);
v___x_3468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3468_, 0, v_inst_3458_);
lean_ctor_set(v___x_3468_, 1, v_s_3464_);
lean_inc_ref(v___y_3465_);
v___x_3469_ = lean_apply_4(v_pureHandle_3459_, v___x_3467_, v___x_3468_, v___y_3465_, lean_box(0));
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v_a_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3504_; 
v_a_3470_ = lean_ctor_get(v___x_3469_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3472_ = v___x_3469_;
v_isShared_3473_ = v_isSharedCheck_3504_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_a_3470_);
lean_dec(v___x_3469_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3504_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v_fst_3474_; lean_object* v_snd_3475_; lean_object* v_response_x3f_3476_; lean_object* v_serialized_3477_; uint8_t v_isComplete_3478_; lean_object* v_a_3480_; 
v_fst_3474_ = lean_ctor_get(v_a_3470_, 0);
lean_inc(v_fst_3474_);
v_snd_3475_ = lean_ctor_get(v_a_3470_, 1);
lean_inc(v_snd_3475_);
lean_dec(v_a_3470_);
v_response_x3f_3476_ = lean_ctor_get(v_fst_3474_, 0);
lean_inc(v_response_x3f_3476_);
v_serialized_3477_ = lean_ctor_get(v_fst_3474_, 1);
lean_inc_ref(v_serialized_3477_);
v_isComplete_3478_ = lean_ctor_get_uint8(v_fst_3474_, sizeof(void*)*2);
lean_dec(v_fst_3474_);
if (lean_obj_tag(v_response_x3f_3476_) == 0)
{
lean_object* v___x_3499_; 
v___x_3499_ = l_Lean_Json_parse(v_serialized_3477_);
if (lean_obj_tag(v___x_3499_) == 1)
{
lean_object* v_a_3500_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_a_3500_);
lean_dec_ref_known(v___x_3499_, 1);
v_a_3480_ = v_a_3500_;
goto v___jp_3479_;
}
else
{
lean_object* v___x_3501_; lean_object* v___x_3502_; 
lean_dec_ref(v___x_3499_);
lean_dec(v_snd_3475_);
lean_del_object(v___x_3472_);
lean_dec(v_p_3463_);
lean_dec_ref(v_handler_3462_);
lean_dec_ref(v_inst_3460_);
lean_dec(v_inst_3458_);
v___x_3501_ = lean_obj_once(&l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3, &l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3_once, _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3);
v___x_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
return v___x_3502_;
}
}
else
{
lean_object* v_val_3503_; 
lean_dec_ref(v_serialized_3477_);
v_val_3503_ = lean_ctor_get(v_response_x3f_3476_, 0);
lean_inc(v_val_3503_);
lean_dec_ref_known(v_response_x3f_3476_, 1);
v_a_3480_ = v_val_3503_;
goto v___jp_3479_;
}
v___jp_3479_:
{
lean_object* v___x_3481_; 
v___x_3481_ = lean_apply_1(v_inst_3460_, v_a_3480_);
if (lean_obj_tag(v___x_3481_) == 1)
{
lean_object* v_a_3482_; lean_object* v___x_3483_; 
lean_del_object(v___x_3472_);
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
lean_inc(v_a_3482_);
lean_dec_ref_known(v___x_3481_, 1);
v___x_3483_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_3461_, v_snd_3475_, v_inst_3458_);
lean_dec(v_inst_3458_);
lean_dec(v_snd_3475_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v_a_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
lean_inc(v_a_3484_);
lean_dec_ref_known(v___x_3483_, 1);
v___x_3485_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3485_, 0, v_a_3482_);
lean_ctor_set_uint8(v___x_3485_, sizeof(void*)*1, v_isComplete_3478_);
lean_inc_ref(v___y_3465_);
v___x_3486_ = lean_apply_5(v_handler_3462_, v_p_3463_, v___x_3485_, v_a_3484_, v___y_3465_, lean_box(0));
return v___x_3486_;
}
else
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3494_; 
lean_dec(v_a_3482_);
lean_dec(v_p_3463_);
lean_dec_ref(v_handler_3462_);
v_a_3487_ = lean_ctor_get(v___x_3483_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3489_ = v___x_3483_;
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3483_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3492_; 
if (v_isShared_3490_ == 0)
{
v___x_3492_ = v___x_3489_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_a_3487_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
else
{
lean_object* v___x_3495_; lean_object* v___x_3497_; 
lean_dec_ref(v___x_3481_);
lean_dec(v_snd_3475_);
lean_dec(v_p_3463_);
lean_dec_ref(v_handler_3462_);
lean_dec(v_inst_3458_);
v___x_3495_ = lean_obj_once(&l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1, &l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1_once, _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1);
if (v_isShared_3473_ == 0)
{
lean_ctor_set_tag(v___x_3472_, 1);
lean_ctor_set(v___x_3472_, 0, v___x_3495_);
v___x_3497_ = v___x_3472_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v___x_3495_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
}
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_dec(v_p_3463_);
lean_dec_ref(v_handler_3462_);
lean_dec_ref(v_inst_3460_);
lean_dec(v_inst_3458_);
v_a_3505_ = lean_ctor_get(v___x_3469_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3469_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3469_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___boxed(lean_object* v_inst_3513_, lean_object* v_inst_3514_, lean_object* v_pureHandle_3515_, lean_object* v_inst_3516_, lean_object* v_method_3517_, lean_object* v_handler_3518_, lean_object* v_p_3519_, lean_object* v_s_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1(v_inst_3513_, v_inst_3514_, v_pureHandle_3515_, v_inst_3516_, v_method_3517_, v_handler_3518_, v_p_3519_, v_s_3520_, v___y_3521_);
lean_dec_ref(v___y_3521_);
lean_dec_ref(v_method_3517_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg(lean_object* v_method_3525_, lean_object* v_inst_3526_, lean_object* v_inst_3527_, lean_object* v_inst_3528_, lean_object* v_inst_3529_, lean_object* v_inst_3530_, lean_object* v_inst_3531_, lean_object* v_handler_3532_, lean_object* v_onDidChange_3533_){
_start:
{
lean_object* v___x_3535_; 
v___x_3535_ = l_Lean_initializing();
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3577_; 
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3538_ = v___x_3535_;
v_isShared_3539_ = v_isSharedCheck_3577_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_3535_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3577_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
uint8_t v___x_3540_; uint8_t v___x_3541_; 
v___x_3540_ = lean_unbox(v_a_3536_);
lean_dec(v_a_3536_);
v___x_3541_ = lean_bool_not(v___x_3540_);
if (v___x_3541_ == 0)
{
lean_object* v___x_3542_; 
v___x_3542_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_3525_);
if (lean_obj_tag(v___x_3542_) == 1)
{
lean_object* v_val_3543_; lean_object* v_pureHandle_3544_; lean_object* v_pureOnDidChange_3545_; lean_object* v_initState_3546_; lean_object* v_completeness_3547_; lean_object* v___x_3548_; 
lean_del_object(v___x_3538_);
v_val_3543_ = lean_ctor_get(v___x_3542_, 0);
lean_inc(v_val_3543_);
lean_dec_ref_known(v___x_3542_, 1);
v_pureHandle_3544_ = lean_ctor_get(v_val_3543_, 1);
lean_inc_ref(v_pureHandle_3544_);
v_pureOnDidChange_3545_ = lean_ctor_get(v_val_3543_, 3);
lean_inc_ref(v_pureOnDidChange_3545_);
v_initState_3546_ = lean_ctor_get(v_val_3543_, 6);
lean_inc(v_initState_3546_);
v_completeness_3547_ = lean_ctor_get(v_val_3543_, 8);
lean_inc(v_completeness_3547_);
lean_dec(v_val_3543_);
v___x_3548_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(v_method_3525_, v_initState_3546_, v_inst_3531_);
lean_dec(v_initState_3546_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v_a_3549_; lean_object* v___f_3550_; lean_object* v___f_3551_; lean_object* v___x_3552_; 
v_a_3549_ = lean_ctor_get(v___x_3548_, 0);
lean_inc(v_a_3549_);
lean_dec_ref_known(v___x_3548_, 1);
lean_inc_ref_n(v_method_3525_, 2);
lean_inc_n(v_inst_3531_, 2);
v___f_3550_ = lean_alloc_closure((void*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_3550_, 0, v_inst_3531_);
lean_closure_set(v___f_3550_, 1, v_pureOnDidChange_3545_);
lean_closure_set(v___f_3550_, 2, v_method_3525_);
lean_closure_set(v___f_3550_, 3, v_onDidChange_3533_);
v___f_3551_ = lean_alloc_closure((void*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___boxed), 10, 6);
lean_closure_set(v___f_3551_, 0, v_inst_3527_);
lean_closure_set(v___f_3551_, 1, v_inst_3531_);
lean_closure_set(v___f_3551_, 2, v_pureHandle_3544_);
lean_closure_set(v___f_3551_, 3, v_inst_3529_);
lean_closure_set(v___f_3551_, 4, v_method_3525_);
lean_closure_set(v___f_3551_, 5, v_handler_3532_);
v___x_3552_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_3525_, v_completeness_3547_, v_inst_3526_, v_inst_3528_, v_inst_3530_, v_inst_3531_, v_a_3549_, v___f_3551_, v___f_3550_);
return v___x_3552_;
}
else
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
lean_dec(v_completeness_3547_);
lean_dec_ref(v_pureOnDidChange_3545_);
lean_dec_ref(v_pureHandle_3544_);
lean_dec_ref(v_onDidChange_3533_);
lean_dec_ref(v_handler_3532_);
lean_dec(v_inst_3531_);
lean_dec_ref(v_inst_3530_);
lean_dec_ref(v_inst_3529_);
lean_dec_ref(v_inst_3528_);
lean_dec_ref(v_inst_3527_);
lean_dec_ref(v_inst_3526_);
lean_dec_ref(v_method_3525_);
v_a_3553_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_3548_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3548_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
else
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3567_; 
lean_dec(v___x_3542_);
lean_dec_ref(v_onDidChange_3533_);
lean_dec_ref(v_handler_3532_);
lean_dec(v_inst_3531_);
lean_dec_ref(v_inst_3530_);
lean_dec_ref(v_inst_3529_);
lean_dec_ref(v_inst_3528_);
lean_dec_ref(v_inst_3527_);
lean_dec_ref(v_inst_3526_);
v___x_3561_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0));
v___x_3562_ = lean_string_append(v___x_3561_, v_method_3525_);
lean_dec_ref(v_method_3525_);
v___x_3563_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__1));
v___x_3564_ = lean_string_append(v___x_3562_, v___x_3563_);
v___x_3565_ = lean_mk_io_user_error(v___x_3564_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set_tag(v___x_3538_, 1);
lean_ctor_set(v___x_3538_, 0, v___x_3565_);
v___x_3567_ = v___x_3538_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_3565_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
else
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3575_; 
lean_dec_ref(v_onDidChange_3533_);
lean_dec_ref(v_handler_3532_);
lean_dec(v_inst_3531_);
lean_dec_ref(v_inst_3530_);
lean_dec_ref(v_inst_3529_);
lean_dec_ref(v_inst_3528_);
lean_dec_ref(v_inst_3527_);
lean_dec_ref(v_inst_3526_);
v___x_3569_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0));
v___x_3570_ = lean_string_append(v___x_3569_, v_method_3525_);
lean_dec_ref(v_method_3525_);
v___x_3571_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__4));
v___x_3572_ = lean_string_append(v___x_3570_, v___x_3571_);
v___x_3573_ = lean_mk_io_user_error(v___x_3572_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set_tag(v___x_3538_, 1);
lean_ctor_set(v___x_3538_, 0, v___x_3573_);
v___x_3575_ = v___x_3538_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3573_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
else
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3585_; 
lean_dec_ref(v_onDidChange_3533_);
lean_dec_ref(v_handler_3532_);
lean_dec(v_inst_3531_);
lean_dec_ref(v_inst_3530_);
lean_dec_ref(v_inst_3529_);
lean_dec_ref(v_inst_3528_);
lean_dec_ref(v_inst_3527_);
lean_dec_ref(v_inst_3526_);
lean_dec_ref(v_method_3525_);
v_a_3578_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3580_ = v___x_3535_;
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3535_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3583_; 
if (v_isShared_3581_ == 0)
{
v___x_3583_ = v___x_3580_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_a_3578_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_3586_, lean_object* v_inst_3587_, lean_object* v_inst_3588_, lean_object* v_inst_3589_, lean_object* v_inst_3590_, lean_object* v_inst_3591_, lean_object* v_inst_3592_, lean_object* v_handler_3593_, lean_object* v_onDidChange_3594_, lean_object* v_a_3595_){
_start:
{
lean_object* v_res_3596_; 
v_res_3596_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg(v_method_3586_, v_inst_3587_, v_inst_3588_, v_inst_3589_, v_inst_3590_, v_inst_3591_, v_inst_3592_, v_handler_3593_, v_onDidChange_3594_);
return v_res_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler(lean_object* v_method_3597_, lean_object* v_paramType_3598_, lean_object* v_inst_3599_, lean_object* v_inst_3600_, lean_object* v_inst_3601_, lean_object* v_respType_3602_, lean_object* v_inst_3603_, lean_object* v_inst_3604_, lean_object* v_stateType_3605_, lean_object* v_inst_3606_, lean_object* v_handler_3607_, lean_object* v_onDidChange_3608_){
_start:
{
lean_object* v___x_3610_; 
v___x_3610_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg(v_method_3597_, v_inst_3599_, v_inst_3600_, v_inst_3601_, v_inst_3603_, v_inst_3604_, v_inst_3606_, v_handler_3607_, v_onDidChange_3608_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___boxed(lean_object* v_method_3611_, lean_object* v_paramType_3612_, lean_object* v_inst_3613_, lean_object* v_inst_3614_, lean_object* v_inst_3615_, lean_object* v_respType_3616_, lean_object* v_inst_3617_, lean_object* v_inst_3618_, lean_object* v_stateType_3619_, lean_object* v_inst_3620_, lean_object* v_handler_3621_, lean_object* v_onDidChange_3622_, lean_object* v_a_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l_Lean_Server_chainStatefulLspRequestHandler(v_method_3611_, v_paramType_3612_, v_inst_3613_, v_inst_3614_, v_inst_3615_, v_respType_3616_, v_inst_3617_, v_inst_3618_, v_stateType_3619_, v_inst_3620_, v_handler_3621_, v_onDidChange_3622_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___lam__0(lean_object* v_p_3625_, lean_object* v_x_3626_, lean_object* v_handler_3627_, lean_object* v___y_3628_){
_start:
{
lean_object* v_onDidChange_3630_; lean_object* v___x_3631_; 
v_onDidChange_3630_ = lean_ctor_get(v_handler_3627_, 4);
lean_inc_ref(v_onDidChange_3630_);
lean_dec_ref(v_handler_3627_);
lean_inc_ref(v___y_3628_);
v___x_3631_ = lean_apply_3(v_onDidChange_3630_, v_p_3625_, v___y_3628_, lean_box(0));
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___lam__0___boxed(lean_object* v_p_3632_, lean_object* v_x_3633_, lean_object* v_handler_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
lean_object* v_res_3637_; 
v_res_3637_ = l_Lean_Server_handleOnDidChange___lam__0(v_p_3632_, v_x_3633_, v_handler_3634_, v___y_3635_);
lean_dec_ref(v___y_3635_);
lean_dec_ref(v_x_3633_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0(lean_object* v_f_3638_, lean_object* v_x_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_){
_start:
{
lean_object* v___x_3644_; 
lean_inc_ref(v___y_3642_);
v___x_3644_ = lean_apply_4(v_f_3638_, v___y_3640_, v___y_3641_, v___y_3642_, lean_box(0));
return v___x_3644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0___boxed(lean_object* v_f_3645_, lean_object* v_x_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0(v_f_3645_, v_x_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
lean_dec_ref(v___y_3649_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_3652_, lean_object* v_keys_3653_, lean_object* v_vals_3654_, lean_object* v_i_3655_, lean_object* v_acc_3656_, lean_object* v___y_3657_){
_start:
{
lean_object* v___x_3659_; uint8_t v___x_3660_; 
v___x_3659_ = lean_array_get_size(v_keys_3653_);
v___x_3660_ = lean_nat_dec_lt(v_i_3655_, v___x_3659_);
if (v___x_3660_ == 0)
{
lean_object* v___x_3661_; 
lean_dec(v_i_3655_);
lean_dec_ref(v_f_3652_);
v___x_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3661_, 0, v_acc_3656_);
return v___x_3661_;
}
else
{
lean_object* v_k_3662_; lean_object* v_v_3663_; lean_object* v___x_3664_; 
v_k_3662_ = lean_array_fget_borrowed(v_keys_3653_, v_i_3655_);
v_v_3663_ = lean_array_fget_borrowed(v_vals_3654_, v_i_3655_);
lean_inc_ref(v_f_3652_);
lean_inc_ref(v___y_3657_);
lean_inc(v_v_3663_);
lean_inc(v_k_3662_);
v___x_3664_ = lean_apply_5(v_f_3652_, v_acc_3656_, v_k_3662_, v_v_3663_, v___y_3657_, lean_box(0));
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_object* v_a_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
lean_inc(v_a_3665_);
lean_dec_ref_known(v___x_3664_, 1);
v___x_3666_ = lean_unsigned_to_nat(1u);
v___x_3667_ = lean_nat_add(v_i_3655_, v___x_3666_);
lean_dec(v_i_3655_);
v_i_3655_ = v___x_3667_;
v_acc_3656_ = v_a_3665_;
goto _start;
}
else
{
lean_dec(v_i_3655_);
lean_dec_ref(v_f_3652_);
return v___x_3664_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_3669_, lean_object* v_keys_3670_, lean_object* v_vals_3671_, lean_object* v_i_3672_, lean_object* v_acc_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3669_, v_keys_3670_, v_vals_3671_, v_i_3672_, v_acc_3673_, v___y_3674_);
lean_dec_ref(v___y_3674_);
lean_dec_ref(v_vals_3671_);
lean_dec_ref(v_keys_3670_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(lean_object* v_f_3677_, lean_object* v_x_3678_, lean_object* v_x_3679_, lean_object* v___y_3680_){
_start:
{
if (lean_obj_tag(v_x_3678_) == 0)
{
lean_object* v_es_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3702_; 
v_es_3682_ = lean_ctor_get(v_x_3678_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v_x_3678_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3684_ = v_x_3678_;
v_isShared_3685_ = v_isSharedCheck_3702_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_es_3682_);
lean_dec(v_x_3678_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3702_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3686_; lean_object* v___x_3687_; uint8_t v___x_3688_; 
v___x_3686_ = lean_unsigned_to_nat(0u);
v___x_3687_ = lean_array_get_size(v_es_3682_);
v___x_3688_ = lean_nat_dec_lt(v___x_3686_, v___x_3687_);
if (v___x_3688_ == 0)
{
lean_object* v___x_3690_; 
lean_dec_ref(v_es_3682_);
lean_dec_ref(v_f_3677_);
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 0, v_x_3679_);
v___x_3690_ = v___x_3684_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_x_3679_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
else
{
uint8_t v___x_3692_; 
v___x_3692_ = lean_nat_dec_le(v___x_3687_, v___x_3687_);
if (v___x_3692_ == 0)
{
if (v___x_3688_ == 0)
{
lean_object* v___x_3694_; 
lean_dec_ref(v_es_3682_);
lean_dec_ref(v_f_3677_);
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 0, v_x_3679_);
v___x_3694_ = v___x_3684_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_x_3679_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
else
{
size_t v___x_3696_; size_t v___x_3697_; lean_object* v___x_3698_; 
lean_del_object(v___x_3684_);
v___x_3696_ = ((size_t)0ULL);
v___x_3697_ = lean_usize_of_nat(v___x_3687_);
v___x_3698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3677_, v_es_3682_, v___x_3696_, v___x_3697_, v_x_3679_, v___y_3680_);
lean_dec_ref(v_es_3682_);
return v___x_3698_;
}
}
else
{
size_t v___x_3699_; size_t v___x_3700_; lean_object* v___x_3701_; 
lean_del_object(v___x_3684_);
v___x_3699_ = ((size_t)0ULL);
v___x_3700_ = lean_usize_of_nat(v___x_3687_);
v___x_3701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3677_, v_es_3682_, v___x_3699_, v___x_3700_, v_x_3679_, v___y_3680_);
lean_dec_ref(v_es_3682_);
return v___x_3701_;
}
}
}
}
else
{
lean_object* v_ks_3703_; lean_object* v_vs_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
v_ks_3703_ = lean_ctor_get(v_x_3678_, 0);
lean_inc_ref(v_ks_3703_);
v_vs_3704_ = lean_ctor_get(v_x_3678_, 1);
lean_inc_ref(v_vs_3704_);
lean_dec_ref_known(v_x_3678_, 2);
v___x_3705_ = lean_unsigned_to_nat(0u);
v___x_3706_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3677_, v_ks_3703_, v_vs_3704_, v___x_3705_, v_x_3679_, v___y_3680_);
lean_dec_ref(v_vs_3704_);
lean_dec_ref(v_ks_3703_);
return v___x_3706_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_3707_, lean_object* v_as_3708_, size_t v_i_3709_, size_t v_stop_3710_, lean_object* v_b_3711_, lean_object* v___y_3712_){
_start:
{
lean_object* v_a_3715_; lean_object* v___y_3720_; uint8_t v___x_3722_; 
v___x_3722_ = lean_usize_dec_eq(v_i_3709_, v_stop_3710_);
if (v___x_3722_ == 0)
{
lean_object* v___x_3723_; 
v___x_3723_ = lean_array_uget_borrowed(v_as_3708_, v_i_3709_);
switch(lean_obj_tag(v___x_3723_))
{
case 0:
{
lean_object* v_key_3724_; lean_object* v_val_3725_; lean_object* v___x_3726_; 
v_key_3724_ = lean_ctor_get(v___x_3723_, 0);
v_val_3725_ = lean_ctor_get(v___x_3723_, 1);
lean_inc_ref(v_f_3707_);
lean_inc_ref(v___y_3712_);
lean_inc(v_val_3725_);
lean_inc(v_key_3724_);
v___x_3726_ = lean_apply_5(v_f_3707_, v_b_3711_, v_key_3724_, v_val_3725_, v___y_3712_, lean_box(0));
v___y_3720_ = v___x_3726_;
goto v___jp_3719_;
}
case 1:
{
lean_object* v_node_3727_; lean_object* v___x_3728_; 
v_node_3727_ = lean_ctor_get(v___x_3723_, 0);
lean_inc(v_node_3727_);
lean_inc_ref(v_f_3707_);
v___x_3728_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3707_, v_node_3727_, v_b_3711_, v___y_3712_);
v___y_3720_ = v___x_3728_;
goto v___jp_3719_;
}
default: 
{
v_a_3715_ = v_b_3711_;
goto v___jp_3714_;
}
}
}
else
{
lean_object* v___x_3729_; 
lean_dec_ref(v_f_3707_);
v___x_3729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3729_, 0, v_b_3711_);
return v___x_3729_;
}
v___jp_3714_:
{
size_t v___x_3716_; size_t v___x_3717_; 
v___x_3716_ = ((size_t)1ULL);
v___x_3717_ = lean_usize_add(v_i_3709_, v___x_3716_);
v_i_3709_ = v___x_3717_;
v_b_3711_ = v_a_3715_;
goto _start;
}
v___jp_3719_:
{
if (lean_obj_tag(v___y_3720_) == 0)
{
lean_object* v_a_3721_; 
v_a_3721_ = lean_ctor_get(v___y_3720_, 0);
lean_inc(v_a_3721_);
lean_dec_ref_known(v___y_3720_, 1);
v_a_3715_ = v_a_3721_;
goto v___jp_3714_;
}
else
{
lean_dec_ref(v_f_3707_);
return v___y_3720_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_3730_, lean_object* v_as_3731_, lean_object* v_i_3732_, lean_object* v_stop_3733_, lean_object* v_b_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
size_t v_i_boxed_3737_; size_t v_stop_boxed_3738_; lean_object* v_res_3739_; 
v_i_boxed_3737_ = lean_unbox_usize(v_i_3732_);
lean_dec(v_i_3732_);
v_stop_boxed_3738_ = lean_unbox_usize(v_stop_3733_);
lean_dec(v_stop_3733_);
v_res_3739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3730_, v_as_3731_, v_i_boxed_3737_, v_stop_boxed_3738_, v_b_3734_, v___y_3735_);
lean_dec_ref(v___y_3735_);
lean_dec_ref(v_as_3731_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_3740_, lean_object* v_x_3741_, lean_object* v_x_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_){
_start:
{
lean_object* v_res_3745_; 
v_res_3745_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3740_, v_x_3741_, v_x_3742_, v___y_3743_);
lean_dec_ref(v___y_3743_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(lean_object* v_map_3746_, lean_object* v_f_3747_, lean_object* v___y_3748_){
_start:
{
lean_object* v___f_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
v___f_3750_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3750_, 0, v_f_3747_);
v___x_3751_ = lean_box(0);
v___x_3752_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v___f_3750_, v_map_3746_, v___x_3751_, v___y_3748_);
return v___x_3752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___boxed(lean_object* v_map_3753_, lean_object* v_f_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v_res_3757_; 
v_res_3757_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(v_map_3753_, v_f_3754_, v___y_3755_);
lean_dec_ref(v___y_3755_);
return v_res_3757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange(lean_object* v_p_3758_, lean_object* v_a_3759_){
_start:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___f_3763_; lean_object* v___x_3764_; 
v___x_3761_ = l_Lean_Server_statefulRequestHandlers;
v___x_3762_ = lean_st_ref_get(v___x_3761_);
v___f_3763_ = lean_alloc_closure((void*)(l_Lean_Server_handleOnDidChange___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3763_, 0, v_p_3758_);
v___x_3764_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(v___x_3762_, v___f_3763_, v_a_3759_);
return v___x_3764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___boxed(lean_object* v_p_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l_Lean_Server_handleOnDidChange(v_p_3765_, v_a_3766_);
lean_dec_ref(v_a_3766_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0(lean_object* v_00_u03b2_3769_, lean_object* v_map_3770_, lean_object* v_f_3771_, lean_object* v___y_3772_){
_start:
{
lean_object* v___x_3774_; 
v___x_3774_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(v_map_3770_, v_f_3771_, v___y_3772_);
return v___x_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___boxed(lean_object* v_00_u03b2_3775_, lean_object* v_map_3776_, lean_object* v_f_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_){
_start:
{
lean_object* v_res_3780_; 
v_res_3780_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0(v_00_u03b2_3775_, v_map_3776_, v_f_3777_, v___y_3778_);
lean_dec_ref(v___y_3778_);
return v_res_3780_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg(lean_object* v_map_3781_, lean_object* v_f_3782_, lean_object* v_init_3783_, lean_object* v___y_3784_){
_start:
{
lean_object* v___x_3786_; 
v___x_3786_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3782_, v_map_3781_, v_init_3783_, v___y_3784_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg___boxed(lean_object* v_map_3787_, lean_object* v_f_3788_, lean_object* v_init_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_){
_start:
{
lean_object* v_res_3792_; 
v_res_3792_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg(v_map_3787_, v_f_3788_, v_init_3789_, v___y_3790_);
lean_dec_ref(v___y_3790_);
return v_res_3792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0(lean_object* v_00_u03c3_3793_, lean_object* v_00_u03b2_3794_, lean_object* v_map_3795_, lean_object* v_f_3796_, lean_object* v_init_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v___x_3800_; 
v___x_3800_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3796_, v_map_3795_, v_init_3797_, v___y_3798_);
return v___x_3800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3801_, lean_object* v_00_u03b2_3802_, lean_object* v_map_3803_, lean_object* v_f_3804_, lean_object* v_init_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_){
_start:
{
lean_object* v_res_3808_; 
v_res_3808_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0(v_00_u03c3_3801_, v_00_u03b2_3802_, v_map_3803_, v_f_3804_, v_init_3805_, v___y_3806_);
lean_dec_ref(v___y_3806_);
return v_res_3808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3809_, lean_object* v_00_u03b1_3810_, lean_object* v_00_u03b2_3811_, lean_object* v_f_3812_, lean_object* v_x_3813_, lean_object* v_x_3814_, lean_object* v___y_3815_){
_start:
{
lean_object* v___x_3817_; 
v___x_3817_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3812_, v_x_3813_, v_x_3814_, v___y_3815_);
return v___x_3817_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3818_, lean_object* v_00_u03b1_3819_, lean_object* v_00_u03b2_3820_, lean_object* v_f_3821_, lean_object* v_x_3822_, lean_object* v_x_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_){
_start:
{
lean_object* v_res_3826_; 
v_res_3826_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1(v_00_u03c3_3818_, v_00_u03b1_3819_, v_00_u03b2_3820_, v_f_3821_, v_x_3822_, v_x_3823_, v___y_3824_);
lean_dec_ref(v___y_3824_);
return v_res_3826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3827_, lean_object* v_00_u03b2_3828_, lean_object* v_00_u03c3_3829_, lean_object* v_f_3830_, lean_object* v_as_3831_, size_t v_i_3832_, size_t v_stop_3833_, lean_object* v_b_3834_, lean_object* v___y_3835_){
_start:
{
lean_object* v___x_3837_; 
v___x_3837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3830_, v_as_3831_, v_i_3832_, v_stop_3833_, v_b_3834_, v___y_3835_);
return v___x_3837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3838_, lean_object* v_00_u03b2_3839_, lean_object* v_00_u03c3_3840_, lean_object* v_f_3841_, lean_object* v_as_3842_, lean_object* v_i_3843_, lean_object* v_stop_3844_, lean_object* v_b_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
size_t v_i_boxed_3848_; size_t v_stop_boxed_3849_; lean_object* v_res_3850_; 
v_i_boxed_3848_ = lean_unbox_usize(v_i_3843_);
lean_dec(v_i_3843_);
v_stop_boxed_3849_ = lean_unbox_usize(v_stop_3844_);
lean_dec(v_stop_3844_);
v_res_3850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3838_, v_00_u03b2_3839_, v_00_u03c3_3840_, v_f_3841_, v_as_3842_, v_i_boxed_3848_, v_stop_boxed_3849_, v_b_3845_, v___y_3846_);
lean_dec_ref(v___y_3846_);
lean_dec_ref(v_as_3842_);
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3851_, lean_object* v_00_u03b1_3852_, lean_object* v_00_u03b2_3853_, lean_object* v_f_3854_, lean_object* v_keys_3855_, lean_object* v_vals_3856_, lean_object* v_heq_3857_, lean_object* v_i_3858_, lean_object* v_acc_3859_, lean_object* v___y_3860_){
_start:
{
lean_object* v___x_3862_; 
v___x_3862_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3854_, v_keys_3855_, v_vals_3856_, v_i_3858_, v_acc_3859_, v___y_3860_);
return v___x_3862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3863_, lean_object* v_00_u03b1_3864_, lean_object* v_00_u03b2_3865_, lean_object* v_f_3866_, lean_object* v_keys_3867_, lean_object* v_vals_3868_, lean_object* v_heq_3869_, lean_object* v_i_3870_, lean_object* v_acc_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3863_, v_00_u03b1_3864_, v_00_u03b2_3865_, v_f_3866_, v_keys_3867_, v_vals_3868_, v_heq_3869_, v_i_3870_, v_acc_3871_, v___y_3872_);
lean_dec_ref(v___y_3872_);
lean_dec_ref(v_vals_3868_);
lean_dec_ref(v_keys_3867_);
return v_res_3874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest(lean_object* v_method_3877_, lean_object* v_params_3878_, lean_object* v_a_3879_){
_start:
{
uint8_t v___x_3881_; 
v___x_3881_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_3877_);
if (v___x_3881_ == 0)
{
lean_object* v___x_3882_; lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3898_; 
v___x_3882_ = l_Lean_Server_lookupLspRequestHandler(v_method_3877_);
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3885_ = v___x_3882_;
v_isShared_3886_ = v_isSharedCheck_3898_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v___x_3882_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3898_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
if (lean_obj_tag(v_a_3883_) == 0)
{
lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3893_; 
lean_dec(v_params_3878_);
v___x_3887_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__0));
v___x_3888_ = lean_string_append(v___x_3887_, v_method_3877_);
v___x_3889_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__1));
v___x_3890_ = lean_string_append(v___x_3888_, v___x_3889_);
v___x_3891_ = l_Lean_Server_RequestError_internalError(v___x_3890_);
if (v_isShared_3886_ == 0)
{
lean_ctor_set_tag(v___x_3885_, 1);
lean_ctor_set(v___x_3885_, 0, v___x_3891_);
v___x_3893_ = v___x_3885_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v___x_3891_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
else
{
lean_object* v_val_3895_; lean_object* v_handle_3896_; lean_object* v___x_3897_; 
lean_del_object(v___x_3885_);
v_val_3895_ = lean_ctor_get(v_a_3883_, 0);
lean_inc(v_val_3895_);
lean_dec_ref_known(v_a_3883_, 1);
v_handle_3896_ = lean_ctor_get(v_val_3895_, 1);
lean_inc_ref(v_handle_3896_);
lean_dec(v_val_3895_);
lean_inc_ref(v_a_3879_);
v___x_3897_ = lean_apply_3(v_handle_3896_, v_params_3878_, v_a_3879_, lean_box(0));
return v___x_3897_;
}
}
}
else
{
lean_object* v___x_3899_; 
v___x_3899_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_3877_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
lean_dec(v_params_3878_);
v___x_3900_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__0));
v___x_3901_ = lean_string_append(v___x_3900_, v_method_3877_);
v___x_3902_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__1));
v___x_3903_ = lean_string_append(v___x_3901_, v___x_3902_);
v___x_3904_ = l_Lean_Server_RequestError_internalError(v___x_3903_);
v___x_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3904_);
return v___x_3905_;
}
else
{
lean_object* v_val_3906_; lean_object* v_handle_3907_; lean_object* v___x_3908_; 
v_val_3906_ = lean_ctor_get(v___x_3899_, 0);
lean_inc(v_val_3906_);
lean_dec_ref_known(v___x_3899_, 1);
v_handle_3907_ = lean_ctor_get(v_val_3906_, 2);
lean_inc_ref(v_handle_3907_);
lean_dec(v_val_3906_);
lean_inc_ref(v_a_3879_);
v___x_3908_ = lean_apply_3(v_handle_3907_, v_params_3878_, v_a_3879_, lean_box(0));
return v___x_3908_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest___boxed(lean_object* v_method_3909_, lean_object* v_params_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_){
_start:
{
lean_object* v_res_3913_; 
v_res_3913_ = l_Lean_Server_handleLspRequest(v_method_3909_, v_params_3910_, v_a_3911_);
lean_dec_ref(v_a_3911_);
lean_dec_ref(v_method_3909_);
return v_res_3913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_routeLspRequest(lean_object* v_method_3914_, lean_object* v_params_3915_){
_start:
{
uint8_t v___x_3917_; 
v___x_3917_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_3914_);
if (v___x_3917_ == 0)
{
lean_object* v___x_3918_; lean_object* v_a_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3934_; 
v___x_3918_ = l_Lean_Server_lookupLspRequestHandler(v_method_3914_);
v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3921_ = v___x_3918_;
v_isShared_3922_ = v_isSharedCheck_3934_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_a_3919_);
lean_dec(v___x_3918_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3934_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
if (lean_obj_tag(v_a_3919_) == 0)
{
lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3926_; 
lean_dec(v_params_3915_);
v___x_3923_ = l_Lean_Server_RequestError_methodNotFound(v_method_3914_);
v___x_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 0, v___x_3924_);
v___x_3926_ = v___x_3921_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v___x_3924_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
else
{
lean_object* v_val_3928_; lean_object* v_fileSource_3929_; lean_object* v___x_3930_; lean_object* v___x_3932_; 
v_val_3928_ = lean_ctor_get(v_a_3919_, 0);
lean_inc(v_val_3928_);
lean_dec_ref_known(v_a_3919_, 1);
v_fileSource_3929_ = lean_ctor_get(v_val_3928_, 0);
lean_inc_ref(v_fileSource_3929_);
lean_dec(v_val_3928_);
v___x_3930_ = lean_apply_1(v_fileSource_3929_, v_params_3915_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 0, v___x_3930_);
v___x_3932_ = v___x_3921_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v___x_3930_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
}
else
{
lean_object* v___x_3935_; 
v___x_3935_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_3914_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; 
lean_dec(v_params_3915_);
v___x_3936_ = l_Lean_Server_RequestError_methodNotFound(v_method_3914_);
v___x_3937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3936_);
v___x_3938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3938_, 0, v___x_3937_);
return v___x_3938_;
}
else
{
lean_object* v_val_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3948_; 
v_val_3939_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3941_ = v___x_3935_;
v_isShared_3942_ = v_isSharedCheck_3948_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_val_3939_);
lean_dec(v___x_3935_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3948_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v_fileSource_3943_; lean_object* v___x_3944_; lean_object* v___x_3946_; 
v_fileSource_3943_ = lean_ctor_get(v_val_3939_, 0);
lean_inc_ref(v_fileSource_3943_);
lean_dec(v_val_3939_);
v___x_3944_ = lean_apply_1(v_fileSource_3943_, v_params_3915_);
if (v_isShared_3942_ == 0)
{
lean_ctor_set_tag(v___x_3941_, 0);
lean_ctor_set(v___x_3941_, 0, v___x_3944_);
v___x_3946_ = v___x_3941_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v___x_3944_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_routeLspRequest___boxed(lean_object* v_method_3949_, lean_object* v_params_3950_, lean_object* v_a_3951_){
_start:
{
lean_object* v_res_3952_; 
v_res_3952_ = l_Lean_Server_routeLspRequest(v_method_3949_, v_params_3950_);
lean_dec_ref(v_method_3949_);
return v_res_3952_;
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
