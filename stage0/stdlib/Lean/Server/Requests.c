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
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
uint8_t l_Lean_initializing();
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_instMonadLiftBaseIOEIO___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadFinallyEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_tryFinally___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* l_StateRefT_x27_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Mutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AsyncList_waitFind_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_EIO_asTask___redArg(lean_object*);
uint8_t l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(lean_object*);
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
static const lean_ctor_object l_Lean_Server_instInhabitedServerRequestResponse_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_instInhabitedRequestError_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_instInhabitedServerRequestResponse_default___redArg___closed__0 = (const lean_object*)&l_Lean_Server_instInhabitedServerRequestResponse_default___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse___redArg();
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse___redArg___boxed(lean_object*);
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
static const lean_closure_object l_Lean_Server_registerLspRequestHandler___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerLspRequestHandler___redArg___closed__0 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___redArg___closed__0_value;
static const lean_string_object l_Lean_Server_registerLspRequestHandler___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Failed to register LSP request handler for '"};
static const lean_object* l_Lean_Server_registerLspRequestHandler___redArg___closed__1 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___redArg___closed__1_value;
static const lean_string_object l_Lean_Server_registerLspRequestHandler___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "': only possible during initialization"};
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
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftBaseIOEIO___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0_value),((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3_value)} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__4 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__4_value),((lean_object*)&l_Lean_Server_instMonadLiftEIOExceptionRequestM___closed__0_value)} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__5 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__5_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadFinallyEIO___aux__1___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__6 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__6_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_tryFinally___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__6_value)} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__7 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__7_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__8 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__8_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0_value),((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__8_value)} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__9 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__9_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__9_value),((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3_value)} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__10 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__10_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__10_value),((lean_object*)&l_Lean_Server_instMonadLiftEIOExceptionRequestM___closed__0_value)} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__11 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__11_value;
static const lean_string_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "Failed to register stateful LSP request handler for '"};
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__12 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__12_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__13 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__13_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__14 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__14_value;
static lean_once_cell_t l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_methodNotFound(lean_object* v_method_14_){
_start:
{
uint8_t v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_15_ = 2;
v___x_16_ = ((lean_object*)(l_Lean_Server_RequestError_methodNotFound___closed__0));
v___x_17_ = lean_string_append(v___x_16_, v_method_14_);
v___x_18_ = ((lean_object*)(l_Lean_Server_RequestError_methodNotFound___closed__1));
v___x_19_ = lean_string_append(v___x_17_, v___x_18_);
v___x_20_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_20_, 0, v___x_19_);
lean_ctor_set_uint8(v___x_20_, sizeof(void*)*1, v___x_15_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_methodNotFound___boxed(lean_object* v_method_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Server_RequestError_methodNotFound(v_method_21_);
lean_dec_ref(v_method_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_invalidParams(lean_object* v_message_23_){
_start:
{
uint8_t v___x_24_; lean_object* v___x_25_; 
v___x_24_ = 3;
v___x_25_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_25_, 0, v_message_23_);
lean_ctor_set_uint8(v___x_25_, sizeof(void*)*1, v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_internalError(lean_object* v_message_26_){
_start:
{
uint8_t v___x_27_; lean_object* v___x_28_; 
v___x_27_ = 4;
v___x_28_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_28_, 0, v_message_26_);
lean_ctor_set_uint8(v___x_28_, sizeof(void*)*1, v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_ofException(lean_object* v_e_38_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_40_ = l_Lean_Exception_toMessageData(v_e_38_);
v___x_41_ = l_Lean_MessageData_toString(v___x_40_);
v___x_42_ = l_Lean_Server_RequestError_internalError(v___x_41_);
v___x_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_ofException___boxed(lean_object* v_e_44_, lean_object* v_a_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Server_RequestError_ofException(v_e_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_ofIoError(lean_object* v_e_47_){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = lean_io_error_to_string(v_e_47_);
v___x_49_ = l_Lean_Server_RequestError_internalError(v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_toLspResponseError(lean_object* v_id_50_, lean_object* v_e_51_){
_start:
{
uint8_t v_code_52_; lean_object* v_message_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v_code_52_ = lean_ctor_get_uint8(v_e_51_, sizeof(void*)*1);
v_message_53_ = lean_ctor_get(v_e_51_, 0);
v___x_54_ = lean_box(0);
lean_inc_ref(v_message_53_);
v___x_55_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_55_, 0, v_id_50_);
lean_ctor_set(v___x_55_, 1, v_message_53_);
lean_ctor_set(v___x_55_, 2, v___x_54_);
lean_ctor_set_uint8(v___x_55_, sizeof(void*)*3, v_code_52_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_toLspResponseError___boxed(lean_object* v_id_56_, lean_object* v_e_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Server_RequestError_toLspResponseError(v_id_56_, v_e_57_);
lean_dec_ref(v_e_57_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___redArg(lean_object* v_inst_61_, lean_object* v_params_62_){
_start:
{
lean_object* v___x_63_; 
lean_inc(v_params_62_);
v___x_63_ = lean_apply_1(v_inst_61_, v_params_62_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v_a_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_79_; 
v_a_64_ = lean_ctor_get(v___x_63_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_79_ == 0)
{
v___x_66_ = v___x_63_;
v_isShared_67_ = v_isSharedCheck_79_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_a_64_);
lean_dec(v___x_63_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_79_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
uint8_t v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_77_; 
v___x_68_ = 3;
v___x_69_ = ((lean_object*)(l_Lean_Server_parseRequestParams___redArg___closed__0));
v___x_70_ = l_Lean_Json_compress(v_params_62_);
v___x_71_ = lean_string_append(v___x_69_, v___x_70_);
lean_dec_ref(v___x_70_);
v___x_72_ = ((lean_object*)(l_Lean_Server_parseRequestParams___redArg___closed__1));
v___x_73_ = lean_string_append(v___x_71_, v___x_72_);
v___x_74_ = lean_string_append(v___x_73_, v_a_64_);
lean_dec(v_a_64_);
v___x_75_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_75_, 0, v___x_74_);
lean_ctor_set_uint8(v___x_75_, sizeof(void*)*1, v___x_68_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 0, v___x_75_);
v___x_77_ = v___x_66_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_75_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
else
{
lean_object* v_a_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_87_; 
lean_dec(v_params_62_);
v_a_80_ = lean_ctor_get(v___x_63_, 0);
v_isSharedCheck_87_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_87_ == 0)
{
v___x_82_ = v___x_63_;
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_a_80_);
lean_dec(v___x_63_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_85_; 
if (v_isShared_83_ == 0)
{
v___x_85_ = v___x_82_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_a_80_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams(lean_object* v_paramType_88_, lean_object* v_inst_89_, lean_object* v_params_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_Server_parseRequestParams___redArg(v_inst_89_, v_params_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___redArg(lean_object* v_x_92_){
_start:
{
if (lean_obj_tag(v_x_92_) == 0)
{
lean_object* v___x_93_; 
v___x_93_ = lean_unsigned_to_nat(0u);
return v___x_93_;
}
else
{
lean_object* v___x_94_; 
v___x_94_ = lean_unsigned_to_nat(1u);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___redArg___boxed(lean_object* v_x_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Server_ServerRequestResponse_ctorIdx___redArg(v_x_95_);
lean_dec_ref(v_x_95_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx(lean_object* v_00_u03b1_97_, lean_object* v_x_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_Server_ServerRequestResponse_ctorIdx___redArg(v_x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___boxed(lean_object* v_00_u03b1_100_, lean_object* v_x_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_Server_ServerRequestResponse_ctorIdx(v_00_u03b1_100_, v_x_101_);
lean_dec_ref(v_x_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorElim___redArg(lean_object* v_t_103_, lean_object* v_k_104_){
_start:
{
if (lean_obj_tag(v_t_103_) == 0)
{
lean_object* v_response_105_; lean_object* v___x_106_; 
v_response_105_ = lean_ctor_get(v_t_103_, 0);
lean_inc(v_response_105_);
lean_dec_ref_known(v_t_103_, 1);
v___x_106_ = lean_apply_1(v_k_104_, v_response_105_);
return v___x_106_;
}
else
{
uint8_t v_code_107_; lean_object* v_message_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v_code_107_ = lean_ctor_get_uint8(v_t_103_, sizeof(void*)*1);
v_message_108_ = lean_ctor_get(v_t_103_, 0);
lean_inc_ref(v_message_108_);
lean_dec_ref_known(v_t_103_, 1);
v___x_109_ = lean_box(v_code_107_);
v___x_110_ = lean_apply_2(v_k_104_, v___x_109_, v_message_108_);
return v___x_110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorElim(lean_object* v_00_u03b1_111_, lean_object* v_motive_112_, lean_object* v_ctorIdx_113_, lean_object* v_t_114_, lean_object* v_h_115_, lean_object* v_k_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_114_, v_k_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorElim___boxed(lean_object* v_00_u03b1_118_, lean_object* v_motive_119_, lean_object* v_ctorIdx_120_, lean_object* v_t_121_, lean_object* v_h_122_, lean_object* v_k_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_Server_ServerRequestResponse_ctorElim(v_00_u03b1_118_, v_motive_119_, v_ctorIdx_120_, v_t_121_, v_h_122_, v_k_123_);
lean_dec(v_ctorIdx_120_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_success_elim___redArg(lean_object* v_t_125_, lean_object* v_success_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_125_, v_success_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_success_elim(lean_object* v_00_u03b1_128_, lean_object* v_motive_129_, lean_object* v_t_130_, lean_object* v_h_131_, lean_object* v_success_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_130_, v_success_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_failure_elim___redArg(lean_object* v_t_134_, lean_object* v_failure_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_134_, v_failure_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_failure_elim(lean_object* v_00_u03b1_137_, lean_object* v_motive_138_, lean_object* v_t_139_, lean_object* v_h_140_, lean_object* v_failure_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_139_, v_failure_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse_default___redArg(){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = ((lean_object*)(l_Lean_Server_instInhabitedServerRequestResponse_default___redArg___closed__0));
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse_default___redArg___boxed(lean_object* v___dummy_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_Server_instInhabitedServerRequestResponse_default___redArg();
return v_res_149_;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0(void){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Lean_Server_instInhabitedServerRequestResponse_default___redArg();
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse_default(lean_object* v_00_u03b1_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = lean_obj_once(&l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0, &l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0_once, _init_l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse___redArg(){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = lean_obj_once(&l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0, &l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0_once, _init_l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse___redArg___boxed(lean_object* v___dummy_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Server_instInhabitedServerRequestResponse___redArg();
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse(lean_object* v_a_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = lean_obj_once(&l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0, &l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0_once, _init_l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run___redArg(lean_object* v_act_159_, lean_object* v_rc_160_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = lean_apply_2(v_act_159_, v_rc_160_, lean_box(0));
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run___redArg___boxed(lean_object* v_act_163_, lean_object* v_rc_164_, lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Server_RequestM_run___redArg(v_act_163_, v_rc_164_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run(lean_object* v_00_u03b1_167_, lean_object* v_act_168_, lean_object* v_rc_169_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lean_apply_2(v_act_168_, v_rc_169_, lean_box(0));
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run___boxed(lean_object* v_00_u03b1_172_, lean_object* v_act_173_, lean_object* v_rc_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_Server_RequestM_run(v_00_u03b1_172_, v_act_173_, v_rc_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestTask_pure___redArg(lean_object* v_a_177_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_178_, 0, v_a_177_);
v___x_179_ = lean_task_pure(v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestTask_pure(lean_object* v_00_u03b1_180_, lean_object* v_a_181_){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_182_, 0, v_a_181_);
v___x_183_ = lean_task_pure(v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM___lam__0(lean_object* v_00_u03b1_184_, lean_object* v_x_185_, lean_object* v___y_186_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = lean_apply_1(v_x_185_, lean_box(0));
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_196_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_196_ == 0)
{
v___x_191_ = v___x_188_;
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_188_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
if (v_isShared_192_ == 0)
{
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_189_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_205_; 
v_a_197_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_205_ == 0)
{
v___x_199_ = v___x_188_;
v_isShared_200_ = v_isSharedCheck_205_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_188_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_205_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_201_ = l_Lean_Server_RequestError_ofIoError(v_a_197_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 0, v___x_201_);
v___x_203_ = v___x_199_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_201_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM___lam__0___boxed(lean_object* v_00_u03b1_206_, lean_object* v_x_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_Server_instMonadLiftIORequestM___lam__0(v_00_u03b1_206_, v_x_207_, v___y_208_);
lean_dec_ref(v___y_208_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0(lean_object* v_00_u03b1_213_, lean_object* v_x_214_, lean_object* v___y_215_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = lean_apply_1(v_x_214_, lean_box(0));
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v___x_217_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
else
{
lean_object* v_a_226_; lean_object* v___x_227_; lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
v_a_226_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_a_226_);
lean_dec_ref_known(v___x_217_, 1);
v___x_227_ = l_Lean_Server_RequestError_ofException(v_a_226_);
v_a_228_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_227_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_227_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
lean_ctor_set_tag(v___x_230_, 1);
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_228_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0___boxed(lean_object* v_00_u03b1_236_, lean_object* v_x_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0(v_00_u03b1_236_, v_x_237_, v___y_238_);
lean_dec_ref(v___y_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0(lean_object* v_00_u03b1_243_, lean_object* v_x_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_cancelTk_247_; lean_object* v___x_248_; 
v_cancelTk_247_ = lean_ctor_get(v___y_245_, 4);
lean_inc_ref(v_cancelTk_247_);
v___x_248_ = lean_apply_2(v_x_244_, v_cancelTk_247_, lean_box(0));
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_261_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_261_ == 0)
{
v___x_251_ = v___x_248_;
v_isShared_252_ = v_isSharedCheck_261_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_248_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_261_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
if (lean_obj_tag(v_a_249_) == 0)
{
lean_object* v___x_253_; lean_object* v___x_255_; 
lean_dec_ref_known(v_a_249_, 1);
v___x_253_ = ((lean_object*)(l_Lean_Server_RequestError_requestCancelled));
if (v_isShared_252_ == 0)
{
lean_ctor_set_tag(v___x_251_, 1);
lean_ctor_set(v___x_251_, 0, v___x_253_);
v___x_255_ = v___x_251_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_253_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
else
{
lean_object* v_a_257_; lean_object* v___x_259_; 
v_a_257_ = lean_ctor_get(v_a_249_, 0);
lean_inc(v_a_257_);
lean_dec_ref_known(v_a_249_, 1);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 0, v_a_257_);
v___x_259_ = v___x_251_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
else
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_270_; 
v_a_262_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_270_ == 0)
{
v___x_264_ = v___x_248_;
v_isShared_265_ = v_isSharedCheck_270_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_248_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_270_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_266_; lean_object* v___x_268_; 
v___x_266_ = l_Lean_Server_RequestError_ofIoError(v_a_262_);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 0, v___x_266_);
v___x_268_ = v___x_264_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_266_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0___boxed(lean_object* v_00_u03b1_271_, lean_object* v_x_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0(v_00_u03b1_271_, v_x_272_, v___y_273_);
lean_dec_ref(v___y_273_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO___redArg(lean_object* v_x_278_, lean_object* v_ctx_279_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = lean_apply_2(v_x_278_, v_ctx_279_, lean_box(0));
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
v_a_282_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_289_ == 0)
{
v___x_284_ = v___x_281_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_281_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_299_; 
v_a_290_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_299_ == 0)
{
v___x_292_ = v___x_281_;
v_isShared_293_ = v_isSharedCheck_299_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_281_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_299_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v_message_294_; lean_object* v___x_295_; lean_object* v___x_297_; 
v_message_294_ = lean_ctor_get(v_a_290_, 0);
lean_inc_ref(v_message_294_);
lean_dec(v_a_290_);
v___x_295_ = lean_mk_io_user_error(v_message_294_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 0, v___x_295_);
v___x_297_ = v___x_292_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO___redArg___boxed(lean_object* v_x_300_, lean_object* v_ctx_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_Server_RequestM_runInIO___redArg(v_x_300_, v_ctx_301_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO(lean_object* v_00_u03b1_304_, lean_object* v_x_305_, lean_object* v_ctx_306_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_Server_RequestM_runInIO___redArg(v_x_305_, v_ctx_306_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO___boxed(lean_object* v_00_u03b1_309_, lean_object* v_x_310_, lean_object* v_ctx_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_Server_RequestM_runInIO(v_00_u03b1_309_, v_x_310_, v_ctx_311_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___redArg___lam__0(lean_object* v_toPure_314_, lean_object* v_rc_315_){
_start:
{
lean_object* v_doc_316_; lean_object* v___x_317_; 
v_doc_316_ = lean_ctor_get(v_rc_315_, 1);
lean_inc_ref(v_doc_316_);
lean_dec_ref(v_rc_315_);
v___x_317_ = lean_apply_2(v_toPure_314_, lean_box(0), v_doc_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___redArg(lean_object* v_inst_318_, lean_object* v_inst_319_){
_start:
{
lean_object* v_toApplicative_320_; lean_object* v_toBind_321_; lean_object* v_toPure_322_; lean_object* v___f_323_; lean_object* v___x_324_; 
v_toApplicative_320_ = lean_ctor_get(v_inst_318_, 0);
lean_inc_ref(v_toApplicative_320_);
v_toBind_321_ = lean_ctor_get(v_inst_318_, 1);
lean_inc(v_toBind_321_);
lean_dec_ref(v_inst_318_);
v_toPure_322_ = lean_ctor_get(v_toApplicative_320_, 1);
lean_inc(v_toPure_322_);
lean_dec_ref(v_toApplicative_320_);
v___f_323_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_readDoc___redArg___lam__0), 2, 1);
lean_closure_set(v___f_323_, 0, v_toPure_322_);
v___x_324_ = lean_apply_4(v_toBind_321_, lean_box(0), lean_box(0), v_inst_319_, v___f_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc(lean_object* v_m_325_, lean_object* v_inst_326_, lean_object* v_inst_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Lean_Server_RequestM_readDoc___redArg(v_inst_326_, v_inst_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg___lam__0(lean_object* v_t_329_, lean_object* v_a_330_){
_start:
{
lean_object* v___x_332_; 
lean_inc_ref(v_a_330_);
v___x_332_ = lean_apply_2(v_t_329_, v_a_330_, lean_box(0));
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg___lam__0___boxed(lean_object* v_t_333_, lean_object* v_a_334_, lean_object* v___y_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_Server_RequestM_asTask___redArg___lam__0(v_t_333_, v_a_334_);
lean_dec_ref(v_a_334_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg(lean_object* v_t_337_, lean_object* v_a_338_){
_start:
{
lean_object* v___f_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
lean_inc_ref(v_a_338_);
v___f_340_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_asTask___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_340_, 0, v_t_337_);
lean_closure_set(v___f_340_, 1, v_a_338_);
v___x_341_ = l_Lean_Server_ServerTask_EIO_asTask___redArg(v___f_340_);
v___x_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg___boxed(lean_object* v_t_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_Server_RequestM_asTask___redArg(v_t_343_, v_a_344_);
lean_dec_ref(v_a_344_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask(lean_object* v_00_u03b1_347_, lean_object* v_t_348_, lean_object* v_a_349_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_Server_RequestM_asTask___redArg(v_t_348_, v_a_349_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___boxed(lean_object* v_00_u03b1_352_, lean_object* v_t_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_Server_RequestM_asTask(v_00_u03b1_352_, v_t_353_, v_a_354_);
lean_dec_ref(v_a_354_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask___redArg(lean_object* v_t_357_, lean_object* v_a_358_){
_start:
{
lean_object* v___x_360_; 
lean_inc_ref(v_a_358_);
v___x_360_ = lean_apply_2(v_t_357_, v_a_358_, lean_box(0));
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_370_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_370_ == 0)
{
v___x_363_ = v___x_360_;
v_isShared_364_ = v_isSharedCheck_370_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_360_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_370_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_365_, 0, v_a_361_);
v___x_366_ = lean_task_pure(v___x_365_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v___x_366_);
v___x_368_ = v___x_363_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
v_a_371_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_360_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_360_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask___redArg___boxed(lean_object* v_t_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Server_RequestM_pureTask___redArg(v_t_379_, v_a_380_);
lean_dec_ref(v_a_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask(lean_object* v_00_u03b1_383_, lean_object* v_t_384_, lean_object* v_a_385_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_Server_RequestM_pureTask___redArg(v_t_384_, v_a_385_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask___boxed(lean_object* v_00_u03b1_388_, lean_object* v_t_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_Server_RequestM_pureTask(v_00_u03b1_388_, v_t_389_, v_a_390_);
lean_dec_ref(v_a_390_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0(lean_object* v_f_393_, lean_object* v_a_394_, lean_object* v_x_395_){
_start:
{
lean_object* v___x_397_; 
lean_inc_ref(v_a_394_);
v___x_397_ = lean_apply_3(v_f_393_, v_x_395_, v_a_394_, lean_box(0));
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0___boxed(lean_object* v_f_398_, lean_object* v_a_399_, lean_object* v_x_400_, lean_object* v___y_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0(v_f_398_, v_a_399_, v_x_400_);
lean_dec_ref(v_a_399_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg(lean_object* v_t_403_, lean_object* v_f_404_, lean_object* v_a_405_){
_start:
{
lean_object* v___f_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
lean_inc_ref(v_a_405_);
v___f_407_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_407_, 0, v_f_404_);
lean_closure_set(v___f_407_, 1, v_a_405_);
v___x_408_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(v___f_407_, v_t_403_);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg___boxed(lean_object* v_t_410_, lean_object* v_f_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_t_410_, v_f_411_, v_a_412_);
lean_dec_ref(v_a_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap(lean_object* v_00_u03b1_415_, lean_object* v_00_u03b2_416_, lean_object* v_t_417_, lean_object* v_f_418_, lean_object* v_a_419_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_t_417_, v_f_418_, v_a_419_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___boxed(lean_object* v_00_u03b1_422_, lean_object* v_00_u03b2_423_, lean_object* v_t_424_, lean_object* v_f_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_Server_RequestM_mapTaskCheap(v_00_u03b1_422_, v_00_u03b2_423_, v_t_424_, v_f_425_, v_a_426_);
lean_dec_ref(v_a_426_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly___redArg(lean_object* v_t_429_, lean_object* v_f_430_, lean_object* v_a_431_){
_start:
{
lean_object* v___f_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
lean_inc_ref(v_a_431_);
v___f_433_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_433_, 0, v_f_430_);
lean_closure_set(v___f_433_, 1, v_a_431_);
v___x_434_ = l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(v___f_433_, v_t_429_);
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly___redArg___boxed(lean_object* v_t_436_, lean_object* v_f_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_t_436_, v_f_437_, v_a_438_);
lean_dec_ref(v_a_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly(lean_object* v_00_u03b1_441_, lean_object* v_00_u03b2_442_, lean_object* v_t_443_, lean_object* v_f_444_, lean_object* v_a_445_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_t_443_, v_f_444_, v_a_445_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly___boxed(lean_object* v_00_u03b1_448_, lean_object* v_00_u03b2_449_, lean_object* v_t_450_, lean_object* v_f_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_Server_RequestM_mapTaskCostly(v_00_u03b1_448_, v_00_u03b2_449_, v_t_450_, v_f_451_, v_a_452_);
lean_dec_ref(v_a_452_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0(lean_object* v_f_455_, lean_object* v_a_456_, lean_object* v_x_457_){
_start:
{
lean_object* v___x_459_; 
lean_inc_ref(v_a_456_);
v___x_459_ = lean_apply_3(v_f_455_, v_x_457_, v_a_456_, lean_box(0));
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0___boxed(lean_object* v_f_460_, lean_object* v_a_461_, lean_object* v_x_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0(v_f_460_, v_a_461_, v_x_462_);
lean_dec_ref(v_a_461_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg(lean_object* v_t_465_, lean_object* v_f_466_, lean_object* v_a_467_){
_start:
{
lean_object* v___f_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
lean_inc_ref(v_a_467_);
v___f_469_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_469_, 0, v_f_466_);
lean_closure_set(v___f_469_, 1, v_a_467_);
v___x_470_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(v_t_465_, v___f_469_);
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg___boxed(lean_object* v_t_472_, lean_object* v_f_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_Server_RequestM_bindTaskCheap___redArg(v_t_472_, v_f_473_, v_a_474_);
lean_dec_ref(v_a_474_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap(lean_object* v_00_u03b1_477_, lean_object* v_00_u03b2_478_, lean_object* v_t_479_, lean_object* v_f_480_, lean_object* v_a_481_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_Server_RequestM_bindTaskCheap___redArg(v_t_479_, v_f_480_, v_a_481_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___boxed(lean_object* v_00_u03b1_484_, lean_object* v_00_u03b2_485_, lean_object* v_t_486_, lean_object* v_f_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_Server_RequestM_bindTaskCheap(v_00_u03b1_484_, v_00_u03b2_485_, v_t_486_, v_f_487_, v_a_488_);
lean_dec_ref(v_a_488_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly___redArg(lean_object* v_t_491_, lean_object* v_f_492_, lean_object* v_a_493_){
_start:
{
lean_object* v___f_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
lean_inc_ref(v_a_493_);
v___f_495_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_495_, 0, v_f_492_);
lean_closure_set(v___f_495_, 1, v_a_493_);
v___x_496_ = l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(v_t_491_, v___f_495_);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly___redArg___boxed(lean_object* v_t_498_, lean_object* v_f_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_t_498_, v_f_499_, v_a_500_);
lean_dec_ref(v_a_500_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly(lean_object* v_00_u03b1_503_, lean_object* v_00_u03b2_504_, lean_object* v_t_505_, lean_object* v_f_506_, lean_object* v_a_507_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_t_505_, v_f_506_, v_a_507_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly___boxed(lean_object* v_00_u03b1_510_, lean_object* v_00_u03b2_511_, lean_object* v_t_512_, lean_object* v_f_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_Server_RequestM_bindTaskCostly(v_00_u03b1_510_, v_00_u03b2_511_, v_t_512_, v_f_513_, v_a_514_);
lean_dec_ref(v_a_514_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0(lean_object* v_f_517_, lean_object* v_x_518_, lean_object* v___y_519_){
_start:
{
if (lean_obj_tag(v_x_518_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
lean_dec_ref(v_f_517_);
v_a_521_ = lean_ctor_get(v_x_518_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v_x_518_);
if (v_isSharedCheck_528_ == 0)
{
v___x_523_ = v_x_518_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v_x_518_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
lean_ctor_set_tag(v___x_523_, 1);
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_521_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
else
{
lean_object* v_a_529_; lean_object* v___x_530_; 
v_a_529_ = lean_ctor_get(v_x_518_, 0);
lean_inc(v_a_529_);
lean_dec_ref_known(v_x_518_, 1);
lean_inc_ref(v___y_519_);
v___x_530_ = lean_apply_3(v_f_517_, v_a_529_, v___y_519_, lean_box(0));
return v___x_530_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0___boxed(lean_object* v_f_531_, lean_object* v_x_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0(v_f_531_, v_x_532_, v___y_533_);
lean_dec_ref(v___y_533_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg(lean_object* v_t_536_, lean_object* v_f_537_, lean_object* v_a_538_){
_start:
{
lean_object* v___f_540_; lean_object* v___x_541_; 
v___f_540_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_540_, 0, v_f_537_);
v___x_541_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_t_536_, v___f_540_, v_a_538_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___boxed(lean_object* v_t_542_, lean_object* v_f_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_Server_RequestM_mapRequestTaskCheap___redArg(v_t_542_, v_f_543_, v_a_544_);
lean_dec_ref(v_a_544_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap(lean_object* v_00_u03b1_547_, lean_object* v_00_u03b2_548_, lean_object* v_t_549_, lean_object* v_f_550_, lean_object* v_a_551_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_Server_RequestM_mapRequestTaskCheap___redArg(v_t_549_, v_f_550_, v_a_551_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___boxed(lean_object* v_00_u03b1_554_, lean_object* v_00_u03b2_555_, lean_object* v_t_556_, lean_object* v_f_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_Server_RequestM_mapRequestTaskCheap(v_00_u03b1_554_, v_00_u03b2_555_, v_t_556_, v_f_557_, v_a_558_);
lean_dec_ref(v_a_558_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(lean_object* v_t_561_, lean_object* v_f_562_, lean_object* v_a_563_){
_start:
{
lean_object* v___f_565_; lean_object* v___x_566_; 
v___f_565_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_565_, 0, v_f_562_);
v___x_566_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_t_561_, v___f_565_, v_a_563_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly___redArg___boxed(lean_object* v_t_567_, lean_object* v_f_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(v_t_567_, v_f_568_, v_a_569_);
lean_dec_ref(v_a_569_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly(lean_object* v_00_u03b1_572_, lean_object* v_00_u03b2_573_, lean_object* v_t_574_, lean_object* v_f_575_, lean_object* v_a_576_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(v_t_574_, v_f_575_, v_a_576_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly___boxed(lean_object* v_00_u03b1_579_, lean_object* v_00_u03b2_580_, lean_object* v_t_581_, lean_object* v_f_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_Server_RequestM_mapRequestTaskCostly(v_00_u03b1_579_, v_00_u03b2_580_, v_t_581_, v_f_582_, v_a_583_);
lean_dec_ref(v_a_583_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0(lean_object* v_f_586_, lean_object* v_x_587_, lean_object* v___y_588_){
_start:
{
if (lean_obj_tag(v_x_587_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_dec_ref(v_f_586_);
v_a_590_ = lean_ctor_get(v_x_587_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v_x_587_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v_x_587_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v_x_587_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set_tag(v___x_592_, 1);
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
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
lean_object* v_a_598_; lean_object* v___x_599_; 
v_a_598_ = lean_ctor_get(v_x_587_, 0);
lean_inc(v_a_598_);
lean_dec_ref_known(v_x_587_, 1);
lean_inc_ref(v___y_588_);
v___x_599_ = lean_apply_3(v_f_586_, v_a_598_, v___y_588_, lean_box(0));
return v___x_599_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0___boxed(lean_object* v_f_600_, lean_object* v_x_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0(v_f_600_, v_x_601_, v___y_602_);
lean_dec_ref(v___y_602_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg(lean_object* v_t_605_, lean_object* v_f_606_, lean_object* v_a_607_){
_start:
{
lean_object* v___f_609_; lean_object* v___x_610_; 
v___f_609_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_609_, 0, v_f_606_);
v___x_610_ = l_Lean_Server_RequestM_bindTaskCheap___redArg(v_t_605_, v___f_609_, v_a_607_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___boxed(lean_object* v_t_611_, lean_object* v_f_612_, lean_object* v_a_613_, lean_object* v_a_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_Server_RequestM_bindRequestTaskCheap___redArg(v_t_611_, v_f_612_, v_a_613_);
lean_dec_ref(v_a_613_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap(lean_object* v_00_u03b1_616_, lean_object* v_00_u03b2_617_, lean_object* v_t_618_, lean_object* v_f_619_, lean_object* v_a_620_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_Server_RequestM_bindRequestTaskCheap___redArg(v_t_618_, v_f_619_, v_a_620_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___boxed(lean_object* v_00_u03b1_623_, lean_object* v_00_u03b2_624_, lean_object* v_t_625_, lean_object* v_f_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_Server_RequestM_bindRequestTaskCheap(v_00_u03b1_623_, v_00_u03b2_624_, v_t_625_, v_f_626_, v_a_627_);
lean_dec_ref(v_a_627_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly___redArg(lean_object* v_t_630_, lean_object* v_f_631_, lean_object* v_a_632_){
_start:
{
lean_object* v___f_634_; lean_object* v___x_635_; 
v___f_634_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_634_, 0, v_f_631_);
v___x_635_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_t_630_, v___f_634_, v_a_632_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly___redArg___boxed(lean_object* v_t_636_, lean_object* v_f_637_, lean_object* v_a_638_, lean_object* v_a_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_Server_RequestM_bindRequestTaskCostly___redArg(v_t_636_, v_f_637_, v_a_638_);
lean_dec_ref(v_a_638_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly(lean_object* v_00_u03b1_641_, lean_object* v_00_u03b2_642_, lean_object* v_t_643_, lean_object* v_f_644_, lean_object* v_a_645_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_Server_RequestM_bindRequestTaskCostly___redArg(v_t_643_, v_f_644_, v_a_645_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly___boxed(lean_object* v_00_u03b1_648_, lean_object* v_00_u03b2_649_, lean_object* v_t_650_, lean_object* v_f_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_Server_RequestM_bindRequestTaskCostly(v_00_u03b1_648_, v_00_u03b2_649_, v_t_650_, v_f_651_, v_a_652_);
lean_dec_ref(v_a_652_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___redArg(lean_object* v_inst_655_, lean_object* v_params_656_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_Server_parseRequestParams___redArg(v_inst_655_, v_params_656_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
lean_ctor_set_tag(v___x_661_, 1);
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_659_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
v_a_667_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_658_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_658_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
lean_ctor_set_tag(v___x_669_, 0);
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___redArg___boxed(lean_object* v_inst_675_, lean_object* v_params_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_675_, v_params_676_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams(lean_object* v_paramType_679_, lean_object* v_inst_680_, lean_object* v_params_681_, lean_object* v_a_682_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_680_, v_params_681_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___boxed(lean_object* v_paramType_685_, lean_object* v_inst_686_, lean_object* v_params_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_Server_RequestM_parseRequestParams(v_paramType_685_, v_inst_686_, v_params_687_, v_a_688_);
lean_dec_ref(v_a_688_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_checkCancelled(lean_object* v_a_691_){
_start:
{
lean_object* v_cancelTk_693_; uint8_t v___x_694_; 
v_cancelTk_693_ = lean_ctor_get(v_a_691_, 4);
v___x_694_ = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_cancelTk_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_box(0);
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
return v___x_696_;
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = ((lean_object*)(l_Lean_Server_RequestError_requestCancelled));
v___x_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
return v___x_698_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_checkCancelled___boxed(lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_Server_RequestM_checkCancelled(v_a_699_);
lean_dec_ref(v_a_699_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0(lean_object* v_inst_703_, lean_object* v_x_704_){
_start:
{
if (lean_obj_tag(v_x_704_) == 0)
{
lean_object* v_response_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_723_; 
v_response_705_ = lean_ctor_get(v_x_704_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v_x_704_);
if (v_isSharedCheck_723_ == 0)
{
v___x_707_ = v_x_704_;
v_isShared_708_ = v_isSharedCheck_723_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_response_705_);
lean_dec(v_x_704_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_723_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; 
lean_inc(v_response_705_);
v___x_709_ = lean_apply_1(v_inst_703_, v_response_705_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; uint8_t v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
lean_del_object(v___x_707_);
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v___x_711_ = 0;
v___x_712_ = ((lean_object*)(l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0___closed__0));
v___x_713_ = l_Lean_Json_compress(v_response_705_);
v___x_714_ = lean_string_append(v___x_712_, v___x_713_);
lean_dec_ref(v___x_713_);
v___x_715_ = ((lean_object*)(l_Lean_Server_parseRequestParams___redArg___closed__1));
v___x_716_ = lean_string_append(v___x_714_, v___x_715_);
v___x_717_ = lean_string_append(v___x_716_, v_a_710_);
lean_dec(v_a_710_);
v___x_718_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set_uint8(v___x_718_, sizeof(void*)*1, v___x_711_);
return v___x_718_;
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; 
lean_dec(v_response_705_);
v_a_719_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_709_, 1);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v_a_719_);
v___x_721_ = v___x_707_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
else
{
uint8_t v_code_724_; lean_object* v_message_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec_ref(v_inst_703_);
v_code_724_ = lean_ctor_get_uint8(v_x_704_, sizeof(void*)*1);
v_message_725_ = lean_ctor_get(v_x_704_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v_x_704_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v_x_704_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_message_725_);
lean_dec(v_x_704_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_message_725_);
lean_ctor_set_uint8(v_reuseFailAlloc_731_, sizeof(void*)*1, v_code_724_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___redArg(lean_object* v_inst_733_, lean_object* v_inst_734_, lean_object* v_method_735_, lean_object* v_param_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_serverRequestEmitter_739_; lean_object* v___f_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v_serverRequestEmitter_739_ = lean_ctor_get(v_a_737_, 5);
v___f_740_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0), 2, 1);
lean_closure_set(v___f_740_, 0, v_inst_734_);
v___x_741_ = lean_apply_1(v_inst_733_, v_param_736_);
lean_inc_ref(v_serverRequestEmitter_739_);
v___x_742_ = lean_apply_3(v_serverRequestEmitter_739_, v_method_735_, v___x_741_, lean_box(0));
v___x_743_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_740_, v___x_742_);
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___redArg___boxed(lean_object* v_inst_745_, lean_object* v_inst_746_, lean_object* v_method_747_, lean_object* v_param_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_Server_RequestM_sendServerRequest___redArg(v_inst_745_, v_inst_746_, v_method_747_, v_param_748_, v_a_749_);
lean_dec_ref(v_a_749_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest(lean_object* v_paramType_752_, lean_object* v_inst_753_, lean_object* v_responseType_754_, lean_object* v_inst_755_, lean_object* v_inst_756_, lean_object* v_method_757_, lean_object* v_param_758_, lean_object* v_a_759_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Lean_Server_RequestM_sendServerRequest___redArg(v_inst_753_, v_inst_755_, v_method_757_, v_param_758_, v_a_759_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___boxed(lean_object* v_paramType_762_, lean_object* v_inst_763_, lean_object* v_responseType_764_, lean_object* v_inst_765_, lean_object* v_inst_766_, lean_object* v_method_767_, lean_object* v_param_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_Server_RequestM_sendServerRequest(v_paramType_762_, v_inst_763_, v_responseType_764_, v_inst_765_, v_inst_766_, v_method_767_, v_param_768_, v_a_769_);
lean_dec_ref(v_a_769_);
lean_dec(v_inst_766_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux___redArg(lean_object* v_notFoundX_772_, lean_object* v_x_773_, lean_object* v_x_774_, lean_object* v_a_775_){
_start:
{
if (lean_obj_tag(v_x_774_) == 0)
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_785_; 
lean_dec_ref(v_x_773_);
lean_dec_ref(v_notFoundX_772_);
v_a_777_ = lean_ctor_get(v_x_774_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v_x_774_);
if (v_isSharedCheck_785_ == 0)
{
v___x_779_ = v_x_774_;
v_isShared_780_ = v_isSharedCheck_785_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v_x_774_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_785_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; lean_object* v___x_783_; 
v___x_781_ = l_Lean_Server_RequestError_ofIoError(v_a_777_);
if (v_isShared_780_ == 0)
{
lean_ctor_set_tag(v___x_779_, 1);
lean_ctor_set(v___x_779_, 0, v___x_781_);
v___x_783_ = v___x_779_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
else
{
lean_object* v_a_786_; 
v_a_786_ = lean_ctor_get(v_x_774_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v_x_774_, 1);
if (lean_obj_tag(v_a_786_) == 0)
{
lean_object* v___x_787_; 
lean_dec_ref(v_x_773_);
lean_inc_ref(v_a_775_);
v___x_787_ = lean_apply_2(v_notFoundX_772_, v_a_775_, lean_box(0));
return v___x_787_;
}
else
{
lean_object* v_val_788_; lean_object* v___x_789_; 
lean_dec_ref(v_notFoundX_772_);
v_val_788_ = lean_ctor_get(v_a_786_, 0);
lean_inc(v_val_788_);
lean_dec_ref_known(v_a_786_, 1);
lean_inc_ref(v_a_775_);
v___x_789_ = lean_apply_3(v_x_773_, v_val_788_, v_a_775_, lean_box(0));
return v___x_789_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux___redArg___boxed(lean_object* v_notFoundX_790_, lean_object* v_x_791_, lean_object* v_x_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Lean_Server_RequestM_waitFindSnapAux___redArg(v_notFoundX_790_, v_x_791_, v_x_792_, v_a_793_);
lean_dec_ref(v_a_793_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux(lean_object* v_00_u03b1_796_, lean_object* v_notFoundX_797_, lean_object* v_x_798_, lean_object* v_x_799_, lean_object* v_a_800_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_Server_RequestM_waitFindSnapAux___redArg(v_notFoundX_797_, v_x_798_, v_x_799_, v_a_800_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux___boxed(lean_object* v_00_u03b1_803_, lean_object* v_notFoundX_804_, lean_object* v_x_805_, lean_object* v_x_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_Server_RequestM_waitFindSnapAux(v_00_u03b1_803_, v_notFoundX_804_, v_x_805_, v_x_806_, v_a_807_);
lean_dec_ref(v_a_807_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___redArg(lean_object* v_doc_810_, lean_object* v_p_811_, lean_object* v_notFoundX_812_, lean_object* v_x_813_, lean_object* v_a_814_){
_start:
{
lean_object* v_toEditableDocumentCore_816_; lean_object* v_cmdSnaps_817_; lean_object* v_findTask_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v_toEditableDocumentCore_816_ = lean_ctor_get(v_doc_810_, 0);
lean_inc_ref(v_toEditableDocumentCore_816_);
lean_dec_ref(v_doc_810_);
v_cmdSnaps_817_ = lean_ctor_get(v_toEditableDocumentCore_816_, 2);
lean_inc(v_cmdSnaps_817_);
lean_dec_ref(v_toEditableDocumentCore_816_);
v_findTask_818_ = l_Lean_AsyncList_waitFind_x3f___redArg(v_p_811_, v_cmdSnaps_817_);
v___x_819_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_waitFindSnapAux___boxed), 6, 3);
lean_closure_set(v___x_819_, 0, lean_box(0));
lean_closure_set(v___x_819_, 1, v_notFoundX_812_);
lean_closure_set(v___x_819_, 2, v_x_813_);
v___x_820_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_findTask_818_, v___x_819_, v_a_814_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___redArg___boxed(lean_object* v_doc_821_, lean_object* v_p_822_, lean_object* v_notFoundX_823_, lean_object* v_x_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_doc_821_, v_p_822_, v_notFoundX_823_, v_x_824_, v_a_825_);
lean_dec_ref(v_a_825_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap(lean_object* v_00_u03b2_828_, lean_object* v_doc_829_, lean_object* v_p_830_, lean_object* v_notFoundX_831_, lean_object* v_x_832_, lean_object* v_a_833_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_doc_829_, v_p_830_, v_notFoundX_831_, v_x_832_, v_a_833_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___boxed(lean_object* v_00_u03b2_836_, lean_object* v_doc_837_, lean_object* v_p_838_, lean_object* v_notFoundX_839_, lean_object* v_x_840_, lean_object* v_a_841_, lean_object* v_a_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_Server_RequestM_withWaitFindSnap(v_00_u03b2_836_, v_doc_837_, v_p_838_, v_notFoundX_839_, v_x_840_, v_a_841_);
lean_dec_ref(v_a_841_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___redArg(lean_object* v_doc_844_, lean_object* v_p_845_, lean_object* v_notFoundX_846_, lean_object* v_x_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_toEditableDocumentCore_850_; lean_object* v_cmdSnaps_851_; lean_object* v_findTask_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v_toEditableDocumentCore_850_ = lean_ctor_get(v_doc_844_, 0);
lean_inc_ref(v_toEditableDocumentCore_850_);
lean_dec_ref(v_doc_844_);
v_cmdSnaps_851_ = lean_ctor_get(v_toEditableDocumentCore_850_, 2);
lean_inc(v_cmdSnaps_851_);
lean_dec_ref(v_toEditableDocumentCore_850_);
v_findTask_852_ = l_Lean_AsyncList_waitFind_x3f___redArg(v_p_845_, v_cmdSnaps_851_);
v___x_853_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_waitFindSnapAux___boxed), 6, 3);
lean_closure_set(v___x_853_, 0, lean_box(0));
lean_closure_set(v___x_853_, 1, v_notFoundX_846_);
lean_closure_set(v___x_853_, 2, v_x_847_);
v___x_854_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_findTask_852_, v___x_853_, v_a_848_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___redArg___boxed(lean_object* v_doc_855_, lean_object* v_p_856_, lean_object* v_notFoundX_857_, lean_object* v_x_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_Server_RequestM_bindWaitFindSnap___redArg(v_doc_855_, v_p_856_, v_notFoundX_857_, v_x_858_, v_a_859_);
lean_dec_ref(v_a_859_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap(lean_object* v_00_u03b2_862_, lean_object* v_doc_863_, lean_object* v_p_864_, lean_object* v_notFoundX_865_, lean_object* v_x_866_, lean_object* v_a_867_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_Server_RequestM_bindWaitFindSnap___redArg(v_doc_863_, v_p_864_, v_notFoundX_865_, v_x_866_, v_a_867_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___boxed(lean_object* v_00_u03b2_870_, lean_object* v_doc_871_, lean_object* v_p_872_, lean_object* v_notFoundX_873_, lean_object* v_x_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lean_Server_RequestM_bindWaitFindSnap(v_00_u03b2_870_, v_doc_871_, v_p_872_, v_notFoundX_873_, v_x_874_, v_a_875_);
lean_dec_ref(v_a_875_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(lean_object* v___y_878_){
_start:
{
lean_object* v_doc_880_; lean_object* v___x_881_; 
v_doc_880_ = lean_ctor_get(v___y_878_, 1);
lean_inc_ref(v_doc_880_);
v___x_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_881_, 0, v_doc_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0___boxed(lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(v___y_882_);
lean_dec_ref(v___y_882_);
return v_res_884_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0(lean_object* v___x_885_, lean_object* v_s_886_){
_start:
{
lean_object* v___x_887_; uint8_t v___x_888_; 
v___x_887_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_s_886_);
v___x_888_ = lean_nat_dec_le(v___x_885_, v___x_887_);
lean_dec(v___x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0___boxed(lean_object* v___x_889_, lean_object* v_s_890_){
_start:
{
uint8_t v_res_891_; lean_object* v_r_892_; 
v_res_891_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0(v___x_889_, v_s_890_);
lean_dec_ref(v_s_890_);
lean_dec(v___x_889_);
v_r_892_ = lean_box(v_res_891_);
return v_r_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1(lean_object* v___x_893_, lean_object* v___y_894_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_893_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1___boxed(lean_object* v___x_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1(v___x_897_, v___y_898_);
lean_dec_ref(v___y_898_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg(lean_object* v_lspPos_905_, lean_object* v_f_906_, lean_object* v_a_907_){
_start:
{
lean_object* v___x_909_; lean_object* v_a_910_; lean_object* v_toEditableDocumentCore_911_; lean_object* v_meta_912_; lean_object* v_text_913_; lean_object* v_line_914_; lean_object* v_character_915_; lean_object* v___x_916_; lean_object* v___f_917_; uint8_t v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___f_931_; lean_object* v___x_932_; 
v___x_909_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(v_a_907_);
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
lean_dec_ref(v___x_909_);
v_toEditableDocumentCore_911_ = lean_ctor_get(v_a_910_, 0);
v_meta_912_ = lean_ctor_get(v_toEditableDocumentCore_911_, 0);
v_text_913_ = lean_ctor_get(v_meta_912_, 3);
v_line_914_ = lean_ctor_get(v_lspPos_905_, 0);
lean_inc(v_line_914_);
v_character_915_ = lean_ctor_get(v_lspPos_905_, 1);
lean_inc(v_character_915_);
v___x_916_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_913_, v_lspPos_905_);
v___f_917_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_917_, 0, v___x_916_);
v___x_918_ = 3;
v___x_919_ = ((lean_object*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__0));
v___x_920_ = ((lean_object*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__1));
v___x_921_ = l_Nat_reprFast(v_line_914_);
v___x_922_ = lean_string_append(v___x_920_, v___x_921_);
lean_dec_ref(v___x_921_);
v___x_923_ = ((lean_object*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__2));
v___x_924_ = lean_string_append(v___x_922_, v___x_923_);
v___x_925_ = l_Nat_reprFast(v_character_915_);
v___x_926_ = lean_string_append(v___x_924_, v___x_925_);
lean_dec_ref(v___x_925_);
v___x_927_ = ((lean_object*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__3));
v___x_928_ = lean_string_append(v___x_926_, v___x_927_);
v___x_929_ = lean_string_append(v___x_919_, v___x_928_);
lean_dec_ref(v___x_928_);
v___x_930_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set_uint8(v___x_930_, sizeof(void*)*1, v___x_918_);
v___f_931_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_931_, 0, v___x_930_);
v___x_932_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_a_910_, v___f_917_, v___f_931_, v_f_906_, v_a_907_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___boxed(lean_object* v_lspPos_933_, lean_object* v_f_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg(v_lspPos_933_, v_f_934_, v_a_935_);
lean_dec_ref(v_a_935_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos(lean_object* v_00_u03b1_938_, lean_object* v_lspPos_939_, lean_object* v_f_940_, lean_object* v_a_941_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg(v_lspPos_939_, v_f_940_, v_a_941_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___boxed(lean_object* v_00_u03b1_944_, lean_object* v_lspPos_945_, lean_object* v_f_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos(v_00_u03b1_944_, v_lspPos_945_, v_f_946_, v_a_947_);
lean_dec_ref(v_a_947_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___redArg(lean_object* v_snap_950_, lean_object* v_c_951_, lean_object* v_a_952_){
_start:
{
lean_object* v_doc_954_; lean_object* v_toEditableDocumentCore_955_; lean_object* v_meta_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v_doc_954_ = lean_ctor_get(v_a_952_, 1);
v_toEditableDocumentCore_955_ = lean_ctor_get(v_doc_954_, 0);
v_meta_956_ = lean_ctor_get(v_toEditableDocumentCore_955_, 0);
lean_inc_ref(v_a_952_);
v___x_957_ = lean_apply_1(v_c_951_, v_a_952_);
v___x_958_ = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(v_snap_950_, v_meta_956_, v___x_957_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_971_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_971_ == 0)
{
v___x_961_ = v___x_958_;
v_isShared_962_ = v_isSharedCheck_971_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_971_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
if (lean_obj_tag(v_a_959_) == 0)
{
lean_object* v_a_963_; lean_object* v___x_965_; 
v_a_963_ = lean_ctor_get(v_a_959_, 0);
lean_inc(v_a_963_);
lean_dec_ref_known(v_a_959_, 1);
if (v_isShared_962_ == 0)
{
lean_ctor_set_tag(v___x_961_, 1);
lean_ctor_set(v___x_961_, 0, v_a_963_);
v___x_965_ = v___x_961_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; 
v_a_967_ = lean_ctor_get(v_a_959_, 0);
lean_inc(v_a_967_);
lean_dec_ref_known(v_a_959_, 1);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v_a_967_);
v___x_969_ = v___x_961_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
else
{
lean_object* v_a_972_; lean_object* v___x_973_; lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
v_a_972_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_972_);
lean_dec_ref_known(v___x_958_, 1);
v___x_973_ = l_Lean_Server_RequestError_ofException(v_a_972_);
v_a_974_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_973_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_973_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
lean_ctor_set_tag(v___x_976_, 1);
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___redArg___boxed(lean_object* v_snap_982_, lean_object* v_c_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_Server_RequestM_runCommandElabM___redArg(v_snap_982_, v_c_983_, v_a_984_);
lean_dec_ref(v_a_984_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM(lean_object* v_00_u03b1_987_, lean_object* v_snap_988_, lean_object* v_c_989_, lean_object* v_a_990_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_Server_RequestM_runCommandElabM___redArg(v_snap_988_, v_c_989_, v_a_990_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___boxed(lean_object* v_00_u03b1_993_, lean_object* v_snap_994_, lean_object* v_c_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_Server_RequestM_runCommandElabM(v_00_u03b1_993_, v_snap_994_, v_c_995_, v_a_996_);
lean_dec_ref(v_a_996_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___redArg(lean_object* v_snap_999_, lean_object* v_c_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_doc_1003_; lean_object* v_toEditableDocumentCore_1004_; lean_object* v_meta_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_doc_1003_ = lean_ctor_get(v_a_1001_, 1);
v_toEditableDocumentCore_1004_ = lean_ctor_get(v_doc_1003_, 0);
v_meta_1005_ = lean_ctor_get(v_toEditableDocumentCore_1004_, 0);
lean_inc_ref(v_a_1001_);
v___x_1006_ = lean_apply_1(v_c_1000_, v_a_1001_);
v___x_1007_ = l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(v_snap_999_, v_meta_1005_, v___x_1006_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1020_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1010_ = v___x_1007_;
v_isShared_1011_ = v_isSharedCheck_1020_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_1007_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1020_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
if (lean_obj_tag(v_a_1008_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1014_; 
v_a_1012_ = lean_ctor_get(v_a_1008_, 0);
lean_inc(v_a_1012_);
lean_dec_ref_known(v_a_1008_, 1);
if (v_isShared_1011_ == 0)
{
lean_ctor_set_tag(v___x_1010_, 1);
lean_ctor_set(v___x_1010_, 0, v_a_1012_);
v___x_1014_ = v___x_1010_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1012_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; 
v_a_1016_ = lean_ctor_get(v_a_1008_, 0);
lean_inc(v_a_1016_);
lean_dec_ref_known(v_a_1008_, 1);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v_a_1016_);
v___x_1018_ = v___x_1010_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1022_; lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
v_a_1021_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___x_1007_, 1);
v___x_1022_ = l_Lean_Server_RequestError_ofException(v_a_1021_);
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
lean_ctor_set_tag(v___x_1025_, 1);
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___redArg___boxed(lean_object* v_snap_1031_, lean_object* v_c_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lean_Server_RequestM_runCoreM___redArg(v_snap_1031_, v_c_1032_, v_a_1033_);
lean_dec_ref(v_a_1033_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM(lean_object* v_00_u03b1_1036_, lean_object* v_snap_1037_, lean_object* v_c_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_Server_RequestM_runCoreM___redArg(v_snap_1037_, v_c_1038_, v_a_1039_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___boxed(lean_object* v_00_u03b1_1042_, lean_object* v_snap_1043_, lean_object* v_c_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lean_Server_RequestM_runCoreM(v_00_u03b1_1042_, v_snap_1043_, v_c_1044_, v_a_1045_);
lean_dec_ref(v_a_1045_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___redArg(lean_object* v_snap_1048_, lean_object* v_c_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v_doc_1052_; lean_object* v_toEditableDocumentCore_1053_; lean_object* v_meta_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v_doc_1052_ = lean_ctor_get(v_a_1050_, 1);
v_toEditableDocumentCore_1053_ = lean_ctor_get(v_doc_1052_, 0);
v_meta_1054_ = lean_ctor_get(v_toEditableDocumentCore_1053_, 0);
lean_inc_ref(v_a_1050_);
v___x_1055_ = lean_apply_1(v_c_1049_, v_a_1050_);
v___x_1056_ = l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg(v_snap_1048_, v_meta_1054_, v___x_1055_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1069_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1059_ = v___x_1056_;
v_isShared_1060_ = v_isSharedCheck_1069_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1056_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1069_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
if (lean_obj_tag(v_a_1057_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1063_; 
v_a_1061_ = lean_ctor_get(v_a_1057_, 0);
lean_inc(v_a_1061_);
lean_dec_ref_known(v_a_1057_, 1);
if (v_isShared_1060_ == 0)
{
lean_ctor_set_tag(v___x_1059_, 1);
lean_ctor_set(v___x_1059_, 0, v_a_1061_);
v___x_1063_ = v___x_1059_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; 
v_a_1065_ = lean_ctor_get(v_a_1057_, 0);
lean_inc(v_a_1065_);
lean_dec_ref_known(v_a_1057_, 1);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 0, v_a_1065_);
v___x_1067_ = v___x_1059_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1071_; lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
v_a_1070_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1070_);
lean_dec_ref_known(v___x_1056_, 1);
v___x_1071_ = l_Lean_Server_RequestError_ofException(v_a_1070_);
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1071_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1071_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
lean_ctor_set_tag(v___x_1074_, 1);
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___redArg___boxed(lean_object* v_snap_1080_, lean_object* v_c_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_Server_RequestM_runTermElabM___redArg(v_snap_1080_, v_c_1081_, v_a_1082_);
lean_dec_ref(v_a_1082_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM(lean_object* v_00_u03b1_1085_, lean_object* v_snap_1086_, lean_object* v_c_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_Server_RequestM_runTermElabM___redArg(v_snap_1086_, v_c_1087_, v_a_1088_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___boxed(lean_object* v_00_u03b1_1091_, lean_object* v_snap_1092_, lean_object* v_c_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_Server_RequestM_runTermElabM(v_00_u03b1_1091_, v_snap_1092_, v_c_1093_, v_a_1094_);
lean_dec_ref(v_a_1094_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage(lean_object* v_id_1103_, lean_object* v_r_1104_){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___y_1108_; 
v___x_1105_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__0));
v___x_1106_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__1));
switch(lean_obj_tag(v_id_1103_))
{
case 0:
{
lean_object* v_s_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
v_s_1122_ = lean_ctor_get(v_id_1103_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_id_1103_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v_id_1103_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_s_1122_);
lean_dec(v_id_1103_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
lean_ctor_set_tag(v___x_1124_, 3);
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_s_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
v___y_1108_ = v___x_1127_;
goto v___jp_1107_;
}
}
}
case 1:
{
lean_object* v_n_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
v_n_1130_ = lean_ctor_get(v_id_1103_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_id_1103_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v_id_1103_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_n_1130_);
lean_dec(v_id_1103_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
lean_ctor_set_tag(v___x_1132_, 2);
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_n_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
v___y_1108_ = v___x_1135_;
goto v___jp_1107_;
}
}
}
default: 
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_box(0);
v___y_1108_ = v___x_1138_;
goto v___jp_1107_;
}
}
v___jp_1107_:
{
lean_object* v_serialized_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v_serialized_1109_ = lean_ctor_get(v_r_1104_, 1);
v___x_1110_ = l_Lean_Json_compress(v___y_1108_);
v___x_1111_ = lean_string_append(v___x_1106_, v___x_1110_);
lean_dec_ref(v___x_1110_);
v___x_1112_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__2));
v___x_1113_ = lean_string_append(v___x_1111_, v___x_1112_);
v___x_1114_ = lean_string_append(v___x_1105_, v___x_1113_);
lean_dec_ref(v___x_1113_);
v___x_1115_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__3));
v___x_1116_ = lean_string_append(v___x_1114_, v___x_1115_);
v___x_1117_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__4));
v___x_1118_ = lean_string_append(v___x_1117_, v_serialized_1109_);
v___x_1119_ = lean_string_append(v___x_1116_, v___x_1118_);
lean_dec_ref(v___x_1118_);
v___x_1120_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__5));
v___x_1121_ = lean_string_append(v___x_1119_, v___x_1120_);
return v___x_1121_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage___boxed(lean_object* v_id_1139_, lean_object* v_r_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_Server_SerializedLspResponse_toSerializedMessage(v_id_1139_, v_r_1140_);
lean_dec_ref(v_r_1140_);
return v_res_1141_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1142_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_);
v___x_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1146_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_);
v___x_1147_ = lean_st_mk_ref(v___x_1146_);
v___x_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2____boxed(lean_object* v_a_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_();
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__0(lean_object* v_inst_1151_, lean_object* v_inst_1152_, lean_object* v_j_1153_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lean_Server_parseRequestParams___redArg(v_inst_1151_, v_j_1153_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec_ref(v_inst_1152_);
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1171_; 
v_a_1163_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1165_ = v___x_1154_;
v_isShared_1166_ = v_isSharedCheck_1171_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1154_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1171_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1167_ = lean_apply_1(v_inst_1152_, v_a_1163_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v___x_1167_);
v___x_1169_ = v___x_1165_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__1(lean_object* v_serialize_x3f_1172_, uint8_t v_val_1173_, lean_object* v_inst_1174_, lean_object* v_r_1175_){
_start:
{
if (lean_obj_tag(v_serialize_x3f_1172_) == 1)
{
lean_object* v_val_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
lean_dec_ref(v_inst_1174_);
v_val_1176_ = lean_ctor_get(v_serialize_x3f_1172_, 0);
lean_inc(v_val_1176_);
lean_dec_ref_known(v_serialize_x3f_1172_, 1);
v___x_1177_ = lean_box(0);
v___x_1178_ = lean_apply_1(v_val_1176_, v_r_1175_);
v___x_1179_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1179_, 0, v___x_1177_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*2, v_val_1173_);
return v___x_1179_;
}
else
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_dec(v_serialize_x3f_1172_);
v___x_1180_ = lean_apply_1(v_inst_1174_, v_r_1175_);
lean_inc(v___x_1180_);
v___x_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
v___x_1182_ = l_Lean_Json_compress(v___x_1180_);
v___x_1183_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1183_, 0, v___x_1181_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*2, v_val_1173_);
return v___x_1183_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__1___boxed(lean_object* v_serialize_x3f_1184_, lean_object* v_val_1185_, lean_object* v_inst_1186_, lean_object* v_r_1187_){
_start:
{
uint8_t v_val_1362__boxed_1188_; lean_object* v_res_1189_; 
v_val_1362__boxed_1188_ = lean_unbox(v_val_1185_);
v_res_1189_ = l_Lean_Server_registerLspRequestHandler___redArg___lam__1(v_serialize_x3f_1184_, v_val_1362__boxed_1188_, v_inst_1186_, v_r_1187_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__2(lean_object* v_inst_1190_, lean_object* v_handler_1191_, lean_object* v___f_1192_, lean_object* v_j_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_1190_, v_j_1193_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; lean_object* v___x_1198_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_a_1197_);
lean_dec_ref_known(v___x_1196_, 1);
lean_inc_ref(v___y_1194_);
v___x_1198_ = lean_apply_3(v_handler_1191_, v_a_1197_, v___y_1194_, lean_box(0));
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1208_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1201_ = v___x_1198_;
v_isShared_1202_ = v_isSharedCheck_1208_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1208_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1203_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_1203_, 0, lean_box(0));
lean_closure_set(v___x_1203_, 1, lean_box(0));
lean_closure_set(v___x_1203_, 2, lean_box(0));
lean_closure_set(v___x_1203_, 3, v___f_1192_);
v___x_1204_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___x_1203_, v_a_1199_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1204_);
v___x_1206_ = v___x_1201_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec_ref(v___f_1192_);
v_a_1209_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1198_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1198_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_dec_ref(v___f_1192_);
lean_dec_ref(v_handler_1191_);
v_a_1217_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1196_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1196_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__2___boxed(lean_object* v_inst_1225_, lean_object* v_handler_1226_, lean_object* v___f_1227_, lean_object* v_j_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_Server_registerLspRequestHandler___redArg___lam__2(v_inst_1225_, v_handler_1226_, v___f_1227_, v_j_1228_, v___y_1229_);
lean_dec_ref(v___y_1229_);
return v_res_1231_;
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___f_1236_; 
v___x_1235_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___f_1236_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1236_, 0, v___x_1235_);
return v___f_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg(lean_object* v_method_1238_, lean_object* v_inst_1239_, lean_object* v_inst_1240_, lean_object* v_inst_1241_, lean_object* v_handler_1242_, lean_object* v_serialize_x3f_1243_){
_start:
{
lean_object* v___f_1245_; lean_object* v___x_1246_; uint8_t v___x_1247_; 
lean_inc_ref(v_inst_1239_);
v___f_1245_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1245_, 0, v_inst_1239_);
lean_closure_set(v___f_1245_, 1, v_inst_1240_);
v___x_1246_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__0));
v___x_1247_ = l_Lean_initializing();
if (v___x_1247_ == 0)
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_dec_ref(v___f_1245_);
lean_dec(v_serialize_x3f_1243_);
lean_dec_ref(v_handler_1242_);
lean_dec_ref(v_inst_1241_);
lean_dec_ref(v_inst_1239_);
v___x_1248_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__1));
v___x_1249_ = lean_string_append(v___x_1248_, v_method_1238_);
lean_dec_ref(v_method_1238_);
v___x_1250_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___x_1251_ = lean_string_append(v___x_1249_, v___x_1250_);
v___x_1252_ = lean_mk_io_user_error(v___x_1251_);
v___x_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
return v___x_1253_;
}
else
{
lean_object* v___x_1254_; lean_object* v___f_1255_; lean_object* v___f_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___f_1259_; uint8_t v___x_1260_; 
v___x_1254_ = lean_box(v___x_1247_);
v___f_1255_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1255_, 0, v_serialize_x3f_1243_);
lean_closure_set(v___f_1255_, 1, v___x_1254_);
lean_closure_set(v___f_1255_, 2, v_inst_1241_);
v___f_1256_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1256_, 0, v_inst_1239_);
lean_closure_set(v___f_1256_, 1, v_handler_1242_);
lean_closure_set(v___f_1256_, 2, v___f_1255_);
v___x_1257_ = l_Lean_Server_requestHandlers;
v___x_1258_ = lean_st_ref_get(v___x_1257_);
v___f_1259_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
lean_inc_ref(v_method_1238_);
v___x_1260_ = l_Lean_PersistentHashMap_contains___redArg(v___f_1259_, v___x_1246_, v___x_1258_, v_method_1238_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1261_ = lean_st_ref_take(v___x_1257_);
v___x_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___f_1245_);
lean_ctor_set(v___x_1262_, 1, v___f_1256_);
v___x_1263_ = l_Lean_PersistentHashMap_insert___redArg(v___f_1259_, v___x_1246_, v___x_1261_, v_method_1238_, v___x_1262_);
v___x_1264_ = lean_st_ref_put(v___x_1257_, v___x_1263_);
v___x_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
return v___x_1265_;
}
else
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec_ref(v___f_1256_);
lean_dec_ref(v___f_1245_);
v___x_1266_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__1));
v___x_1267_ = lean_string_append(v___x_1266_, v_method_1238_);
lean_dec_ref(v_method_1238_);
v___x_1268_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__4));
v___x_1269_ = lean_string_append(v___x_1267_, v___x_1268_);
v___x_1270_ = lean_mk_io_user_error(v___x_1269_);
v___x_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
return v___x_1271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___boxed(lean_object* v_method_1272_, lean_object* v_inst_1273_, lean_object* v_inst_1274_, lean_object* v_inst_1275_, lean_object* v_handler_1276_, lean_object* v_serialize_x3f_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_Server_registerLspRequestHandler___redArg(v_method_1272_, v_inst_1273_, v_inst_1274_, v_inst_1275_, v_handler_1276_, v_serialize_x3f_1277_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler(lean_object* v_method_1280_, lean_object* v_paramType_1281_, lean_object* v_inst_1282_, lean_object* v_inst_1283_, lean_object* v_respType_1284_, lean_object* v_inst_1285_, lean_object* v_handler_1286_, lean_object* v_serialize_x3f_1287_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_Lean_Server_registerLspRequestHandler___redArg(v_method_1280_, v_inst_1282_, v_inst_1283_, v_inst_1285_, v_handler_1286_, v_serialize_x3f_1287_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___boxed(lean_object* v_method_1290_, lean_object* v_paramType_1291_, lean_object* v_inst_1292_, lean_object* v_inst_1293_, lean_object* v_respType_1294_, lean_object* v_inst_1295_, lean_object* v_handler_1296_, lean_object* v_serialize_x3f_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_Server_registerLspRequestHandler(v_method_1290_, v_paramType_1291_, v_inst_1292_, v_inst_1293_, v_respType_1294_, v_inst_1295_, v_handler_1296_, v_serialize_x3f_1297_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1300_, lean_object* v_vals_1301_, lean_object* v_i_1302_, lean_object* v_k_1303_){
_start:
{
lean_object* v___x_1304_; uint8_t v___x_1305_; 
v___x_1304_ = lean_array_get_size(v_keys_1300_);
v___x_1305_ = lean_nat_dec_lt(v_i_1302_, v___x_1304_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; 
lean_dec(v_i_1302_);
v___x_1306_ = lean_box(0);
return v___x_1306_;
}
else
{
lean_object* v_k_x27_1307_; uint8_t v___x_1308_; 
v_k_x27_1307_ = lean_array_fget_borrowed(v_keys_1300_, v_i_1302_);
v___x_1308_ = lean_string_dec_eq(v_k_1303_, v_k_x27_1307_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_unsigned_to_nat(1u);
v___x_1310_ = lean_nat_add(v_i_1302_, v___x_1309_);
lean_dec(v_i_1302_);
v_i_1302_ = v___x_1310_;
goto _start;
}
else
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = lean_array_fget_borrowed(v_vals_1301_, v_i_1302_);
lean_dec(v_i_1302_);
lean_inc(v___x_1312_);
v___x_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
return v___x_1313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1314_, lean_object* v_vals_1315_, lean_object* v_i_1316_, lean_object* v_k_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(v_keys_1314_, v_vals_1315_, v_i_1316_, v_k_1317_);
lean_dec_ref(v_k_1317_);
lean_dec_ref(v_vals_1315_);
lean_dec_ref(v_keys_1314_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(lean_object* v_x_1319_, size_t v_x_1320_, lean_object* v_x_1321_){
_start:
{
if (lean_obj_tag(v_x_1319_) == 0)
{
lean_object* v_es_1322_; lean_object* v___x_1323_; size_t v___x_1324_; size_t v___x_1325_; lean_object* v_j_1326_; lean_object* v___x_1327_; 
v_es_1322_ = lean_ctor_get(v_x_1319_, 0);
v___x_1323_ = lean_box(2);
v___x_1324_ = ((size_t)31ULL);
v___x_1325_ = lean_usize_land(v_x_1320_, v___x_1324_);
v_j_1326_ = lean_usize_to_nat(v___x_1325_);
v___x_1327_ = lean_array_get_borrowed(v___x_1323_, v_es_1322_, v_j_1326_);
lean_dec(v_j_1326_);
switch(lean_obj_tag(v___x_1327_))
{
case 0:
{
lean_object* v_key_1328_; lean_object* v_val_1329_; uint8_t v___x_1330_; 
v_key_1328_ = lean_ctor_get(v___x_1327_, 0);
v_val_1329_ = lean_ctor_get(v___x_1327_, 1);
v___x_1330_ = lean_string_dec_eq(v_x_1321_, v_key_1328_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; 
v___x_1331_ = lean_box(0);
return v___x_1331_;
}
else
{
lean_object* v___x_1332_; 
lean_inc(v_val_1329_);
v___x_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1332_, 0, v_val_1329_);
return v___x_1332_;
}
}
case 1:
{
lean_object* v_node_1333_; size_t v___x_1334_; size_t v___x_1335_; 
v_node_1333_ = lean_ctor_get(v___x_1327_, 0);
v___x_1334_ = ((size_t)5ULL);
v___x_1335_ = lean_usize_shift_right(v_x_1320_, v___x_1334_);
v_x_1319_ = v_node_1333_;
v_x_1320_ = v___x_1335_;
goto _start;
}
default: 
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_box(0);
return v___x_1337_;
}
}
}
else
{
lean_object* v_ks_1338_; lean_object* v_vs_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v_ks_1338_ = lean_ctor_get(v_x_1319_, 0);
v_vs_1339_ = lean_ctor_get(v_x_1319_, 1);
v___x_1340_ = lean_unsigned_to_nat(0u);
v___x_1341_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(v_ks_1338_, v_vs_1339_, v___x_1340_, v_x_1321_);
return v___x_1341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___boxed(lean_object* v_x_1342_, lean_object* v_x_1343_, lean_object* v_x_1344_){
_start:
{
size_t v_x_277__boxed_1345_; lean_object* v_res_1346_; 
v_x_277__boxed_1345_ = lean_unbox_usize(v_x_1343_);
lean_dec(v_x_1343_);
v_res_1346_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_1342_, v_x_277__boxed_1345_, v_x_1344_);
lean_dec_ref(v_x_1344_);
lean_dec_ref(v_x_1342_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(lean_object* v_x_1347_, lean_object* v_x_1348_){
_start:
{
uint64_t v___x_1349_; size_t v___x_1350_; lean_object* v___x_1351_; 
v___x_1349_ = lean_string_hash(v_x_1348_);
v___x_1350_ = lean_uint64_to_usize(v___x_1349_);
v___x_1351_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_1347_, v___x_1350_, v_x_1348_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg___boxed(lean_object* v_x_1352_, lean_object* v_x_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v_x_1352_, v_x_1353_);
lean_dec_ref(v_x_1353_);
lean_dec_ref(v_x_1352_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupLspRequestHandler(lean_object* v_method_1355_){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1357_ = l_Lean_Server_requestHandlers;
v___x_1358_ = lean_st_ref_get(v___x_1357_);
v___x_1359_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v___x_1358_, v_method_1355_);
lean_dec(v___x_1358_);
v___x_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupLspRequestHandler___boxed(lean_object* v_method_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_Server_lookupLspRequestHandler(v_method_1361_);
lean_dec_ref(v_method_1361_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0(lean_object* v_00_u03b2_1364_, lean_object* v_x_1365_, lean_object* v_x_1366_){
_start:
{
lean_object* v___x_1367_; 
v___x_1367_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v_x_1365_, v_x_1366_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___boxed(lean_object* v_00_u03b2_1368_, lean_object* v_x_1369_, lean_object* v_x_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0(v_00_u03b2_1368_, v_x_1369_, v_x_1370_);
lean_dec_ref(v_x_1370_);
lean_dec_ref(v_x_1369_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0(lean_object* v_00_u03b2_1372_, lean_object* v_x_1373_, size_t v_x_1374_, lean_object* v_x_1375_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_1373_, v_x_1374_, v_x_1375_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1377_, lean_object* v_x_1378_, lean_object* v_x_1379_, lean_object* v_x_1380_){
_start:
{
size_t v_x_355__boxed_1381_; lean_object* v_res_1382_; 
v_x_355__boxed_1381_ = lean_unbox_usize(v_x_1379_);
lean_dec(v_x_1379_);
v_res_1382_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0(v_00_u03b2_1377_, v_x_1378_, v_x_355__boxed_1381_, v_x_1380_);
lean_dec_ref(v_x_1380_);
lean_dec_ref(v_x_1378_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1383_, lean_object* v_keys_1384_, lean_object* v_vals_1385_, lean_object* v_heq_1386_, lean_object* v_i_1387_, lean_object* v_k_1388_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(v_keys_1384_, v_vals_1385_, v_i_1387_, v_k_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1390_, lean_object* v_keys_1391_, lean_object* v_vals_1392_, lean_object* v_heq_1393_, lean_object* v_i_1394_, lean_object* v_k_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1(v_00_u03b2_1390_, v_keys_1391_, v_vals_1392_, v_heq_1393_, v_i_1394_, v_k_1395_);
lean_dec_ref(v_k_1395_);
lean_dec_ref(v_vals_1392_);
lean_dec_ref(v_keys_1391_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__0(lean_object* v_inst_1400_, lean_object* v_method_1401_, lean_object* v_x_1402_){
_start:
{
lean_object* v_response_1404_; 
if (lean_obj_tag(v_x_1402_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_dec_ref(v_inst_1400_);
v_a_1428_ = lean_ctor_get(v_x_1402_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v_x_1402_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v_x_1402_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v_x_1402_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v_response_x3f_1437_; 
v_a_1436_ = lean_ctor_get(v_x_1402_, 0);
lean_inc(v_a_1436_);
lean_dec_ref_known(v_x_1402_, 1);
v_response_x3f_1437_ = lean_ctor_get(v_a_1436_, 0);
if (lean_obj_tag(v_response_x3f_1437_) == 0)
{
lean_object* v_serialized_1438_; lean_object* v___x_1439_; 
v_serialized_1438_ = lean_ctor_get(v_a_1436_, 1);
lean_inc_ref(v_serialized_1438_);
lean_dec(v_a_1436_);
v___x_1439_ = l_Lean_Json_parse(v_serialized_1438_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1453_; 
lean_dec_ref(v_inst_1400_);
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1442_ = v___x_1439_;
v_isShared_1443_ = v_isSharedCheck_1453_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1439_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1453_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1444_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__2));
v___x_1445_ = lean_string_append(v___x_1444_, v_method_1401_);
v___x_1446_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1));
v___x_1447_ = lean_string_append(v___x_1445_, v___x_1446_);
v___x_1448_ = lean_string_append(v___x_1447_, v_a_1440_);
lean_dec(v_a_1440_);
v___x_1449_ = l_Lean_Server_RequestError_internalError(v___x_1448_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 0, v___x_1449_);
v___x_1451_ = v___x_1442_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
else
{
lean_object* v_a_1454_; 
v_a_1454_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1454_);
lean_dec_ref_known(v___x_1439_, 1);
v_response_1404_ = v_a_1454_;
goto v___jp_1403_;
}
}
else
{
lean_object* v_val_1455_; 
lean_inc_ref(v_response_x3f_1437_);
lean_dec(v_a_1436_);
v_val_1455_ = lean_ctor_get(v_response_x3f_1437_, 0);
lean_inc(v_val_1455_);
lean_dec_ref_known(v_response_x3f_1437_, 1);
v_response_1404_ = v_val_1455_;
goto v___jp_1403_;
}
}
v___jp_1403_:
{
lean_object* v___x_1405_; 
v___x_1405_ = lean_apply_1(v_inst_1400_, v_response_1404_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1419_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1419_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1419_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1417_; 
v___x_1410_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__0));
v___x_1411_ = lean_string_append(v___x_1410_, v_method_1401_);
v___x_1412_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1));
v___x_1413_ = lean_string_append(v___x_1411_, v___x_1412_);
v___x_1414_ = lean_string_append(v___x_1413_, v_a_1406_);
lean_dec(v_a_1406_);
v___x_1415_ = l_Lean_Server_RequestError_internalError(v___x_1414_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1415_);
v___x_1417_ = v___x_1408_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
v_a_1420_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1405_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1405_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__0___boxed(lean_object* v_inst_1456_, lean_object* v_method_1457_, lean_object* v_x_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__0(v_inst_1456_, v_method_1457_, v_x_1458_);
lean_dec_ref(v_method_1457_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__1(lean_object* v_inst_1460_, uint8_t v_val_1461_, lean_object* v_r_1462_){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1463_ = lean_apply_1(v_inst_1460_, v_r_1462_);
lean_inc(v___x_1463_);
v___x_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1463_);
v___x_1465_ = l_Lean_Json_compress(v___x_1463_);
v___x_1466_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1466_, 0, v___x_1464_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
lean_ctor_set_uint8(v___x_1466_, sizeof(void*)*2, v_val_1461_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__1___boxed(lean_object* v_inst_1467_, lean_object* v_val_1468_, lean_object* v_r_1469_){
_start:
{
uint8_t v_val_2282__boxed_1470_; lean_object* v_res_1471_; 
v_val_2282__boxed_1470_ = lean_unbox(v_val_1468_);
v_res_1471_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__1(v_inst_1467_, v_val_2282__boxed_1470_, v_r_1469_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__2(lean_object* v_val_1472_, lean_object* v___f_1473_, lean_object* v_inst_1474_, lean_object* v_handler_1475_, lean_object* v___f_1476_, lean_object* v_j_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_handle_1480_; lean_object* v___x_1481_; 
v_handle_1480_ = lean_ctor_get(v_val_1472_, 1);
lean_inc_ref(v_handle_1480_);
lean_dec_ref(v_val_1472_);
lean_inc_ref(v___y_1478_);
lean_inc(v_j_1477_);
v___x_1481_ = lean_apply_3(v_handle_1480_, v_j_1477_, v___y_1478_, lean_box(0));
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_a_1482_);
lean_dec_ref_known(v___x_1481_, 1);
v___x_1483_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_1473_, v_a_1482_);
v___x_1484_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_1474_, v_j_1477_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v___x_1486_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1485_);
lean_dec_ref_known(v___x_1484_, 1);
lean_inc_ref(v___y_1478_);
v___x_1486_ = lean_apply_4(v_handler_1475_, v_a_1485_, v___x_1483_, v___y_1478_, lean_box(0));
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1496_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1489_ = v___x_1486_;
v_isShared_1490_ = v_isSharedCheck_1496_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1486_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1496_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1494_; 
v___x_1491_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_1491_, 0, lean_box(0));
lean_closure_set(v___x_1491_, 1, lean_box(0));
lean_closure_set(v___x_1491_, 2, lean_box(0));
lean_closure_set(v___x_1491_, 3, v___f_1476_);
v___x_1492_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___x_1491_, v_a_1487_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 0, v___x_1492_);
v___x_1494_ = v___x_1489_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1492_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
lean_dec_ref(v___f_1476_);
v_a_1497_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1486_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1486_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_dec_ref(v___x_1483_);
lean_dec_ref(v___f_1476_);
lean_dec_ref(v_handler_1475_);
v_a_1505_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1484_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1484_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
else
{
lean_dec(v_j_1477_);
lean_dec_ref(v___f_1476_);
lean_dec_ref(v_handler_1475_);
lean_dec_ref(v_inst_1474_);
lean_dec_ref(v___f_1473_);
return v___x_1481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__2___boxed(lean_object* v_val_1513_, lean_object* v___f_1514_, lean_object* v_inst_1515_, lean_object* v_handler_1516_, lean_object* v___f_1517_, lean_object* v_j_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__2(v_val_1513_, v___f_1514_, v_inst_1515_, v_handler_1516_, v___f_1517_, v_j_1518_, v___y_1519_);
lean_dec_ref(v___y_1519_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg(lean_object* v_method_1524_, lean_object* v_inst_1525_, lean_object* v_inst_1526_, lean_object* v_inst_1527_, lean_object* v_handler_1528_){
_start:
{
lean_object* v___f_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; 
lean_inc_ref(v_method_1524_);
v___f_1530_ = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1530_, 0, v_inst_1526_);
lean_closure_set(v___f_1530_, 1, v_method_1524_);
v___x_1531_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__0));
v___x_1532_ = l_Lean_initializing();
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
lean_dec_ref(v___f_1530_);
lean_dec_ref(v_handler_1528_);
lean_dec_ref(v_inst_1527_);
lean_dec_ref(v_inst_1525_);
v___x_1533_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__0));
v___x_1534_ = lean_string_append(v___x_1533_, v_method_1524_);
lean_dec_ref(v_method_1524_);
v___x_1535_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___x_1536_ = lean_string_append(v___x_1534_, v___x_1535_);
v___x_1537_ = lean_mk_io_user_error(v___x_1536_);
v___x_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
return v___x_1538_;
}
else
{
lean_object* v___x_1539_; lean_object* v___f_1540_; lean_object* v___x_1541_; lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1573_; 
v___x_1539_ = lean_box(v___x_1532_);
v___f_1540_ = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_1540_, 0, v_inst_1527_);
lean_closure_set(v___f_1540_, 1, v___x_1539_);
v___x_1541_ = l_Lean_Server_lookupLspRequestHandler(v_method_1524_);
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1544_ = v___x_1541_;
v_isShared_1545_ = v_isSharedCheck_1573_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1541_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1573_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
if (lean_obj_tag(v_a_1542_) == 1)
{
lean_object* v_val_1546_; lean_object* v___f_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v_fileSource_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1563_; 
v_val_1546_ = lean_ctor_get(v_a_1542_, 0);
lean_inc_n(v_val_1546_, 2);
lean_dec_ref_known(v_a_1542_, 1);
v___f_1547_ = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_1547_, 0, v_val_1546_);
lean_closure_set(v___f_1547_, 1, v___f_1530_);
lean_closure_set(v___f_1547_, 2, v_inst_1525_);
lean_closure_set(v___f_1547_, 3, v_handler_1528_);
lean_closure_set(v___f_1547_, 4, v___f_1540_);
v___x_1548_ = l_Lean_Server_requestHandlers;
v___x_1549_ = lean_st_ref_take(v___x_1548_);
v_fileSource_1550_ = lean_ctor_get(v_val_1546_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v_val_1546_);
if (v_isSharedCheck_1563_ == 0)
{
lean_object* v_unused_1564_; 
v_unused_1564_ = lean_ctor_get(v_val_1546_, 1);
lean_dec(v_unused_1564_);
v___x_1552_ = v_val_1546_;
v_isShared_1553_ = v_isSharedCheck_1563_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_fileSource_1550_);
lean_dec(v_val_1546_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1563_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___f_1554_; lean_object* v___x_1556_; 
v___f_1554_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 1, v___f_1547_);
v___x_1556_ = v___x_1552_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_fileSource_1550_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v___f_1547_);
v___x_1556_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1560_; 
v___x_1557_ = l_Lean_PersistentHashMap_insert___redArg(v___f_1554_, v___x_1531_, v___x_1549_, v_method_1524_, v___x_1556_);
v___x_1558_ = lean_st_ref_put(v___x_1548_, v___x_1557_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 0, v___x_1558_);
v___x_1560_ = v___x_1544_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1558_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
else
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1571_; 
lean_dec(v_a_1542_);
lean_dec_ref(v___f_1540_);
lean_dec_ref(v___f_1530_);
lean_dec_ref(v_handler_1528_);
lean_dec_ref(v_inst_1525_);
v___x_1565_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__0));
v___x_1566_ = lean_string_append(v___x_1565_, v_method_1524_);
lean_dec_ref(v_method_1524_);
v___x_1567_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__1));
v___x_1568_ = lean_string_append(v___x_1566_, v___x_1567_);
v___x_1569_ = lean_mk_io_user_error(v___x_1568_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set_tag(v___x_1544_, 1);
lean_ctor_set(v___x_1544_, 0, v___x_1569_);
v___x_1571_ = v___x_1544_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1569_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___boxed(lean_object* v_method_1574_, lean_object* v_inst_1575_, lean_object* v_inst_1576_, lean_object* v_inst_1577_, lean_object* v_handler_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lean_Server_chainLspRequestHandler___redArg(v_method_1574_, v_inst_1575_, v_inst_1576_, v_inst_1577_, v_handler_1578_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler(lean_object* v_method_1581_, lean_object* v_paramType_1582_, lean_object* v_inst_1583_, lean_object* v_respType_1584_, lean_object* v_inst_1585_, lean_object* v_inst_1586_, lean_object* v_handler_1587_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_Server_chainLspRequestHandler___redArg(v_method_1581_, v_inst_1583_, v_inst_1585_, v_inst_1586_, v_handler_1587_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___boxed(lean_object* v_method_1590_, lean_object* v_paramType_1591_, lean_object* v_inst_1592_, lean_object* v_respType_1593_, lean_object* v_inst_1594_, lean_object* v_inst_1595_, lean_object* v_handler_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_Server_chainLspRequestHandler(v_method_1590_, v_paramType_1591_, v_inst_1592_, v_respType_1593_, v_inst_1594_, v_inst_1595_, v_handler_1596_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorIdx(lean_object* v_x_1599_){
_start:
{
if (lean_obj_tag(v_x_1599_) == 0)
{
lean_object* v___x_1600_; 
v___x_1600_ = lean_unsigned_to_nat(0u);
return v___x_1600_;
}
else
{
lean_object* v___x_1601_; 
v___x_1601_ = lean_unsigned_to_nat(1u);
return v___x_1601_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorIdx___boxed(lean_object* v_x_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Lean_Server_RequestHandlerCompleteness_ctorIdx(v_x_1602_);
lean_dec(v_x_1602_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(lean_object* v_t_1604_, lean_object* v_k_1605_){
_start:
{
if (lean_obj_tag(v_t_1604_) == 0)
{
return v_k_1605_;
}
else
{
lean_object* v_refreshMethod_1606_; lean_object* v_refreshIntervalMs_1607_; lean_object* v___x_1608_; 
v_refreshMethod_1606_ = lean_ctor_get(v_t_1604_, 0);
lean_inc_ref(v_refreshMethod_1606_);
v_refreshIntervalMs_1607_ = lean_ctor_get(v_t_1604_, 1);
lean_inc(v_refreshIntervalMs_1607_);
lean_dec_ref_known(v_t_1604_, 2);
v___x_1608_ = lean_apply_2(v_k_1605_, v_refreshMethod_1606_, v_refreshIntervalMs_1607_);
return v___x_1608_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim(lean_object* v_motive_1609_, lean_object* v_ctorIdx_1610_, lean_object* v_t_1611_, lean_object* v_h_1612_, lean_object* v_k_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_1611_, v_k_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim___boxed(lean_object* v_motive_1615_, lean_object* v_ctorIdx_1616_, lean_object* v_t_1617_, lean_object* v_h_1618_, lean_object* v_k_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim(v_motive_1615_, v_ctorIdx_1616_, v_t_1617_, v_h_1618_, v_k_1619_);
lean_dec(v_ctorIdx_1616_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_complete_elim___redArg(lean_object* v_t_1621_, lean_object* v_complete_1622_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_1621_, v_complete_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_complete_elim(lean_object* v_motive_1624_, lean_object* v_t_1625_, lean_object* v_h_1626_, lean_object* v_complete_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_1625_, v_complete_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_partial_elim___redArg(lean_object* v_t_1629_, lean_object* v_partial_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_1629_, v_partial_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_partial_elim(lean_object* v_motive_1632_, lean_object* v_t_1633_, lean_object* v_h_1634_, lean_object* v_partial_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_1633_, v_partial_1635_);
return v___x_1636_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_);
v___x_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1640_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_);
v___x_1641_ = lean_st_mk_ref(v___x_1640_);
v___x_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2____boxed(lean_object* v_a_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_();
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(lean_object* v_method_1646_, lean_object* v_state_1647_, lean_object* v_inst_1648_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_state_1647_, v_inst_1648_);
if (lean_obj_tag(v___x_1650_) == 1)
{
lean_object* v_val_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
v_val_1651_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1650_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_val_1651_);
lean_dec(v___x_1650_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
lean_ctor_set_tag(v___x_1653_, 0);
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_val_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
else
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
lean_dec(v___x_1650_);
v___x_1659_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0));
v___x_1660_ = lean_string_append(v___x_1659_, v_method_1646_);
v___x_1661_ = l_Lean_Server_RequestError_internalError(v___x_1660_);
v___x_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
return v___x_1662_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___boxed(lean_object* v_method_1663_, lean_object* v_state_1664_, lean_object* v_inst_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_1663_, v_state_1664_, v_inst_1665_);
lean_dec(v_inst_1665_);
lean_dec(v_state_1664_);
lean_dec_ref(v_method_1663_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(lean_object* v_method_1668_, lean_object* v_state_1669_, lean_object* v_stateType_1670_, lean_object* v_inst_1671_, lean_object* v_a_1672_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_1668_, v_state_1669_, v_inst_1671_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___boxed(lean_object* v_method_1675_, lean_object* v_state_1676_, lean_object* v_stateType_1677_, lean_object* v_inst_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_1675_, v_state_1676_, v_stateType_1677_, v_inst_1678_, v_a_1679_);
lean_dec_ref(v_a_1679_);
lean_dec(v_inst_1678_);
lean_dec(v_state_1676_);
lean_dec_ref(v_method_1675_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(lean_object* v_method_1682_, lean_object* v_state_1683_, lean_object* v_inst_1684_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_state_1683_, v_inst_1684_);
if (lean_obj_tag(v___x_1686_) == 1)
{
lean_object* v_val_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
v_val_1687_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1686_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_val_1687_);
lean_dec(v___x_1686_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
lean_ctor_set_tag(v___x_1689_, 0);
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_val_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
else
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
lean_dec(v___x_1686_);
v___x_1695_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0));
v___x_1696_ = lean_string_append(v___x_1695_, v_method_1682_);
v___x_1697_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
v___x_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1697_);
return v___x_1698_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg___boxed(lean_object* v_method_1699_, lean_object* v_state_1700_, lean_object* v_inst_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(v_method_1699_, v_state_1700_, v_inst_1701_);
lean_dec(v_inst_1701_);
lean_dec(v_state_1700_);
lean_dec_ref(v_method_1699_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21(lean_object* v_method_1704_, lean_object* v_state_1705_, lean_object* v_stateType_1706_, lean_object* v_inst_1707_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(v_method_1704_, v_state_1705_, v_inst_1707_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___boxed(lean_object* v_method_1710_, lean_object* v_state_1711_, lean_object* v_stateType_1712_, lean_object* v_inst_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21(v_method_1710_, v_state_1711_, v_stateType_1712_, v_inst_1713_);
lean_dec(v_inst_1713_);
lean_dec(v_state_1711_);
lean_dec_ref(v_method_1710_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1(lean_object* v_inst_1716_, lean_object* v_method_1717_, lean_object* v_inst_1718_, lean_object* v_handler_1719_, lean_object* v_inst_1720_, lean_object* v_param_1721_, lean_object* v_state_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_1716_, v_param_1721_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1727_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1725_, 1);
v___x_1727_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_1717_, v_state_1722_, v_inst_1718_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1729_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1728_);
lean_dec_ref_known(v___x_1727_, 1);
lean_inc_ref(v___y_1723_);
v___x_1729_ = lean_apply_4(v_handler_1719_, v_a_1726_, v_a_1728_, v___y_1723_, lean_box(0));
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1753_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1732_ = v___x_1729_;
v_isShared_1733_ = v_isSharedCheck_1753_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1729_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1753_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v_fst_1734_; lean_object* v_snd_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1752_; 
v_fst_1734_ = lean_ctor_get(v_a_1730_, 0);
v_snd_1735_ = lean_ctor_get(v_a_1730_, 1);
v_isSharedCheck_1752_ = !lean_is_exclusive(v_a_1730_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1737_ = v_a_1730_;
v_isShared_1738_ = v_isSharedCheck_1752_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_snd_1735_);
lean_inc(v_fst_1734_);
lean_dec(v_a_1730_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1752_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v_response_1739_; uint8_t v_isComplete_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1746_; 
v_response_1739_ = lean_ctor_get(v_fst_1734_, 0);
lean_inc(v_response_1739_);
v_isComplete_1740_ = lean_ctor_get_uint8(v_fst_1734_, sizeof(void*)*1);
lean_dec(v_fst_1734_);
v___x_1741_ = lean_apply_1(v_inst_1720_, v_response_1739_);
lean_inc(v___x_1741_);
v___x_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
v___x_1743_ = l_Lean_Json_compress(v___x_1741_);
v___x_1744_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1744_, 0, v___x_1742_);
lean_ctor_set(v___x_1744_, 1, v___x_1743_);
lean_ctor_set_uint8(v___x_1744_, sizeof(void*)*2, v_isComplete_1740_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 0, v_inst_1718_);
v___x_1746_ = v___x_1737_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_inst_1718_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v_snd_1735_);
v___x_1746_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
lean_object* v___x_1747_; lean_object* v___x_1749_; 
v___x_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1744_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 0, v___x_1747_);
v___x_1749_ = v___x_1732_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec_ref(v_inst_1720_);
lean_dec(v_inst_1718_);
v_a_1754_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1729_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1729_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec(v_a_1726_);
lean_dec_ref(v_inst_1720_);
lean_dec_ref(v_handler_1719_);
lean_dec(v_inst_1718_);
v_a_1762_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1727_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1727_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_dec_ref(v_inst_1720_);
lean_dec_ref(v_handler_1719_);
lean_dec(v_inst_1718_);
v_a_1770_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1725_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1725_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1___boxed(lean_object* v_inst_1778_, lean_object* v_method_1779_, lean_object* v_inst_1780_, lean_object* v_handler_1781_, lean_object* v_inst_1782_, lean_object* v_param_1783_, lean_object* v_state_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1(v_inst_1778_, v_method_1779_, v_inst_1780_, v_handler_1781_, v_inst_1782_, v_param_1783_, v_state_1784_, v___y_1785_);
lean_dec_ref(v___y_1785_);
lean_dec(v_state_1784_);
lean_dec_ref(v_method_1779_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0(lean_object* v_method_1788_, lean_object* v_inst_1789_, lean_object* v_onDidChange_1790_, lean_object* v_param_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_1788_, v___y_1792_, v_inst_1789_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; lean_object* v___x_1797_; 
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
lean_inc(v_a_1796_);
lean_dec_ref_known(v___x_1795_, 1);
lean_inc_ref(v___y_1793_);
v___x_1797_ = lean_apply_4(v_onDidChange_1790_, v_param_1791_, v_a_1796_, v___y_1793_, lean_box(0));
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1816_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1816_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1816_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v_snd_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1814_; 
v_snd_1802_ = lean_ctor_get(v_a_1798_, 1);
v_isSharedCheck_1814_ = !lean_is_exclusive(v_a_1798_);
if (v_isSharedCheck_1814_ == 0)
{
lean_object* v_unused_1815_; 
v_unused_1815_ = lean_ctor_get(v_a_1798_, 0);
lean_dec(v_unused_1815_);
v___x_1804_ = v_a_1798_;
v_isShared_1805_ = v_isSharedCheck_1814_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_snd_1802_);
lean_dec(v_a_1798_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1814_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v_inst_1789_);
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_inst_1789_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v_snd_1802_);
v___x_1807_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1811_; 
v___x_1808_ = lean_box(0);
v___x_1809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
lean_ctor_set(v___x_1809_, 1, v___x_1807_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1809_);
v___x_1811_ = v___x_1800_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
lean_dec(v_inst_1789_);
v_a_1817_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1797_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1797_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
lean_dec_ref(v_param_1791_);
lean_dec_ref(v_onDidChange_1790_);
lean_dec(v_inst_1789_);
v_a_1825_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1795_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1795_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object* v_method_1833_, lean_object* v_inst_1834_, lean_object* v_onDidChange_1835_, lean_object* v_param_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0(v_method_1833_, v_inst_1834_, v_onDidChange_1835_, v_param_1836_, v___y_1837_, v___y_1838_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v_method_1833_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2(lean_object* v___x_1841_, lean_object* v_x_1842_){
_start:
{
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2___boxed(lean_object* v___x_1843_, lean_object* v_x_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2(v___x_1843_, v_x_1844_);
lean_dec_ref(v_x_1844_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3(lean_object* v___x_1846_, lean_object* v_x_1847_){
_start:
{
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3___boxed(lean_object* v___x_1848_, lean_object* v_x_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3(v___x_1848_, v_x_1849_);
lean_dec_ref(v_x_1849_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4(lean_object* v_val_1851_, lean_object* v___f_1852_, lean_object* v_param_1853_, lean_object* v_x_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = lean_st_ref_get(v_val_1851_);
lean_inc_ref(v___y_1855_);
v___x_1858_ = lean_apply_4(v___f_1852_, v_param_1853_, v___x_1857_, v___y_1855_, lean_box(0));
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1869_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1861_ = v___x_1858_;
v_isShared_1862_ = v_isSharedCheck_1869_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1858_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1869_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v_fst_1863_; lean_object* v_snd_1864_; lean_object* v___x_1865_; lean_object* v___x_1867_; 
v_fst_1863_ = lean_ctor_get(v_a_1859_, 0);
lean_inc(v_fst_1863_);
v_snd_1864_ = lean_ctor_get(v_a_1859_, 1);
lean_inc(v_snd_1864_);
lean_dec(v_a_1859_);
v___x_1865_ = lean_st_ref_swap(v_val_1851_, v_snd_1864_);
lean_dec(v___x_1865_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v_fst_1863_);
v___x_1867_ = v___x_1861_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_fst_1863_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
v_a_1870_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1858_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1858_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4___boxed(lean_object* v_val_1878_, lean_object* v___f_1879_, lean_object* v_param_1880_, lean_object* v_x_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4(v_val_1878_, v___f_1879_, v_param_1880_, v_x_1881_, v___y_1882_);
lean_dec_ref(v___y_1882_);
lean_dec(v_val_1878_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5(lean_object* v___f_1885_, lean_object* v___f_1886_, lean_object* v_lastTask_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v___x_1891_; lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1901_; 
v___x_1891_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_lastTask_1887_, v___f_1885_, v___y_1889_);
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1894_ = v___x_1891_;
v_isShared_1895_ = v_isSharedCheck_1901_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1891_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1901_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1899_; 
lean_inc(v_a_1892_);
v___x_1896_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_1886_, v_a_1892_);
v___x_1897_ = lean_st_ref_swap(v___y_1888_, v___x_1896_);
lean_dec(v___x_1897_);
if (v_isShared_1895_ == 0)
{
v___x_1899_ = v___x_1894_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1892_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5___boxed(lean_object* v___f_1902_, lean_object* v___f_1903_, lean_object* v_lastTask_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5(v___f_1902_, v___f_1903_, v_lastTask_1904_, v___y_1905_, v___y_1906_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6(lean_object* v_val_1909_, lean_object* v___f_1910_, lean_object* v___f_1911_, lean_object* v___f_1912_, lean_object* v___x_1913_, lean_object* v___f_1914_, lean_object* v___f_1915_, lean_object* v_val_1916_, lean_object* v_param_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v___f_1920_; lean_object* v___f_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_6224__overap_1924_; lean_object* v___x_1925_; 
v___f_1920_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_1920_, 0, v_val_1909_);
lean_closure_set(v___f_1920_, 1, v___f_1910_);
lean_closure_set(v___f_1920_, 2, v_param_1917_);
v___f_1921_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5___boxed), 6, 2);
lean_closure_set(v___f_1921_, 0, v___f_1920_);
lean_closure_set(v___f_1921_, 1, v___f_1911_);
v___x_1922_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_1922_, 0, lean_box(0));
lean_closure_set(v___x_1922_, 1, lean_box(0));
lean_closure_set(v___x_1922_, 2, lean_box(0));
lean_closure_set(v___x_1922_, 3, v___f_1912_);
lean_inc_ref(v___x_1913_);
v___x_1923_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_1923_, 0, lean_box(0));
lean_closure_set(v___x_1923_, 1, lean_box(0));
lean_closure_set(v___x_1923_, 2, v___x_1913_);
lean_closure_set(v___x_1923_, 3, lean_box(0));
lean_closure_set(v___x_1923_, 4, lean_box(0));
lean_closure_set(v___x_1923_, 5, v___x_1922_);
lean_closure_set(v___x_1923_, 6, v___f_1921_);
v___x_6224__overap_1924_ = l_Std_Mutex_atomically___redArg(v___x_1913_, v___f_1914_, v___f_1915_, v_val_1916_, v___x_1923_);
lean_inc_ref(v___y_1918_);
v___x_1925_ = lean_apply_2(v___x_6224__overap_1924_, v___y_1918_, lean_box(0));
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6___boxed(lean_object* v_val_1926_, lean_object* v___f_1927_, lean_object* v___f_1928_, lean_object* v___f_1929_, lean_object* v___x_1930_, lean_object* v___f_1931_, lean_object* v___f_1932_, lean_object* v_val_1933_, lean_object* v_param_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6(v_val_1926_, v___f_1927_, v___f_1928_, v___f_1929_, v___x_1930_, v___f_1931_, v___f_1932_, v_val_1933_, v_param_1934_, v___y_1935_);
lean_dec_ref(v___y_1935_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7(lean_object* v_val_1938_, lean_object* v___f_1939_, lean_object* v_param_1940_, lean_object* v___x_1941_, lean_object* v_x_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = lean_st_ref_get(v_val_1938_);
lean_inc_ref(v___y_1943_);
v___x_1946_ = lean_apply_4(v___f_1939_, v_param_1940_, v___x_1945_, v___y_1943_, lean_box(0));
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1956_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1949_ = v___x_1946_;
v_isShared_1950_ = v_isSharedCheck_1956_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1946_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1956_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v_snd_1951_; lean_object* v___x_1952_; lean_object* v___x_1954_; 
v_snd_1951_ = lean_ctor_get(v_a_1947_, 1);
lean_inc(v_snd_1951_);
lean_dec(v_a_1947_);
v___x_1952_ = lean_st_ref_swap(v_val_1938_, v_snd_1951_);
lean_dec(v___x_1952_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 0, v___x_1941_);
v___x_1954_ = v___x_1949_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1941_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
v_a_1957_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1946_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1946_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7___boxed(lean_object* v_val_1965_, lean_object* v___f_1966_, lean_object* v_param_1967_, lean_object* v___x_1968_, lean_object* v_x_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7(v_val_1965_, v___f_1966_, v_param_1967_, v___x_1968_, v_x_1969_, v___y_1970_);
lean_dec_ref(v___y_1970_);
lean_dec(v_val_1965_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8(lean_object* v___f_1973_, lean_object* v___f_1974_, lean_object* v___x_1975_, lean_object* v_lastTask_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v___x_1980_; lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1990_; 
v___x_1980_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_lastTask_1976_, v___f_1973_, v___y_1978_);
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1983_ = v___x_1980_;
v_isShared_1984_ = v_isSharedCheck_1990_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1980_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1990_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1988_; 
v___x_1985_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_1974_, v_a_1981_);
v___x_1986_ = lean_st_ref_swap(v___y_1977_, v___x_1985_);
lean_dec(v___x_1986_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_1975_);
v___x_1988_ = v___x_1983_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1975_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8___boxed(lean_object* v___f_1991_, lean_object* v___f_1992_, lean_object* v___x_1993_, lean_object* v_lastTask_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8(v___f_1991_, v___f_1992_, v___x_1993_, v_lastTask_1994_, v___y_1995_, v___y_1996_);
lean_dec_ref(v___y_1996_);
lean_dec(v___y_1995_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9(lean_object* v_val_1999_, lean_object* v___f_2000_, lean_object* v___x_2001_, lean_object* v___f_2002_, lean_object* v___f_2003_, lean_object* v___x_2004_, lean_object* v___f_2005_, lean_object* v___f_2006_, lean_object* v_val_2007_, lean_object* v_param_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v___f_2011_; lean_object* v___f_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_6278__overap_2015_; lean_object* v___x_2016_; 
v___f_2011_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_2011_, 0, v_val_1999_);
lean_closure_set(v___f_2011_, 1, v___f_2000_);
lean_closure_set(v___f_2011_, 2, v_param_2008_);
lean_closure_set(v___f_2011_, 3, v___x_2001_);
v___f_2012_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8___boxed), 7, 3);
lean_closure_set(v___f_2012_, 0, v___f_2011_);
lean_closure_set(v___f_2012_, 1, v___f_2002_);
lean_closure_set(v___f_2012_, 2, v___x_2001_);
v___x_2013_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_2013_, 0, lean_box(0));
lean_closure_set(v___x_2013_, 1, lean_box(0));
lean_closure_set(v___x_2013_, 2, lean_box(0));
lean_closure_set(v___x_2013_, 3, v___f_2003_);
lean_inc_ref(v___x_2004_);
v___x_2014_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2014_, 0, lean_box(0));
lean_closure_set(v___x_2014_, 1, lean_box(0));
lean_closure_set(v___x_2014_, 2, v___x_2004_);
lean_closure_set(v___x_2014_, 3, lean_box(0));
lean_closure_set(v___x_2014_, 4, lean_box(0));
lean_closure_set(v___x_2014_, 5, v___x_2013_);
lean_closure_set(v___x_2014_, 6, v___f_2012_);
v___x_6278__overap_2015_ = l_Std_Mutex_atomically___redArg(v___x_2004_, v___f_2005_, v___f_2006_, v_val_2007_, v___x_2014_);
lean_inc_ref(v___y_2009_);
v___x_2016_ = lean_apply_2(v___x_6278__overap_2015_, v___y_2009_, lean_box(0));
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9___boxed(lean_object* v_val_2017_, lean_object* v___f_2018_, lean_object* v___x_2019_, lean_object* v___f_2020_, lean_object* v___f_2021_, lean_object* v___x_2022_, lean_object* v___f_2023_, lean_object* v___f_2024_, lean_object* v_val_2025_, lean_object* v_param_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9(v_val_2017_, v___f_2018_, v___x_2019_, v___f_2020_, v___f_2021_, v___x_2022_, v___f_2023_, v___f_2024_, v_val_2025_, v_param_2026_, v___y_2027_);
lean_dec_ref(v___y_2027_);
return v_res_2029_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1(void){
_start:
{
lean_object* v___x_2031_; 
v___x_2031_ = l_instMonadEIO___redArg();
return v___x_2031_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2(void){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1);
v___x_2033_ = l_ReaderT_instMonad___redArg(v___x_2032_);
return v___x_2033_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15(void){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = lean_box(0);
v___x_2060_ = lean_task_pure(v___x_2059_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(lean_object* v_method_2061_, lean_object* v_completeness_2062_, lean_object* v_inst_2063_, lean_object* v_inst_2064_, lean_object* v_inst_2065_, lean_object* v_inst_2066_, lean_object* v_initState_2067_, lean_object* v_handler_2068_, lean_object* v_onDidChange_2069_){
_start:
{
lean_object* v___f_2071_; lean_object* v___f_2072_; lean_object* v___f_2073_; lean_object* v___x_2074_; lean_object* v___f_2075_; lean_object* v___f_2076_; lean_object* v___f_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; 
lean_inc_ref(v_inst_2063_);
v___f_2071_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2071_, 0, v_inst_2063_);
lean_closure_set(v___f_2071_, 1, v_inst_2064_);
lean_inc_n(v_inst_2066_, 2);
lean_inc_ref_n(v_method_2061_, 2);
v___f_2072_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1___boxed), 9, 5);
lean_closure_set(v___f_2072_, 0, v_inst_2063_);
lean_closure_set(v___f_2072_, 1, v_method_2061_);
lean_closure_set(v___f_2072_, 2, v_inst_2066_);
lean_closure_set(v___f_2072_, 3, v_handler_2068_);
lean_closure_set(v___f_2072_, 4, v_inst_2065_);
v___f_2073_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0___boxed), 7, 3);
lean_closure_set(v___f_2073_, 0, v_method_2061_);
lean_closure_set(v___f_2073_, 1, v_inst_2066_);
lean_closure_set(v___f_2073_, 2, v_onDidChange_2069_);
v___x_2074_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2);
v___f_2075_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__5));
v___f_2076_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__7));
v___f_2077_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__11));
v___x_2078_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__0));
v___x_2079_ = l_Lean_initializing();
if (v___x_2079_ == 0)
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
lean_dec_ref(v___f_2073_);
lean_dec_ref(v___f_2072_);
lean_dec_ref(v___f_2071_);
lean_dec(v_initState_2067_);
lean_dec(v_inst_2066_);
lean_dec(v_completeness_2062_);
v___x_2080_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__12));
v___x_2081_ = lean_string_append(v___x_2080_, v_method_2061_);
lean_dec_ref(v_method_2061_);
v___x_2082_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___x_2083_ = lean_string_append(v___x_2081_, v___x_2082_);
v___x_2084_ = lean_mk_io_user_error(v___x_2083_);
v___x_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
return v___x_2085_;
}
else
{
lean_object* v___x_2086_; lean_object* v___f_2087_; lean_object* v___f_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___f_2093_; lean_object* v___f_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___f_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2086_ = lean_box(0);
v___f_2087_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__13));
v___f_2088_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__14));
v___x_2089_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15);
v___x_2090_ = l_Std_Mutex_new___redArg(v___x_2089_);
v___x_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2091_, 0, v_inst_2066_);
lean_ctor_set(v___x_2091_, 1, v_initState_2067_);
lean_inc_ref(v___x_2091_);
v___x_2092_ = lean_st_mk_ref(v___x_2091_);
lean_inc_ref_n(v___x_2090_, 2);
lean_inc_ref(v___f_2072_);
lean_inc_n(v___x_2092_, 2);
v___f_2093_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6___boxed), 11, 8);
lean_closure_set(v___f_2093_, 0, v___x_2092_);
lean_closure_set(v___f_2093_, 1, v___f_2072_);
lean_closure_set(v___f_2093_, 2, v___f_2087_);
lean_closure_set(v___f_2093_, 3, v___f_2077_);
lean_closure_set(v___f_2093_, 4, v___x_2074_);
lean_closure_set(v___f_2093_, 5, v___f_2075_);
lean_closure_set(v___f_2093_, 6, v___f_2076_);
lean_closure_set(v___f_2093_, 7, v___x_2090_);
lean_inc_ref(v___f_2073_);
v___f_2094_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9___boxed), 12, 9);
lean_closure_set(v___f_2094_, 0, v___x_2092_);
lean_closure_set(v___f_2094_, 1, v___f_2073_);
lean_closure_set(v___f_2094_, 2, v___x_2086_);
lean_closure_set(v___f_2094_, 3, v___f_2088_);
lean_closure_set(v___f_2094_, 4, v___f_2077_);
lean_closure_set(v___f_2094_, 5, v___x_2074_);
lean_closure_set(v___f_2094_, 6, v___f_2075_);
lean_closure_set(v___f_2094_, 7, v___f_2076_);
lean_closure_set(v___f_2094_, 8, v___x_2090_);
v___x_2095_ = l_Lean_Server_statefulRequestHandlers;
v___x_2096_ = lean_st_ref_take(v___x_2095_);
v___f_2097_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
v___x_2098_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2098_, 0, v___f_2071_);
lean_ctor_set(v___x_2098_, 1, v___f_2072_);
lean_ctor_set(v___x_2098_, 2, v___f_2093_);
lean_ctor_set(v___x_2098_, 3, v___f_2073_);
lean_ctor_set(v___x_2098_, 4, v___f_2094_);
lean_ctor_set(v___x_2098_, 5, v___x_2090_);
lean_ctor_set(v___x_2098_, 6, v___x_2091_);
lean_ctor_set(v___x_2098_, 7, v___x_2092_);
lean_ctor_set(v___x_2098_, 8, v_completeness_2062_);
v___x_2099_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2097_, v___x_2078_, v___x_2096_, v_method_2061_, v___x_2098_);
v___x_2100_ = lean_st_ref_put(v___x_2095_, v___x_2099_);
v___x_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
return v___x_2101_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2102_, lean_object* v_completeness_2103_, lean_object* v_inst_2104_, lean_object* v_inst_2105_, lean_object* v_inst_2106_, lean_object* v_inst_2107_, lean_object* v_initState_2108_, lean_object* v_handler_2109_, lean_object* v_onDidChange_2110_, lean_object* v_a_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2102_, v_completeness_2103_, v_inst_2104_, v_inst_2105_, v_inst_2106_, v_inst_2107_, v_initState_2108_, v_handler_2109_, v_onDidChange_2110_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(lean_object* v_method_2113_, lean_object* v_completeness_2114_, lean_object* v_paramType_2115_, lean_object* v_inst_2116_, lean_object* v_inst_2117_, lean_object* v_respType_2118_, lean_object* v_inst_2119_, lean_object* v_stateType_2120_, lean_object* v_inst_2121_, lean_object* v_initState_2122_, lean_object* v_handler_2123_, lean_object* v_onDidChange_2124_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2113_, v_completeness_2114_, v_inst_2116_, v_inst_2117_, v_inst_2119_, v_inst_2121_, v_initState_2122_, v_handler_2123_, v_onDidChange_2124_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___boxed(lean_object* v_method_2127_, lean_object* v_completeness_2128_, lean_object* v_paramType_2129_, lean_object* v_inst_2130_, lean_object* v_inst_2131_, lean_object* v_respType_2132_, lean_object* v_inst_2133_, lean_object* v_stateType_2134_, lean_object* v_inst_2135_, lean_object* v_initState_2136_, lean_object* v_handler_2137_, lean_object* v_onDidChange_2138_, lean_object* v_a_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(v_method_2127_, v_completeness_2128_, v_paramType_2129_, v_inst_2130_, v_inst_2131_, v_respType_2132_, v_inst_2133_, v_stateType_2134_, v_inst_2135_, v_initState_2136_, v_handler_2137_, v_onDidChange_2138_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(lean_object* v_method_2141_, lean_object* v_completeness_2142_, lean_object* v_inst_2143_, lean_object* v_inst_2144_, lean_object* v_inst_2145_, lean_object* v_inst_2146_, lean_object* v_initState_2147_, lean_object* v_handler_2148_, lean_object* v_onDidChange_2149_){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___f_2154_; uint8_t v___x_2155_; 
v___x_2151_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__0));
v___x_2152_ = l_Lean_Server_requestHandlers;
v___x_2153_ = lean_st_ref_get(v___x_2152_);
v___f_2154_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
lean_inc_ref(v_method_2141_);
v___x_2155_ = l_Lean_PersistentHashMap_contains___redArg(v___f_2154_, v___x_2151_, v___x_2153_, v_method_2141_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; 
v___x_2156_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2141_, v_completeness_2142_, v_inst_2143_, v_inst_2144_, v_inst_2145_, v_inst_2146_, v_initState_2147_, v_handler_2148_, v_onDidChange_2149_);
return v___x_2156_;
}
else
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
lean_dec_ref(v_onDidChange_2149_);
lean_dec_ref(v_handler_2148_);
lean_dec(v_initState_2147_);
lean_dec(v_inst_2146_);
lean_dec_ref(v_inst_2145_);
lean_dec_ref(v_inst_2144_);
lean_dec_ref(v_inst_2143_);
lean_dec(v_completeness_2142_);
v___x_2157_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__12));
v___x_2158_ = lean_string_append(v___x_2157_, v_method_2141_);
lean_dec_ref(v_method_2141_);
v___x_2159_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__4));
v___x_2160_ = lean_string_append(v___x_2158_, v___x_2159_);
v___x_2161_ = lean_mk_io_user_error(v___x_2160_);
v___x_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
return v___x_2162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2163_, lean_object* v_completeness_2164_, lean_object* v_inst_2165_, lean_object* v_inst_2166_, lean_object* v_inst_2167_, lean_object* v_inst_2168_, lean_object* v_initState_2169_, lean_object* v_handler_2170_, lean_object* v_onDidChange_2171_, lean_object* v_a_2172_){
_start:
{
lean_object* v_res_2173_; 
v_res_2173_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2163_, v_completeness_2164_, v_inst_2165_, v_inst_2166_, v_inst_2167_, v_inst_2168_, v_initState_2169_, v_handler_2170_, v_onDidChange_2171_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler(lean_object* v_method_2174_, lean_object* v_completeness_2175_, lean_object* v_paramType_2176_, lean_object* v_inst_2177_, lean_object* v_inst_2178_, lean_object* v_respType_2179_, lean_object* v_inst_2180_, lean_object* v_stateType_2181_, lean_object* v_inst_2182_, lean_object* v_initState_2183_, lean_object* v_handler_2184_, lean_object* v_onDidChange_2185_){
_start:
{
lean_object* v___x_2187_; 
v___x_2187_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2174_, v_completeness_2175_, v_inst_2177_, v_inst_2178_, v_inst_2180_, v_inst_2182_, v_initState_2183_, v_handler_2184_, v_onDidChange_2185_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___boxed(lean_object* v_method_2188_, lean_object* v_completeness_2189_, lean_object* v_paramType_2190_, lean_object* v_inst_2191_, lean_object* v_inst_2192_, lean_object* v_respType_2193_, lean_object* v_inst_2194_, lean_object* v_stateType_2195_, lean_object* v_inst_2196_, lean_object* v_initState_2197_, lean_object* v_handler_2198_, lean_object* v_onDidChange_2199_, lean_object* v_a_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler(v_method_2188_, v_completeness_2189_, v_paramType_2190_, v_inst_2191_, v_inst_2192_, v_respType_2193_, v_inst_2194_, v_stateType_2195_, v_inst_2196_, v_initState_2197_, v_handler_2198_, v_onDidChange_2199_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0(lean_object* v_handler_2202_, lean_object* v_p_2203_, lean_object* v_s_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v___x_2207_; 
lean_inc_ref(v___y_2205_);
v___x_2207_ = lean_apply_4(v_handler_2202_, v_p_2203_, v_s_2204_, v___y_2205_, lean_box(0));
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2226_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2210_ = v___x_2207_;
v_isShared_2211_ = v_isSharedCheck_2226_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2207_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2226_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v_fst_2212_; lean_object* v_snd_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2225_; 
v_fst_2212_ = lean_ctor_get(v_a_2208_, 0);
v_snd_2213_ = lean_ctor_get(v_a_2208_, 1);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_a_2208_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2215_ = v_a_2208_;
v_isShared_2216_ = v_isSharedCheck_2225_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_snd_2213_);
lean_inc(v_fst_2212_);
lean_dec(v_a_2208_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2225_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
uint8_t v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2220_; 
v___x_2217_ = 1;
v___x_2218_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2218_, 0, v_fst_2212_);
lean_ctor_set_uint8(v___x_2218_, sizeof(void*)*1, v___x_2217_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 0, v___x_2218_);
v___x_2220_ = v___x_2215_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2218_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_snd_2213_);
v___x_2220_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
lean_object* v___x_2222_; 
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 0, v___x_2220_);
v___x_2222_ = v___x_2210_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2220_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
v_a_2227_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2207_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2207_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object* v_handler_2235_, lean_object* v_p_2236_, lean_object* v_s_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0(v_handler_2235_, v_p_2236_, v_s_2237_, v___y_2238_);
lean_dec_ref(v___y_2238_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(lean_object* v_method_2241_, lean_object* v_inst_2242_, lean_object* v_inst_2243_, lean_object* v_inst_2244_, lean_object* v_inst_2245_, lean_object* v_initState_2246_, lean_object* v_handler_2247_, lean_object* v_onDidChange_2248_){
_start:
{
lean_object* v_handler_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v_handler_2250_ = lean_alloc_closure((void*)(l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v_handler_2250_, 0, v_handler_2247_);
v___x_2251_ = lean_box(0);
v___x_2252_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2241_, v___x_2251_, v_inst_2242_, v_inst_2243_, v_inst_2244_, v_inst_2245_, v_initState_2246_, v_handler_2250_, v_onDidChange_2248_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2253_, lean_object* v_inst_2254_, lean_object* v_inst_2255_, lean_object* v_inst_2256_, lean_object* v_inst_2257_, lean_object* v_initState_2258_, lean_object* v_handler_2259_, lean_object* v_onDidChange_2260_, lean_object* v_a_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(v_method_2253_, v_inst_2254_, v_inst_2255_, v_inst_2256_, v_inst_2257_, v_initState_2258_, v_handler_2259_, v_onDidChange_2260_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler(lean_object* v_method_2263_, lean_object* v_paramType_2264_, lean_object* v_inst_2265_, lean_object* v_inst_2266_, lean_object* v_respType_2267_, lean_object* v_inst_2268_, lean_object* v_stateType_2269_, lean_object* v_inst_2270_, lean_object* v_initState_2271_, lean_object* v_handler_2272_, lean_object* v_onDidChange_2273_){
_start:
{
lean_object* v___x_2275_; 
v___x_2275_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(v_method_2263_, v_inst_2265_, v_inst_2266_, v_inst_2268_, v_inst_2270_, v_initState_2271_, v_handler_2272_, v_onDidChange_2273_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___boxed(lean_object* v_method_2276_, lean_object* v_paramType_2277_, lean_object* v_inst_2278_, lean_object* v_inst_2279_, lean_object* v_respType_2280_, lean_object* v_inst_2281_, lean_object* v_stateType_2282_, lean_object* v_inst_2283_, lean_object* v_initState_2284_, lean_object* v_handler_2285_, lean_object* v_onDidChange_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler(v_method_2276_, v_paramType_2277_, v_inst_2278_, v_inst_2279_, v_respType_2280_, v_inst_2281_, v_stateType_2282_, v_inst_2283_, v_initState_2284_, v_handler_2285_, v_onDidChange_2286_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(lean_object* v_method_2289_, lean_object* v_refreshMethod_2290_, lean_object* v_refreshIntervalMs_2291_, lean_object* v_inst_2292_, lean_object* v_inst_2293_, lean_object* v_inst_2294_, lean_object* v_inst_2295_, lean_object* v_initState_2296_, lean_object* v_handler_2297_, lean_object* v_onDidChange_2298_){
_start:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2300_, 0, v_refreshMethod_2290_);
lean_ctor_set(v___x_2300_, 1, v_refreshIntervalMs_2291_);
v___x_2301_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2289_, v___x_2300_, v_inst_2292_, v_inst_2293_, v_inst_2294_, v_inst_2295_, v_initState_2296_, v_handler_2297_, v_onDidChange_2298_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2302_, lean_object* v_refreshMethod_2303_, lean_object* v_refreshIntervalMs_2304_, lean_object* v_inst_2305_, lean_object* v_inst_2306_, lean_object* v_inst_2307_, lean_object* v_inst_2308_, lean_object* v_initState_2309_, lean_object* v_handler_2310_, lean_object* v_onDidChange_2311_, lean_object* v_a_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(v_method_2302_, v_refreshMethod_2303_, v_refreshIntervalMs_2304_, v_inst_2305_, v_inst_2306_, v_inst_2307_, v_inst_2308_, v_initState_2309_, v_handler_2310_, v_onDidChange_2311_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler(lean_object* v_method_2314_, lean_object* v_refreshMethod_2315_, lean_object* v_refreshIntervalMs_2316_, lean_object* v_paramType_2317_, lean_object* v_inst_2318_, lean_object* v_inst_2319_, lean_object* v_respType_2320_, lean_object* v_inst_2321_, lean_object* v_stateType_2322_, lean_object* v_inst_2323_, lean_object* v_initState_2324_, lean_object* v_handler_2325_, lean_object* v_onDidChange_2326_){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(v_method_2314_, v_refreshMethod_2315_, v_refreshIntervalMs_2316_, v_inst_2318_, v_inst_2319_, v_inst_2321_, v_inst_2323_, v_initState_2324_, v_handler_2325_, v_onDidChange_2326_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___boxed(lean_object* v_method_2329_, lean_object* v_refreshMethod_2330_, lean_object* v_refreshIntervalMs_2331_, lean_object* v_paramType_2332_, lean_object* v_inst_2333_, lean_object* v_inst_2334_, lean_object* v_respType_2335_, lean_object* v_inst_2336_, lean_object* v_stateType_2337_, lean_object* v_inst_2338_, lean_object* v_initState_2339_, lean_object* v_handler_2340_, lean_object* v_onDidChange_2341_, lean_object* v_a_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l_Lean_Server_registerPartialStatefulLspRequestHandler(v_method_2329_, v_refreshMethod_2330_, v_refreshIntervalMs_2331_, v_paramType_2332_, v_inst_2333_, v_inst_2334_, v_respType_2335_, v_inst_2336_, v_stateType_2337_, v_inst_2338_, v_initState_2339_, v_handler_2340_, v_onDidChange_2341_);
return v_res_2343_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2344_, lean_object* v_i_2345_, lean_object* v_k_2346_){
_start:
{
lean_object* v___x_2347_; uint8_t v___x_2348_; 
v___x_2347_ = lean_array_get_size(v_keys_2344_);
v___x_2348_ = lean_nat_dec_lt(v_i_2345_, v___x_2347_);
if (v___x_2348_ == 0)
{
lean_dec(v_i_2345_);
return v___x_2348_;
}
else
{
lean_object* v_k_x27_2349_; uint8_t v___x_2350_; 
v_k_x27_2349_ = lean_array_fget_borrowed(v_keys_2344_, v_i_2345_);
v___x_2350_ = lean_string_dec_eq(v_k_2346_, v_k_x27_2349_);
if (v___x_2350_ == 0)
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = lean_unsigned_to_nat(1u);
v___x_2352_ = lean_nat_add(v_i_2345_, v___x_2351_);
lean_dec(v_i_2345_);
v_i_2345_ = v___x_2352_;
goto _start;
}
else
{
lean_dec(v_i_2345_);
return v___x_2348_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2354_, lean_object* v_i_2355_, lean_object* v_k_2356_){
_start:
{
uint8_t v_res_2357_; lean_object* v_r_2358_; 
v_res_2357_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_keys_2354_, v_i_2355_, v_k_2356_);
lean_dec_ref(v_k_2356_);
lean_dec_ref(v_keys_2354_);
v_r_2358_ = lean_box(v_res_2357_);
return v_r_2358_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(lean_object* v_x_2359_, size_t v_x_2360_, lean_object* v_x_2361_){
_start:
{
if (lean_obj_tag(v_x_2359_) == 0)
{
lean_object* v_es_2362_; lean_object* v___x_2363_; size_t v___x_2364_; size_t v___x_2365_; lean_object* v_j_2366_; lean_object* v___x_2367_; 
v_es_2362_ = lean_ctor_get(v_x_2359_, 0);
v___x_2363_ = lean_box(2);
v___x_2364_ = ((size_t)31ULL);
v___x_2365_ = lean_usize_land(v_x_2360_, v___x_2364_);
v_j_2366_ = lean_usize_to_nat(v___x_2365_);
v___x_2367_ = lean_array_get_borrowed(v___x_2363_, v_es_2362_, v_j_2366_);
lean_dec(v_j_2366_);
switch(lean_obj_tag(v___x_2367_))
{
case 0:
{
lean_object* v_key_2368_; uint8_t v___x_2369_; 
v_key_2368_ = lean_ctor_get(v___x_2367_, 0);
v___x_2369_ = lean_string_dec_eq(v_x_2361_, v_key_2368_);
return v___x_2369_;
}
case 1:
{
lean_object* v_node_2370_; size_t v___x_2371_; size_t v___x_2372_; 
v_node_2370_ = lean_ctor_get(v___x_2367_, 0);
v___x_2371_ = ((size_t)5ULL);
v___x_2372_ = lean_usize_shift_right(v_x_2360_, v___x_2371_);
v_x_2359_ = v_node_2370_;
v_x_2360_ = v___x_2372_;
goto _start;
}
default: 
{
uint8_t v___x_2374_; 
v___x_2374_ = 0;
return v___x_2374_;
}
}
}
else
{
lean_object* v_ks_2375_; lean_object* v___x_2376_; uint8_t v___x_2377_; 
v_ks_2375_ = lean_ctor_get(v_x_2359_, 0);
v___x_2376_ = lean_unsigned_to_nat(0u);
v___x_2377_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_ks_2375_, v___x_2376_, v_x_2361_);
return v___x_2377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg___boxed(lean_object* v_x_2378_, lean_object* v_x_2379_, lean_object* v_x_2380_){
_start:
{
size_t v_x_226__boxed_2381_; uint8_t v_res_2382_; lean_object* v_r_2383_; 
v_x_226__boxed_2381_ = lean_unbox_usize(v_x_2379_);
lean_dec(v_x_2379_);
v_res_2382_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_2378_, v_x_226__boxed_2381_, v_x_2380_);
lean_dec_ref(v_x_2380_);
lean_dec_ref(v_x_2378_);
v_r_2383_ = lean_box(v_res_2382_);
return v_r_2383_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(lean_object* v_x_2384_, lean_object* v_x_2385_){
_start:
{
uint64_t v___x_2386_; size_t v___x_2387_; uint8_t v___x_2388_; 
v___x_2386_ = lean_string_hash(v_x_2385_);
v___x_2387_ = lean_uint64_to_usize(v___x_2386_);
v___x_2388_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_2384_, v___x_2387_, v_x_2385_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg___boxed(lean_object* v_x_2389_, lean_object* v_x_2390_){
_start:
{
uint8_t v_res_2391_; lean_object* v_r_2392_; 
v_res_2391_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v_x_2389_, v_x_2390_);
lean_dec_ref(v_x_2390_);
lean_dec_ref(v_x_2389_);
v_r_2392_ = lean_box(v_res_2391_);
return v_r_2392_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_isStatefulLspRequestMethod(lean_object* v_method_2393_){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; uint8_t v___x_2397_; 
v___x_2395_ = l_Lean_Server_statefulRequestHandlers;
v___x_2396_ = lean_st_ref_get(v___x_2395_);
v___x_2397_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v___x_2396_, v_method_2393_);
lean_dec(v___x_2396_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_isStatefulLspRequestMethod___boxed(lean_object* v_method_2398_, lean_object* v_a_2399_){
_start:
{
uint8_t v_res_2400_; lean_object* v_r_2401_; 
v_res_2400_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_2398_);
lean_dec_ref(v_method_2398_);
v_r_2401_ = lean_box(v_res_2400_);
return v_r_2401_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0(lean_object* v_00_u03b2_2402_, lean_object* v_x_2403_, lean_object* v_x_2404_){
_start:
{
uint8_t v___x_2405_; 
v___x_2405_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v_x_2403_, v_x_2404_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___boxed(lean_object* v_00_u03b2_2406_, lean_object* v_x_2407_, lean_object* v_x_2408_){
_start:
{
uint8_t v_res_2409_; lean_object* v_r_2410_; 
v_res_2409_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0(v_00_u03b2_2406_, v_x_2407_, v_x_2408_);
lean_dec_ref(v_x_2408_);
lean_dec_ref(v_x_2407_);
v_r_2410_ = lean_box(v_res_2409_);
return v_r_2410_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0(lean_object* v_00_u03b2_2411_, lean_object* v_x_2412_, size_t v_x_2413_, lean_object* v_x_2414_){
_start:
{
uint8_t v___x_2415_; 
v___x_2415_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_2412_, v_x_2413_, v_x_2414_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2416_, lean_object* v_x_2417_, lean_object* v_x_2418_, lean_object* v_x_2419_){
_start:
{
size_t v_x_296__boxed_2420_; uint8_t v_res_2421_; lean_object* v_r_2422_; 
v_x_296__boxed_2420_ = lean_unbox_usize(v_x_2418_);
lean_dec(v_x_2418_);
v_res_2421_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0(v_00_u03b2_2416_, v_x_2417_, v_x_296__boxed_2420_, v_x_2419_);
lean_dec_ref(v_x_2419_);
lean_dec_ref(v_x_2417_);
v_r_2422_ = lean_box(v_res_2421_);
return v_r_2422_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2423_, lean_object* v_keys_2424_, lean_object* v_vals_2425_, lean_object* v_heq_2426_, lean_object* v_i_2427_, lean_object* v_k_2428_){
_start:
{
uint8_t v___x_2429_; 
v___x_2429_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_keys_2424_, v_i_2427_, v_k_2428_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2430_, lean_object* v_keys_2431_, lean_object* v_vals_2432_, lean_object* v_heq_2433_, lean_object* v_i_2434_, lean_object* v_k_2435_){
_start:
{
uint8_t v_res_2436_; lean_object* v_r_2437_; 
v_res_2436_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1(v_00_u03b2_2430_, v_keys_2431_, v_vals_2432_, v_heq_2433_, v_i_2434_, v_k_2435_);
lean_dec_ref(v_k_2435_);
lean_dec_ref(v_vals_2432_);
lean_dec_ref(v_keys_2431_);
v_r_2437_ = lean_box(v_res_2436_);
return v_r_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupStatefulLspRequestHandler(lean_object* v_method_2438_){
_start:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2440_ = l_Lean_Server_statefulRequestHandlers;
v___x_2441_ = lean_st_ref_get(v___x_2440_);
v___x_2442_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v___x_2441_, v_method_2438_);
lean_dec(v___x_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupStatefulLspRequestHandler___boxed(lean_object* v_method_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_2443_);
lean_dec_ref(v_method_2443_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(lean_object* v_as_2446_, size_t v_i_2447_, size_t v_stop_2448_, lean_object* v_b_2449_){
_start:
{
lean_object* v___y_2451_; uint8_t v___x_2455_; 
v___x_2455_ = lean_usize_dec_eq(v_i_2447_, v_stop_2448_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2456_; lean_object* v_snd_2457_; lean_object* v_completeness_2458_; 
v___x_2456_ = lean_array_uget(v_as_2446_, v_i_2447_);
v_snd_2457_ = lean_ctor_get(v___x_2456_, 1);
v_completeness_2458_ = lean_ctor_get(v_snd_2457_, 8);
lean_inc(v_completeness_2458_);
if (lean_obj_tag(v_completeness_2458_) == 1)
{
lean_object* v_fst_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2476_; 
v_fst_2459_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2476_ == 0)
{
lean_object* v_unused_2477_; 
v_unused_2477_ = lean_ctor_get(v___x_2456_, 1);
lean_dec(v_unused_2477_);
v___x_2461_ = v___x_2456_;
v_isShared_2462_ = v_isSharedCheck_2476_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_fst_2459_);
lean_dec(v___x_2456_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2476_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v_refreshMethod_2463_; lean_object* v_refreshIntervalMs_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2475_; 
v_refreshMethod_2463_ = lean_ctor_get(v_completeness_2458_, 0);
v_refreshIntervalMs_2464_ = lean_ctor_get(v_completeness_2458_, 1);
v_isSharedCheck_2475_ = !lean_is_exclusive(v_completeness_2458_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2466_ = v_completeness_2458_;
v_isShared_2467_ = v_isSharedCheck_2475_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_refreshIntervalMs_2464_);
lean_inc(v_refreshMethod_2463_);
lean_dec(v_completeness_2458_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2475_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 1, v_refreshIntervalMs_2464_);
lean_ctor_set(v___x_2461_, 0, v_refreshMethod_2463_);
v___x_2469_ = v___x_2461_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_refreshMethod_2463_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v_refreshIntervalMs_2464_);
v___x_2469_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
lean_object* v___x_2471_; 
if (v_isShared_2467_ == 0)
{
lean_ctor_set_tag(v___x_2466_, 0);
lean_ctor_set(v___x_2466_, 1, v___x_2469_);
lean_ctor_set(v___x_2466_, 0, v_fst_2459_);
v___x_2471_ = v___x_2466_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_fst_2459_);
lean_ctor_set(v_reuseFailAlloc_2473_, 1, v___x_2469_);
v___x_2471_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
lean_object* v___x_2472_; 
v___x_2472_ = lean_array_push(v_b_2449_, v___x_2471_);
v___y_2451_ = v___x_2472_;
goto v___jp_2450_;
}
}
}
}
}
else
{
lean_dec(v_completeness_2458_);
lean_dec(v___x_2456_);
v___y_2451_ = v_b_2449_;
goto v___jp_2450_;
}
}
else
{
return v_b_2449_;
}
v___jp_2450_:
{
size_t v___x_2452_; size_t v___x_2453_; 
v___x_2452_ = ((size_t)1ULL);
v___x_2453_ = lean_usize_add(v_i_2447_, v___x_2452_);
v_i_2447_ = v___x_2453_;
v_b_2449_ = v___y_2451_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2___boxed(lean_object* v_as_2478_, lean_object* v_i_2479_, lean_object* v_stop_2480_, lean_object* v_b_2481_){
_start:
{
size_t v_i_boxed_2482_; size_t v_stop_boxed_2483_; lean_object* v_res_2484_; 
v_i_boxed_2482_ = lean_unbox_usize(v_i_2479_);
lean_dec(v_i_2479_);
v_stop_boxed_2483_ = lean_unbox_usize(v_stop_2480_);
lean_dec(v_stop_2480_);
v_res_2484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_2478_, v_i_boxed_2482_, v_stop_boxed_2483_, v_b_2481_);
lean_dec_ref(v_as_2478_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(lean_object* v_as_2487_, lean_object* v_start_2488_, lean_object* v_stop_2489_){
_start:
{
lean_object* v___x_2490_; uint8_t v___x_2491_; 
v___x_2490_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___closed__0));
v___x_2491_ = lean_nat_dec_lt(v_start_2488_, v_stop_2489_);
if (v___x_2491_ == 0)
{
return v___x_2490_;
}
else
{
lean_object* v___x_2492_; uint8_t v___x_2493_; 
v___x_2492_ = lean_array_get_size(v_as_2487_);
v___x_2493_ = lean_nat_dec_le(v_stop_2489_, v___x_2492_);
if (v___x_2493_ == 0)
{
uint8_t v___x_2494_; 
v___x_2494_ = lean_nat_dec_lt(v_start_2488_, v___x_2492_);
if (v___x_2494_ == 0)
{
return v___x_2490_;
}
else
{
size_t v___x_2495_; size_t v___x_2496_; lean_object* v___x_2497_; 
v___x_2495_ = lean_usize_of_nat(v_start_2488_);
v___x_2496_ = lean_usize_of_nat(v___x_2492_);
v___x_2497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_2487_, v___x_2495_, v___x_2496_, v___x_2490_);
return v___x_2497_;
}
}
else
{
size_t v___x_2498_; size_t v___x_2499_; lean_object* v___x_2500_; 
v___x_2498_ = lean_usize_of_nat(v_start_2488_);
v___x_2499_ = lean_usize_of_nat(v_stop_2489_);
v___x_2500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_2487_, v___x_2498_, v___x_2499_, v___x_2490_);
return v___x_2500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___boxed(lean_object* v_as_2501_, lean_object* v_start_2502_, lean_object* v_stop_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(v_as_2501_, v_start_2502_, v_stop_2503_);
lean_dec(v_stop_2503_);
lean_dec(v_start_2502_);
lean_dec_ref(v_as_2501_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_f_2505_, lean_object* v_keys_2506_, lean_object* v_vals_2507_, lean_object* v_i_2508_, lean_object* v_acc_2509_){
_start:
{
lean_object* v___x_2510_; uint8_t v___x_2511_; 
v___x_2510_ = lean_array_get_size(v_keys_2506_);
v___x_2511_ = lean_nat_dec_lt(v_i_2508_, v___x_2510_);
if (v___x_2511_ == 0)
{
lean_dec(v_i_2508_);
lean_dec(v_f_2505_);
return v_acc_2509_;
}
else
{
lean_object* v_k_2512_; lean_object* v_v_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v_k_2512_ = lean_array_fget_borrowed(v_keys_2506_, v_i_2508_);
v_v_2513_ = lean_array_fget_borrowed(v_vals_2507_, v_i_2508_);
lean_inc(v_f_2505_);
lean_inc(v_v_2513_);
lean_inc(v_k_2512_);
v___x_2514_ = lean_apply_3(v_f_2505_, v_acc_2509_, v_k_2512_, v_v_2513_);
v___x_2515_ = lean_unsigned_to_nat(1u);
v___x_2516_ = lean_nat_add(v_i_2508_, v___x_2515_);
lean_dec(v_i_2508_);
v_i_2508_ = v___x_2516_;
v_acc_2509_ = v___x_2514_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_f_2518_, lean_object* v_keys_2519_, lean_object* v_vals_2520_, lean_object* v_i_2521_, lean_object* v_acc_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_2518_, v_keys_2519_, v_vals_2520_, v_i_2521_, v_acc_2522_);
lean_dec_ref(v_vals_2520_);
lean_dec_ref(v_keys_2519_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_f_2524_, lean_object* v_as_2525_, size_t v_i_2526_, size_t v_stop_2527_, lean_object* v_b_2528_){
_start:
{
lean_object* v___y_2530_; uint8_t v___x_2534_; 
v___x_2534_ = lean_usize_dec_eq(v_i_2526_, v_stop_2527_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; 
v___x_2535_ = lean_array_uget_borrowed(v_as_2525_, v_i_2526_);
switch(lean_obj_tag(v___x_2535_))
{
case 0:
{
lean_object* v_key_2536_; lean_object* v_val_2537_; lean_object* v___x_2538_; 
v_key_2536_ = lean_ctor_get(v___x_2535_, 0);
v_val_2537_ = lean_ctor_get(v___x_2535_, 1);
lean_inc(v_f_2524_);
lean_inc(v_val_2537_);
lean_inc(v_key_2536_);
v___x_2538_ = lean_apply_3(v_f_2524_, v_b_2528_, v_key_2536_, v_val_2537_);
v___y_2530_ = v___x_2538_;
goto v___jp_2529_;
}
case 1:
{
lean_object* v_node_2539_; lean_object* v___x_2540_; 
v_node_2539_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_f_2524_);
v___x_2540_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2524_, v_node_2539_, v_b_2528_);
v___y_2530_ = v___x_2540_;
goto v___jp_2529_;
}
default: 
{
v___y_2530_ = v_b_2528_;
goto v___jp_2529_;
}
}
}
else
{
lean_dec(v_f_2524_);
return v_b_2528_;
}
v___jp_2529_:
{
size_t v___x_2531_; size_t v___x_2532_; 
v___x_2531_ = ((size_t)1ULL);
v___x_2532_ = lean_usize_add(v_i_2526_, v___x_2531_);
v_i_2526_ = v___x_2532_;
v_b_2528_ = v___y_2530_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_2541_, lean_object* v_x_2542_, lean_object* v_x_2543_){
_start:
{
if (lean_obj_tag(v_x_2542_) == 0)
{
lean_object* v_es_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; 
v_es_2544_ = lean_ctor_get(v_x_2542_, 0);
v___x_2545_ = lean_unsigned_to_nat(0u);
v___x_2546_ = lean_array_get_size(v_es_2544_);
v___x_2547_ = lean_nat_dec_lt(v___x_2545_, v___x_2546_);
if (v___x_2547_ == 0)
{
lean_dec(v_f_2541_);
return v_x_2543_;
}
else
{
size_t v___x_2548_; size_t v___x_2549_; lean_object* v___x_2550_; 
v___x_2548_ = ((size_t)0ULL);
v___x_2549_ = lean_usize_of_nat(v___x_2546_);
v___x_2550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_2541_, v_es_2544_, v___x_2548_, v___x_2549_, v_x_2543_);
return v___x_2550_;
}
}
else
{
lean_object* v_ks_2551_; lean_object* v_vs_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v_ks_2551_ = lean_ctor_get(v_x_2542_, 0);
v_vs_2552_ = lean_ctor_get(v_x_2542_, 1);
v___x_2553_ = lean_unsigned_to_nat(0u);
v___x_2554_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_2541_, v_ks_2551_, v_vs_2552_, v___x_2553_, v_x_2543_);
return v___x_2554_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_2555_, lean_object* v_x_2556_, lean_object* v_x_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2555_, v_x_2556_, v_x_2557_);
lean_dec_ref(v_x_2556_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_f_2559_, lean_object* v_as_2560_, lean_object* v_i_2561_, lean_object* v_stop_2562_, lean_object* v_b_2563_){
_start:
{
size_t v_i_boxed_2564_; size_t v_stop_boxed_2565_; lean_object* v_res_2566_; 
v_i_boxed_2564_ = lean_unbox_usize(v_i_2561_);
lean_dec(v_i_2561_);
v_stop_boxed_2565_ = lean_unbox_usize(v_stop_2562_);
lean_dec(v_stop_2562_);
v_res_2566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_2559_, v_as_2560_, v_i_boxed_2564_, v_stop_boxed_2565_, v_b_2563_);
lean_dec_ref(v_as_2560_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___lam__0(lean_object* v_f_2567_, lean_object* v_x1_2568_, lean_object* v_x2_2569_, lean_object* v_x3_2570_){
_start:
{
lean_object* v___x_2571_; 
v___x_2571_ = lean_apply_3(v_f_2567_, v_x1_2568_, v_x2_2569_, v_x3_2570_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(lean_object* v_map_2572_, lean_object* v_f_2573_, lean_object* v_init_2574_){
_start:
{
lean_object* v___f_2575_; lean_object* v___x_2576_; 
v___f_2575_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2575_, 0, v_f_2573_);
v___x_2576_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v___f_2575_, v_map_2572_, v_init_2574_);
return v___x_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___boxed(lean_object* v_map_2577_, lean_object* v_f_2578_, lean_object* v_init_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_map_2577_, v_f_2578_, v_init_2579_);
lean_dec_ref(v_map_2577_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___lam__0(lean_object* v_ps_2581_, lean_object* v_k_2582_, lean_object* v_v_2583_){
_start:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2584_, 0, v_k_2582_);
lean_ctor_set(v___x_2584_, 1, v_v_2583_);
v___x_2585_ = lean_array_push(v_ps_2581_, v___x_2584_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(lean_object* v_m_2589_){
_start:
{
lean_object* v___f_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___f_2590_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__0));
v___x_2591_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__1));
v___x_2592_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_m_2589_, v___f_2590_, v___x_2591_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___boxed(lean_object* v_m_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v_m_2593_);
lean_dec_ref(v_m_2593_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_partialLspRequestHandlerMethods(){
_start:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2596_ = l_Lean_Server_statefulRequestHandlers;
v___x_2597_ = lean_st_ref_get(v___x_2596_);
v___x_2598_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v___x_2597_);
lean_dec(v___x_2597_);
v___x_2599_ = lean_unsigned_to_nat(0u);
v___x_2600_ = lean_array_get_size(v___x_2598_);
v___x_2601_ = l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(v___x_2598_, v___x_2599_, v___x_2600_);
lean_dec_ref(v___x_2598_);
v___x_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2601_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_partialLspRequestHandlerMethods___boxed(lean_object* v_a_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Lean_Server_partialLspRequestHandlerMethods();
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0(lean_object* v_00_u03b2_2605_, lean_object* v_m_2606_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v_m_2606_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___boxed(lean_object* v_00_u03b2_2608_, lean_object* v_m_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0(v_00_u03b2_2608_, v_m_2609_);
lean_dec_ref(v_m_2609_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0(lean_object* v_00_u03c3_2611_, lean_object* v_00_u03b2_2612_, lean_object* v_map_2613_, lean_object* v_f_2614_, lean_object* v_init_2615_){
_start:
{
lean_object* v___x_2616_; 
v___x_2616_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_map_2613_, v_f_2614_, v_init_2615_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___boxed(lean_object* v_00_u03c3_2617_, lean_object* v_00_u03b2_2618_, lean_object* v_map_2619_, lean_object* v_f_2620_, lean_object* v_init_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0(v_00_u03c3_2617_, v_00_u03b2_2618_, v_map_2619_, v_f_2620_, v_init_2621_);
lean_dec_ref(v_map_2619_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg(lean_object* v_map_2623_, lean_object* v_f_2624_, lean_object* v_init_2625_){
_start:
{
lean_object* v___x_2626_; 
v___x_2626_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2624_, v_map_2623_, v_init_2625_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_2627_, lean_object* v_f_2628_, lean_object* v_init_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg(v_map_2627_, v_f_2628_, v_init_2629_);
lean_dec_ref(v_map_2627_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_2631_, lean_object* v_00_u03b2_2632_, lean_object* v_map_2633_, lean_object* v_f_2634_, lean_object* v_init_2635_){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2634_, v_map_2633_, v_init_2635_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_2637_, lean_object* v_00_u03b2_2638_, lean_object* v_map_2639_, lean_object* v_f_2640_, lean_object* v_init_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1(v_00_u03c3_2637_, v_00_u03b2_2638_, v_map_2639_, v_f_2640_, v_init_2641_);
lean_dec_ref(v_map_2639_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_2643_, lean_object* v_00_u03b1_2644_, lean_object* v_00_u03b2_2645_, lean_object* v_f_2646_, lean_object* v_x_2647_, lean_object* v_x_2648_){
_start:
{
lean_object* v___x_2649_; 
v___x_2649_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2646_, v_x_2647_, v_x_2648_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_2650_, lean_object* v_00_u03b1_2651_, lean_object* v_00_u03b2_2652_, lean_object* v_f_2653_, lean_object* v_x_2654_, lean_object* v_x_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_2650_, v_00_u03b1_2651_, v_00_u03b2_2652_, v_f_2653_, v_x_2654_, v_x_2655_);
lean_dec_ref(v_x_2654_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_2657_, lean_object* v_00_u03b2_2658_, lean_object* v_00_u03c3_2659_, lean_object* v_f_2660_, lean_object* v_as_2661_, size_t v_i_2662_, size_t v_stop_2663_, lean_object* v_b_2664_){
_start:
{
lean_object* v___x_2665_; 
v___x_2665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_2660_, v_as_2661_, v_i_2662_, v_stop_2663_, v_b_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2666_, lean_object* v_00_u03b2_2667_, lean_object* v_00_u03c3_2668_, lean_object* v_f_2669_, lean_object* v_as_2670_, lean_object* v_i_2671_, lean_object* v_stop_2672_, lean_object* v_b_2673_){
_start:
{
size_t v_i_boxed_2674_; size_t v_stop_boxed_2675_; lean_object* v_res_2676_; 
v_i_boxed_2674_ = lean_unbox_usize(v_i_2671_);
lean_dec(v_i_2671_);
v_stop_boxed_2675_ = lean_unbox_usize(v_stop_2672_);
lean_dec(v_stop_2672_);
v_res_2676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_2666_, v_00_u03b2_2667_, v_00_u03c3_2668_, v_f_2669_, v_as_2670_, v_i_boxed_2674_, v_stop_boxed_2675_, v_b_2673_);
lean_dec_ref(v_as_2670_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03c3_2677_, lean_object* v_00_u03b1_2678_, lean_object* v_00_u03b2_2679_, lean_object* v_f_2680_, lean_object* v_keys_2681_, lean_object* v_vals_2682_, lean_object* v_heq_2683_, lean_object* v_i_2684_, lean_object* v_acc_2685_){
_start:
{
lean_object* v___x_2686_; 
v___x_2686_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_2680_, v_keys_2681_, v_vals_2682_, v_i_2684_, v_acc_2685_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03c3_2687_, lean_object* v_00_u03b1_2688_, lean_object* v_00_u03b2_2689_, lean_object* v_f_2690_, lean_object* v_keys_2691_, lean_object* v_vals_2692_, lean_object* v_heq_2693_, lean_object* v_i_2694_, lean_object* v_acc_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6(v_00_u03c3_2687_, v_00_u03b1_2688_, v_00_u03b2_2689_, v_f_2690_, v_keys_2691_, v_vals_2692_, v_heq_2693_, v_i_2694_, v_acc_2695_);
lean_dec_ref(v_vals_2692_);
lean_dec_ref(v_keys_2691_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0(lean_object* v_inst_2697_, lean_object* v_pureOnDidChange_2698_, lean_object* v_method_2699_, lean_object* v_onDidChange_2700_, lean_object* v_p_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; 
lean_inc(v_inst_2697_);
v___x_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2705_, 0, v_inst_2697_);
lean_ctor_set(v___x_2705_, 1, v___y_2702_);
lean_inc_ref(v___y_2703_);
lean_inc_ref(v_p_2701_);
v___x_2706_ = lean_apply_4(v_pureOnDidChange_2698_, v_p_2701_, v___x_2705_, v___y_2703_, lean_box(0));
if (lean_obj_tag(v___x_2706_) == 0)
{
lean_object* v_a_2707_; lean_object* v_snd_2708_; lean_object* v___x_2709_; 
v_a_2707_ = lean_ctor_get(v___x_2706_, 0);
lean_inc(v_a_2707_);
lean_dec_ref_known(v___x_2706_, 1);
v_snd_2708_ = lean_ctor_get(v_a_2707_, 1);
lean_inc(v_snd_2708_);
lean_dec(v_a_2707_);
v___x_2709_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_2699_, v_snd_2708_, v_inst_2697_);
lean_dec(v_inst_2697_);
lean_dec(v_snd_2708_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2711_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_a_2710_);
lean_dec_ref_known(v___x_2709_, 1);
lean_inc_ref(v___y_2703_);
v___x_2711_ = lean_apply_4(v_onDidChange_2700_, v_p_2701_, v_a_2710_, v___y_2703_, lean_box(0));
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2729_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2714_ = v___x_2711_;
v_isShared_2715_ = v_isSharedCheck_2729_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2711_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2729_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v_snd_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2727_; 
v_snd_2716_ = lean_ctor_get(v_a_2712_, 1);
v_isSharedCheck_2727_ = !lean_is_exclusive(v_a_2712_);
if (v_isSharedCheck_2727_ == 0)
{
lean_object* v_unused_2728_; 
v_unused_2728_ = lean_ctor_get(v_a_2712_, 0);
lean_dec(v_unused_2728_);
v___x_2718_ = v_a_2712_;
v_isShared_2719_ = v_isSharedCheck_2727_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_snd_2716_);
lean_dec(v_a_2712_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2727_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2720_; lean_object* v___x_2722_; 
v___x_2720_ = lean_box(0);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v___x_2720_);
v___x_2722_ = v___x_2718_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2720_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v_snd_2716_);
v___x_2722_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
lean_object* v___x_2724_; 
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 0, v___x_2722_);
v___x_2724_ = v___x_2714_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
}
else
{
return v___x_2711_;
}
}
else
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2737_; 
lean_dec_ref(v_p_2701_);
lean_dec_ref(v_onDidChange_2700_);
v_a_2730_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2732_ = v___x_2709_;
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2709_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2733_ == 0)
{
v___x_2735_ = v___x_2732_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_dec_ref(v_p_2701_);
lean_dec_ref(v_onDidChange_2700_);
lean_dec(v_inst_2697_);
v_a_2738_ = lean_ctor_get(v___x_2706_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___x_2706_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2706_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object* v_inst_2746_, lean_object* v_pureOnDidChange_2747_, lean_object* v_method_2748_, lean_object* v_onDidChange_2749_, lean_object* v_p_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0(v_inst_2746_, v_pureOnDidChange_2747_, v_method_2748_, v_onDidChange_2749_, v_p_2750_, v___y_2751_, v___y_2752_);
lean_dec_ref(v___y_2752_);
lean_dec_ref(v_method_2748_);
return v_res_2754_;
}
}
static lean_object* _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2756_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__0));
v___x_2757_ = l_Lean_Server_RequestError_internalError(v___x_2756_);
return v___x_2757_;
}
}
static lean_object* _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__2));
v___x_2760_ = l_Lean_Server_RequestError_internalError(v___x_2759_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1(lean_object* v_inst_2761_, lean_object* v_inst_2762_, lean_object* v_pureHandle_2763_, lean_object* v_inst_2764_, lean_object* v_method_2765_, lean_object* v_handler_2766_, lean_object* v_p_2767_, lean_object* v_s_2768_, lean_object* v___y_2769_){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
lean_inc(v_p_2767_);
v___x_2771_ = lean_apply_1(v_inst_2761_, v_p_2767_);
lean_inc(v_inst_2762_);
v___x_2772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2772_, 0, v_inst_2762_);
lean_ctor_set(v___x_2772_, 1, v_s_2768_);
lean_inc_ref(v___y_2769_);
v___x_2773_ = lean_apply_4(v_pureHandle_2763_, v___x_2771_, v___x_2772_, v___y_2769_, lean_box(0));
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2808_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2776_ = v___x_2773_;
v_isShared_2777_ = v_isSharedCheck_2808_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2773_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2808_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v_fst_2778_; lean_object* v_snd_2779_; lean_object* v_response_x3f_2780_; lean_object* v_serialized_2781_; uint8_t v_isComplete_2782_; lean_object* v_a_2784_; 
v_fst_2778_ = lean_ctor_get(v_a_2774_, 0);
lean_inc(v_fst_2778_);
v_snd_2779_ = lean_ctor_get(v_a_2774_, 1);
lean_inc(v_snd_2779_);
lean_dec(v_a_2774_);
v_response_x3f_2780_ = lean_ctor_get(v_fst_2778_, 0);
lean_inc(v_response_x3f_2780_);
v_serialized_2781_ = lean_ctor_get(v_fst_2778_, 1);
lean_inc_ref(v_serialized_2781_);
v_isComplete_2782_ = lean_ctor_get_uint8(v_fst_2778_, sizeof(void*)*2);
lean_dec(v_fst_2778_);
if (lean_obj_tag(v_response_x3f_2780_) == 0)
{
lean_object* v___x_2803_; 
v___x_2803_ = l_Lean_Json_parse(v_serialized_2781_);
if (lean_obj_tag(v___x_2803_) == 1)
{
lean_object* v_a_2804_; 
v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
lean_inc(v_a_2804_);
lean_dec_ref_known(v___x_2803_, 1);
v_a_2784_ = v_a_2804_;
goto v___jp_2783_;
}
else
{
lean_object* v___x_2805_; lean_object* v___x_2806_; 
lean_dec_ref(v___x_2803_);
lean_dec(v_snd_2779_);
lean_del_object(v___x_2776_);
lean_dec(v_p_2767_);
lean_dec_ref(v_handler_2766_);
lean_dec_ref(v_inst_2764_);
lean_dec(v_inst_2762_);
v___x_2805_ = lean_obj_once(&l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3, &l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3_once, _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3);
v___x_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2805_);
return v___x_2806_;
}
}
else
{
lean_object* v_val_2807_; 
lean_dec_ref(v_serialized_2781_);
v_val_2807_ = lean_ctor_get(v_response_x3f_2780_, 0);
lean_inc(v_val_2807_);
lean_dec_ref_known(v_response_x3f_2780_, 1);
v_a_2784_ = v_val_2807_;
goto v___jp_2783_;
}
v___jp_2783_:
{
lean_object* v___x_2785_; 
v___x_2785_ = lean_apply_1(v_inst_2764_, v_a_2784_);
if (lean_obj_tag(v___x_2785_) == 1)
{
lean_object* v_a_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
lean_del_object(v___x_2776_);
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_a_2786_);
lean_dec_ref_known(v___x_2785_, 1);
v___x_2787_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2787_, 0, v_a_2786_);
lean_ctor_set_uint8(v___x_2787_, sizeof(void*)*1, v_isComplete_2782_);
v___x_2788_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_2765_, v_snd_2779_, v_inst_2762_);
lean_dec(v_inst_2762_);
lean_dec(v_snd_2779_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2790_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___x_2788_, 1);
lean_inc_ref(v___y_2769_);
v___x_2790_ = lean_apply_5(v_handler_2766_, v_p_2767_, v___x_2787_, v_a_2789_, v___y_2769_, lean_box(0));
return v___x_2790_;
}
else
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
lean_dec_ref_known(v___x_2787_, 1);
lean_dec(v_p_2767_);
lean_dec_ref(v_handler_2766_);
v_a_2791_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___x_2788_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2788_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
else
{
lean_object* v___x_2799_; lean_object* v___x_2801_; 
lean_dec_ref(v___x_2785_);
lean_dec(v_snd_2779_);
lean_dec(v_p_2767_);
lean_dec_ref(v_handler_2766_);
lean_dec(v_inst_2762_);
v___x_2799_ = lean_obj_once(&l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1, &l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1_once, _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1);
if (v_isShared_2777_ == 0)
{
lean_ctor_set_tag(v___x_2776_, 1);
lean_ctor_set(v___x_2776_, 0, v___x_2799_);
v___x_2801_ = v___x_2776_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2799_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
lean_dec(v_p_2767_);
lean_dec_ref(v_handler_2766_);
lean_dec_ref(v_inst_2764_);
lean_dec(v_inst_2762_);
v_a_2809_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2773_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2773_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___boxed(lean_object* v_inst_2817_, lean_object* v_inst_2818_, lean_object* v_pureHandle_2819_, lean_object* v_inst_2820_, lean_object* v_method_2821_, lean_object* v_handler_2822_, lean_object* v_p_2823_, lean_object* v_s_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
lean_object* v_res_2827_; 
v_res_2827_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1(v_inst_2817_, v_inst_2818_, v_pureHandle_2819_, v_inst_2820_, v_method_2821_, v_handler_2822_, v_p_2823_, v_s_2824_, v___y_2825_);
lean_dec_ref(v___y_2825_);
lean_dec_ref(v_method_2821_);
return v_res_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg(lean_object* v_method_2829_, lean_object* v_inst_2830_, lean_object* v_inst_2831_, lean_object* v_inst_2832_, lean_object* v_inst_2833_, lean_object* v_inst_2834_, lean_object* v_inst_2835_, lean_object* v_handler_2836_, lean_object* v_onDidChange_2837_){
_start:
{
uint8_t v___x_2839_; 
v___x_2839_ = l_Lean_initializing();
if (v___x_2839_ == 0)
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
lean_dec_ref(v_onDidChange_2837_);
lean_dec_ref(v_handler_2836_);
lean_dec(v_inst_2835_);
lean_dec_ref(v_inst_2834_);
lean_dec_ref(v_inst_2833_);
lean_dec_ref(v_inst_2832_);
lean_dec_ref(v_inst_2831_);
lean_dec_ref(v_inst_2830_);
v___x_2840_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0));
v___x_2841_ = lean_string_append(v___x_2840_, v_method_2829_);
lean_dec_ref(v_method_2829_);
v___x_2842_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___x_2843_ = lean_string_append(v___x_2841_, v___x_2842_);
v___x_2844_ = lean_mk_io_user_error(v___x_2843_);
v___x_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2844_);
return v___x_2845_;
}
else
{
lean_object* v___x_2846_; 
v___x_2846_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_2829_);
if (lean_obj_tag(v___x_2846_) == 1)
{
lean_object* v_val_2847_; lean_object* v_pureHandle_2848_; lean_object* v_pureOnDidChange_2849_; lean_object* v_initState_2850_; lean_object* v_completeness_2851_; lean_object* v___f_2852_; lean_object* v___f_2853_; lean_object* v___x_2854_; 
v_val_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_val_2847_);
lean_dec_ref_known(v___x_2846_, 1);
v_pureHandle_2848_ = lean_ctor_get(v_val_2847_, 1);
lean_inc_ref(v_pureHandle_2848_);
v_pureOnDidChange_2849_ = lean_ctor_get(v_val_2847_, 3);
lean_inc_ref(v_pureOnDidChange_2849_);
v_initState_2850_ = lean_ctor_get(v_val_2847_, 6);
lean_inc(v_initState_2850_);
v_completeness_2851_ = lean_ctor_get(v_val_2847_, 8);
lean_inc(v_completeness_2851_);
lean_dec(v_val_2847_);
lean_inc_ref_n(v_method_2829_, 2);
lean_inc_n(v_inst_2835_, 2);
v___f_2852_ = lean_alloc_closure((void*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_2852_, 0, v_inst_2835_);
lean_closure_set(v___f_2852_, 1, v_pureOnDidChange_2849_);
lean_closure_set(v___f_2852_, 2, v_method_2829_);
lean_closure_set(v___f_2852_, 3, v_onDidChange_2837_);
v___f_2853_ = lean_alloc_closure((void*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___boxed), 10, 6);
lean_closure_set(v___f_2853_, 0, v_inst_2831_);
lean_closure_set(v___f_2853_, 1, v_inst_2835_);
lean_closure_set(v___f_2853_, 2, v_pureHandle_2848_);
lean_closure_set(v___f_2853_, 3, v_inst_2833_);
lean_closure_set(v___f_2853_, 4, v_method_2829_);
lean_closure_set(v___f_2853_, 5, v_handler_2836_);
v___x_2854_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(v_method_2829_, v_initState_2850_, v_inst_2835_);
lean_dec(v_initState_2850_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2856_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2855_);
lean_dec_ref_known(v___x_2854_, 1);
v___x_2856_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2829_, v_completeness_2851_, v_inst_2830_, v_inst_2832_, v_inst_2834_, v_inst_2835_, v_a_2855_, v___f_2853_, v___f_2852_);
return v___x_2856_;
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_dec_ref(v___f_2853_);
lean_dec_ref(v___f_2852_);
lean_dec(v_completeness_2851_);
lean_dec(v_inst_2835_);
lean_dec_ref(v_inst_2834_);
lean_dec_ref(v_inst_2832_);
lean_dec_ref(v_inst_2830_);
lean_dec_ref(v_method_2829_);
v_a_2857_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2854_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2854_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2857_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
}
else
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
lean_dec(v___x_2846_);
lean_dec_ref(v_onDidChange_2837_);
lean_dec_ref(v_handler_2836_);
lean_dec(v_inst_2835_);
lean_dec_ref(v_inst_2834_);
lean_dec_ref(v_inst_2833_);
lean_dec_ref(v_inst_2832_);
lean_dec_ref(v_inst_2831_);
lean_dec_ref(v_inst_2830_);
v___x_2865_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0));
v___x_2866_ = lean_string_append(v___x_2865_, v_method_2829_);
lean_dec_ref(v_method_2829_);
v___x_2867_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__1));
v___x_2868_ = lean_string_append(v___x_2866_, v___x_2867_);
v___x_2869_ = lean_mk_io_user_error(v___x_2868_);
v___x_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2869_);
return v___x_2870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2871_, lean_object* v_inst_2872_, lean_object* v_inst_2873_, lean_object* v_inst_2874_, lean_object* v_inst_2875_, lean_object* v_inst_2876_, lean_object* v_inst_2877_, lean_object* v_handler_2878_, lean_object* v_onDidChange_2879_, lean_object* v_a_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg(v_method_2871_, v_inst_2872_, v_inst_2873_, v_inst_2874_, v_inst_2875_, v_inst_2876_, v_inst_2877_, v_handler_2878_, v_onDidChange_2879_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler(lean_object* v_method_2882_, lean_object* v_paramType_2883_, lean_object* v_inst_2884_, lean_object* v_inst_2885_, lean_object* v_inst_2886_, lean_object* v_respType_2887_, lean_object* v_inst_2888_, lean_object* v_inst_2889_, lean_object* v_stateType_2890_, lean_object* v_inst_2891_, lean_object* v_handler_2892_, lean_object* v_onDidChange_2893_){
_start:
{
lean_object* v___x_2895_; 
v___x_2895_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg(v_method_2882_, v_inst_2884_, v_inst_2885_, v_inst_2886_, v_inst_2888_, v_inst_2889_, v_inst_2891_, v_handler_2892_, v_onDidChange_2893_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___boxed(lean_object* v_method_2896_, lean_object* v_paramType_2897_, lean_object* v_inst_2898_, lean_object* v_inst_2899_, lean_object* v_inst_2900_, lean_object* v_respType_2901_, lean_object* v_inst_2902_, lean_object* v_inst_2903_, lean_object* v_stateType_2904_, lean_object* v_inst_2905_, lean_object* v_handler_2906_, lean_object* v_onDidChange_2907_, lean_object* v_a_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l_Lean_Server_chainStatefulLspRequestHandler(v_method_2896_, v_paramType_2897_, v_inst_2898_, v_inst_2899_, v_inst_2900_, v_respType_2901_, v_inst_2902_, v_inst_2903_, v_stateType_2904_, v_inst_2905_, v_handler_2906_, v_onDidChange_2907_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___lam__0(lean_object* v_p_2910_, lean_object* v_x_2911_, lean_object* v_handler_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v_onDidChange_2915_; lean_object* v___x_2916_; 
v_onDidChange_2915_ = lean_ctor_get(v_handler_2912_, 4);
lean_inc_ref(v_onDidChange_2915_);
lean_dec_ref(v_handler_2912_);
lean_inc_ref(v___y_2913_);
v___x_2916_ = lean_apply_3(v_onDidChange_2915_, v_p_2910_, v___y_2913_, lean_box(0));
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___lam__0___boxed(lean_object* v_p_2917_, lean_object* v_x_2918_, lean_object* v_handler_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
lean_object* v_res_2922_; 
v_res_2922_ = l_Lean_Server_handleOnDidChange___lam__0(v_p_2917_, v_x_2918_, v_handler_2919_, v___y_2920_);
lean_dec_ref(v___y_2920_);
lean_dec_ref(v_x_2918_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0(lean_object* v_f_2923_, lean_object* v_x_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v___x_2929_; 
lean_inc_ref(v___y_2927_);
v___x_2929_ = lean_apply_4(v_f_2923_, v___y_2925_, v___y_2926_, v___y_2927_, lean_box(0));
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0___boxed(lean_object* v_f_2930_, lean_object* v_x_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0(v_f_2930_, v_x_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
lean_dec_ref(v___y_2934_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_2937_, lean_object* v_keys_2938_, lean_object* v_vals_2939_, lean_object* v_i_2940_, lean_object* v_acc_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v___x_2944_; uint8_t v___x_2945_; 
v___x_2944_ = lean_array_get_size(v_keys_2938_);
v___x_2945_ = lean_nat_dec_lt(v_i_2940_, v___x_2944_);
if (v___x_2945_ == 0)
{
lean_object* v___x_2946_; 
lean_dec(v_i_2940_);
lean_dec_ref(v_f_2937_);
v___x_2946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2946_, 0, v_acc_2941_);
return v___x_2946_;
}
else
{
lean_object* v_k_2947_; lean_object* v_v_2948_; lean_object* v___x_2949_; 
v_k_2947_ = lean_array_fget_borrowed(v_keys_2938_, v_i_2940_);
v_v_2948_ = lean_array_fget_borrowed(v_vals_2939_, v_i_2940_);
lean_inc_ref(v_f_2937_);
lean_inc_ref(v___y_2942_);
lean_inc(v_v_2948_);
lean_inc(v_k_2947_);
v___x_2949_ = lean_apply_5(v_f_2937_, v_acc_2941_, v_k_2947_, v_v_2948_, v___y_2942_, lean_box(0));
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2950_);
lean_dec_ref_known(v___x_2949_, 1);
v___x_2951_ = lean_unsigned_to_nat(1u);
v___x_2952_ = lean_nat_add(v_i_2940_, v___x_2951_);
lean_dec(v_i_2940_);
v_i_2940_ = v___x_2952_;
v_acc_2941_ = v_a_2950_;
goto _start;
}
else
{
lean_dec(v_i_2940_);
lean_dec_ref(v_f_2937_);
return v___x_2949_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_2954_, lean_object* v_keys_2955_, lean_object* v_vals_2956_, lean_object* v_i_2957_, lean_object* v_acc_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2954_, v_keys_2955_, v_vals_2956_, v_i_2957_, v_acc_2958_, v___y_2959_);
lean_dec_ref(v___y_2959_);
lean_dec_ref(v_vals_2956_);
lean_dec_ref(v_keys_2955_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_2962_, lean_object* v_as_2963_, size_t v_i_2964_, size_t v_stop_2965_, lean_object* v_b_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_a_2970_; lean_object* v___y_2975_; uint8_t v___x_2977_; 
v___x_2977_ = lean_usize_dec_eq(v_i_2964_, v_stop_2965_);
if (v___x_2977_ == 0)
{
lean_object* v___x_2978_; 
v___x_2978_ = lean_array_uget_borrowed(v_as_2963_, v_i_2964_);
switch(lean_obj_tag(v___x_2978_))
{
case 0:
{
lean_object* v_key_2979_; lean_object* v_val_2980_; lean_object* v___x_2981_; 
v_key_2979_ = lean_ctor_get(v___x_2978_, 0);
v_val_2980_ = lean_ctor_get(v___x_2978_, 1);
lean_inc_ref(v_f_2962_);
lean_inc_ref(v___y_2967_);
lean_inc(v_val_2980_);
lean_inc(v_key_2979_);
v___x_2981_ = lean_apply_5(v_f_2962_, v_b_2966_, v_key_2979_, v_val_2980_, v___y_2967_, lean_box(0));
v___y_2975_ = v___x_2981_;
goto v___jp_2974_;
}
case 1:
{
lean_object* v_node_2982_; lean_object* v___x_2983_; 
v_node_2982_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_node_2982_);
lean_inc_ref(v_f_2962_);
v___x_2983_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_2962_, v_node_2982_, v_b_2966_, v___y_2967_);
v___y_2975_ = v___x_2983_;
goto v___jp_2974_;
}
default: 
{
v_a_2970_ = v_b_2966_;
goto v___jp_2969_;
}
}
}
else
{
lean_object* v___x_2984_; 
lean_dec_ref(v_f_2962_);
v___x_2984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2984_, 0, v_b_2966_);
return v___x_2984_;
}
v___jp_2969_:
{
size_t v___x_2971_; size_t v___x_2972_; 
v___x_2971_ = ((size_t)1ULL);
v___x_2972_ = lean_usize_add(v_i_2964_, v___x_2971_);
v_i_2964_ = v___x_2972_;
v_b_2966_ = v_a_2970_;
goto _start;
}
v___jp_2974_:
{
if (lean_obj_tag(v___y_2975_) == 0)
{
lean_object* v_a_2976_; 
v_a_2976_ = lean_ctor_get(v___y_2975_, 0);
lean_inc(v_a_2976_);
lean_dec_ref_known(v___y_2975_, 1);
v_a_2970_ = v_a_2976_;
goto v___jp_2969_;
}
else
{
lean_dec_ref(v_f_2962_);
return v___y_2975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2985_, lean_object* v_x_2986_, lean_object* v_x_2987_, lean_object* v___y_2988_){
_start:
{
if (lean_obj_tag(v_x_2986_) == 0)
{
lean_object* v_es_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3003_; 
v_es_2990_ = lean_ctor_get(v_x_2986_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v_x_2986_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2992_ = v_x_2986_;
v_isShared_2993_ = v_isSharedCheck_3003_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_es_2990_);
lean_dec(v_x_2986_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3003_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; uint8_t v___x_2996_; 
v___x_2994_ = lean_unsigned_to_nat(0u);
v___x_2995_ = lean_array_get_size(v_es_2990_);
v___x_2996_ = lean_nat_dec_lt(v___x_2994_, v___x_2995_);
if (v___x_2996_ == 0)
{
lean_object* v___x_2998_; 
lean_dec_ref(v_es_2990_);
lean_dec_ref(v_f_2985_);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 0, v_x_2987_);
v___x_2998_ = v___x_2992_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_x_2987_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
else
{
size_t v___x_3000_; size_t v___x_3001_; lean_object* v___x_3002_; 
lean_del_object(v___x_2992_);
v___x_3000_ = ((size_t)0ULL);
v___x_3001_ = lean_usize_of_nat(v___x_2995_);
v___x_3002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2985_, v_es_2990_, v___x_3000_, v___x_3001_, v_x_2987_, v___y_2988_);
lean_dec_ref(v_es_2990_);
return v___x_3002_;
}
}
}
else
{
lean_object* v_ks_3004_; lean_object* v_vs_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v_ks_3004_ = lean_ctor_get(v_x_2986_, 0);
lean_inc_ref(v_ks_3004_);
v_vs_3005_ = lean_ctor_get(v_x_2986_, 1);
lean_inc_ref(v_vs_3005_);
lean_dec_ref_known(v_x_2986_, 2);
v___x_3006_ = lean_unsigned_to_nat(0u);
v___x_3007_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2985_, v_ks_3004_, v_vs_3005_, v___x_3006_, v_x_2987_, v___y_2988_);
lean_dec_ref(v_vs_3005_);
lean_dec_ref(v_ks_3004_);
return v___x_3007_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_3008_, lean_object* v_x_3009_, lean_object* v_x_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3008_, v_x_3009_, v_x_3010_, v___y_3011_);
lean_dec_ref(v___y_3011_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_3014_, lean_object* v_as_3015_, lean_object* v_i_3016_, lean_object* v_stop_3017_, lean_object* v_b_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
size_t v_i_boxed_3021_; size_t v_stop_boxed_3022_; lean_object* v_res_3023_; 
v_i_boxed_3021_ = lean_unbox_usize(v_i_3016_);
lean_dec(v_i_3016_);
v_stop_boxed_3022_ = lean_unbox_usize(v_stop_3017_);
lean_dec(v_stop_3017_);
v_res_3023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3014_, v_as_3015_, v_i_boxed_3021_, v_stop_boxed_3022_, v_b_3018_, v___y_3019_);
lean_dec_ref(v___y_3019_);
lean_dec_ref(v_as_3015_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(lean_object* v_map_3024_, lean_object* v_f_3025_, lean_object* v___y_3026_){
_start:
{
lean_object* v___f_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___f_3028_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3028_, 0, v_f_3025_);
v___x_3029_ = lean_box(0);
v___x_3030_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v___f_3028_, v_map_3024_, v___x_3029_, v___y_3026_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___boxed(lean_object* v_map_3031_, lean_object* v_f_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(v_map_3031_, v_f_3032_, v___y_3033_);
lean_dec_ref(v___y_3033_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange(lean_object* v_p_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v___f_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___f_3039_ = lean_alloc_closure((void*)(l_Lean_Server_handleOnDidChange___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3039_, 0, v_p_3036_);
v___x_3040_ = l_Lean_Server_statefulRequestHandlers;
v___x_3041_ = lean_st_ref_get(v___x_3040_);
v___x_3042_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(v___x_3041_, v___f_3039_, v_a_3037_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___boxed(lean_object* v_p_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_){
_start:
{
lean_object* v_res_3046_; 
v_res_3046_ = l_Lean_Server_handleOnDidChange(v_p_3043_, v_a_3044_);
lean_dec_ref(v_a_3044_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0(lean_object* v_00_u03b2_3047_, lean_object* v_map_3048_, lean_object* v_f_3049_, lean_object* v___y_3050_){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(v_map_3048_, v_f_3049_, v___y_3050_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___boxed(lean_object* v_00_u03b2_3053_, lean_object* v_map_3054_, lean_object* v_f_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0(v_00_u03b2_3053_, v_map_3054_, v_f_3055_, v___y_3056_);
lean_dec_ref(v___y_3056_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg(lean_object* v_map_3059_, lean_object* v_f_3060_, lean_object* v_init_3061_, lean_object* v___y_3062_){
_start:
{
lean_object* v___x_3064_; 
v___x_3064_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3060_, v_map_3059_, v_init_3061_, v___y_3062_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg___boxed(lean_object* v_map_3065_, lean_object* v_f_3066_, lean_object* v_init_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg(v_map_3065_, v_f_3066_, v_init_3067_, v___y_3068_);
lean_dec_ref(v___y_3068_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0(lean_object* v_00_u03c3_3071_, lean_object* v_00_u03b2_3072_, lean_object* v_map_3073_, lean_object* v_f_3074_, lean_object* v_init_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v___x_3078_; 
v___x_3078_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3074_, v_map_3073_, v_init_3075_, v___y_3076_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3079_, lean_object* v_00_u03b2_3080_, lean_object* v_map_3081_, lean_object* v_f_3082_, lean_object* v_init_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0(v_00_u03c3_3079_, v_00_u03b2_3080_, v_map_3081_, v_f_3082_, v_init_3083_, v___y_3084_);
lean_dec_ref(v___y_3084_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3087_, lean_object* v_00_u03b1_3088_, lean_object* v_00_u03b2_3089_, lean_object* v_f_3090_, lean_object* v_x_3091_, lean_object* v_x_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v___x_3095_; 
v___x_3095_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3090_, v_x_3091_, v_x_3092_, v___y_3093_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3096_, lean_object* v_00_u03b1_3097_, lean_object* v_00_u03b2_3098_, lean_object* v_f_3099_, lean_object* v_x_3100_, lean_object* v_x_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
lean_object* v_res_3104_; 
v_res_3104_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1(v_00_u03c3_3096_, v_00_u03b1_3097_, v_00_u03b2_3098_, v_f_3099_, v_x_3100_, v_x_3101_, v___y_3102_);
lean_dec_ref(v___y_3102_);
return v_res_3104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3105_, lean_object* v_00_u03b2_3106_, lean_object* v_00_u03c3_3107_, lean_object* v_f_3108_, lean_object* v_as_3109_, size_t v_i_3110_, size_t v_stop_3111_, lean_object* v_b_3112_, lean_object* v___y_3113_){
_start:
{
lean_object* v___x_3115_; 
v___x_3115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3108_, v_as_3109_, v_i_3110_, v_stop_3111_, v_b_3112_, v___y_3113_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3116_, lean_object* v_00_u03b2_3117_, lean_object* v_00_u03c3_3118_, lean_object* v_f_3119_, lean_object* v_as_3120_, lean_object* v_i_3121_, lean_object* v_stop_3122_, lean_object* v_b_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
size_t v_i_boxed_3126_; size_t v_stop_boxed_3127_; lean_object* v_res_3128_; 
v_i_boxed_3126_ = lean_unbox_usize(v_i_3121_);
lean_dec(v_i_3121_);
v_stop_boxed_3127_ = lean_unbox_usize(v_stop_3122_);
lean_dec(v_stop_3122_);
v_res_3128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3116_, v_00_u03b2_3117_, v_00_u03c3_3118_, v_f_3119_, v_as_3120_, v_i_boxed_3126_, v_stop_boxed_3127_, v_b_3123_, v___y_3124_);
lean_dec_ref(v___y_3124_);
lean_dec_ref(v_as_3120_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3129_, lean_object* v_00_u03b1_3130_, lean_object* v_00_u03b2_3131_, lean_object* v_f_3132_, lean_object* v_keys_3133_, lean_object* v_vals_3134_, lean_object* v_heq_3135_, lean_object* v_i_3136_, lean_object* v_acc_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v___x_3140_; 
v___x_3140_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3132_, v_keys_3133_, v_vals_3134_, v_i_3136_, v_acc_3137_, v___y_3138_);
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3141_, lean_object* v_00_u03b1_3142_, lean_object* v_00_u03b2_3143_, lean_object* v_f_3144_, lean_object* v_keys_3145_, lean_object* v_vals_3146_, lean_object* v_heq_3147_, lean_object* v_i_3148_, lean_object* v_acc_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_){
_start:
{
lean_object* v_res_3152_; 
v_res_3152_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3141_, v_00_u03b1_3142_, v_00_u03b2_3143_, v_f_3144_, v_keys_3145_, v_vals_3146_, v_heq_3147_, v_i_3148_, v_acc_3149_, v___y_3150_);
lean_dec_ref(v___y_3150_);
lean_dec_ref(v_vals_3146_);
lean_dec_ref(v_keys_3145_);
return v_res_3152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest(lean_object* v_method_3155_, lean_object* v_params_3156_, lean_object* v_a_3157_){
_start:
{
uint8_t v___x_3159_; 
v___x_3159_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_3155_);
if (v___x_3159_ == 0)
{
lean_object* v___x_3160_; lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3176_; 
v___x_3160_ = l_Lean_Server_lookupLspRequestHandler(v_method_3155_);
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3163_ = v___x_3160_;
v_isShared_3164_ = v_isSharedCheck_3176_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3160_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3176_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
if (lean_obj_tag(v_a_3161_) == 0)
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3171_; 
lean_dec(v_params_3156_);
v___x_3165_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__0));
v___x_3166_ = lean_string_append(v___x_3165_, v_method_3155_);
v___x_3167_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__1));
v___x_3168_ = lean_string_append(v___x_3166_, v___x_3167_);
v___x_3169_ = l_Lean_Server_RequestError_internalError(v___x_3168_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set_tag(v___x_3163_, 1);
lean_ctor_set(v___x_3163_, 0, v___x_3169_);
v___x_3171_ = v___x_3163_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3169_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
else
{
lean_object* v_val_3173_; lean_object* v_handle_3174_; lean_object* v___x_3175_; 
lean_del_object(v___x_3163_);
v_val_3173_ = lean_ctor_get(v_a_3161_, 0);
lean_inc(v_val_3173_);
lean_dec_ref_known(v_a_3161_, 1);
v_handle_3174_ = lean_ctor_get(v_val_3173_, 1);
lean_inc_ref(v_handle_3174_);
lean_dec(v_val_3173_);
lean_inc_ref(v_a_3157_);
v___x_3175_ = lean_apply_3(v_handle_3174_, v_params_3156_, v_a_3157_, lean_box(0));
return v___x_3175_;
}
}
}
else
{
lean_object* v___x_3177_; 
v___x_3177_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_3155_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
lean_dec(v_params_3156_);
v___x_3178_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__0));
v___x_3179_ = lean_string_append(v___x_3178_, v_method_3155_);
v___x_3180_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__1));
v___x_3181_ = lean_string_append(v___x_3179_, v___x_3180_);
v___x_3182_ = l_Lean_Server_RequestError_internalError(v___x_3181_);
v___x_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
return v___x_3183_;
}
else
{
lean_object* v_val_3184_; lean_object* v_handle_3185_; lean_object* v___x_3186_; 
v_val_3184_ = lean_ctor_get(v___x_3177_, 0);
lean_inc(v_val_3184_);
lean_dec_ref_known(v___x_3177_, 1);
v_handle_3185_ = lean_ctor_get(v_val_3184_, 2);
lean_inc_ref(v_handle_3185_);
lean_dec(v_val_3184_);
lean_inc_ref(v_a_3157_);
v___x_3186_ = lean_apply_3(v_handle_3185_, v_params_3156_, v_a_3157_, lean_box(0));
return v___x_3186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest___boxed(lean_object* v_method_3187_, lean_object* v_params_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l_Lean_Server_handleLspRequest(v_method_3187_, v_params_3188_, v_a_3189_);
lean_dec_ref(v_a_3189_);
lean_dec_ref(v_method_3187_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_routeLspRequest(lean_object* v_method_3192_, lean_object* v_params_3193_){
_start:
{
uint8_t v___x_3195_; 
v___x_3195_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_3192_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3212_; 
v___x_3196_ = l_Lean_Server_lookupLspRequestHandler(v_method_3192_);
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3199_ = v___x_3196_;
v_isShared_3200_ = v_isSharedCheck_3212_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3196_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3212_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
if (lean_obj_tag(v_a_3197_) == 0)
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3204_; 
lean_dec(v_params_3193_);
v___x_3201_ = l_Lean_Server_RequestError_methodNotFound(v_method_3192_);
v___x_3202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3201_);
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 0, v___x_3202_);
v___x_3204_ = v___x_3199_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3202_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
else
{
lean_object* v_val_3206_; lean_object* v_fileSource_3207_; lean_object* v___x_3208_; lean_object* v___x_3210_; 
v_val_3206_ = lean_ctor_get(v_a_3197_, 0);
lean_inc(v_val_3206_);
lean_dec_ref_known(v_a_3197_, 1);
v_fileSource_3207_ = lean_ctor_get(v_val_3206_, 0);
lean_inc_ref(v_fileSource_3207_);
lean_dec(v_val_3206_);
v___x_3208_ = lean_apply_1(v_fileSource_3207_, v_params_3193_);
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 0, v___x_3208_);
v___x_3210_ = v___x_3199_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3208_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
}
else
{
lean_object* v___x_3213_; 
v___x_3213_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_3192_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
lean_dec(v_params_3193_);
v___x_3214_ = l_Lean_Server_RequestError_methodNotFound(v_method_3192_);
v___x_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3214_);
v___x_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3215_);
return v___x_3216_;
}
else
{
lean_object* v_val_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3226_; 
v_val_3217_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3219_ = v___x_3213_;
v_isShared_3220_ = v_isSharedCheck_3226_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_val_3217_);
lean_dec(v___x_3213_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3226_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v_fileSource_3221_; lean_object* v___x_3222_; lean_object* v___x_3224_; 
v_fileSource_3221_ = lean_ctor_get(v_val_3217_, 0);
lean_inc_ref(v_fileSource_3221_);
lean_dec(v_val_3217_);
v___x_3222_ = lean_apply_1(v_fileSource_3221_, v_params_3193_);
if (v_isShared_3220_ == 0)
{
lean_ctor_set_tag(v___x_3219_, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3222_);
v___x_3224_ = v___x_3219_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3222_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_routeLspRequest___boxed(lean_object* v_method_3227_, lean_object* v_params_3228_, lean_object* v_a_3229_){
_start:
{
lean_object* v_res_3230_; 
v_res_3230_ = l_Lean_Server_routeLspRequest(v_method_3227_, v_params_3228_);
lean_dec_ref(v_method_3227_);
return v_res_3230_;
}
}
lean_object* runtime_initialize_Lean_Server_RequestCancellation(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_FileSource(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_FileWorker_Utils(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_Mutex(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Requests(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
