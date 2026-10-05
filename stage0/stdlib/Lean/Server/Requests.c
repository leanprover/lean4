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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___impl___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___impl___redArg(lean_object* v_x_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lean_obj_tag_nat(v_x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___impl___redArg___boxed(lean_object* v_x_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lean_Server_ServerRequestResponse_ctorIdx___impl___redArg(v_x_94_);
lean_dec_ref(v_x_94_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___impl(lean_object* v_00_u03b1_96_, lean_object* v_x_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_obj_tag_nat(v_x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___impl___boxed(lean_object* v_00_u03b1_99_, lean_object* v_x_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_Server_ServerRequestResponse_ctorIdx___impl(v_00_u03b1_99_, v_x_100_);
lean_dec_ref(v_x_100_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorElim___redArg(lean_object* v_t_102_, lean_object* v_k_103_){
_start:
{
if (lean_obj_tag(v_t_102_) == 0)
{
lean_object* v_response_104_; lean_object* v___x_105_; 
v_response_104_ = lean_ctor_get(v_t_102_, 0);
lean_inc(v_response_104_);
lean_dec_ref_known(v_t_102_, 1);
v___x_105_ = lean_apply_1(v_k_103_, v_response_104_);
return v___x_105_;
}
else
{
uint8_t v_code_106_; lean_object* v_message_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v_code_106_ = lean_ctor_get_uint8(v_t_102_, sizeof(void*)*1);
v_message_107_ = lean_ctor_get(v_t_102_, 0);
lean_inc_ref(v_message_107_);
lean_dec_ref_known(v_t_102_, 1);
v___x_108_ = lean_box(v_code_106_);
v___x_109_ = lean_apply_2(v_k_103_, v___x_108_, v_message_107_);
return v___x_109_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorElim(lean_object* v_00_u03b1_110_, lean_object* v_motive_111_, lean_object* v_ctorIdx_112_, lean_object* v_t_113_, lean_object* v_h_114_, lean_object* v_k_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_113_, v_k_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorElim___boxed(lean_object* v_00_u03b1_117_, lean_object* v_motive_118_, lean_object* v_ctorIdx_119_, lean_object* v_t_120_, lean_object* v_h_121_, lean_object* v_k_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lean_Server_ServerRequestResponse_ctorElim(v_00_u03b1_117_, v_motive_118_, v_ctorIdx_119_, v_t_120_, v_h_121_, v_k_122_);
lean_dec(v_ctorIdx_119_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_success_elim___redArg(lean_object* v_t_124_, lean_object* v_success_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_124_, v_success_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_success_elim(lean_object* v_00_u03b1_127_, lean_object* v_motive_128_, lean_object* v_t_129_, lean_object* v_h_130_, lean_object* v_success_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_129_, v_success_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_failure_elim___redArg(lean_object* v_t_133_, lean_object* v_failure_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_133_, v_failure_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_failure_elim(lean_object* v_00_u03b1_136_, lean_object* v_motive_137_, lean_object* v_t_138_, lean_object* v_h_139_, lean_object* v_failure_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_138_, v_failure_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse_default___redArg(){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = ((lean_object*)(l_Lean_Server_instInhabitedServerRequestResponse_default___redArg___closed__0));
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse_default___redArg___boxed(lean_object* v___dummy_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_Server_instInhabitedServerRequestResponse_default___redArg();
return v_res_148_;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0(void){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_Server_instInhabitedServerRequestResponse_default___redArg();
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse_default(lean_object* v_00_u03b1_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_obj_once(&l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0, &l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0_once, _init_l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse___redArg(){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = lean_obj_once(&l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0, &l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0_once, _init_l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse___redArg___boxed(lean_object* v___dummy_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_Server_instInhabitedServerRequestResponse___redArg();
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse(lean_object* v_a_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = lean_obj_once(&l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0, &l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0_once, _init_l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run___redArg(lean_object* v_act_158_, lean_object* v_rc_159_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = lean_apply_2(v_act_158_, v_rc_159_, lean_box(0));
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run___redArg___boxed(lean_object* v_act_162_, lean_object* v_rc_163_, lean_object* v_a_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_Server_RequestM_run___redArg(v_act_162_, v_rc_163_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run(lean_object* v_00_u03b1_166_, lean_object* v_act_167_, lean_object* v_rc_168_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lean_apply_2(v_act_167_, v_rc_168_, lean_box(0));
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run___boxed(lean_object* v_00_u03b1_171_, lean_object* v_act_172_, lean_object* v_rc_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_Server_RequestM_run(v_00_u03b1_171_, v_act_172_, v_rc_173_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestTask_pure___redArg(lean_object* v_a_176_){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_177_, 0, v_a_176_);
v___x_178_ = lean_task_pure(v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestTask_pure(lean_object* v_00_u03b1_179_, lean_object* v_a_180_){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_181_, 0, v_a_180_);
v___x_182_ = lean_task_pure(v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM___lam__0(lean_object* v_00_u03b1_183_, lean_object* v_x_184_, lean_object* v___y_185_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = lean_apply_1(v_x_184_, lean_box(0));
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_195_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_195_ == 0)
{
v___x_190_ = v___x_187_;
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_187_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_a_188_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_204_; 
v_a_196_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_204_ == 0)
{
v___x_198_ = v___x_187_;
v_isShared_199_ = v_isSharedCheck_204_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_187_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_204_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_200_ = l_Lean_Server_RequestError_ofIoError(v_a_196_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 0, v___x_200_);
v___x_202_ = v___x_198_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_200_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM___lam__0___boxed(lean_object* v_00_u03b1_205_, lean_object* v_x_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Server_instMonadLiftIORequestM___lam__0(v_00_u03b1_205_, v_x_206_, v___y_207_);
lean_dec_ref(v___y_207_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0(lean_object* v_00_u03b1_212_, lean_object* v_x_213_, lean_object* v___y_214_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = lean_apply_1(v_x_213_, lean_box(0));
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_224_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_224_ == 0)
{
v___x_219_ = v___x_216_;
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_216_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_222_; 
if (v_isShared_220_ == 0)
{
v___x_222_ = v___x_219_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_a_217_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
else
{
lean_object* v_a_225_; lean_object* v___x_226_; lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
v_a_225_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_a_225_);
lean_dec_ref_known(v___x_216_, 1);
v___x_226_ = l_Lean_Server_RequestError_ofException(v_a_225_);
v_a_227_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v___x_226_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_226_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
lean_ctor_set_tag(v___x_229_, 1);
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_227_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0___boxed(lean_object* v_00_u03b1_235_, lean_object* v_x_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0(v_00_u03b1_235_, v_x_236_, v___y_237_);
lean_dec_ref(v___y_237_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0(lean_object* v_00_u03b1_242_, lean_object* v_x_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_cancelTk_246_; lean_object* v___x_247_; 
v_cancelTk_246_ = lean_ctor_get(v___y_244_, 4);
lean_inc_ref(v_cancelTk_246_);
v___x_247_ = lean_apply_2(v_x_243_, v_cancelTk_246_, lean_box(0));
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_260_; 
v_a_248_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_260_ == 0)
{
v___x_250_ = v___x_247_;
v_isShared_251_ = v_isSharedCheck_260_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_247_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_260_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
if (lean_obj_tag(v_a_248_) == 0)
{
lean_object* v___x_252_; lean_object* v___x_254_; 
lean_dec_ref_known(v_a_248_, 1);
v___x_252_ = ((lean_object*)(l_Lean_Server_RequestError_requestCancelled));
if (v_isShared_251_ == 0)
{
lean_ctor_set_tag(v___x_250_, 1);
lean_ctor_set(v___x_250_, 0, v___x_252_);
v___x_254_ = v___x_250_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_252_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
else
{
lean_object* v_a_256_; lean_object* v___x_258_; 
v_a_256_ = lean_ctor_get(v_a_248_, 0);
lean_inc(v_a_256_);
lean_dec_ref_known(v_a_248_, 1);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 0, v_a_256_);
v___x_258_ = v___x_250_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_269_; 
v_a_261_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_269_ == 0)
{
v___x_263_ = v___x_247_;
v_isShared_264_ = v_isSharedCheck_269_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_247_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_269_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_265_ = l_Lean_Server_RequestError_ofIoError(v_a_261_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 0, v___x_265_);
v___x_267_ = v___x_263_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_265_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0___boxed(lean_object* v_00_u03b1_270_, lean_object* v_x_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0(v_00_u03b1_270_, v_x_271_, v___y_272_);
lean_dec_ref(v___y_272_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO___redArg(lean_object* v_x_277_, lean_object* v_ctx_278_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lean_apply_2(v_x_277_, v_ctx_278_, lean_box(0));
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_288_ == 0)
{
v___x_283_ = v___x_280_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_a_281_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_298_; 
v_a_289_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_298_ == 0)
{
v___x_291_ = v___x_280_;
v_isShared_292_ = v_isSharedCheck_298_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_280_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_298_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v_message_293_; lean_object* v___x_294_; lean_object* v___x_296_; 
v_message_293_ = lean_ctor_get(v_a_289_, 0);
lean_inc_ref(v_message_293_);
lean_dec(v_a_289_);
v___x_294_ = lean_mk_io_user_error(v_message_293_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v___x_294_);
v___x_296_ = v___x_291_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO___redArg___boxed(lean_object* v_x_299_, lean_object* v_ctx_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Server_RequestM_runInIO___redArg(v_x_299_, v_ctx_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO(lean_object* v_00_u03b1_303_, lean_object* v_x_304_, lean_object* v_ctx_305_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Lean_Server_RequestM_runInIO___redArg(v_x_304_, v_ctx_305_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO___boxed(lean_object* v_00_u03b1_308_, lean_object* v_x_309_, lean_object* v_ctx_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_Server_RequestM_runInIO(v_00_u03b1_308_, v_x_309_, v_ctx_310_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___redArg___lam__0(lean_object* v_toPure_313_, lean_object* v_rc_314_){
_start:
{
lean_object* v_doc_315_; lean_object* v___x_316_; 
v_doc_315_ = lean_ctor_get(v_rc_314_, 1);
lean_inc_ref(v_doc_315_);
lean_dec_ref(v_rc_314_);
v___x_316_ = lean_apply_2(v_toPure_313_, lean_box(0), v_doc_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___redArg(lean_object* v_inst_317_, lean_object* v_inst_318_){
_start:
{
lean_object* v_toApplicative_319_; lean_object* v_toBind_320_; lean_object* v_toPure_321_; lean_object* v___f_322_; lean_object* v___x_323_; 
v_toApplicative_319_ = lean_ctor_get(v_inst_317_, 0);
lean_inc_ref(v_toApplicative_319_);
v_toBind_320_ = lean_ctor_get(v_inst_317_, 1);
lean_inc(v_toBind_320_);
lean_dec_ref(v_inst_317_);
v_toPure_321_ = lean_ctor_get(v_toApplicative_319_, 1);
lean_inc(v_toPure_321_);
lean_dec_ref(v_toApplicative_319_);
v___f_322_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_readDoc___redArg___lam__0), 2, 1);
lean_closure_set(v___f_322_, 0, v_toPure_321_);
v___x_323_ = lean_apply_4(v_toBind_320_, lean_box(0), lean_box(0), v_inst_318_, v___f_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc(lean_object* v_m_324_, lean_object* v_inst_325_, lean_object* v_inst_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_Server_RequestM_readDoc___redArg(v_inst_325_, v_inst_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg___lam__0(lean_object* v_t_328_, lean_object* v_a_329_){
_start:
{
lean_object* v___x_331_; 
lean_inc_ref(v_a_329_);
v___x_331_ = lean_apply_2(v_t_328_, v_a_329_, lean_box(0));
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg___lam__0___boxed(lean_object* v_t_332_, lean_object* v_a_333_, lean_object* v___y_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Server_RequestM_asTask___redArg___lam__0(v_t_332_, v_a_333_);
lean_dec_ref(v_a_333_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg(lean_object* v_t_336_, lean_object* v_a_337_){
_start:
{
lean_object* v___f_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
lean_inc_ref(v_a_337_);
v___f_339_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_asTask___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_339_, 0, v_t_336_);
lean_closure_set(v___f_339_, 1, v_a_337_);
v___x_340_ = l_Lean_Server_ServerTask_EIO_asTask___redArg(v___f_339_);
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg___boxed(lean_object* v_t_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_Server_RequestM_asTask___redArg(v_t_342_, v_a_343_);
lean_dec_ref(v_a_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask(lean_object* v_00_u03b1_346_, lean_object* v_t_347_, lean_object* v_a_348_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Lean_Server_RequestM_asTask___redArg(v_t_347_, v_a_348_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___boxed(lean_object* v_00_u03b1_351_, lean_object* v_t_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_Server_RequestM_asTask(v_00_u03b1_351_, v_t_352_, v_a_353_);
lean_dec_ref(v_a_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask___redArg(lean_object* v_t_356_, lean_object* v_a_357_){
_start:
{
lean_object* v___x_359_; 
lean_inc_ref(v_a_357_);
v___x_359_ = lean_apply_2(v_t_356_, v_a_357_, lean_box(0));
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_369_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_369_ == 0)
{
v___x_362_ = v___x_359_;
v_isShared_363_ = v_isSharedCheck_369_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_359_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_369_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_367_; 
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v_a_360_);
v___x_365_ = lean_task_pure(v___x_364_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v___x_365_);
v___x_367_ = v___x_362_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_365_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
v_a_370_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_359_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_359_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask___redArg___boxed(lean_object* v_t_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Server_RequestM_pureTask___redArg(v_t_378_, v_a_379_);
lean_dec_ref(v_a_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask(lean_object* v_00_u03b1_382_, lean_object* v_t_383_, lean_object* v_a_384_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Server_RequestM_pureTask___redArg(v_t_383_, v_a_384_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask___boxed(lean_object* v_00_u03b1_387_, lean_object* v_t_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_Server_RequestM_pureTask(v_00_u03b1_387_, v_t_388_, v_a_389_);
lean_dec_ref(v_a_389_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0(lean_object* v_f_392_, lean_object* v_a_393_, lean_object* v_x_394_){
_start:
{
lean_object* v___x_396_; 
lean_inc_ref(v_a_393_);
v___x_396_ = lean_apply_3(v_f_392_, v_x_394_, v_a_393_, lean_box(0));
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0___boxed(lean_object* v_f_397_, lean_object* v_a_398_, lean_object* v_x_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0(v_f_397_, v_a_398_, v_x_399_);
lean_dec_ref(v_a_398_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg(lean_object* v_t_402_, lean_object* v_f_403_, lean_object* v_a_404_){
_start:
{
lean_object* v___f_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
lean_inc_ref(v_a_404_);
v___f_406_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_406_, 0, v_f_403_);
lean_closure_set(v___f_406_, 1, v_a_404_);
v___x_407_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(v___f_406_, v_t_402_);
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg___boxed(lean_object* v_t_409_, lean_object* v_f_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_t_409_, v_f_410_, v_a_411_);
lean_dec_ref(v_a_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap(lean_object* v_00_u03b1_414_, lean_object* v_00_u03b2_415_, lean_object* v_t_416_, lean_object* v_f_417_, lean_object* v_a_418_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_t_416_, v_f_417_, v_a_418_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___boxed(lean_object* v_00_u03b1_421_, lean_object* v_00_u03b2_422_, lean_object* v_t_423_, lean_object* v_f_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_Server_RequestM_mapTaskCheap(v_00_u03b1_421_, v_00_u03b2_422_, v_t_423_, v_f_424_, v_a_425_);
lean_dec_ref(v_a_425_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly___redArg(lean_object* v_t_428_, lean_object* v_f_429_, lean_object* v_a_430_){
_start:
{
lean_object* v___f_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
lean_inc_ref(v_a_430_);
v___f_432_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_432_, 0, v_f_429_);
lean_closure_set(v___f_432_, 1, v_a_430_);
v___x_433_ = l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(v___f_432_, v_t_428_);
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly___redArg___boxed(lean_object* v_t_435_, lean_object* v_f_436_, lean_object* v_a_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_t_435_, v_f_436_, v_a_437_);
lean_dec_ref(v_a_437_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly(lean_object* v_00_u03b1_440_, lean_object* v_00_u03b2_441_, lean_object* v_t_442_, lean_object* v_f_443_, lean_object* v_a_444_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_t_442_, v_f_443_, v_a_444_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly___boxed(lean_object* v_00_u03b1_447_, lean_object* v_00_u03b2_448_, lean_object* v_t_449_, lean_object* v_f_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_Server_RequestM_mapTaskCostly(v_00_u03b1_447_, v_00_u03b2_448_, v_t_449_, v_f_450_, v_a_451_);
lean_dec_ref(v_a_451_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0(lean_object* v_f_454_, lean_object* v_a_455_, lean_object* v_x_456_){
_start:
{
lean_object* v___x_458_; 
lean_inc_ref(v_a_455_);
v___x_458_ = lean_apply_3(v_f_454_, v_x_456_, v_a_455_, lean_box(0));
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0___boxed(lean_object* v_f_459_, lean_object* v_a_460_, lean_object* v_x_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0(v_f_459_, v_a_460_, v_x_461_);
lean_dec_ref(v_a_460_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg(lean_object* v_t_464_, lean_object* v_f_465_, lean_object* v_a_466_){
_start:
{
lean_object* v___f_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
lean_inc_ref(v_a_466_);
v___f_468_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_468_, 0, v_f_465_);
lean_closure_set(v___f_468_, 1, v_a_466_);
v___x_469_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(v_t_464_, v___f_468_);
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg___boxed(lean_object* v_t_471_, lean_object* v_f_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_Server_RequestM_bindTaskCheap___redArg(v_t_471_, v_f_472_, v_a_473_);
lean_dec_ref(v_a_473_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap(lean_object* v_00_u03b1_476_, lean_object* v_00_u03b2_477_, lean_object* v_t_478_, lean_object* v_f_479_, lean_object* v_a_480_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_Server_RequestM_bindTaskCheap___redArg(v_t_478_, v_f_479_, v_a_480_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___boxed(lean_object* v_00_u03b1_483_, lean_object* v_00_u03b2_484_, lean_object* v_t_485_, lean_object* v_f_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_Server_RequestM_bindTaskCheap(v_00_u03b1_483_, v_00_u03b2_484_, v_t_485_, v_f_486_, v_a_487_);
lean_dec_ref(v_a_487_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly___redArg(lean_object* v_t_490_, lean_object* v_f_491_, lean_object* v_a_492_){
_start:
{
lean_object* v___f_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
lean_inc_ref(v_a_492_);
v___f_494_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_494_, 0, v_f_491_);
lean_closure_set(v___f_494_, 1, v_a_492_);
v___x_495_ = l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(v_t_490_, v___f_494_);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly___redArg___boxed(lean_object* v_t_497_, lean_object* v_f_498_, lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_t_497_, v_f_498_, v_a_499_);
lean_dec_ref(v_a_499_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly(lean_object* v_00_u03b1_502_, lean_object* v_00_u03b2_503_, lean_object* v_t_504_, lean_object* v_f_505_, lean_object* v_a_506_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_t_504_, v_f_505_, v_a_506_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly___boxed(lean_object* v_00_u03b1_509_, lean_object* v_00_u03b2_510_, lean_object* v_t_511_, lean_object* v_f_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_Server_RequestM_bindTaskCostly(v_00_u03b1_509_, v_00_u03b2_510_, v_t_511_, v_f_512_, v_a_513_);
lean_dec_ref(v_a_513_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0(lean_object* v_f_516_, lean_object* v_x_517_, lean_object* v___y_518_){
_start:
{
if (lean_obj_tag(v_x_517_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
lean_dec_ref(v_f_516_);
v_a_520_ = lean_ctor_get(v_x_517_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v_x_517_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v_x_517_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v_x_517_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
lean_ctor_set_tag(v___x_522_, 1);
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_529_; 
v_a_528_ = lean_ctor_get(v_x_517_, 0);
lean_inc(v_a_528_);
lean_dec_ref_known(v_x_517_, 1);
lean_inc_ref(v___y_518_);
v___x_529_ = lean_apply_3(v_f_516_, v_a_528_, v___y_518_, lean_box(0));
return v___x_529_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0___boxed(lean_object* v_f_530_, lean_object* v_x_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0(v_f_530_, v_x_531_, v___y_532_);
lean_dec_ref(v___y_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg(lean_object* v_t_535_, lean_object* v_f_536_, lean_object* v_a_537_){
_start:
{
lean_object* v___f_539_; lean_object* v___x_540_; 
v___f_539_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_539_, 0, v_f_536_);
v___x_540_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_t_535_, v___f_539_, v_a_537_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___boxed(lean_object* v_t_541_, lean_object* v_f_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_Server_RequestM_mapRequestTaskCheap___redArg(v_t_541_, v_f_542_, v_a_543_);
lean_dec_ref(v_a_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap(lean_object* v_00_u03b1_546_, lean_object* v_00_u03b2_547_, lean_object* v_t_548_, lean_object* v_f_549_, lean_object* v_a_550_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Lean_Server_RequestM_mapRequestTaskCheap___redArg(v_t_548_, v_f_549_, v_a_550_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___boxed(lean_object* v_00_u03b1_553_, lean_object* v_00_u03b2_554_, lean_object* v_t_555_, lean_object* v_f_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_Server_RequestM_mapRequestTaskCheap(v_00_u03b1_553_, v_00_u03b2_554_, v_t_555_, v_f_556_, v_a_557_);
lean_dec_ref(v_a_557_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(lean_object* v_t_560_, lean_object* v_f_561_, lean_object* v_a_562_){
_start:
{
lean_object* v___f_564_; lean_object* v___x_565_; 
v___f_564_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_564_, 0, v_f_561_);
v___x_565_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_t_560_, v___f_564_, v_a_562_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly___redArg___boxed(lean_object* v_t_566_, lean_object* v_f_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(v_t_566_, v_f_567_, v_a_568_);
lean_dec_ref(v_a_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly(lean_object* v_00_u03b1_571_, lean_object* v_00_u03b2_572_, lean_object* v_t_573_, lean_object* v_f_574_, lean_object* v_a_575_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(v_t_573_, v_f_574_, v_a_575_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly___boxed(lean_object* v_00_u03b1_578_, lean_object* v_00_u03b2_579_, lean_object* v_t_580_, lean_object* v_f_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_Server_RequestM_mapRequestTaskCostly(v_00_u03b1_578_, v_00_u03b2_579_, v_t_580_, v_f_581_, v_a_582_);
lean_dec_ref(v_a_582_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0(lean_object* v_f_585_, lean_object* v_x_586_, lean_object* v___y_587_){
_start:
{
if (lean_obj_tag(v_x_586_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec_ref(v_f_585_);
v_a_589_ = lean_ctor_get(v_x_586_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v_x_586_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v_x_586_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v_x_586_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
lean_ctor_set_tag(v___x_591_, 1);
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
else
{
lean_object* v_a_597_; lean_object* v___x_598_; 
v_a_597_ = lean_ctor_get(v_x_586_, 0);
lean_inc(v_a_597_);
lean_dec_ref_known(v_x_586_, 1);
lean_inc_ref(v___y_587_);
v___x_598_ = lean_apply_3(v_f_585_, v_a_597_, v___y_587_, lean_box(0));
return v___x_598_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0___boxed(lean_object* v_f_599_, lean_object* v_x_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0(v_f_599_, v_x_600_, v___y_601_);
lean_dec_ref(v___y_601_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg(lean_object* v_t_604_, lean_object* v_f_605_, lean_object* v_a_606_){
_start:
{
lean_object* v___f_608_; lean_object* v___x_609_; 
v___f_608_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_608_, 0, v_f_605_);
v___x_609_ = l_Lean_Server_RequestM_bindTaskCheap___redArg(v_t_604_, v___f_608_, v_a_606_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___boxed(lean_object* v_t_610_, lean_object* v_f_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_Server_RequestM_bindRequestTaskCheap___redArg(v_t_610_, v_f_611_, v_a_612_);
lean_dec_ref(v_a_612_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap(lean_object* v_00_u03b1_615_, lean_object* v_00_u03b2_616_, lean_object* v_t_617_, lean_object* v_f_618_, lean_object* v_a_619_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_Server_RequestM_bindRequestTaskCheap___redArg(v_t_617_, v_f_618_, v_a_619_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___boxed(lean_object* v_00_u03b1_622_, lean_object* v_00_u03b2_623_, lean_object* v_t_624_, lean_object* v_f_625_, lean_object* v_a_626_, lean_object* v_a_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_Server_RequestM_bindRequestTaskCheap(v_00_u03b1_622_, v_00_u03b2_623_, v_t_624_, v_f_625_, v_a_626_);
lean_dec_ref(v_a_626_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly___redArg(lean_object* v_t_629_, lean_object* v_f_630_, lean_object* v_a_631_){
_start:
{
lean_object* v___f_633_; lean_object* v___x_634_; 
v___f_633_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_633_, 0, v_f_630_);
v___x_634_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_t_629_, v___f_633_, v_a_631_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly___redArg___boxed(lean_object* v_t_635_, lean_object* v_f_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_Server_RequestM_bindRequestTaskCostly___redArg(v_t_635_, v_f_636_, v_a_637_);
lean_dec_ref(v_a_637_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly(lean_object* v_00_u03b1_640_, lean_object* v_00_u03b2_641_, lean_object* v_t_642_, lean_object* v_f_643_, lean_object* v_a_644_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_Server_RequestM_bindRequestTaskCostly___redArg(v_t_642_, v_f_643_, v_a_644_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly___boxed(lean_object* v_00_u03b1_647_, lean_object* v_00_u03b2_648_, lean_object* v_t_649_, lean_object* v_f_650_, lean_object* v_a_651_, lean_object* v_a_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_Server_RequestM_bindRequestTaskCostly(v_00_u03b1_647_, v_00_u03b2_648_, v_t_649_, v_f_650_, v_a_651_);
lean_dec_ref(v_a_651_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___redArg(lean_object* v_inst_654_, lean_object* v_params_655_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_Server_parseRequestParams___redArg(v_inst_654_, v_params_655_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_657_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
lean_ctor_set_tag(v___x_660_, 1);
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
v_a_666_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_657_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_657_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
lean_ctor_set_tag(v___x_668_, 0);
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___redArg___boxed(lean_object* v_inst_674_, lean_object* v_params_675_, lean_object* v_a_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_674_, v_params_675_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams(lean_object* v_paramType_678_, lean_object* v_inst_679_, lean_object* v_params_680_, lean_object* v_a_681_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_679_, v_params_680_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___boxed(lean_object* v_paramType_684_, lean_object* v_inst_685_, lean_object* v_params_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_Server_RequestM_parseRequestParams(v_paramType_684_, v_inst_685_, v_params_686_, v_a_687_);
lean_dec_ref(v_a_687_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_checkCancelled(lean_object* v_a_690_){
_start:
{
lean_object* v_cancelTk_692_; uint8_t v___x_693_; 
v_cancelTk_692_ = lean_ctor_get(v_a_690_, 4);
v___x_693_ = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_cancelTk_692_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_box(0);
v___x_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
return v___x_695_;
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = ((lean_object*)(l_Lean_Server_RequestError_requestCancelled));
v___x_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_checkCancelled___boxed(lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Server_RequestM_checkCancelled(v_a_698_);
lean_dec_ref(v_a_698_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0(lean_object* v_inst_702_, lean_object* v_x_703_){
_start:
{
if (lean_obj_tag(v_x_703_) == 0)
{
lean_object* v_response_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_722_; 
v_response_704_ = lean_ctor_get(v_x_703_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v_x_703_);
if (v_isSharedCheck_722_ == 0)
{
v___x_706_ = v_x_703_;
v_isShared_707_ = v_isSharedCheck_722_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_response_704_);
lean_dec(v_x_703_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_722_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_708_; 
lean_inc(v_response_704_);
v___x_708_ = lean_apply_1(v_inst_702_, v_response_704_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; uint8_t v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
lean_del_object(v___x_706_);
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_708_, 1);
v___x_710_ = 0;
v___x_711_ = ((lean_object*)(l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0___closed__0));
v___x_712_ = l_Lean_Json_compress(v_response_704_);
v___x_713_ = lean_string_append(v___x_711_, v___x_712_);
lean_dec_ref(v___x_712_);
v___x_714_ = ((lean_object*)(l_Lean_Server_parseRequestParams___redArg___closed__1));
v___x_715_ = lean_string_append(v___x_713_, v___x_714_);
v___x_716_ = lean_string_append(v___x_715_, v_a_709_);
lean_dec(v_a_709_);
v___x_717_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_717_, 0, v___x_716_);
lean_ctor_set_uint8(v___x_717_, sizeof(void*)*1, v___x_710_);
return v___x_717_;
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; 
lean_dec(v_response_704_);
v_a_718_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v___x_708_, 1);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v_a_718_);
v___x_720_ = v___x_706_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
else
{
uint8_t v_code_723_; lean_object* v_message_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec_ref(v_inst_702_);
v_code_723_ = lean_ctor_get_uint8(v_x_703_, sizeof(void*)*1);
v_message_724_ = lean_ctor_get(v_x_703_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v_x_703_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v_x_703_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_message_724_);
lean_dec(v_x_703_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_message_724_);
lean_ctor_set_uint8(v_reuseFailAlloc_730_, sizeof(void*)*1, v_code_723_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___redArg(lean_object* v_inst_732_, lean_object* v_inst_733_, lean_object* v_method_734_, lean_object* v_param_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_serverRequestEmitter_738_; lean_object* v___f_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_serverRequestEmitter_738_ = lean_ctor_get(v_a_736_, 5);
v___f_739_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0), 2, 1);
lean_closure_set(v___f_739_, 0, v_inst_733_);
v___x_740_ = lean_apply_1(v_inst_732_, v_param_735_);
lean_inc_ref(v_serverRequestEmitter_738_);
v___x_741_ = lean_apply_3(v_serverRequestEmitter_738_, v_method_734_, v___x_740_, lean_box(0));
v___x_742_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_739_, v___x_741_);
v___x_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___redArg___boxed(lean_object* v_inst_744_, lean_object* v_inst_745_, lean_object* v_method_746_, lean_object* v_param_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_Server_RequestM_sendServerRequest___redArg(v_inst_744_, v_inst_745_, v_method_746_, v_param_747_, v_a_748_);
lean_dec_ref(v_a_748_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest(lean_object* v_paramType_751_, lean_object* v_inst_752_, lean_object* v_responseType_753_, lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_method_756_, lean_object* v_param_757_, lean_object* v_a_758_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_Server_RequestM_sendServerRequest___redArg(v_inst_752_, v_inst_754_, v_method_756_, v_param_757_, v_a_758_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___boxed(lean_object* v_paramType_761_, lean_object* v_inst_762_, lean_object* v_responseType_763_, lean_object* v_inst_764_, lean_object* v_inst_765_, lean_object* v_method_766_, lean_object* v_param_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_Server_RequestM_sendServerRequest(v_paramType_761_, v_inst_762_, v_responseType_763_, v_inst_764_, v_inst_765_, v_method_766_, v_param_767_, v_a_768_);
lean_dec_ref(v_a_768_);
lean_dec(v_inst_765_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux___redArg(lean_object* v_notFoundX_771_, lean_object* v_x_772_, lean_object* v_x_773_, lean_object* v_a_774_){
_start:
{
if (lean_obj_tag(v_x_773_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_784_; 
lean_dec_ref(v_x_772_);
lean_dec_ref(v_notFoundX_771_);
v_a_776_ = lean_ctor_get(v_x_773_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v_x_773_);
if (v_isSharedCheck_784_ == 0)
{
v___x_778_ = v_x_773_;
v_isShared_779_ = v_isSharedCheck_784_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v_x_773_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_784_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v___x_782_; 
v___x_780_ = l_Lean_Server_RequestError_ofIoError(v_a_776_);
if (v_isShared_779_ == 0)
{
lean_ctor_set_tag(v___x_778_, 1);
lean_ctor_set(v___x_778_, 0, v___x_780_);
v___x_782_ = v___x_778_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
else
{
lean_object* v_a_785_; 
v_a_785_ = lean_ctor_get(v_x_773_, 0);
lean_inc(v_a_785_);
lean_dec_ref_known(v_x_773_, 1);
if (lean_obj_tag(v_a_785_) == 0)
{
lean_object* v___x_786_; 
lean_dec_ref(v_x_772_);
lean_inc_ref(v_a_774_);
v___x_786_ = lean_apply_2(v_notFoundX_771_, v_a_774_, lean_box(0));
return v___x_786_;
}
else
{
lean_object* v_val_787_; lean_object* v___x_788_; 
lean_dec_ref(v_notFoundX_771_);
v_val_787_ = lean_ctor_get(v_a_785_, 0);
lean_inc(v_val_787_);
lean_dec_ref_known(v_a_785_, 1);
lean_inc_ref(v_a_774_);
v___x_788_ = lean_apply_3(v_x_772_, v_val_787_, v_a_774_, lean_box(0));
return v___x_788_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux___redArg___boxed(lean_object* v_notFoundX_789_, lean_object* v_x_790_, lean_object* v_x_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_Server_RequestM_waitFindSnapAux___redArg(v_notFoundX_789_, v_x_790_, v_x_791_, v_a_792_);
lean_dec_ref(v_a_792_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux(lean_object* v_00_u03b1_795_, lean_object* v_notFoundX_796_, lean_object* v_x_797_, lean_object* v_x_798_, lean_object* v_a_799_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_Server_RequestM_waitFindSnapAux___redArg(v_notFoundX_796_, v_x_797_, v_x_798_, v_a_799_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux___boxed(lean_object* v_00_u03b1_802_, lean_object* v_notFoundX_803_, lean_object* v_x_804_, lean_object* v_x_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_Server_RequestM_waitFindSnapAux(v_00_u03b1_802_, v_notFoundX_803_, v_x_804_, v_x_805_, v_a_806_);
lean_dec_ref(v_a_806_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___redArg(lean_object* v_doc_809_, lean_object* v_p_810_, lean_object* v_notFoundX_811_, lean_object* v_x_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_toEditableDocumentCore_815_; lean_object* v_cmdSnaps_816_; lean_object* v_findTask_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v_toEditableDocumentCore_815_ = lean_ctor_get(v_doc_809_, 0);
lean_inc_ref(v_toEditableDocumentCore_815_);
lean_dec_ref(v_doc_809_);
v_cmdSnaps_816_ = lean_ctor_get(v_toEditableDocumentCore_815_, 2);
lean_inc(v_cmdSnaps_816_);
lean_dec_ref(v_toEditableDocumentCore_815_);
v_findTask_817_ = l_Lean_AsyncList_waitFind_x3f___redArg(v_p_810_, v_cmdSnaps_816_);
v___x_818_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_waitFindSnapAux___boxed), 6, 3);
lean_closure_set(v___x_818_, 0, lean_box(0));
lean_closure_set(v___x_818_, 1, v_notFoundX_811_);
lean_closure_set(v___x_818_, 2, v_x_812_);
v___x_819_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_findTask_817_, v___x_818_, v_a_813_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___redArg___boxed(lean_object* v_doc_820_, lean_object* v_p_821_, lean_object* v_notFoundX_822_, lean_object* v_x_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_doc_820_, v_p_821_, v_notFoundX_822_, v_x_823_, v_a_824_);
lean_dec_ref(v_a_824_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap(lean_object* v_00_u03b2_827_, lean_object* v_doc_828_, lean_object* v_p_829_, lean_object* v_notFoundX_830_, lean_object* v_x_831_, lean_object* v_a_832_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_doc_828_, v_p_829_, v_notFoundX_830_, v_x_831_, v_a_832_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___boxed(lean_object* v_00_u03b2_835_, lean_object* v_doc_836_, lean_object* v_p_837_, lean_object* v_notFoundX_838_, lean_object* v_x_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lean_Server_RequestM_withWaitFindSnap(v_00_u03b2_835_, v_doc_836_, v_p_837_, v_notFoundX_838_, v_x_839_, v_a_840_);
lean_dec_ref(v_a_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___redArg(lean_object* v_doc_843_, lean_object* v_p_844_, lean_object* v_notFoundX_845_, lean_object* v_x_846_, lean_object* v_a_847_){
_start:
{
lean_object* v_toEditableDocumentCore_849_; lean_object* v_cmdSnaps_850_; lean_object* v_findTask_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_toEditableDocumentCore_849_ = lean_ctor_get(v_doc_843_, 0);
lean_inc_ref(v_toEditableDocumentCore_849_);
lean_dec_ref(v_doc_843_);
v_cmdSnaps_850_ = lean_ctor_get(v_toEditableDocumentCore_849_, 2);
lean_inc(v_cmdSnaps_850_);
lean_dec_ref(v_toEditableDocumentCore_849_);
v_findTask_851_ = l_Lean_AsyncList_waitFind_x3f___redArg(v_p_844_, v_cmdSnaps_850_);
v___x_852_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_waitFindSnapAux___boxed), 6, 3);
lean_closure_set(v___x_852_, 0, lean_box(0));
lean_closure_set(v___x_852_, 1, v_notFoundX_845_);
lean_closure_set(v___x_852_, 2, v_x_846_);
v___x_853_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_findTask_851_, v___x_852_, v_a_847_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___redArg___boxed(lean_object* v_doc_854_, lean_object* v_p_855_, lean_object* v_notFoundX_856_, lean_object* v_x_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_Server_RequestM_bindWaitFindSnap___redArg(v_doc_854_, v_p_855_, v_notFoundX_856_, v_x_857_, v_a_858_);
lean_dec_ref(v_a_858_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap(lean_object* v_00_u03b2_861_, lean_object* v_doc_862_, lean_object* v_p_863_, lean_object* v_notFoundX_864_, lean_object* v_x_865_, lean_object* v_a_866_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Lean_Server_RequestM_bindWaitFindSnap___redArg(v_doc_862_, v_p_863_, v_notFoundX_864_, v_x_865_, v_a_866_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___boxed(lean_object* v_00_u03b2_869_, lean_object* v_doc_870_, lean_object* v_p_871_, lean_object* v_notFoundX_872_, lean_object* v_x_873_, lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_Server_RequestM_bindWaitFindSnap(v_00_u03b2_869_, v_doc_870_, v_p_871_, v_notFoundX_872_, v_x_873_, v_a_874_);
lean_dec_ref(v_a_874_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(lean_object* v___y_877_){
_start:
{
lean_object* v_doc_879_; lean_object* v___x_880_; 
v_doc_879_ = lean_ctor_get(v___y_877_, 1);
lean_inc_ref(v_doc_879_);
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v_doc_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0___boxed(lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(v___y_881_);
lean_dec_ref(v___y_881_);
return v_res_883_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0(lean_object* v___x_884_, lean_object* v_s_885_){
_start:
{
lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_886_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_s_885_);
v___x_887_ = lean_nat_dec_le(v___x_884_, v___x_886_);
lean_dec(v___x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0___boxed(lean_object* v___x_888_, lean_object* v_s_889_){
_start:
{
uint8_t v_res_890_; lean_object* v_r_891_; 
v_res_890_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0(v___x_888_, v_s_889_);
lean_dec_ref(v_s_889_);
lean_dec(v___x_888_);
v_r_891_ = lean_box(v_res_890_);
return v_r_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1(lean_object* v___x_892_, lean_object* v___y_893_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_892_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1___boxed(lean_object* v___x_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1(v___x_896_, v___y_897_);
lean_dec_ref(v___y_897_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg(lean_object* v_lspPos_904_, lean_object* v_f_905_, lean_object* v_a_906_){
_start:
{
lean_object* v___x_908_; lean_object* v_a_909_; lean_object* v_toEditableDocumentCore_910_; lean_object* v_meta_911_; lean_object* v_text_912_; lean_object* v_line_913_; lean_object* v_character_914_; lean_object* v___x_915_; lean_object* v___f_916_; uint8_t v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___f_930_; lean_object* v___x_931_; 
v___x_908_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(v_a_906_);
v_a_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_a_909_);
lean_dec_ref(v___x_908_);
v_toEditableDocumentCore_910_ = lean_ctor_get(v_a_909_, 0);
v_meta_911_ = lean_ctor_get(v_toEditableDocumentCore_910_, 0);
v_text_912_ = lean_ctor_get(v_meta_911_, 3);
v_line_913_ = lean_ctor_get(v_lspPos_904_, 0);
lean_inc(v_line_913_);
v_character_914_ = lean_ctor_get(v_lspPos_904_, 1);
lean_inc(v_character_914_);
v___x_915_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_912_, v_lspPos_904_);
v___f_916_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_916_, 0, v___x_915_);
v___x_917_ = 3;
v___x_918_ = ((lean_object*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__0));
v___x_919_ = ((lean_object*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__1));
v___x_920_ = l_Nat_reprFast(v_line_913_);
v___x_921_ = lean_string_append(v___x_919_, v___x_920_);
lean_dec_ref(v___x_920_);
v___x_922_ = ((lean_object*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__2));
v___x_923_ = lean_string_append(v___x_921_, v___x_922_);
v___x_924_ = l_Nat_reprFast(v_character_914_);
v___x_925_ = lean_string_append(v___x_923_, v___x_924_);
lean_dec_ref(v___x_924_);
v___x_926_ = ((lean_object*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__3));
v___x_927_ = lean_string_append(v___x_925_, v___x_926_);
v___x_928_ = lean_string_append(v___x_918_, v___x_927_);
lean_dec_ref(v___x_927_);
v___x_929_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set_uint8(v___x_929_, sizeof(void*)*1, v___x_917_);
v___f_930_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_930_, 0, v___x_929_);
v___x_931_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_a_909_, v___f_916_, v___f_930_, v_f_905_, v_a_906_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___boxed(lean_object* v_lspPos_932_, lean_object* v_f_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg(v_lspPos_932_, v_f_933_, v_a_934_);
lean_dec_ref(v_a_934_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos(lean_object* v_00_u03b1_937_, lean_object* v_lspPos_938_, lean_object* v_f_939_, lean_object* v_a_940_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg(v_lspPos_938_, v_f_939_, v_a_940_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___boxed(lean_object* v_00_u03b1_943_, lean_object* v_lspPos_944_, lean_object* v_f_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos(v_00_u03b1_943_, v_lspPos_944_, v_f_945_, v_a_946_);
lean_dec_ref(v_a_946_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___redArg(lean_object* v_snap_949_, lean_object* v_c_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_doc_953_; lean_object* v_toEditableDocumentCore_954_; lean_object* v_meta_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_doc_953_ = lean_ctor_get(v_a_951_, 1);
v_toEditableDocumentCore_954_ = lean_ctor_get(v_doc_953_, 0);
v_meta_955_ = lean_ctor_get(v_toEditableDocumentCore_954_, 0);
lean_inc_ref(v_a_951_);
v___x_956_ = lean_apply_1(v_c_950_, v_a_951_);
v___x_957_ = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(v_snap_949_, v_meta_955_, v___x_956_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_970_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_970_ == 0)
{
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_970_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_970_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
if (lean_obj_tag(v_a_958_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_964_; 
v_a_962_ = lean_ctor_get(v_a_958_, 0);
lean_inc(v_a_962_);
lean_dec_ref_known(v_a_958_, 1);
if (v_isShared_961_ == 0)
{
lean_ctor_set_tag(v___x_960_, 1);
lean_ctor_set(v___x_960_, 0, v_a_962_);
v___x_964_ = v___x_960_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; 
v_a_966_ = lean_ctor_get(v_a_958_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v_a_958_, 1);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v_a_966_);
v___x_968_ = v___x_960_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
else
{
lean_object* v_a_971_; lean_object* v___x_972_; lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
v_a_971_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_971_);
lean_dec_ref_known(v___x_957_, 1);
v___x_972_ = l_Lean_Server_RequestError_ofException(v_a_971_);
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set_tag(v___x_975_, 1);
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___redArg___boxed(lean_object* v_snap_981_, lean_object* v_c_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Lean_Server_RequestM_runCommandElabM___redArg(v_snap_981_, v_c_982_, v_a_983_);
lean_dec_ref(v_a_983_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM(lean_object* v_00_u03b1_986_, lean_object* v_snap_987_, lean_object* v_c_988_, lean_object* v_a_989_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_Server_RequestM_runCommandElabM___redArg(v_snap_987_, v_c_988_, v_a_989_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___boxed(lean_object* v_00_u03b1_992_, lean_object* v_snap_993_, lean_object* v_c_994_, lean_object* v_a_995_, lean_object* v_a_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_Server_RequestM_runCommandElabM(v_00_u03b1_992_, v_snap_993_, v_c_994_, v_a_995_);
lean_dec_ref(v_a_995_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___redArg(lean_object* v_snap_998_, lean_object* v_c_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_doc_1002_; lean_object* v_toEditableDocumentCore_1003_; lean_object* v_meta_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v_doc_1002_ = lean_ctor_get(v_a_1000_, 1);
v_toEditableDocumentCore_1003_ = lean_ctor_get(v_doc_1002_, 0);
v_meta_1004_ = lean_ctor_get(v_toEditableDocumentCore_1003_, 0);
lean_inc_ref(v_a_1000_);
v___x_1005_ = lean_apply_1(v_c_999_, v_a_1000_);
v___x_1006_ = l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(v_snap_998_, v_meta_1004_, v___x_1005_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1019_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1009_ = v___x_1006_;
v_isShared_1010_ = v_isSharedCheck_1019_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1006_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1019_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
if (lean_obj_tag(v_a_1007_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1013_; 
v_a_1011_ = lean_ctor_get(v_a_1007_, 0);
lean_inc(v_a_1011_);
lean_dec_ref_known(v_a_1007_, 1);
if (v_isShared_1010_ == 0)
{
lean_ctor_set_tag(v___x_1009_, 1);
lean_ctor_set(v___x_1009_, 0, v_a_1011_);
v___x_1013_ = v___x_1009_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1011_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; 
v_a_1015_ = lean_ctor_get(v_a_1007_, 0);
lean_inc(v_a_1015_);
lean_dec_ref_known(v_a_1007_, 1);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v_a_1015_);
v___x_1017_ = v___x_1009_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1021_; lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
v_a_1020_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1020_);
lean_dec_ref_known(v___x_1006_, 1);
v___x_1021_ = l_Lean_Server_RequestError_ofException(v_a_1020_);
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_1021_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1021_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
lean_ctor_set_tag(v___x_1024_, 1);
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___redArg___boxed(lean_object* v_snap_1030_, lean_object* v_c_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_Server_RequestM_runCoreM___redArg(v_snap_1030_, v_c_1031_, v_a_1032_);
lean_dec_ref(v_a_1032_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM(lean_object* v_00_u03b1_1035_, lean_object* v_snap_1036_, lean_object* v_c_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_Server_RequestM_runCoreM___redArg(v_snap_1036_, v_c_1037_, v_a_1038_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___boxed(lean_object* v_00_u03b1_1041_, lean_object* v_snap_1042_, lean_object* v_c_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_Server_RequestM_runCoreM(v_00_u03b1_1041_, v_snap_1042_, v_c_1043_, v_a_1044_);
lean_dec_ref(v_a_1044_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___redArg(lean_object* v_snap_1047_, lean_object* v_c_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_doc_1051_; lean_object* v_toEditableDocumentCore_1052_; lean_object* v_meta_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v_doc_1051_ = lean_ctor_get(v_a_1049_, 1);
v_toEditableDocumentCore_1052_ = lean_ctor_get(v_doc_1051_, 0);
v_meta_1053_ = lean_ctor_get(v_toEditableDocumentCore_1052_, 0);
lean_inc_ref(v_a_1049_);
v___x_1054_ = lean_apply_1(v_c_1048_, v_a_1049_);
v___x_1055_ = l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg(v_snap_1047_, v_meta_1053_, v___x_1054_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1068_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1058_ = v___x_1055_;
v_isShared_1059_ = v_isSharedCheck_1068_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1055_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1068_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
if (lean_obj_tag(v_a_1056_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1062_; 
v_a_1060_ = lean_ctor_get(v_a_1056_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v_a_1056_, 1);
if (v_isShared_1059_ == 0)
{
lean_ctor_set_tag(v___x_1058_, 1);
lean_ctor_set(v___x_1058_, 0, v_a_1060_);
v___x_1062_ = v___x_1058_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; 
v_a_1064_ = lean_ctor_get(v_a_1056_, 0);
lean_inc(v_a_1064_);
lean_dec_ref_known(v_a_1056_, 1);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v_a_1064_);
v___x_1066_ = v___x_1058_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1070_; lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
v_a_1069_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1055_, 1);
v___x_1070_ = l_Lean_Server_RequestError_ofException(v_a_1069_);
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1070_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
lean_ctor_set_tag(v___x_1073_, 1);
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___redArg___boxed(lean_object* v_snap_1079_, lean_object* v_c_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_Server_RequestM_runTermElabM___redArg(v_snap_1079_, v_c_1080_, v_a_1081_);
lean_dec_ref(v_a_1081_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM(lean_object* v_00_u03b1_1084_, lean_object* v_snap_1085_, lean_object* v_c_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_Server_RequestM_runTermElabM___redArg(v_snap_1085_, v_c_1086_, v_a_1087_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___boxed(lean_object* v_00_u03b1_1090_, lean_object* v_snap_1091_, lean_object* v_c_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_Server_RequestM_runTermElabM(v_00_u03b1_1090_, v_snap_1091_, v_c_1092_, v_a_1093_);
lean_dec_ref(v_a_1093_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage(lean_object* v_id_1102_, lean_object* v_r_1103_){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___y_1107_; 
v___x_1104_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__0));
v___x_1105_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__1));
switch(lean_obj_tag(v_id_1102_))
{
case 0:
{
lean_object* v_s_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
v_s_1121_ = lean_ctor_get(v_id_1102_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_id_1102_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v_id_1102_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_s_1121_);
lean_dec(v_id_1102_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
lean_ctor_set_tag(v___x_1123_, 3);
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_s_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
v___y_1107_ = v___x_1126_;
goto v___jp_1106_;
}
}
}
case 1:
{
lean_object* v_n_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
v_n_1129_ = lean_ctor_get(v_id_1102_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_id_1102_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v_id_1102_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_n_1129_);
lean_dec(v_id_1102_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
lean_ctor_set_tag(v___x_1131_, 2);
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_n_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
v___y_1107_ = v___x_1134_;
goto v___jp_1106_;
}
}
}
default: 
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_box(0);
v___y_1107_ = v___x_1137_;
goto v___jp_1106_;
}
}
v___jp_1106_:
{
lean_object* v_serialized_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v_serialized_1108_ = lean_ctor_get(v_r_1103_, 1);
v___x_1109_ = l_Lean_Json_compress(v___y_1107_);
v___x_1110_ = lean_string_append(v___x_1105_, v___x_1109_);
lean_dec_ref(v___x_1109_);
v___x_1111_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__2));
v___x_1112_ = lean_string_append(v___x_1110_, v___x_1111_);
v___x_1113_ = lean_string_append(v___x_1104_, v___x_1112_);
lean_dec_ref(v___x_1112_);
v___x_1114_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__3));
v___x_1115_ = lean_string_append(v___x_1113_, v___x_1114_);
v___x_1116_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__4));
v___x_1117_ = lean_string_append(v___x_1116_, v_serialized_1108_);
v___x_1118_ = lean_string_append(v___x_1115_, v___x_1117_);
lean_dec_ref(v___x_1117_);
v___x_1119_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__5));
v___x_1120_ = lean_string_append(v___x_1118_, v___x_1119_);
return v___x_1120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage___boxed(lean_object* v_id_1138_, lean_object* v_r_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lean_Server_SerializedLspResponse_toSerializedMessage(v_id_1138_, v_r_1139_);
lean_dec_ref(v_r_1139_);
return v_res_1140_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1141_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_);
v___x_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1145_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_);
v___x_1146_ = lean_st_mk_ref(v___x_1145_);
v___x_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2____boxed(lean_object* v_a_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_();
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__0(lean_object* v_inst_1150_, lean_object* v_inst_1151_, lean_object* v_j_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l_Lean_Server_parseRequestParams___redArg(v_inst_1150_, v_j_1152_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec_ref(v_inst_1151_);
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1153_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1153_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
else
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1170_; 
v_a_1162_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1164_ = v___x_1153_;
v_isShared_1165_ = v_isSharedCheck_1170_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1153_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1170_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1166_ = lean_apply_1(v_inst_1151_, v_a_1162_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v___x_1166_);
v___x_1168_ = v___x_1164_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__1(lean_object* v_serialize_x3f_1171_, uint8_t v_val_1172_, lean_object* v_inst_1173_, lean_object* v_r_1174_){
_start:
{
if (lean_obj_tag(v_serialize_x3f_1171_) == 1)
{
lean_object* v_val_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_dec_ref(v_inst_1173_);
v_val_1175_ = lean_ctor_get(v_serialize_x3f_1171_, 0);
lean_inc(v_val_1175_);
lean_dec_ref_known(v_serialize_x3f_1171_, 1);
v___x_1176_ = lean_box(0);
v___x_1177_ = lean_apply_1(v_val_1175_, v_r_1174_);
v___x_1178_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1178_, 0, v___x_1176_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
lean_ctor_set_uint8(v___x_1178_, sizeof(void*)*2, v_val_1172_);
return v___x_1178_;
}
else
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
lean_dec(v_serialize_x3f_1171_);
v___x_1179_ = lean_apply_1(v_inst_1173_, v_r_1174_);
lean_inc(v___x_1179_);
v___x_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
v___x_1181_ = l_Lean_Json_compress(v___x_1179_);
v___x_1182_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1182_, 0, v___x_1180_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
lean_ctor_set_uint8(v___x_1182_, sizeof(void*)*2, v_val_1172_);
return v___x_1182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__1___boxed(lean_object* v_serialize_x3f_1183_, lean_object* v_val_1184_, lean_object* v_inst_1185_, lean_object* v_r_1186_){
_start:
{
uint8_t v_val_1362__boxed_1187_; lean_object* v_res_1188_; 
v_val_1362__boxed_1187_ = lean_unbox(v_val_1184_);
v_res_1188_ = l_Lean_Server_registerLspRequestHandler___redArg___lam__1(v_serialize_x3f_1183_, v_val_1362__boxed_1187_, v_inst_1185_, v_r_1186_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__2(lean_object* v_inst_1189_, lean_object* v_handler_1190_, lean_object* v___f_1191_, lean_object* v_j_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_1189_, v_j_1192_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_a_1196_; lean_object* v___x_1197_; 
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_a_1196_);
lean_dec_ref_known(v___x_1195_, 1);
lean_inc_ref(v___y_1193_);
v___x_1197_ = lean_apply_3(v_handler_1190_, v_a_1196_, v___y_1193_, lean_box(0));
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1207_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1200_ = v___x_1197_;
v_isShared_1201_ = v_isSharedCheck_1207_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1197_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1207_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1202_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_1202_, 0, lean_box(0));
lean_closure_set(v___x_1202_, 1, lean_box(0));
lean_closure_set(v___x_1202_, 2, lean_box(0));
lean_closure_set(v___x_1202_, 3, v___f_1191_);
v___x_1203_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___x_1202_, v_a_1198_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___x_1203_);
v___x_1205_ = v___x_1200_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
lean_dec_ref(v___f_1191_);
v_a_1208_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1197_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1197_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec_ref(v___f_1191_);
lean_dec_ref(v_handler_1190_);
v_a_1216_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1195_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1195_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__2___boxed(lean_object* v_inst_1224_, lean_object* v_handler_1225_, lean_object* v___f_1226_, lean_object* v_j_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_Server_registerLspRequestHandler___redArg___lam__2(v_inst_1224_, v_handler_1225_, v___f_1226_, v_j_1227_, v___y_1228_);
lean_dec_ref(v___y_1228_);
return v_res_1230_;
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3(void){
_start:
{
lean_object* v___x_1234_; lean_object* v___f_1235_; 
v___x_1234_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___f_1235_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1235_, 0, v___x_1234_);
return v___f_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg(lean_object* v_method_1237_, lean_object* v_inst_1238_, lean_object* v_inst_1239_, lean_object* v_inst_1240_, lean_object* v_handler_1241_, lean_object* v_serialize_x3f_1242_){
_start:
{
lean_object* v___f_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
lean_inc_ref(v_inst_1238_);
v___f_1244_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1244_, 0, v_inst_1238_);
lean_closure_set(v___f_1244_, 1, v_inst_1239_);
v___x_1245_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__0));
v___x_1246_ = l_Lean_initializing();
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
lean_dec_ref(v___f_1244_);
lean_dec(v_serialize_x3f_1242_);
lean_dec_ref(v_handler_1241_);
lean_dec_ref(v_inst_1240_);
lean_dec_ref(v_inst_1238_);
v___x_1247_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__1));
v___x_1248_ = lean_string_append(v___x_1247_, v_method_1237_);
lean_dec_ref(v_method_1237_);
v___x_1249_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___x_1250_ = lean_string_append(v___x_1248_, v___x_1249_);
v___x_1251_ = lean_mk_io_user_error(v___x_1250_);
v___x_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
return v___x_1252_;
}
else
{
lean_object* v___x_1253_; lean_object* v___f_1254_; lean_object* v___f_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___f_1258_; uint8_t v___x_1259_; 
v___x_1253_ = lean_box(v___x_1246_);
v___f_1254_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1254_, 0, v_serialize_x3f_1242_);
lean_closure_set(v___f_1254_, 1, v___x_1253_);
lean_closure_set(v___f_1254_, 2, v_inst_1240_);
v___f_1255_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1255_, 0, v_inst_1238_);
lean_closure_set(v___f_1255_, 1, v_handler_1241_);
lean_closure_set(v___f_1255_, 2, v___f_1254_);
v___x_1256_ = l_Lean_Server_requestHandlers;
v___x_1257_ = lean_st_ref_get(v___x_1256_);
v___f_1258_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
lean_inc_ref(v_method_1237_);
v___x_1259_ = l_Lean_PersistentHashMap_contains___redArg(v___f_1258_, v___x_1245_, v___x_1257_, v_method_1237_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1260_ = lean_st_ref_take(v___x_1256_);
v___x_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___f_1244_);
lean_ctor_set(v___x_1261_, 1, v___f_1255_);
v___x_1262_ = l_Lean_PersistentHashMap_insert___redArg(v___f_1258_, v___x_1245_, v___x_1260_, v_method_1237_, v___x_1261_);
v___x_1263_ = lean_st_ref_put(v___x_1256_, v___x_1262_);
v___x_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
return v___x_1264_;
}
else
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
lean_dec_ref(v___f_1255_);
lean_dec_ref(v___f_1244_);
v___x_1265_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__1));
v___x_1266_ = lean_string_append(v___x_1265_, v_method_1237_);
lean_dec_ref(v_method_1237_);
v___x_1267_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__4));
v___x_1268_ = lean_string_append(v___x_1266_, v___x_1267_);
v___x_1269_ = lean_mk_io_user_error(v___x_1268_);
v___x_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
return v___x_1270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___boxed(lean_object* v_method_1271_, lean_object* v_inst_1272_, lean_object* v_inst_1273_, lean_object* v_inst_1274_, lean_object* v_handler_1275_, lean_object* v_serialize_x3f_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_Server_registerLspRequestHandler___redArg(v_method_1271_, v_inst_1272_, v_inst_1273_, v_inst_1274_, v_handler_1275_, v_serialize_x3f_1276_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler(lean_object* v_method_1279_, lean_object* v_paramType_1280_, lean_object* v_inst_1281_, lean_object* v_inst_1282_, lean_object* v_respType_1283_, lean_object* v_inst_1284_, lean_object* v_handler_1285_, lean_object* v_serialize_x3f_1286_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l_Lean_Server_registerLspRequestHandler___redArg(v_method_1279_, v_inst_1281_, v_inst_1282_, v_inst_1284_, v_handler_1285_, v_serialize_x3f_1286_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___boxed(lean_object* v_method_1289_, lean_object* v_paramType_1290_, lean_object* v_inst_1291_, lean_object* v_inst_1292_, lean_object* v_respType_1293_, lean_object* v_inst_1294_, lean_object* v_handler_1295_, lean_object* v_serialize_x3f_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Lean_Server_registerLspRequestHandler(v_method_1289_, v_paramType_1290_, v_inst_1291_, v_inst_1292_, v_respType_1293_, v_inst_1294_, v_handler_1295_, v_serialize_x3f_1296_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1299_, lean_object* v_vals_1300_, lean_object* v_i_1301_, lean_object* v_k_1302_){
_start:
{
lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = lean_array_get_size(v_keys_1299_);
v___x_1304_ = lean_nat_dec_lt(v_i_1301_, v___x_1303_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; 
lean_dec(v_i_1301_);
v___x_1305_ = lean_box(0);
return v___x_1305_;
}
else
{
lean_object* v_k_x27_1306_; uint8_t v___x_1307_; 
v_k_x27_1306_ = lean_array_fget_borrowed(v_keys_1299_, v_i_1301_);
v___x_1307_ = lean_string_dec_eq(v_k_1302_, v_k_x27_1306_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = lean_unsigned_to_nat(1u);
v___x_1309_ = lean_nat_add(v_i_1301_, v___x_1308_);
lean_dec(v_i_1301_);
v_i_1301_ = v___x_1309_;
goto _start;
}
else
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = lean_array_fget_borrowed(v_vals_1300_, v_i_1301_);
lean_dec(v_i_1301_);
lean_inc(v___x_1311_);
v___x_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
return v___x_1312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1313_, lean_object* v_vals_1314_, lean_object* v_i_1315_, lean_object* v_k_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(v_keys_1313_, v_vals_1314_, v_i_1315_, v_k_1316_);
lean_dec_ref(v_k_1316_);
lean_dec_ref(v_vals_1314_);
lean_dec_ref(v_keys_1313_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(lean_object* v_x_1318_, size_t v_x_1319_, lean_object* v_x_1320_){
_start:
{
if (lean_obj_tag(v_x_1318_) == 0)
{
lean_object* v_es_1321_; lean_object* v___x_1322_; size_t v___x_1323_; size_t v___x_1324_; lean_object* v_j_1325_; lean_object* v___x_1326_; 
v_es_1321_ = lean_ctor_get(v_x_1318_, 0);
v___x_1322_ = lean_box(2);
v___x_1323_ = ((size_t)31ULL);
v___x_1324_ = lean_usize_land(v_x_1319_, v___x_1323_);
v_j_1325_ = lean_usize_to_nat(v___x_1324_);
v___x_1326_ = lean_array_get_borrowed(v___x_1322_, v_es_1321_, v_j_1325_);
lean_dec(v_j_1325_);
switch(lean_obj_tag(v___x_1326_))
{
case 0:
{
lean_object* v_key_1327_; lean_object* v_val_1328_; uint8_t v___x_1329_; 
v_key_1327_ = lean_ctor_get(v___x_1326_, 0);
v_val_1328_ = lean_ctor_get(v___x_1326_, 1);
v___x_1329_ = lean_string_dec_eq(v_x_1320_, v_key_1327_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_box(0);
return v___x_1330_;
}
else
{
lean_object* v___x_1331_; 
lean_inc(v_val_1328_);
v___x_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1331_, 0, v_val_1328_);
return v___x_1331_;
}
}
case 1:
{
lean_object* v_node_1332_; size_t v___x_1333_; size_t v___x_1334_; 
v_node_1332_ = lean_ctor_get(v___x_1326_, 0);
v___x_1333_ = ((size_t)5ULL);
v___x_1334_ = lean_usize_shift_right(v_x_1319_, v___x_1333_);
v_x_1318_ = v_node_1332_;
v_x_1319_ = v___x_1334_;
goto _start;
}
default: 
{
lean_object* v___x_1336_; 
v___x_1336_ = lean_box(0);
return v___x_1336_;
}
}
}
else
{
lean_object* v_ks_1337_; lean_object* v_vs_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v_ks_1337_ = lean_ctor_get(v_x_1318_, 0);
v_vs_1338_ = lean_ctor_get(v_x_1318_, 1);
v___x_1339_ = lean_unsigned_to_nat(0u);
v___x_1340_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(v_ks_1337_, v_vs_1338_, v___x_1339_, v_x_1320_);
return v___x_1340_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___boxed(lean_object* v_x_1341_, lean_object* v_x_1342_, lean_object* v_x_1343_){
_start:
{
size_t v_x_277__boxed_1344_; lean_object* v_res_1345_; 
v_x_277__boxed_1344_ = lean_unbox_usize(v_x_1342_);
lean_dec(v_x_1342_);
v_res_1345_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_1341_, v_x_277__boxed_1344_, v_x_1343_);
lean_dec_ref(v_x_1343_);
lean_dec_ref(v_x_1341_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(lean_object* v_x_1346_, lean_object* v_x_1347_){
_start:
{
uint64_t v___x_1348_; size_t v___x_1349_; lean_object* v___x_1350_; 
v___x_1348_ = lean_string_hash(v_x_1347_);
v___x_1349_ = lean_uint64_to_usize(v___x_1348_);
v___x_1350_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_1346_, v___x_1349_, v_x_1347_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg___boxed(lean_object* v_x_1351_, lean_object* v_x_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v_x_1351_, v_x_1352_);
lean_dec_ref(v_x_1352_);
lean_dec_ref(v_x_1351_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupLspRequestHandler(lean_object* v_method_1354_){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1356_ = l_Lean_Server_requestHandlers;
v___x_1357_ = lean_st_ref_get(v___x_1356_);
v___x_1358_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v___x_1357_, v_method_1354_);
lean_dec(v___x_1357_);
v___x_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupLspRequestHandler___boxed(lean_object* v_method_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Lean_Server_lookupLspRequestHandler(v_method_1360_);
lean_dec_ref(v_method_1360_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0(lean_object* v_00_u03b2_1363_, lean_object* v_x_1364_, lean_object* v_x_1365_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v_x_1364_, v_x_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___boxed(lean_object* v_00_u03b2_1367_, lean_object* v_x_1368_, lean_object* v_x_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0(v_00_u03b2_1367_, v_x_1368_, v_x_1369_);
lean_dec_ref(v_x_1369_);
lean_dec_ref(v_x_1368_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0(lean_object* v_00_u03b2_1371_, lean_object* v_x_1372_, size_t v_x_1373_, lean_object* v_x_1374_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_1372_, v_x_1373_, v_x_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1376_, lean_object* v_x_1377_, lean_object* v_x_1378_, lean_object* v_x_1379_){
_start:
{
size_t v_x_355__boxed_1380_; lean_object* v_res_1381_; 
v_x_355__boxed_1380_ = lean_unbox_usize(v_x_1378_);
lean_dec(v_x_1378_);
v_res_1381_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0(v_00_u03b2_1376_, v_x_1377_, v_x_355__boxed_1380_, v_x_1379_);
lean_dec_ref(v_x_1379_);
lean_dec_ref(v_x_1377_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1382_, lean_object* v_keys_1383_, lean_object* v_vals_1384_, lean_object* v_heq_1385_, lean_object* v_i_1386_, lean_object* v_k_1387_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(v_keys_1383_, v_vals_1384_, v_i_1386_, v_k_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1389_, lean_object* v_keys_1390_, lean_object* v_vals_1391_, lean_object* v_heq_1392_, lean_object* v_i_1393_, lean_object* v_k_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1(v_00_u03b2_1389_, v_keys_1390_, v_vals_1391_, v_heq_1392_, v_i_1393_, v_k_1394_);
lean_dec_ref(v_k_1394_);
lean_dec_ref(v_vals_1391_);
lean_dec_ref(v_keys_1390_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__0(lean_object* v_inst_1399_, lean_object* v_method_1400_, lean_object* v_x_1401_){
_start:
{
lean_object* v_response_1403_; 
if (lean_obj_tag(v_x_1401_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
lean_dec_ref(v_inst_1399_);
v_a_1427_ = lean_ctor_get(v_x_1401_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_x_1401_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v_x_1401_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v_x_1401_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
else
{
lean_object* v_a_1435_; lean_object* v_response_x3f_1436_; 
v_a_1435_ = lean_ctor_get(v_x_1401_, 0);
lean_inc(v_a_1435_);
lean_dec_ref_known(v_x_1401_, 1);
v_response_x3f_1436_ = lean_ctor_get(v_a_1435_, 0);
if (lean_obj_tag(v_response_x3f_1436_) == 0)
{
lean_object* v_serialized_1437_; lean_object* v___x_1438_; 
v_serialized_1437_ = lean_ctor_get(v_a_1435_, 1);
lean_inc_ref(v_serialized_1437_);
lean_dec(v_a_1435_);
v___x_1438_ = l_Lean_Json_parse(v_serialized_1437_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1452_; 
lean_dec_ref(v_inst_1399_);
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1441_ = v___x_1438_;
v_isShared_1442_ = v_isSharedCheck_1452_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1438_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1452_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1443_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__2));
v___x_1444_ = lean_string_append(v___x_1443_, v_method_1400_);
v___x_1445_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1));
v___x_1446_ = lean_string_append(v___x_1444_, v___x_1445_);
v___x_1447_ = lean_string_append(v___x_1446_, v_a_1439_);
lean_dec(v_a_1439_);
v___x_1448_ = l_Lean_Server_RequestError_internalError(v___x_1447_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v___x_1448_);
v___x_1450_ = v___x_1441_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
else
{
lean_object* v_a_1453_; 
v_a_1453_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_a_1453_);
lean_dec_ref_known(v___x_1438_, 1);
v_response_1403_ = v_a_1453_;
goto v___jp_1402_;
}
}
else
{
lean_object* v_val_1454_; 
lean_inc_ref(v_response_x3f_1436_);
lean_dec(v_a_1435_);
v_val_1454_ = lean_ctor_get(v_response_x3f_1436_, 0);
lean_inc(v_val_1454_);
lean_dec_ref_known(v_response_x3f_1436_, 1);
v_response_1403_ = v_val_1454_;
goto v___jp_1402_;
}
}
v___jp_1402_:
{
lean_object* v___x_1404_; 
v___x_1404_ = lean_apply_1(v_inst_1399_, v_response_1403_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1418_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1407_ = v___x_1404_;
v_isShared_1408_ = v_isSharedCheck_1418_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1404_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1418_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1409_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__0));
v___x_1410_ = lean_string_append(v___x_1409_, v_method_1400_);
v___x_1411_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1));
v___x_1412_ = lean_string_append(v___x_1410_, v___x_1411_);
v___x_1413_ = lean_string_append(v___x_1412_, v_a_1405_);
lean_dec(v_a_1405_);
v___x_1414_ = l_Lean_Server_RequestError_internalError(v___x_1413_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 0, v___x_1414_);
v___x_1416_ = v___x_1407_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
v_a_1419_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1404_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1404_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__0___boxed(lean_object* v_inst_1455_, lean_object* v_method_1456_, lean_object* v_x_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__0(v_inst_1455_, v_method_1456_, v_x_1457_);
lean_dec_ref(v_method_1456_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__1(lean_object* v_inst_1459_, uint8_t v_val_1460_, lean_object* v_r_1461_){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1462_ = lean_apply_1(v_inst_1459_, v_r_1461_);
lean_inc(v___x_1462_);
v___x_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
v___x_1464_ = l_Lean_Json_compress(v___x_1462_);
v___x_1465_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1465_, 0, v___x_1463_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
lean_ctor_set_uint8(v___x_1465_, sizeof(void*)*2, v_val_1460_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__1___boxed(lean_object* v_inst_1466_, lean_object* v_val_1467_, lean_object* v_r_1468_){
_start:
{
uint8_t v_val_2282__boxed_1469_; lean_object* v_res_1470_; 
v_val_2282__boxed_1469_ = lean_unbox(v_val_1467_);
v_res_1470_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__1(v_inst_1466_, v_val_2282__boxed_1469_, v_r_1468_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__2(lean_object* v_val_1471_, lean_object* v___f_1472_, lean_object* v_inst_1473_, lean_object* v_handler_1474_, lean_object* v___f_1475_, lean_object* v_j_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v_handle_1479_; lean_object* v___x_1480_; 
v_handle_1479_ = lean_ctor_get(v_val_1471_, 1);
lean_inc_ref(v_handle_1479_);
lean_dec_ref(v_val_1471_);
lean_inc_ref(v___y_1477_);
lean_inc(v_j_1476_);
v___x_1480_ = lean_apply_3(v_handle_1479_, v_j_1476_, v___y_1477_, lean_box(0));
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_a_1481_);
lean_dec_ref_known(v___x_1480_, 1);
v___x_1482_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_1472_, v_a_1481_);
v___x_1483_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_1473_, v_j_1476_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1485_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref_known(v___x_1483_, 1);
lean_inc_ref(v___y_1477_);
v___x_1485_ = lean_apply_4(v_handler_1474_, v_a_1484_, v___x_1482_, v___y_1477_, lean_box(0));
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1495_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1495_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1495_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1490_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_1490_, 0, lean_box(0));
lean_closure_set(v___x_1490_, 1, lean_box(0));
lean_closure_set(v___x_1490_, 2, lean_box(0));
lean_closure_set(v___x_1490_, 3, v___f_1475_);
v___x_1491_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___x_1490_, v_a_1486_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1491_);
v___x_1493_ = v___x_1488_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_dec_ref(v___f_1475_);
v_a_1496_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1485_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1485_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
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
else
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
lean_dec_ref(v___x_1482_);
lean_dec_ref(v___f_1475_);
lean_dec_ref(v_handler_1474_);
v_a_1504_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1483_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1483_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
else
{
lean_dec(v_j_1476_);
lean_dec_ref(v___f_1475_);
lean_dec_ref(v_handler_1474_);
lean_dec_ref(v_inst_1473_);
lean_dec_ref(v___f_1472_);
return v___x_1480_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__2___boxed(lean_object* v_val_1512_, lean_object* v___f_1513_, lean_object* v_inst_1514_, lean_object* v_handler_1515_, lean_object* v___f_1516_, lean_object* v_j_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__2(v_val_1512_, v___f_1513_, v_inst_1514_, v_handler_1515_, v___f_1516_, v_j_1517_, v___y_1518_);
lean_dec_ref(v___y_1518_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg(lean_object* v_method_1523_, lean_object* v_inst_1524_, lean_object* v_inst_1525_, lean_object* v_inst_1526_, lean_object* v_handler_1527_){
_start:
{
lean_object* v___f_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
lean_inc_ref(v_method_1523_);
v___f_1529_ = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1529_, 0, v_inst_1525_);
lean_closure_set(v___f_1529_, 1, v_method_1523_);
v___x_1530_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__0));
v___x_1531_ = l_Lean_initializing();
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_dec_ref(v___f_1529_);
lean_dec_ref(v_handler_1527_);
lean_dec_ref(v_inst_1526_);
lean_dec_ref(v_inst_1524_);
v___x_1532_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__0));
v___x_1533_ = lean_string_append(v___x_1532_, v_method_1523_);
lean_dec_ref(v_method_1523_);
v___x_1534_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___x_1535_ = lean_string_append(v___x_1533_, v___x_1534_);
v___x_1536_ = lean_mk_io_user_error(v___x_1535_);
v___x_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
return v___x_1537_;
}
else
{
lean_object* v___x_1538_; lean_object* v___f_1539_; lean_object* v___x_1540_; lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1572_; 
v___x_1538_ = lean_box(v___x_1531_);
v___f_1539_ = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_1539_, 0, v_inst_1526_);
lean_closure_set(v___f_1539_, 1, v___x_1538_);
v___x_1540_ = l_Lean_Server_lookupLspRequestHandler(v_method_1523_);
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1543_ = v___x_1540_;
v_isShared_1544_ = v_isSharedCheck_1572_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1540_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1572_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
if (lean_obj_tag(v_a_1541_) == 1)
{
lean_object* v_val_1545_; lean_object* v___f_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v_fileSource_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1562_; 
v_val_1545_ = lean_ctor_get(v_a_1541_, 0);
lean_inc_n(v_val_1545_, 2);
lean_dec_ref_known(v_a_1541_, 1);
v___f_1546_ = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_1546_, 0, v_val_1545_);
lean_closure_set(v___f_1546_, 1, v___f_1529_);
lean_closure_set(v___f_1546_, 2, v_inst_1524_);
lean_closure_set(v___f_1546_, 3, v_handler_1527_);
lean_closure_set(v___f_1546_, 4, v___f_1539_);
v___x_1547_ = l_Lean_Server_requestHandlers;
v___x_1548_ = lean_st_ref_take(v___x_1547_);
v_fileSource_1549_ = lean_ctor_get(v_val_1545_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v_val_1545_);
if (v_isSharedCheck_1562_ == 0)
{
lean_object* v_unused_1563_; 
v_unused_1563_ = lean_ctor_get(v_val_1545_, 1);
lean_dec(v_unused_1563_);
v___x_1551_ = v_val_1545_;
v_isShared_1552_ = v_isSharedCheck_1562_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_fileSource_1549_);
lean_dec(v_val_1545_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1562_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___f_1553_; lean_object* v___x_1555_; 
v___f_1553_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 1, v___f_1546_);
v___x_1555_ = v___x_1551_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_fileSource_1549_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v___f_1546_);
v___x_1555_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1556_ = l_Lean_PersistentHashMap_insert___redArg(v___f_1553_, v___x_1530_, v___x_1548_, v_method_1523_, v___x_1555_);
v___x_1557_ = lean_st_ref_put(v___x_1547_, v___x_1556_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 0, v___x_1557_);
v___x_1559_ = v___x_1543_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
else
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1570_; 
lean_dec(v_a_1541_);
lean_dec_ref(v___f_1539_);
lean_dec_ref(v___f_1529_);
lean_dec_ref(v_handler_1527_);
lean_dec_ref(v_inst_1524_);
v___x_1564_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__0));
v___x_1565_ = lean_string_append(v___x_1564_, v_method_1523_);
lean_dec_ref(v_method_1523_);
v___x_1566_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__1));
v___x_1567_ = lean_string_append(v___x_1565_, v___x_1566_);
v___x_1568_ = lean_mk_io_user_error(v___x_1567_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set_tag(v___x_1543_, 1);
lean_ctor_set(v___x_1543_, 0, v___x_1568_);
v___x_1570_ = v___x_1543_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___boxed(lean_object* v_method_1573_, lean_object* v_inst_1574_, lean_object* v_inst_1575_, lean_object* v_inst_1576_, lean_object* v_handler_1577_, lean_object* v_a_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean_Server_chainLspRequestHandler___redArg(v_method_1573_, v_inst_1574_, v_inst_1575_, v_inst_1576_, v_handler_1577_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler(lean_object* v_method_1580_, lean_object* v_paramType_1581_, lean_object* v_inst_1582_, lean_object* v_respType_1583_, lean_object* v_inst_1584_, lean_object* v_inst_1585_, lean_object* v_handler_1586_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Lean_Server_chainLspRequestHandler___redArg(v_method_1580_, v_inst_1582_, v_inst_1584_, v_inst_1585_, v_handler_1586_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___boxed(lean_object* v_method_1589_, lean_object* v_paramType_1590_, lean_object* v_inst_1591_, lean_object* v_respType_1592_, lean_object* v_inst_1593_, lean_object* v_inst_1594_, lean_object* v_handler_1595_, lean_object* v_a_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Lean_Server_chainLspRequestHandler(v_method_1589_, v_paramType_1590_, v_inst_1591_, v_respType_1592_, v_inst_1593_, v_inst_1594_, v_handler_1595_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorIdx___impl(lean_object* v_x_1598_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_obj_tag_nat(v_x_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorIdx___impl___boxed(lean_object* v_x_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Lean_Server_RequestHandlerCompleteness_ctorIdx___impl(v_x_1600_);
lean_dec(v_x_1600_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(lean_object* v_t_1602_, lean_object* v_k_1603_){
_start:
{
if (lean_obj_tag(v_t_1602_) == 0)
{
return v_k_1603_;
}
else
{
lean_object* v_refreshMethod_1604_; lean_object* v_refreshIntervalMs_1605_; lean_object* v___x_1606_; 
v_refreshMethod_1604_ = lean_ctor_get(v_t_1602_, 0);
lean_inc_ref(v_refreshMethod_1604_);
v_refreshIntervalMs_1605_ = lean_ctor_get(v_t_1602_, 1);
lean_inc(v_refreshIntervalMs_1605_);
lean_dec_ref_known(v_t_1602_, 2);
v___x_1606_ = lean_apply_2(v_k_1603_, v_refreshMethod_1604_, v_refreshIntervalMs_1605_);
return v___x_1606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim(lean_object* v_motive_1607_, lean_object* v_ctorIdx_1608_, lean_object* v_t_1609_, lean_object* v_h_1610_, lean_object* v_k_1611_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_1609_, v_k_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim___boxed(lean_object* v_motive_1613_, lean_object* v_ctorIdx_1614_, lean_object* v_t_1615_, lean_object* v_h_1616_, lean_object* v_k_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim(v_motive_1613_, v_ctorIdx_1614_, v_t_1615_, v_h_1616_, v_k_1617_);
lean_dec(v_ctorIdx_1614_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_complete_elim___redArg(lean_object* v_t_1619_, lean_object* v_complete_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_1619_, v_complete_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_complete_elim(lean_object* v_motive_1622_, lean_object* v_t_1623_, lean_object* v_h_1624_, lean_object* v_complete_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_1623_, v_complete_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_partial_elim___redArg(lean_object* v_t_1627_, lean_object* v_partial_1628_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_1627_, v_partial_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_partial_elim(lean_object* v_motive_1630_, lean_object* v_t_1631_, lean_object* v_h_1632_, lean_object* v_partial_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_1631_, v_partial_1633_);
return v___x_1634_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_);
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1638_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_);
v___x_1639_ = lean_st_mk_ref(v___x_1638_);
v___x_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2____boxed(lean_object* v_a_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_();
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(lean_object* v_method_1644_, lean_object* v_state_1645_, lean_object* v_inst_1646_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_state_1645_, v_inst_1646_);
if (lean_obj_tag(v___x_1648_) == 1)
{
lean_object* v_val_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
v_val_1649_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1648_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_val_1649_);
lean_dec(v___x_1648_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
lean_ctor_set_tag(v___x_1651_, 0);
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_val_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
else
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
lean_dec(v___x_1648_);
v___x_1657_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0));
v___x_1658_ = lean_string_append(v___x_1657_, v_method_1644_);
v___x_1659_ = l_Lean_Server_RequestError_internalError(v___x_1658_);
v___x_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1659_);
return v___x_1660_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___boxed(lean_object* v_method_1661_, lean_object* v_state_1662_, lean_object* v_inst_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_1661_, v_state_1662_, v_inst_1663_);
lean_dec(v_inst_1663_);
lean_dec(v_state_1662_);
lean_dec_ref(v_method_1661_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(lean_object* v_method_1666_, lean_object* v_state_1667_, lean_object* v_stateType_1668_, lean_object* v_inst_1669_, lean_object* v_a_1670_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_1666_, v_state_1667_, v_inst_1669_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___boxed(lean_object* v_method_1673_, lean_object* v_state_1674_, lean_object* v_stateType_1675_, lean_object* v_inst_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_1673_, v_state_1674_, v_stateType_1675_, v_inst_1676_, v_a_1677_);
lean_dec_ref(v_a_1677_);
lean_dec(v_inst_1676_);
lean_dec(v_state_1674_);
lean_dec_ref(v_method_1673_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(lean_object* v_method_1680_, lean_object* v_state_1681_, lean_object* v_inst_1682_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_state_1681_, v_inst_1682_);
if (lean_obj_tag(v___x_1684_) == 1)
{
lean_object* v_val_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
v_val_1685_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1684_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_val_1685_);
lean_dec(v___x_1684_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
lean_ctor_set_tag(v___x_1687_, 0);
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_val_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
lean_dec(v___x_1684_);
v___x_1693_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0));
v___x_1694_ = lean_string_append(v___x_1693_, v_method_1680_);
v___x_1695_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
v___x_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1695_);
return v___x_1696_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg___boxed(lean_object* v_method_1697_, lean_object* v_state_1698_, lean_object* v_inst_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(v_method_1697_, v_state_1698_, v_inst_1699_);
lean_dec(v_inst_1699_);
lean_dec(v_state_1698_);
lean_dec_ref(v_method_1697_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21(lean_object* v_method_1702_, lean_object* v_state_1703_, lean_object* v_stateType_1704_, lean_object* v_inst_1705_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(v_method_1702_, v_state_1703_, v_inst_1705_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___boxed(lean_object* v_method_1708_, lean_object* v_state_1709_, lean_object* v_stateType_1710_, lean_object* v_inst_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21(v_method_1708_, v_state_1709_, v_stateType_1710_, v_inst_1711_);
lean_dec(v_inst_1711_);
lean_dec(v_state_1709_);
lean_dec_ref(v_method_1708_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1(lean_object* v_inst_1714_, lean_object* v_method_1715_, lean_object* v_inst_1716_, lean_object* v_handler_1717_, lean_object* v_inst_1718_, lean_object* v_param_1719_, lean_object* v_state_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_1714_, v_param_1719_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1725_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1724_);
lean_dec_ref_known(v___x_1723_, 1);
v___x_1725_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_1715_, v_state_1720_, v_inst_1716_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1727_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1725_, 1);
lean_inc_ref(v___y_1721_);
v___x_1727_ = lean_apply_4(v_handler_1717_, v_a_1724_, v_a_1726_, v___y_1721_, lean_box(0));
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1751_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1730_ = v___x_1727_;
v_isShared_1731_ = v_isSharedCheck_1751_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1727_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1751_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v_fst_1732_; lean_object* v_snd_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1750_; 
v_fst_1732_ = lean_ctor_get(v_a_1728_, 0);
v_snd_1733_ = lean_ctor_get(v_a_1728_, 1);
v_isSharedCheck_1750_ = !lean_is_exclusive(v_a_1728_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1735_ = v_a_1728_;
v_isShared_1736_ = v_isSharedCheck_1750_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_snd_1733_);
lean_inc(v_fst_1732_);
lean_dec(v_a_1728_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1750_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v_response_1737_; uint8_t v_isComplete_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1744_; 
v_response_1737_ = lean_ctor_get(v_fst_1732_, 0);
lean_inc(v_response_1737_);
v_isComplete_1738_ = lean_ctor_get_uint8(v_fst_1732_, sizeof(void*)*1);
lean_dec(v_fst_1732_);
v___x_1739_ = lean_apply_1(v_inst_1718_, v_response_1737_);
lean_inc(v___x_1739_);
v___x_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1739_);
v___x_1741_ = l_Lean_Json_compress(v___x_1739_);
v___x_1742_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1742_, 0, v___x_1740_);
lean_ctor_set(v___x_1742_, 1, v___x_1741_);
lean_ctor_set_uint8(v___x_1742_, sizeof(void*)*2, v_isComplete_1738_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 0, v_inst_1716_);
v___x_1744_ = v___x_1735_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_inst_1716_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v_snd_1733_);
v___x_1744_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
lean_object* v___x_1745_; lean_object* v___x_1747_; 
v___x_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1742_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v___x_1745_);
v___x_1747_ = v___x_1730_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
lean_dec_ref(v_inst_1718_);
lean_dec(v_inst_1716_);
v_a_1752_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1727_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1727_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
lean_dec(v_a_1724_);
lean_dec_ref(v_inst_1718_);
lean_dec_ref(v_handler_1717_);
lean_dec(v_inst_1716_);
v_a_1760_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1725_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1725_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
lean_dec_ref(v_inst_1718_);
lean_dec_ref(v_handler_1717_);
lean_dec(v_inst_1716_);
v_a_1768_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1723_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1723_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1___boxed(lean_object* v_inst_1776_, lean_object* v_method_1777_, lean_object* v_inst_1778_, lean_object* v_handler_1779_, lean_object* v_inst_1780_, lean_object* v_param_1781_, lean_object* v_state_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1(v_inst_1776_, v_method_1777_, v_inst_1778_, v_handler_1779_, v_inst_1780_, v_param_1781_, v_state_1782_, v___y_1783_);
lean_dec_ref(v___y_1783_);
lean_dec(v_state_1782_);
lean_dec_ref(v_method_1777_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0(lean_object* v_method_1786_, lean_object* v_inst_1787_, lean_object* v_onDidChange_1788_, lean_object* v_param_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_1786_, v___y_1790_, v_inst_1787_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v___x_1795_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1794_);
lean_dec_ref_known(v___x_1793_, 1);
lean_inc_ref(v___y_1791_);
v___x_1795_ = lean_apply_4(v_onDidChange_1788_, v_param_1789_, v_a_1794_, v___y_1791_, lean_box(0));
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1814_; 
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1798_ = v___x_1795_;
v_isShared_1799_ = v_isSharedCheck_1814_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1795_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1814_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v_snd_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1812_; 
v_snd_1800_ = lean_ctor_get(v_a_1796_, 1);
v_isSharedCheck_1812_ = !lean_is_exclusive(v_a_1796_);
if (v_isSharedCheck_1812_ == 0)
{
lean_object* v_unused_1813_; 
v_unused_1813_ = lean_ctor_get(v_a_1796_, 0);
lean_dec(v_unused_1813_);
v___x_1802_ = v_a_1796_;
v_isShared_1803_ = v_isSharedCheck_1812_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_snd_1800_);
lean_dec(v_a_1796_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1812_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v_inst_1787_);
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_inst_1787_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v_snd_1800_);
v___x_1805_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1809_; 
v___x_1806_ = lean_box(0);
v___x_1807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
lean_ctor_set(v___x_1807_, 1, v___x_1805_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v___x_1807_);
v___x_1809_ = v___x_1798_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1807_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
}
else
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1822_; 
lean_dec(v_inst_1787_);
v_a_1815_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1817_ = v___x_1795_;
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1795_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
lean_dec_ref(v_param_1789_);
lean_dec_ref(v_onDidChange_1788_);
lean_dec(v_inst_1787_);
v_a_1823_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1793_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1793_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object* v_method_1831_, lean_object* v_inst_1832_, lean_object* v_onDidChange_1833_, lean_object* v_param_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0(v_method_1831_, v_inst_1832_, v_onDidChange_1833_, v_param_1834_, v___y_1835_, v___y_1836_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec_ref(v_method_1831_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2(lean_object* v___x_1839_, lean_object* v_x_1840_){
_start:
{
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2___boxed(lean_object* v___x_1841_, lean_object* v_x_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2(v___x_1841_, v_x_1842_);
lean_dec_ref(v_x_1842_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3(lean_object* v___x_1844_, lean_object* v_x_1845_){
_start:
{
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3___boxed(lean_object* v___x_1846_, lean_object* v_x_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3(v___x_1846_, v_x_1847_);
lean_dec_ref(v_x_1847_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4(lean_object* v_val_1849_, lean_object* v___f_1850_, lean_object* v_param_1851_, lean_object* v_x_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = lean_st_ref_get(v_val_1849_);
lean_inc_ref(v___y_1853_);
v___x_1856_ = lean_apply_4(v___f_1850_, v_param_1851_, v___x_1855_, v___y_1853_, lean_box(0));
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1867_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1859_ = v___x_1856_;
v_isShared_1860_ = v_isSharedCheck_1867_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1856_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1867_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v_fst_1861_; lean_object* v_snd_1862_; lean_object* v___x_1863_; lean_object* v___x_1865_; 
v_fst_1861_ = lean_ctor_get(v_a_1857_, 0);
lean_inc(v_fst_1861_);
v_snd_1862_ = lean_ctor_get(v_a_1857_, 1);
lean_inc(v_snd_1862_);
lean_dec(v_a_1857_);
v___x_1863_ = lean_st_ref_swap(v_val_1849_, v_snd_1862_);
lean_dec(v___x_1863_);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v_fst_1861_);
v___x_1865_ = v___x_1859_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_fst_1861_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
v_a_1868_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1856_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1856_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4___boxed(lean_object* v_val_1876_, lean_object* v___f_1877_, lean_object* v_param_1878_, lean_object* v_x_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4(v_val_1876_, v___f_1877_, v_param_1878_, v_x_1879_, v___y_1880_);
lean_dec_ref(v___y_1880_);
lean_dec(v_val_1876_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5(lean_object* v___f_1883_, lean_object* v___f_1884_, lean_object* v_lastTask_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v___x_1889_; lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1899_; 
v___x_1889_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_lastTask_1885_, v___f_1883_, v___y_1887_);
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1892_ = v___x_1889_;
v_isShared_1893_ = v_isSharedCheck_1899_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1889_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1899_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1897_; 
lean_inc(v_a_1890_);
v___x_1894_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_1884_, v_a_1890_);
v___x_1895_ = lean_st_ref_swap(v___y_1886_, v___x_1894_);
lean_dec(v___x_1895_);
if (v_isShared_1893_ == 0)
{
v___x_1897_ = v___x_1892_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1890_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5___boxed(lean_object* v___f_1900_, lean_object* v___f_1901_, lean_object* v_lastTask_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5(v___f_1900_, v___f_1901_, v_lastTask_1902_, v___y_1903_, v___y_1904_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6(lean_object* v_val_1907_, lean_object* v___f_1908_, lean_object* v___f_1909_, lean_object* v___f_1910_, lean_object* v___x_1911_, lean_object* v___f_1912_, lean_object* v___f_1913_, lean_object* v_val_1914_, lean_object* v_param_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v___f_1918_; lean_object* v___f_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_6224__overap_1922_; lean_object* v___x_1923_; 
v___f_1918_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_1918_, 0, v_val_1907_);
lean_closure_set(v___f_1918_, 1, v___f_1908_);
lean_closure_set(v___f_1918_, 2, v_param_1915_);
v___f_1919_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5___boxed), 6, 2);
lean_closure_set(v___f_1919_, 0, v___f_1918_);
lean_closure_set(v___f_1919_, 1, v___f_1909_);
v___x_1920_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_1920_, 0, lean_box(0));
lean_closure_set(v___x_1920_, 1, lean_box(0));
lean_closure_set(v___x_1920_, 2, lean_box(0));
lean_closure_set(v___x_1920_, 3, v___f_1910_);
lean_inc_ref(v___x_1911_);
v___x_1921_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_1921_, 0, lean_box(0));
lean_closure_set(v___x_1921_, 1, lean_box(0));
lean_closure_set(v___x_1921_, 2, v___x_1911_);
lean_closure_set(v___x_1921_, 3, lean_box(0));
lean_closure_set(v___x_1921_, 4, lean_box(0));
lean_closure_set(v___x_1921_, 5, v___x_1920_);
lean_closure_set(v___x_1921_, 6, v___f_1919_);
v___x_6224__overap_1922_ = l_Std_Mutex_atomically___redArg(v___x_1911_, v___f_1912_, v___f_1913_, v_val_1914_, v___x_1921_);
lean_inc_ref(v___y_1916_);
v___x_1923_ = lean_apply_2(v___x_6224__overap_1922_, v___y_1916_, lean_box(0));
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6___boxed(lean_object* v_val_1924_, lean_object* v___f_1925_, lean_object* v___f_1926_, lean_object* v___f_1927_, lean_object* v___x_1928_, lean_object* v___f_1929_, lean_object* v___f_1930_, lean_object* v_val_1931_, lean_object* v_param_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6(v_val_1924_, v___f_1925_, v___f_1926_, v___f_1927_, v___x_1928_, v___f_1929_, v___f_1930_, v_val_1931_, v_param_1932_, v___y_1933_);
lean_dec_ref(v___y_1933_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7(lean_object* v_val_1936_, lean_object* v___f_1937_, lean_object* v_param_1938_, lean_object* v___x_1939_, lean_object* v_x_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1943_ = lean_st_ref_get(v_val_1936_);
lean_inc_ref(v___y_1941_);
v___x_1944_ = lean_apply_4(v___f_1937_, v_param_1938_, v___x_1943_, v___y_1941_, lean_box(0));
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1954_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1947_ = v___x_1944_;
v_isShared_1948_ = v_isSharedCheck_1954_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1944_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1954_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v_snd_1949_; lean_object* v___x_1950_; lean_object* v___x_1952_; 
v_snd_1949_ = lean_ctor_get(v_a_1945_, 1);
lean_inc(v_snd_1949_);
lean_dec(v_a_1945_);
v___x_1950_ = lean_st_ref_swap(v_val_1936_, v_snd_1949_);
lean_dec(v___x_1950_);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 0, v___x_1939_);
v___x_1952_ = v___x_1947_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1939_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
v_a_1955_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1944_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1944_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7___boxed(lean_object* v_val_1963_, lean_object* v___f_1964_, lean_object* v_param_1965_, lean_object* v___x_1966_, lean_object* v_x_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7(v_val_1963_, v___f_1964_, v_param_1965_, v___x_1966_, v_x_1967_, v___y_1968_);
lean_dec_ref(v___y_1968_);
lean_dec(v_val_1963_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8(lean_object* v___f_1971_, lean_object* v___f_1972_, lean_object* v___x_1973_, lean_object* v_lastTask_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v___x_1978_; lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1988_; 
v___x_1978_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_lastTask_1974_, v___f_1971_, v___y_1976_);
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1981_ = v___x_1978_;
v_isShared_1982_ = v_isSharedCheck_1988_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1978_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1988_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1986_; 
v___x_1983_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_1972_, v_a_1979_);
v___x_1984_ = lean_st_ref_swap(v___y_1975_, v___x_1983_);
lean_dec(v___x_1984_);
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 0, v___x_1973_);
v___x_1986_ = v___x_1981_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1973_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8___boxed(lean_object* v___f_1989_, lean_object* v___f_1990_, lean_object* v___x_1991_, lean_object* v_lastTask_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8(v___f_1989_, v___f_1990_, v___x_1991_, v_lastTask_1992_, v___y_1993_, v___y_1994_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9(lean_object* v_val_1997_, lean_object* v___f_1998_, lean_object* v___x_1999_, lean_object* v___f_2000_, lean_object* v___f_2001_, lean_object* v___x_2002_, lean_object* v___f_2003_, lean_object* v___f_2004_, lean_object* v_val_2005_, lean_object* v_param_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v___f_2009_; lean_object* v___f_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_6278__overap_2013_; lean_object* v___x_2014_; 
v___f_2009_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_2009_, 0, v_val_1997_);
lean_closure_set(v___f_2009_, 1, v___f_1998_);
lean_closure_set(v___f_2009_, 2, v_param_2006_);
lean_closure_set(v___f_2009_, 3, v___x_1999_);
v___f_2010_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8___boxed), 7, 3);
lean_closure_set(v___f_2010_, 0, v___f_2009_);
lean_closure_set(v___f_2010_, 1, v___f_2000_);
lean_closure_set(v___f_2010_, 2, v___x_1999_);
v___x_2011_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_2011_, 0, lean_box(0));
lean_closure_set(v___x_2011_, 1, lean_box(0));
lean_closure_set(v___x_2011_, 2, lean_box(0));
lean_closure_set(v___x_2011_, 3, v___f_2001_);
lean_inc_ref(v___x_2002_);
v___x_2012_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2012_, 0, lean_box(0));
lean_closure_set(v___x_2012_, 1, lean_box(0));
lean_closure_set(v___x_2012_, 2, v___x_2002_);
lean_closure_set(v___x_2012_, 3, lean_box(0));
lean_closure_set(v___x_2012_, 4, lean_box(0));
lean_closure_set(v___x_2012_, 5, v___x_2011_);
lean_closure_set(v___x_2012_, 6, v___f_2010_);
v___x_6278__overap_2013_ = l_Std_Mutex_atomically___redArg(v___x_2002_, v___f_2003_, v___f_2004_, v_val_2005_, v___x_2012_);
lean_inc_ref(v___y_2007_);
v___x_2014_ = lean_apply_2(v___x_6278__overap_2013_, v___y_2007_, lean_box(0));
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9___boxed(lean_object* v_val_2015_, lean_object* v___f_2016_, lean_object* v___x_2017_, lean_object* v___f_2018_, lean_object* v___f_2019_, lean_object* v___x_2020_, lean_object* v___f_2021_, lean_object* v___f_2022_, lean_object* v_val_2023_, lean_object* v_param_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9(v_val_2015_, v___f_2016_, v___x_2017_, v___f_2018_, v___f_2019_, v___x_2020_, v___f_2021_, v___f_2022_, v_val_2023_, v_param_2024_, v___y_2025_);
lean_dec_ref(v___y_2025_);
return v_res_2027_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1(void){
_start:
{
lean_object* v___x_2029_; 
v___x_2029_ = l_instMonadEIO___redArg();
return v___x_2029_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1);
v___x_2031_ = l_ReaderT_instMonad___redArg(v___x_2030_);
return v___x_2031_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15(void){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = lean_box(0);
v___x_2058_ = lean_task_pure(v___x_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(lean_object* v_method_2059_, lean_object* v_completeness_2060_, lean_object* v_inst_2061_, lean_object* v_inst_2062_, lean_object* v_inst_2063_, lean_object* v_inst_2064_, lean_object* v_initState_2065_, lean_object* v_handler_2066_, lean_object* v_onDidChange_2067_){
_start:
{
lean_object* v___f_2069_; lean_object* v___f_2070_; lean_object* v___f_2071_; lean_object* v___x_2072_; lean_object* v___f_2073_; lean_object* v___f_2074_; lean_object* v___f_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; 
lean_inc_ref(v_inst_2061_);
v___f_2069_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2069_, 0, v_inst_2061_);
lean_closure_set(v___f_2069_, 1, v_inst_2062_);
lean_inc_n(v_inst_2064_, 2);
lean_inc_ref_n(v_method_2059_, 2);
v___f_2070_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1___boxed), 9, 5);
lean_closure_set(v___f_2070_, 0, v_inst_2061_);
lean_closure_set(v___f_2070_, 1, v_method_2059_);
lean_closure_set(v___f_2070_, 2, v_inst_2064_);
lean_closure_set(v___f_2070_, 3, v_handler_2066_);
lean_closure_set(v___f_2070_, 4, v_inst_2063_);
v___f_2071_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0___boxed), 7, 3);
lean_closure_set(v___f_2071_, 0, v_method_2059_);
lean_closure_set(v___f_2071_, 1, v_inst_2064_);
lean_closure_set(v___f_2071_, 2, v_onDidChange_2067_);
v___x_2072_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2);
v___f_2073_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__5));
v___f_2074_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__7));
v___f_2075_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__11));
v___x_2076_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__0));
v___x_2077_ = l_Lean_initializing();
if (v___x_2077_ == 0)
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
lean_dec_ref(v___f_2071_);
lean_dec_ref(v___f_2070_);
lean_dec_ref(v___f_2069_);
lean_dec(v_initState_2065_);
lean_dec(v_inst_2064_);
lean_dec(v_completeness_2060_);
v___x_2078_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__12));
v___x_2079_ = lean_string_append(v___x_2078_, v_method_2059_);
lean_dec_ref(v_method_2059_);
v___x_2080_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___x_2081_ = lean_string_append(v___x_2079_, v___x_2080_);
v___x_2082_ = lean_mk_io_user_error(v___x_2081_);
v___x_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
return v___x_2083_;
}
else
{
lean_object* v___x_2084_; lean_object* v___f_2085_; lean_object* v___f_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___f_2091_; lean_object* v___f_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___f_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2084_ = lean_box(0);
v___f_2085_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__13));
v___f_2086_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__14));
v___x_2087_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15);
v___x_2088_ = l_Std_Mutex_new___redArg(v___x_2087_);
v___x_2089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2089_, 0, v_inst_2064_);
lean_ctor_set(v___x_2089_, 1, v_initState_2065_);
lean_inc_ref(v___x_2089_);
v___x_2090_ = lean_st_mk_ref(v___x_2089_);
lean_inc_ref_n(v___x_2088_, 2);
lean_inc_ref(v___f_2070_);
lean_inc_n(v___x_2090_, 2);
v___f_2091_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6___boxed), 11, 8);
lean_closure_set(v___f_2091_, 0, v___x_2090_);
lean_closure_set(v___f_2091_, 1, v___f_2070_);
lean_closure_set(v___f_2091_, 2, v___f_2085_);
lean_closure_set(v___f_2091_, 3, v___f_2075_);
lean_closure_set(v___f_2091_, 4, v___x_2072_);
lean_closure_set(v___f_2091_, 5, v___f_2073_);
lean_closure_set(v___f_2091_, 6, v___f_2074_);
lean_closure_set(v___f_2091_, 7, v___x_2088_);
lean_inc_ref(v___f_2071_);
v___f_2092_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9___boxed), 12, 9);
lean_closure_set(v___f_2092_, 0, v___x_2090_);
lean_closure_set(v___f_2092_, 1, v___f_2071_);
lean_closure_set(v___f_2092_, 2, v___x_2084_);
lean_closure_set(v___f_2092_, 3, v___f_2086_);
lean_closure_set(v___f_2092_, 4, v___f_2075_);
lean_closure_set(v___f_2092_, 5, v___x_2072_);
lean_closure_set(v___f_2092_, 6, v___f_2073_);
lean_closure_set(v___f_2092_, 7, v___f_2074_);
lean_closure_set(v___f_2092_, 8, v___x_2088_);
v___x_2093_ = l_Lean_Server_statefulRequestHandlers;
v___x_2094_ = lean_st_ref_take(v___x_2093_);
v___f_2095_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
v___x_2096_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2096_, 0, v___f_2069_);
lean_ctor_set(v___x_2096_, 1, v___f_2070_);
lean_ctor_set(v___x_2096_, 2, v___f_2091_);
lean_ctor_set(v___x_2096_, 3, v___f_2071_);
lean_ctor_set(v___x_2096_, 4, v___f_2092_);
lean_ctor_set(v___x_2096_, 5, v___x_2088_);
lean_ctor_set(v___x_2096_, 6, v___x_2089_);
lean_ctor_set(v___x_2096_, 7, v___x_2090_);
lean_ctor_set(v___x_2096_, 8, v_completeness_2060_);
v___x_2097_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2095_, v___x_2076_, v___x_2094_, v_method_2059_, v___x_2096_);
v___x_2098_ = lean_st_ref_put(v___x_2093_, v___x_2097_);
v___x_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
return v___x_2099_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2100_, lean_object* v_completeness_2101_, lean_object* v_inst_2102_, lean_object* v_inst_2103_, lean_object* v_inst_2104_, lean_object* v_inst_2105_, lean_object* v_initState_2106_, lean_object* v_handler_2107_, lean_object* v_onDidChange_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2100_, v_completeness_2101_, v_inst_2102_, v_inst_2103_, v_inst_2104_, v_inst_2105_, v_initState_2106_, v_handler_2107_, v_onDidChange_2108_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(lean_object* v_method_2111_, lean_object* v_completeness_2112_, lean_object* v_paramType_2113_, lean_object* v_inst_2114_, lean_object* v_inst_2115_, lean_object* v_respType_2116_, lean_object* v_inst_2117_, lean_object* v_stateType_2118_, lean_object* v_inst_2119_, lean_object* v_initState_2120_, lean_object* v_handler_2121_, lean_object* v_onDidChange_2122_){
_start:
{
lean_object* v___x_2124_; 
v___x_2124_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2111_, v_completeness_2112_, v_inst_2114_, v_inst_2115_, v_inst_2117_, v_inst_2119_, v_initState_2120_, v_handler_2121_, v_onDidChange_2122_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___boxed(lean_object* v_method_2125_, lean_object* v_completeness_2126_, lean_object* v_paramType_2127_, lean_object* v_inst_2128_, lean_object* v_inst_2129_, lean_object* v_respType_2130_, lean_object* v_inst_2131_, lean_object* v_stateType_2132_, lean_object* v_inst_2133_, lean_object* v_initState_2134_, lean_object* v_handler_2135_, lean_object* v_onDidChange_2136_, lean_object* v_a_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(v_method_2125_, v_completeness_2126_, v_paramType_2127_, v_inst_2128_, v_inst_2129_, v_respType_2130_, v_inst_2131_, v_stateType_2132_, v_inst_2133_, v_initState_2134_, v_handler_2135_, v_onDidChange_2136_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(lean_object* v_method_2139_, lean_object* v_completeness_2140_, lean_object* v_inst_2141_, lean_object* v_inst_2142_, lean_object* v_inst_2143_, lean_object* v_inst_2144_, lean_object* v_initState_2145_, lean_object* v_handler_2146_, lean_object* v_onDidChange_2147_){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___f_2152_; uint8_t v___x_2153_; 
v___x_2149_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__0));
v___x_2150_ = l_Lean_Server_requestHandlers;
v___x_2151_ = lean_st_ref_get(v___x_2150_);
v___f_2152_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
lean_inc_ref(v_method_2139_);
v___x_2153_ = l_Lean_PersistentHashMap_contains___redArg(v___f_2152_, v___x_2149_, v___x_2151_, v_method_2139_);
if (v___x_2153_ == 0)
{
lean_object* v___x_2154_; 
v___x_2154_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2139_, v_completeness_2140_, v_inst_2141_, v_inst_2142_, v_inst_2143_, v_inst_2144_, v_initState_2145_, v_handler_2146_, v_onDidChange_2147_);
return v___x_2154_;
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
lean_dec_ref(v_onDidChange_2147_);
lean_dec_ref(v_handler_2146_);
lean_dec(v_initState_2145_);
lean_dec(v_inst_2144_);
lean_dec_ref(v_inst_2143_);
lean_dec_ref(v_inst_2142_);
lean_dec_ref(v_inst_2141_);
lean_dec(v_completeness_2140_);
v___x_2155_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__12));
v___x_2156_ = lean_string_append(v___x_2155_, v_method_2139_);
lean_dec_ref(v_method_2139_);
v___x_2157_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__4));
v___x_2158_ = lean_string_append(v___x_2156_, v___x_2157_);
v___x_2159_ = lean_mk_io_user_error(v___x_2158_);
v___x_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
return v___x_2160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2161_, lean_object* v_completeness_2162_, lean_object* v_inst_2163_, lean_object* v_inst_2164_, lean_object* v_inst_2165_, lean_object* v_inst_2166_, lean_object* v_initState_2167_, lean_object* v_handler_2168_, lean_object* v_onDidChange_2169_, lean_object* v_a_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2161_, v_completeness_2162_, v_inst_2163_, v_inst_2164_, v_inst_2165_, v_inst_2166_, v_initState_2167_, v_handler_2168_, v_onDidChange_2169_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler(lean_object* v_method_2172_, lean_object* v_completeness_2173_, lean_object* v_paramType_2174_, lean_object* v_inst_2175_, lean_object* v_inst_2176_, lean_object* v_respType_2177_, lean_object* v_inst_2178_, lean_object* v_stateType_2179_, lean_object* v_inst_2180_, lean_object* v_initState_2181_, lean_object* v_handler_2182_, lean_object* v_onDidChange_2183_){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2172_, v_completeness_2173_, v_inst_2175_, v_inst_2176_, v_inst_2178_, v_inst_2180_, v_initState_2181_, v_handler_2182_, v_onDidChange_2183_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___boxed(lean_object* v_method_2186_, lean_object* v_completeness_2187_, lean_object* v_paramType_2188_, lean_object* v_inst_2189_, lean_object* v_inst_2190_, lean_object* v_respType_2191_, lean_object* v_inst_2192_, lean_object* v_stateType_2193_, lean_object* v_inst_2194_, lean_object* v_initState_2195_, lean_object* v_handler_2196_, lean_object* v_onDidChange_2197_, lean_object* v_a_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler(v_method_2186_, v_completeness_2187_, v_paramType_2188_, v_inst_2189_, v_inst_2190_, v_respType_2191_, v_inst_2192_, v_stateType_2193_, v_inst_2194_, v_initState_2195_, v_handler_2196_, v_onDidChange_2197_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0(lean_object* v_handler_2200_, lean_object* v_p_2201_, lean_object* v_s_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v___x_2205_; 
lean_inc_ref(v___y_2203_);
v___x_2205_ = lean_apply_4(v_handler_2200_, v_p_2201_, v_s_2202_, v___y_2203_, lean_box(0));
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2224_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2208_ = v___x_2205_;
v_isShared_2209_ = v_isSharedCheck_2224_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2205_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2224_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v_fst_2210_; lean_object* v_snd_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2223_; 
v_fst_2210_ = lean_ctor_get(v_a_2206_, 0);
v_snd_2211_ = lean_ctor_get(v_a_2206_, 1);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_a_2206_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2213_ = v_a_2206_;
v_isShared_2214_ = v_isSharedCheck_2223_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_snd_2211_);
lean_inc(v_fst_2210_);
lean_dec(v_a_2206_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2223_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
uint8_t v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2218_; 
v___x_2215_ = 1;
v___x_2216_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2216_, 0, v_fst_2210_);
lean_ctor_set_uint8(v___x_2216_, sizeof(void*)*1, v___x_2215_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 0, v___x_2216_);
v___x_2218_ = v___x_2213_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2216_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_snd_2211_);
v___x_2218_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
lean_object* v___x_2220_; 
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v___x_2218_);
v___x_2220_ = v___x_2208_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
v_a_2225_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2205_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2205_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object* v_handler_2233_, lean_object* v_p_2234_, lean_object* v_s_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0(v_handler_2233_, v_p_2234_, v_s_2235_, v___y_2236_);
lean_dec_ref(v___y_2236_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(lean_object* v_method_2239_, lean_object* v_inst_2240_, lean_object* v_inst_2241_, lean_object* v_inst_2242_, lean_object* v_inst_2243_, lean_object* v_initState_2244_, lean_object* v_handler_2245_, lean_object* v_onDidChange_2246_){
_start:
{
lean_object* v_handler_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v_handler_2248_ = lean_alloc_closure((void*)(l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v_handler_2248_, 0, v_handler_2245_);
v___x_2249_ = lean_box(0);
v___x_2250_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2239_, v___x_2249_, v_inst_2240_, v_inst_2241_, v_inst_2242_, v_inst_2243_, v_initState_2244_, v_handler_2248_, v_onDidChange_2246_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2251_, lean_object* v_inst_2252_, lean_object* v_inst_2253_, lean_object* v_inst_2254_, lean_object* v_inst_2255_, lean_object* v_initState_2256_, lean_object* v_handler_2257_, lean_object* v_onDidChange_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(v_method_2251_, v_inst_2252_, v_inst_2253_, v_inst_2254_, v_inst_2255_, v_initState_2256_, v_handler_2257_, v_onDidChange_2258_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler(lean_object* v_method_2261_, lean_object* v_paramType_2262_, lean_object* v_inst_2263_, lean_object* v_inst_2264_, lean_object* v_respType_2265_, lean_object* v_inst_2266_, lean_object* v_stateType_2267_, lean_object* v_inst_2268_, lean_object* v_initState_2269_, lean_object* v_handler_2270_, lean_object* v_onDidChange_2271_){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(v_method_2261_, v_inst_2263_, v_inst_2264_, v_inst_2266_, v_inst_2268_, v_initState_2269_, v_handler_2270_, v_onDidChange_2271_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___boxed(lean_object* v_method_2274_, lean_object* v_paramType_2275_, lean_object* v_inst_2276_, lean_object* v_inst_2277_, lean_object* v_respType_2278_, lean_object* v_inst_2279_, lean_object* v_stateType_2280_, lean_object* v_inst_2281_, lean_object* v_initState_2282_, lean_object* v_handler_2283_, lean_object* v_onDidChange_2284_, lean_object* v_a_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler(v_method_2274_, v_paramType_2275_, v_inst_2276_, v_inst_2277_, v_respType_2278_, v_inst_2279_, v_stateType_2280_, v_inst_2281_, v_initState_2282_, v_handler_2283_, v_onDidChange_2284_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(lean_object* v_method_2287_, lean_object* v_refreshMethod_2288_, lean_object* v_refreshIntervalMs_2289_, lean_object* v_inst_2290_, lean_object* v_inst_2291_, lean_object* v_inst_2292_, lean_object* v_inst_2293_, lean_object* v_initState_2294_, lean_object* v_handler_2295_, lean_object* v_onDidChange_2296_){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2298_, 0, v_refreshMethod_2288_);
lean_ctor_set(v___x_2298_, 1, v_refreshIntervalMs_2289_);
v___x_2299_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2287_, v___x_2298_, v_inst_2290_, v_inst_2291_, v_inst_2292_, v_inst_2293_, v_initState_2294_, v_handler_2295_, v_onDidChange_2296_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2300_, lean_object* v_refreshMethod_2301_, lean_object* v_refreshIntervalMs_2302_, lean_object* v_inst_2303_, lean_object* v_inst_2304_, lean_object* v_inst_2305_, lean_object* v_inst_2306_, lean_object* v_initState_2307_, lean_object* v_handler_2308_, lean_object* v_onDidChange_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(v_method_2300_, v_refreshMethod_2301_, v_refreshIntervalMs_2302_, v_inst_2303_, v_inst_2304_, v_inst_2305_, v_inst_2306_, v_initState_2307_, v_handler_2308_, v_onDidChange_2309_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler(lean_object* v_method_2312_, lean_object* v_refreshMethod_2313_, lean_object* v_refreshIntervalMs_2314_, lean_object* v_paramType_2315_, lean_object* v_inst_2316_, lean_object* v_inst_2317_, lean_object* v_respType_2318_, lean_object* v_inst_2319_, lean_object* v_stateType_2320_, lean_object* v_inst_2321_, lean_object* v_initState_2322_, lean_object* v_handler_2323_, lean_object* v_onDidChange_2324_){
_start:
{
lean_object* v___x_2326_; 
v___x_2326_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(v_method_2312_, v_refreshMethod_2313_, v_refreshIntervalMs_2314_, v_inst_2316_, v_inst_2317_, v_inst_2319_, v_inst_2321_, v_initState_2322_, v_handler_2323_, v_onDidChange_2324_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___boxed(lean_object* v_method_2327_, lean_object* v_refreshMethod_2328_, lean_object* v_refreshIntervalMs_2329_, lean_object* v_paramType_2330_, lean_object* v_inst_2331_, lean_object* v_inst_2332_, lean_object* v_respType_2333_, lean_object* v_inst_2334_, lean_object* v_stateType_2335_, lean_object* v_inst_2336_, lean_object* v_initState_2337_, lean_object* v_handler_2338_, lean_object* v_onDidChange_2339_, lean_object* v_a_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_Lean_Server_registerPartialStatefulLspRequestHandler(v_method_2327_, v_refreshMethod_2328_, v_refreshIntervalMs_2329_, v_paramType_2330_, v_inst_2331_, v_inst_2332_, v_respType_2333_, v_inst_2334_, v_stateType_2335_, v_inst_2336_, v_initState_2337_, v_handler_2338_, v_onDidChange_2339_);
return v_res_2341_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2342_, lean_object* v_i_2343_, lean_object* v_k_2344_){
_start:
{
lean_object* v___x_2345_; uint8_t v___x_2346_; 
v___x_2345_ = lean_array_get_size(v_keys_2342_);
v___x_2346_ = lean_nat_dec_lt(v_i_2343_, v___x_2345_);
if (v___x_2346_ == 0)
{
lean_dec(v_i_2343_);
return v___x_2346_;
}
else
{
lean_object* v_k_x27_2347_; uint8_t v___x_2348_; 
v_k_x27_2347_ = lean_array_fget_borrowed(v_keys_2342_, v_i_2343_);
v___x_2348_ = lean_string_dec_eq(v_k_2344_, v_k_x27_2347_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2349_ = lean_unsigned_to_nat(1u);
v___x_2350_ = lean_nat_add(v_i_2343_, v___x_2349_);
lean_dec(v_i_2343_);
v_i_2343_ = v___x_2350_;
goto _start;
}
else
{
lean_dec(v_i_2343_);
return v___x_2346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2352_, lean_object* v_i_2353_, lean_object* v_k_2354_){
_start:
{
uint8_t v_res_2355_; lean_object* v_r_2356_; 
v_res_2355_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_keys_2352_, v_i_2353_, v_k_2354_);
lean_dec_ref(v_k_2354_);
lean_dec_ref(v_keys_2352_);
v_r_2356_ = lean_box(v_res_2355_);
return v_r_2356_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(lean_object* v_x_2357_, size_t v_x_2358_, lean_object* v_x_2359_){
_start:
{
if (lean_obj_tag(v_x_2357_) == 0)
{
lean_object* v_es_2360_; lean_object* v___x_2361_; size_t v___x_2362_; size_t v___x_2363_; lean_object* v_j_2364_; lean_object* v___x_2365_; 
v_es_2360_ = lean_ctor_get(v_x_2357_, 0);
v___x_2361_ = lean_box(2);
v___x_2362_ = ((size_t)31ULL);
v___x_2363_ = lean_usize_land(v_x_2358_, v___x_2362_);
v_j_2364_ = lean_usize_to_nat(v___x_2363_);
v___x_2365_ = lean_array_get_borrowed(v___x_2361_, v_es_2360_, v_j_2364_);
lean_dec(v_j_2364_);
switch(lean_obj_tag(v___x_2365_))
{
case 0:
{
lean_object* v_key_2366_; uint8_t v___x_2367_; 
v_key_2366_ = lean_ctor_get(v___x_2365_, 0);
v___x_2367_ = lean_string_dec_eq(v_x_2359_, v_key_2366_);
return v___x_2367_;
}
case 1:
{
lean_object* v_node_2368_; size_t v___x_2369_; size_t v___x_2370_; 
v_node_2368_ = lean_ctor_get(v___x_2365_, 0);
v___x_2369_ = ((size_t)5ULL);
v___x_2370_ = lean_usize_shift_right(v_x_2358_, v___x_2369_);
v_x_2357_ = v_node_2368_;
v_x_2358_ = v___x_2370_;
goto _start;
}
default: 
{
uint8_t v___x_2372_; 
v___x_2372_ = 0;
return v___x_2372_;
}
}
}
else
{
lean_object* v_ks_2373_; lean_object* v___x_2374_; uint8_t v___x_2375_; 
v_ks_2373_ = lean_ctor_get(v_x_2357_, 0);
v___x_2374_ = lean_unsigned_to_nat(0u);
v___x_2375_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_ks_2373_, v___x_2374_, v_x_2359_);
return v___x_2375_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg___boxed(lean_object* v_x_2376_, lean_object* v_x_2377_, lean_object* v_x_2378_){
_start:
{
size_t v_x_226__boxed_2379_; uint8_t v_res_2380_; lean_object* v_r_2381_; 
v_x_226__boxed_2379_ = lean_unbox_usize(v_x_2377_);
lean_dec(v_x_2377_);
v_res_2380_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_2376_, v_x_226__boxed_2379_, v_x_2378_);
lean_dec_ref(v_x_2378_);
lean_dec_ref(v_x_2376_);
v_r_2381_ = lean_box(v_res_2380_);
return v_r_2381_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(lean_object* v_x_2382_, lean_object* v_x_2383_){
_start:
{
uint64_t v___x_2384_; size_t v___x_2385_; uint8_t v___x_2386_; 
v___x_2384_ = lean_string_hash(v_x_2383_);
v___x_2385_ = lean_uint64_to_usize(v___x_2384_);
v___x_2386_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_2382_, v___x_2385_, v_x_2383_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg___boxed(lean_object* v_x_2387_, lean_object* v_x_2388_){
_start:
{
uint8_t v_res_2389_; lean_object* v_r_2390_; 
v_res_2389_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v_x_2387_, v_x_2388_);
lean_dec_ref(v_x_2388_);
lean_dec_ref(v_x_2387_);
v_r_2390_ = lean_box(v_res_2389_);
return v_r_2390_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_isStatefulLspRequestMethod(lean_object* v_method_2391_){
_start:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; uint8_t v___x_2395_; 
v___x_2393_ = l_Lean_Server_statefulRequestHandlers;
v___x_2394_ = lean_st_ref_get(v___x_2393_);
v___x_2395_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v___x_2394_, v_method_2391_);
lean_dec(v___x_2394_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_isStatefulLspRequestMethod___boxed(lean_object* v_method_2396_, lean_object* v_a_2397_){
_start:
{
uint8_t v_res_2398_; lean_object* v_r_2399_; 
v_res_2398_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_2396_);
lean_dec_ref(v_method_2396_);
v_r_2399_ = lean_box(v_res_2398_);
return v_r_2399_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0(lean_object* v_00_u03b2_2400_, lean_object* v_x_2401_, lean_object* v_x_2402_){
_start:
{
uint8_t v___x_2403_; 
v___x_2403_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v_x_2401_, v_x_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___boxed(lean_object* v_00_u03b2_2404_, lean_object* v_x_2405_, lean_object* v_x_2406_){
_start:
{
uint8_t v_res_2407_; lean_object* v_r_2408_; 
v_res_2407_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0(v_00_u03b2_2404_, v_x_2405_, v_x_2406_);
lean_dec_ref(v_x_2406_);
lean_dec_ref(v_x_2405_);
v_r_2408_ = lean_box(v_res_2407_);
return v_r_2408_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0(lean_object* v_00_u03b2_2409_, lean_object* v_x_2410_, size_t v_x_2411_, lean_object* v_x_2412_){
_start:
{
uint8_t v___x_2413_; 
v___x_2413_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_2410_, v_x_2411_, v_x_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2414_, lean_object* v_x_2415_, lean_object* v_x_2416_, lean_object* v_x_2417_){
_start:
{
size_t v_x_296__boxed_2418_; uint8_t v_res_2419_; lean_object* v_r_2420_; 
v_x_296__boxed_2418_ = lean_unbox_usize(v_x_2416_);
lean_dec(v_x_2416_);
v_res_2419_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0(v_00_u03b2_2414_, v_x_2415_, v_x_296__boxed_2418_, v_x_2417_);
lean_dec_ref(v_x_2417_);
lean_dec_ref(v_x_2415_);
v_r_2420_ = lean_box(v_res_2419_);
return v_r_2420_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2421_, lean_object* v_keys_2422_, lean_object* v_vals_2423_, lean_object* v_heq_2424_, lean_object* v_i_2425_, lean_object* v_k_2426_){
_start:
{
uint8_t v___x_2427_; 
v___x_2427_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_keys_2422_, v_i_2425_, v_k_2426_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2428_, lean_object* v_keys_2429_, lean_object* v_vals_2430_, lean_object* v_heq_2431_, lean_object* v_i_2432_, lean_object* v_k_2433_){
_start:
{
uint8_t v_res_2434_; lean_object* v_r_2435_; 
v_res_2434_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1(v_00_u03b2_2428_, v_keys_2429_, v_vals_2430_, v_heq_2431_, v_i_2432_, v_k_2433_);
lean_dec_ref(v_k_2433_);
lean_dec_ref(v_vals_2430_);
lean_dec_ref(v_keys_2429_);
v_r_2435_ = lean_box(v_res_2434_);
return v_r_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupStatefulLspRequestHandler(lean_object* v_method_2436_){
_start:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2438_ = l_Lean_Server_statefulRequestHandlers;
v___x_2439_ = lean_st_ref_get(v___x_2438_);
v___x_2440_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v___x_2439_, v_method_2436_);
lean_dec(v___x_2439_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupStatefulLspRequestHandler___boxed(lean_object* v_method_2441_, lean_object* v_a_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_2441_);
lean_dec_ref(v_method_2441_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(lean_object* v_as_2444_, size_t v_i_2445_, size_t v_stop_2446_, lean_object* v_b_2447_){
_start:
{
lean_object* v___y_2449_; uint8_t v___x_2453_; 
v___x_2453_ = lean_usize_dec_eq(v_i_2445_, v_stop_2446_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2454_; lean_object* v_snd_2455_; lean_object* v_completeness_2456_; 
v___x_2454_ = lean_array_uget(v_as_2444_, v_i_2445_);
v_snd_2455_ = lean_ctor_get(v___x_2454_, 1);
v_completeness_2456_ = lean_ctor_get(v_snd_2455_, 8);
lean_inc(v_completeness_2456_);
if (lean_obj_tag(v_completeness_2456_) == 1)
{
lean_object* v_fst_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2474_; 
v_fst_2457_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2474_ == 0)
{
lean_object* v_unused_2475_; 
v_unused_2475_ = lean_ctor_get(v___x_2454_, 1);
lean_dec(v_unused_2475_);
v___x_2459_ = v___x_2454_;
v_isShared_2460_ = v_isSharedCheck_2474_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_fst_2457_);
lean_dec(v___x_2454_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2474_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v_refreshMethod_2461_; lean_object* v_refreshIntervalMs_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2473_; 
v_refreshMethod_2461_ = lean_ctor_get(v_completeness_2456_, 0);
v_refreshIntervalMs_2462_ = lean_ctor_get(v_completeness_2456_, 1);
v_isSharedCheck_2473_ = !lean_is_exclusive(v_completeness_2456_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2464_ = v_completeness_2456_;
v_isShared_2465_ = v_isSharedCheck_2473_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_refreshIntervalMs_2462_);
lean_inc(v_refreshMethod_2461_);
lean_dec(v_completeness_2456_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2473_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 1, v_refreshIntervalMs_2462_);
lean_ctor_set(v___x_2459_, 0, v_refreshMethod_2461_);
v___x_2467_ = v___x_2459_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_refreshMethod_2461_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v_refreshIntervalMs_2462_);
v___x_2467_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
lean_object* v___x_2469_; 
if (v_isShared_2465_ == 0)
{
lean_ctor_set_tag(v___x_2464_, 0);
lean_ctor_set(v___x_2464_, 1, v___x_2467_);
lean_ctor_set(v___x_2464_, 0, v_fst_2457_);
v___x_2469_ = v___x_2464_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_fst_2457_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v___x_2467_);
v___x_2469_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
lean_object* v___x_2470_; 
v___x_2470_ = lean_array_push(v_b_2447_, v___x_2469_);
v___y_2449_ = v___x_2470_;
goto v___jp_2448_;
}
}
}
}
}
else
{
lean_dec(v_completeness_2456_);
lean_dec(v___x_2454_);
v___y_2449_ = v_b_2447_;
goto v___jp_2448_;
}
}
else
{
return v_b_2447_;
}
v___jp_2448_:
{
size_t v___x_2450_; size_t v___x_2451_; 
v___x_2450_ = ((size_t)1ULL);
v___x_2451_ = lean_usize_add(v_i_2445_, v___x_2450_);
v_i_2445_ = v___x_2451_;
v_b_2447_ = v___y_2449_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2___boxed(lean_object* v_as_2476_, lean_object* v_i_2477_, lean_object* v_stop_2478_, lean_object* v_b_2479_){
_start:
{
size_t v_i_boxed_2480_; size_t v_stop_boxed_2481_; lean_object* v_res_2482_; 
v_i_boxed_2480_ = lean_unbox_usize(v_i_2477_);
lean_dec(v_i_2477_);
v_stop_boxed_2481_ = lean_unbox_usize(v_stop_2478_);
lean_dec(v_stop_2478_);
v_res_2482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_2476_, v_i_boxed_2480_, v_stop_boxed_2481_, v_b_2479_);
lean_dec_ref(v_as_2476_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(lean_object* v_as_2485_, lean_object* v_start_2486_, lean_object* v_stop_2487_){
_start:
{
lean_object* v___x_2488_; uint8_t v___x_2489_; 
v___x_2488_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___closed__0));
v___x_2489_ = lean_nat_dec_lt(v_start_2486_, v_stop_2487_);
if (v___x_2489_ == 0)
{
return v___x_2488_;
}
else
{
lean_object* v___x_2490_; uint8_t v___x_2491_; 
v___x_2490_ = lean_array_get_size(v_as_2485_);
v___x_2491_ = lean_nat_dec_le(v_stop_2487_, v___x_2490_);
if (v___x_2491_ == 0)
{
uint8_t v___x_2492_; 
v___x_2492_ = lean_nat_dec_lt(v_start_2486_, v___x_2490_);
if (v___x_2492_ == 0)
{
return v___x_2488_;
}
else
{
size_t v___x_2493_; size_t v___x_2494_; lean_object* v___x_2495_; 
v___x_2493_ = lean_usize_of_nat(v_start_2486_);
v___x_2494_ = lean_usize_of_nat(v___x_2490_);
v___x_2495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_2485_, v___x_2493_, v___x_2494_, v___x_2488_);
return v___x_2495_;
}
}
else
{
size_t v___x_2496_; size_t v___x_2497_; lean_object* v___x_2498_; 
v___x_2496_ = lean_usize_of_nat(v_start_2486_);
v___x_2497_ = lean_usize_of_nat(v_stop_2487_);
v___x_2498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_2485_, v___x_2496_, v___x_2497_, v___x_2488_);
return v___x_2498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___boxed(lean_object* v_as_2499_, lean_object* v_start_2500_, lean_object* v_stop_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(v_as_2499_, v_start_2500_, v_stop_2501_);
lean_dec(v_stop_2501_);
lean_dec(v_start_2500_);
lean_dec_ref(v_as_2499_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_f_2503_, lean_object* v_keys_2504_, lean_object* v_vals_2505_, lean_object* v_i_2506_, lean_object* v_acc_2507_){
_start:
{
lean_object* v___x_2508_; uint8_t v___x_2509_; 
v___x_2508_ = lean_array_get_size(v_keys_2504_);
v___x_2509_ = lean_nat_dec_lt(v_i_2506_, v___x_2508_);
if (v___x_2509_ == 0)
{
lean_dec(v_i_2506_);
lean_dec(v_f_2503_);
return v_acc_2507_;
}
else
{
lean_object* v_k_2510_; lean_object* v_v_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v_k_2510_ = lean_array_fget_borrowed(v_keys_2504_, v_i_2506_);
v_v_2511_ = lean_array_fget_borrowed(v_vals_2505_, v_i_2506_);
lean_inc(v_f_2503_);
lean_inc(v_v_2511_);
lean_inc(v_k_2510_);
v___x_2512_ = lean_apply_3(v_f_2503_, v_acc_2507_, v_k_2510_, v_v_2511_);
v___x_2513_ = lean_unsigned_to_nat(1u);
v___x_2514_ = lean_nat_add(v_i_2506_, v___x_2513_);
lean_dec(v_i_2506_);
v_i_2506_ = v___x_2514_;
v_acc_2507_ = v___x_2512_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_f_2516_, lean_object* v_keys_2517_, lean_object* v_vals_2518_, lean_object* v_i_2519_, lean_object* v_acc_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_2516_, v_keys_2517_, v_vals_2518_, v_i_2519_, v_acc_2520_);
lean_dec_ref(v_vals_2518_);
lean_dec_ref(v_keys_2517_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_f_2522_, lean_object* v_as_2523_, size_t v_i_2524_, size_t v_stop_2525_, lean_object* v_b_2526_){
_start:
{
lean_object* v___y_2528_; uint8_t v___x_2532_; 
v___x_2532_ = lean_usize_dec_eq(v_i_2524_, v_stop_2525_);
if (v___x_2532_ == 0)
{
lean_object* v___x_2533_; 
v___x_2533_ = lean_array_uget_borrowed(v_as_2523_, v_i_2524_);
switch(lean_obj_tag(v___x_2533_))
{
case 0:
{
lean_object* v_key_2534_; lean_object* v_val_2535_; lean_object* v___x_2536_; 
v_key_2534_ = lean_ctor_get(v___x_2533_, 0);
v_val_2535_ = lean_ctor_get(v___x_2533_, 1);
lean_inc(v_f_2522_);
lean_inc(v_val_2535_);
lean_inc(v_key_2534_);
v___x_2536_ = lean_apply_3(v_f_2522_, v_b_2526_, v_key_2534_, v_val_2535_);
v___y_2528_ = v___x_2536_;
goto v___jp_2527_;
}
case 1:
{
lean_object* v_node_2537_; lean_object* v___x_2538_; 
v_node_2537_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_f_2522_);
v___x_2538_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2522_, v_node_2537_, v_b_2526_);
v___y_2528_ = v___x_2538_;
goto v___jp_2527_;
}
default: 
{
v___y_2528_ = v_b_2526_;
goto v___jp_2527_;
}
}
}
else
{
lean_dec(v_f_2522_);
return v_b_2526_;
}
v___jp_2527_:
{
size_t v___x_2529_; size_t v___x_2530_; 
v___x_2529_ = ((size_t)1ULL);
v___x_2530_ = lean_usize_add(v_i_2524_, v___x_2529_);
v_i_2524_ = v___x_2530_;
v_b_2526_ = v___y_2528_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_2539_, lean_object* v_x_2540_, lean_object* v_x_2541_){
_start:
{
if (lean_obj_tag(v_x_2540_) == 0)
{
lean_object* v_es_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; uint8_t v___x_2545_; 
v_es_2542_ = lean_ctor_get(v_x_2540_, 0);
v___x_2543_ = lean_unsigned_to_nat(0u);
v___x_2544_ = lean_array_get_size(v_es_2542_);
v___x_2545_ = lean_nat_dec_lt(v___x_2543_, v___x_2544_);
if (v___x_2545_ == 0)
{
lean_dec(v_f_2539_);
return v_x_2541_;
}
else
{
size_t v___x_2546_; size_t v___x_2547_; lean_object* v___x_2548_; 
v___x_2546_ = ((size_t)0ULL);
v___x_2547_ = lean_usize_of_nat(v___x_2544_);
v___x_2548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_2539_, v_es_2542_, v___x_2546_, v___x_2547_, v_x_2541_);
return v___x_2548_;
}
}
else
{
lean_object* v_ks_2549_; lean_object* v_vs_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v_ks_2549_ = lean_ctor_get(v_x_2540_, 0);
v_vs_2550_ = lean_ctor_get(v_x_2540_, 1);
v___x_2551_ = lean_unsigned_to_nat(0u);
v___x_2552_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_2539_, v_ks_2549_, v_vs_2550_, v___x_2551_, v_x_2541_);
return v___x_2552_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_2553_, lean_object* v_x_2554_, lean_object* v_x_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2553_, v_x_2554_, v_x_2555_);
lean_dec_ref(v_x_2554_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_f_2557_, lean_object* v_as_2558_, lean_object* v_i_2559_, lean_object* v_stop_2560_, lean_object* v_b_2561_){
_start:
{
size_t v_i_boxed_2562_; size_t v_stop_boxed_2563_; lean_object* v_res_2564_; 
v_i_boxed_2562_ = lean_unbox_usize(v_i_2559_);
lean_dec(v_i_2559_);
v_stop_boxed_2563_ = lean_unbox_usize(v_stop_2560_);
lean_dec(v_stop_2560_);
v_res_2564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_2557_, v_as_2558_, v_i_boxed_2562_, v_stop_boxed_2563_, v_b_2561_);
lean_dec_ref(v_as_2558_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___lam__0(lean_object* v_f_2565_, lean_object* v_x1_2566_, lean_object* v_x2_2567_, lean_object* v_x3_2568_){
_start:
{
lean_object* v___x_2569_; 
v___x_2569_ = lean_apply_3(v_f_2565_, v_x1_2566_, v_x2_2567_, v_x3_2568_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(lean_object* v_map_2570_, lean_object* v_f_2571_, lean_object* v_init_2572_){
_start:
{
lean_object* v___f_2573_; lean_object* v___x_2574_; 
v___f_2573_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2573_, 0, v_f_2571_);
v___x_2574_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v___f_2573_, v_map_2570_, v_init_2572_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___boxed(lean_object* v_map_2575_, lean_object* v_f_2576_, lean_object* v_init_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_map_2575_, v_f_2576_, v_init_2577_);
lean_dec_ref(v_map_2575_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___lam__0(lean_object* v_ps_2579_, lean_object* v_k_2580_, lean_object* v_v_2581_){
_start:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2582_, 0, v_k_2580_);
lean_ctor_set(v___x_2582_, 1, v_v_2581_);
v___x_2583_ = lean_array_push(v_ps_2579_, v___x_2582_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(lean_object* v_m_2587_){
_start:
{
lean_object* v___f_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___f_2588_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__0));
v___x_2589_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__1));
v___x_2590_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_m_2587_, v___f_2588_, v___x_2589_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___boxed(lean_object* v_m_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v_m_2591_);
lean_dec_ref(v_m_2591_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_partialLspRequestHandlerMethods(){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2594_ = l_Lean_Server_statefulRequestHandlers;
v___x_2595_ = lean_st_ref_get(v___x_2594_);
v___x_2596_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v___x_2595_);
lean_dec(v___x_2595_);
v___x_2597_ = lean_unsigned_to_nat(0u);
v___x_2598_ = lean_array_get_size(v___x_2596_);
v___x_2599_ = l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(v___x_2596_, v___x_2597_, v___x_2598_);
lean_dec_ref(v___x_2596_);
v___x_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_partialLspRequestHandlerMethods___boxed(lean_object* v_a_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Lean_Server_partialLspRequestHandlerMethods();
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0(lean_object* v_00_u03b2_2603_, lean_object* v_m_2604_){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v_m_2604_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___boxed(lean_object* v_00_u03b2_2606_, lean_object* v_m_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0(v_00_u03b2_2606_, v_m_2607_);
lean_dec_ref(v_m_2607_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0(lean_object* v_00_u03c3_2609_, lean_object* v_00_u03b2_2610_, lean_object* v_map_2611_, lean_object* v_f_2612_, lean_object* v_init_2613_){
_start:
{
lean_object* v___x_2614_; 
v___x_2614_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_map_2611_, v_f_2612_, v_init_2613_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___boxed(lean_object* v_00_u03c3_2615_, lean_object* v_00_u03b2_2616_, lean_object* v_map_2617_, lean_object* v_f_2618_, lean_object* v_init_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0(v_00_u03c3_2615_, v_00_u03b2_2616_, v_map_2617_, v_f_2618_, v_init_2619_);
lean_dec_ref(v_map_2617_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg(lean_object* v_map_2621_, lean_object* v_f_2622_, lean_object* v_init_2623_){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2622_, v_map_2621_, v_init_2623_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_2625_, lean_object* v_f_2626_, lean_object* v_init_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg(v_map_2625_, v_f_2626_, v_init_2627_);
lean_dec_ref(v_map_2625_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_2629_, lean_object* v_00_u03b2_2630_, lean_object* v_map_2631_, lean_object* v_f_2632_, lean_object* v_init_2633_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2632_, v_map_2631_, v_init_2633_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_2635_, lean_object* v_00_u03b2_2636_, lean_object* v_map_2637_, lean_object* v_f_2638_, lean_object* v_init_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1(v_00_u03c3_2635_, v_00_u03b2_2636_, v_map_2637_, v_f_2638_, v_init_2639_);
lean_dec_ref(v_map_2637_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_2641_, lean_object* v_00_u03b1_2642_, lean_object* v_00_u03b2_2643_, lean_object* v_f_2644_, lean_object* v_x_2645_, lean_object* v_x_2646_){
_start:
{
lean_object* v___x_2647_; 
v___x_2647_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2644_, v_x_2645_, v_x_2646_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_2648_, lean_object* v_00_u03b1_2649_, lean_object* v_00_u03b2_2650_, lean_object* v_f_2651_, lean_object* v_x_2652_, lean_object* v_x_2653_){
_start:
{
lean_object* v_res_2654_; 
v_res_2654_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_2648_, v_00_u03b1_2649_, v_00_u03b2_2650_, v_f_2651_, v_x_2652_, v_x_2653_);
lean_dec_ref(v_x_2652_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_2655_, lean_object* v_00_u03b2_2656_, lean_object* v_00_u03c3_2657_, lean_object* v_f_2658_, lean_object* v_as_2659_, size_t v_i_2660_, size_t v_stop_2661_, lean_object* v_b_2662_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_2658_, v_as_2659_, v_i_2660_, v_stop_2661_, v_b_2662_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2664_, lean_object* v_00_u03b2_2665_, lean_object* v_00_u03c3_2666_, lean_object* v_f_2667_, lean_object* v_as_2668_, lean_object* v_i_2669_, lean_object* v_stop_2670_, lean_object* v_b_2671_){
_start:
{
size_t v_i_boxed_2672_; size_t v_stop_boxed_2673_; lean_object* v_res_2674_; 
v_i_boxed_2672_ = lean_unbox_usize(v_i_2669_);
lean_dec(v_i_2669_);
v_stop_boxed_2673_ = lean_unbox_usize(v_stop_2670_);
lean_dec(v_stop_2670_);
v_res_2674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_2664_, v_00_u03b2_2665_, v_00_u03c3_2666_, v_f_2667_, v_as_2668_, v_i_boxed_2672_, v_stop_boxed_2673_, v_b_2671_);
lean_dec_ref(v_as_2668_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03c3_2675_, lean_object* v_00_u03b1_2676_, lean_object* v_00_u03b2_2677_, lean_object* v_f_2678_, lean_object* v_keys_2679_, lean_object* v_vals_2680_, lean_object* v_heq_2681_, lean_object* v_i_2682_, lean_object* v_acc_2683_){
_start:
{
lean_object* v___x_2684_; 
v___x_2684_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_2678_, v_keys_2679_, v_vals_2680_, v_i_2682_, v_acc_2683_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03c3_2685_, lean_object* v_00_u03b1_2686_, lean_object* v_00_u03b2_2687_, lean_object* v_f_2688_, lean_object* v_keys_2689_, lean_object* v_vals_2690_, lean_object* v_heq_2691_, lean_object* v_i_2692_, lean_object* v_acc_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6(v_00_u03c3_2685_, v_00_u03b1_2686_, v_00_u03b2_2687_, v_f_2688_, v_keys_2689_, v_vals_2690_, v_heq_2691_, v_i_2692_, v_acc_2693_);
lean_dec_ref(v_vals_2690_);
lean_dec_ref(v_keys_2689_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0(lean_object* v_inst_2695_, lean_object* v_pureOnDidChange_2696_, lean_object* v_method_2697_, lean_object* v_onDidChange_2698_, lean_object* v_p_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
lean_inc(v_inst_2695_);
v___x_2703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2703_, 0, v_inst_2695_);
lean_ctor_set(v___x_2703_, 1, v___y_2700_);
lean_inc_ref(v___y_2701_);
lean_inc_ref(v_p_2699_);
v___x_2704_ = lean_apply_4(v_pureOnDidChange_2696_, v_p_2699_, v___x_2703_, v___y_2701_, lean_box(0));
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v_a_2705_; lean_object* v_snd_2706_; lean_object* v___x_2707_; 
v_a_2705_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_a_2705_);
lean_dec_ref_known(v___x_2704_, 1);
v_snd_2706_ = lean_ctor_get(v_a_2705_, 1);
lean_inc(v_snd_2706_);
lean_dec(v_a_2705_);
v___x_2707_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_2697_, v_snd_2706_, v_inst_2695_);
lean_dec(v_inst_2695_);
lean_dec(v_snd_2706_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; lean_object* v___x_2709_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
lean_inc(v_a_2708_);
lean_dec_ref_known(v___x_2707_, 1);
lean_inc_ref(v___y_2701_);
v___x_2709_ = lean_apply_4(v_onDidChange_2698_, v_p_2699_, v_a_2708_, v___y_2701_, lean_box(0));
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2727_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2712_ = v___x_2709_;
v_isShared_2713_ = v_isSharedCheck_2727_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2709_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2727_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v_snd_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2725_; 
v_snd_2714_ = lean_ctor_get(v_a_2710_, 1);
v_isSharedCheck_2725_ = !lean_is_exclusive(v_a_2710_);
if (v_isSharedCheck_2725_ == 0)
{
lean_object* v_unused_2726_; 
v_unused_2726_ = lean_ctor_get(v_a_2710_, 0);
lean_dec(v_unused_2726_);
v___x_2716_ = v_a_2710_;
v_isShared_2717_ = v_isSharedCheck_2725_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_snd_2714_);
lean_dec(v_a_2710_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2725_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2718_; lean_object* v___x_2720_; 
v___x_2718_ = lean_box(0);
if (v_isShared_2717_ == 0)
{
lean_ctor_set(v___x_2716_, 0, v___x_2718_);
v___x_2720_ = v___x_2716_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2718_);
lean_ctor_set(v_reuseFailAlloc_2724_, 1, v_snd_2714_);
v___x_2720_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
lean_object* v___x_2722_; 
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 0, v___x_2720_);
v___x_2722_ = v___x_2712_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2720_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
}
else
{
return v___x_2709_;
}
}
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
lean_dec_ref(v_p_2699_);
lean_dec_ref(v_onDidChange_2698_);
v_a_2728_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2707_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2707_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
else
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2743_; 
lean_dec_ref(v_p_2699_);
lean_dec_ref(v_onDidChange_2698_);
lean_dec(v_inst_2695_);
v_a_2736_ = lean_ctor_get(v___x_2704_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2738_ = v___x_2704_;
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2704_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2741_; 
if (v_isShared_2739_ == 0)
{
v___x_2741_ = v___x_2738_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2736_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object* v_inst_2744_, lean_object* v_pureOnDidChange_2745_, lean_object* v_method_2746_, lean_object* v_onDidChange_2747_, lean_object* v_p_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0(v_inst_2744_, v_pureOnDidChange_2745_, v_method_2746_, v_onDidChange_2747_, v_p_2748_, v___y_2749_, v___y_2750_);
lean_dec_ref(v___y_2750_);
lean_dec_ref(v_method_2746_);
return v_res_2752_;
}
}
static lean_object* _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2754_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__0));
v___x_2755_ = l_Lean_Server_RequestError_internalError(v___x_2754_);
return v___x_2755_;
}
}
static lean_object* _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__2));
v___x_2758_ = l_Lean_Server_RequestError_internalError(v___x_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1(lean_object* v_inst_2759_, lean_object* v_inst_2760_, lean_object* v_pureHandle_2761_, lean_object* v_inst_2762_, lean_object* v_method_2763_, lean_object* v_handler_2764_, lean_object* v_p_2765_, lean_object* v_s_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
lean_inc(v_p_2765_);
v___x_2769_ = lean_apply_1(v_inst_2759_, v_p_2765_);
lean_inc(v_inst_2760_);
v___x_2770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2770_, 0, v_inst_2760_);
lean_ctor_set(v___x_2770_, 1, v_s_2766_);
lean_inc_ref(v___y_2767_);
v___x_2771_ = lean_apply_4(v_pureHandle_2761_, v___x_2769_, v___x_2770_, v___y_2767_, lean_box(0));
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2806_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2774_ = v___x_2771_;
v_isShared_2775_ = v_isSharedCheck_2806_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2771_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2806_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v_fst_2776_; lean_object* v_snd_2777_; lean_object* v_response_x3f_2778_; lean_object* v_serialized_2779_; uint8_t v_isComplete_2780_; lean_object* v_a_2782_; 
v_fst_2776_ = lean_ctor_get(v_a_2772_, 0);
lean_inc(v_fst_2776_);
v_snd_2777_ = lean_ctor_get(v_a_2772_, 1);
lean_inc(v_snd_2777_);
lean_dec(v_a_2772_);
v_response_x3f_2778_ = lean_ctor_get(v_fst_2776_, 0);
lean_inc(v_response_x3f_2778_);
v_serialized_2779_ = lean_ctor_get(v_fst_2776_, 1);
lean_inc_ref(v_serialized_2779_);
v_isComplete_2780_ = lean_ctor_get_uint8(v_fst_2776_, sizeof(void*)*2);
lean_dec(v_fst_2776_);
if (lean_obj_tag(v_response_x3f_2778_) == 0)
{
lean_object* v___x_2801_; 
v___x_2801_ = l_Lean_Json_parse(v_serialized_2779_);
if (lean_obj_tag(v___x_2801_) == 1)
{
lean_object* v_a_2802_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2802_);
lean_dec_ref_known(v___x_2801_, 1);
v_a_2782_ = v_a_2802_;
goto v___jp_2781_;
}
else
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
lean_dec_ref(v___x_2801_);
lean_dec(v_snd_2777_);
lean_del_object(v___x_2774_);
lean_dec(v_p_2765_);
lean_dec_ref(v_handler_2764_);
lean_dec_ref(v_inst_2762_);
lean_dec(v_inst_2760_);
v___x_2803_ = lean_obj_once(&l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3, &l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3_once, _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3);
v___x_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2803_);
return v___x_2804_;
}
}
else
{
lean_object* v_val_2805_; 
lean_dec_ref(v_serialized_2779_);
v_val_2805_ = lean_ctor_get(v_response_x3f_2778_, 0);
lean_inc(v_val_2805_);
lean_dec_ref_known(v_response_x3f_2778_, 1);
v_a_2782_ = v_val_2805_;
goto v___jp_2781_;
}
v___jp_2781_:
{
lean_object* v___x_2783_; 
v___x_2783_ = lean_apply_1(v_inst_2762_, v_a_2782_);
if (lean_obj_tag(v___x_2783_) == 1)
{
lean_object* v_a_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
lean_del_object(v___x_2774_);
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_a_2784_);
lean_dec_ref_known(v___x_2783_, 1);
v___x_2785_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2785_, 0, v_a_2784_);
lean_ctor_set_uint8(v___x_2785_, sizeof(void*)*1, v_isComplete_2780_);
v___x_2786_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_2763_, v_snd_2777_, v_inst_2760_);
lean_dec(v_inst_2760_);
lean_dec(v_snd_2777_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; lean_object* v___x_2788_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
lean_dec_ref_known(v___x_2786_, 1);
lean_inc_ref(v___y_2767_);
v___x_2788_ = lean_apply_5(v_handler_2764_, v_p_2765_, v___x_2785_, v_a_2787_, v___y_2767_, lean_box(0));
return v___x_2788_;
}
else
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
lean_dec_ref_known(v___x_2785_, 1);
lean_dec(v_p_2765_);
lean_dec_ref(v_handler_2764_);
v_a_2789_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v___x_2786_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2786_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
}
else
{
lean_object* v___x_2797_; lean_object* v___x_2799_; 
lean_dec_ref(v___x_2783_);
lean_dec(v_snd_2777_);
lean_dec(v_p_2765_);
lean_dec_ref(v_handler_2764_);
lean_dec(v_inst_2760_);
v___x_2797_ = lean_obj_once(&l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1, &l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1_once, _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1);
if (v_isShared_2775_ == 0)
{
lean_ctor_set_tag(v___x_2774_, 1);
lean_ctor_set(v___x_2774_, 0, v___x_2797_);
v___x_2799_ = v___x_2774_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v___x_2797_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
lean_dec(v_p_2765_);
lean_dec_ref(v_handler_2764_);
lean_dec_ref(v_inst_2762_);
lean_dec(v_inst_2760_);
v_a_2807_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2809_ = v___x_2771_;
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2771_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___boxed(lean_object* v_inst_2815_, lean_object* v_inst_2816_, lean_object* v_pureHandle_2817_, lean_object* v_inst_2818_, lean_object* v_method_2819_, lean_object* v_handler_2820_, lean_object* v_p_2821_, lean_object* v_s_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1(v_inst_2815_, v_inst_2816_, v_pureHandle_2817_, v_inst_2818_, v_method_2819_, v_handler_2820_, v_p_2821_, v_s_2822_, v___y_2823_);
lean_dec_ref(v___y_2823_);
lean_dec_ref(v_method_2819_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg(lean_object* v_method_2827_, lean_object* v_inst_2828_, lean_object* v_inst_2829_, lean_object* v_inst_2830_, lean_object* v_inst_2831_, lean_object* v_inst_2832_, lean_object* v_inst_2833_, lean_object* v_handler_2834_, lean_object* v_onDidChange_2835_){
_start:
{
uint8_t v___x_2837_; 
v___x_2837_ = l_Lean_initializing();
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; 
lean_dec_ref(v_onDidChange_2835_);
lean_dec_ref(v_handler_2834_);
lean_dec(v_inst_2833_);
lean_dec_ref(v_inst_2832_);
lean_dec_ref(v_inst_2831_);
lean_dec_ref(v_inst_2830_);
lean_dec_ref(v_inst_2829_);
lean_dec_ref(v_inst_2828_);
v___x_2838_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0));
v___x_2839_ = lean_string_append(v___x_2838_, v_method_2827_);
lean_dec_ref(v_method_2827_);
v___x_2840_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___x_2841_ = lean_string_append(v___x_2839_, v___x_2840_);
v___x_2842_ = lean_mk_io_user_error(v___x_2841_);
v___x_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2842_);
return v___x_2843_;
}
else
{
lean_object* v___x_2844_; 
v___x_2844_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_2827_);
if (lean_obj_tag(v___x_2844_) == 1)
{
lean_object* v_val_2845_; lean_object* v_pureHandle_2846_; lean_object* v_pureOnDidChange_2847_; lean_object* v_initState_2848_; lean_object* v_completeness_2849_; lean_object* v___f_2850_; lean_object* v___f_2851_; lean_object* v___x_2852_; 
v_val_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_val_2845_);
lean_dec_ref_known(v___x_2844_, 1);
v_pureHandle_2846_ = lean_ctor_get(v_val_2845_, 1);
lean_inc_ref(v_pureHandle_2846_);
v_pureOnDidChange_2847_ = lean_ctor_get(v_val_2845_, 3);
lean_inc_ref(v_pureOnDidChange_2847_);
v_initState_2848_ = lean_ctor_get(v_val_2845_, 6);
lean_inc(v_initState_2848_);
v_completeness_2849_ = lean_ctor_get(v_val_2845_, 8);
lean_inc(v_completeness_2849_);
lean_dec(v_val_2845_);
lean_inc_ref_n(v_method_2827_, 2);
lean_inc_n(v_inst_2833_, 2);
v___f_2850_ = lean_alloc_closure((void*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_2850_, 0, v_inst_2833_);
lean_closure_set(v___f_2850_, 1, v_pureOnDidChange_2847_);
lean_closure_set(v___f_2850_, 2, v_method_2827_);
lean_closure_set(v___f_2850_, 3, v_onDidChange_2835_);
v___f_2851_ = lean_alloc_closure((void*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___boxed), 10, 6);
lean_closure_set(v___f_2851_, 0, v_inst_2829_);
lean_closure_set(v___f_2851_, 1, v_inst_2833_);
lean_closure_set(v___f_2851_, 2, v_pureHandle_2846_);
lean_closure_set(v___f_2851_, 3, v_inst_2831_);
lean_closure_set(v___f_2851_, 4, v_method_2827_);
lean_closure_set(v___f_2851_, 5, v_handler_2834_);
v___x_2852_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(v_method_2827_, v_initState_2848_, v_inst_2833_);
lean_dec(v_initState_2848_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2854_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2853_);
lean_dec_ref_known(v___x_2852_, 1);
v___x_2854_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2827_, v_completeness_2849_, v_inst_2828_, v_inst_2830_, v_inst_2832_, v_inst_2833_, v_a_2853_, v___f_2851_, v___f_2850_);
return v___x_2854_;
}
else
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
lean_dec_ref(v___f_2851_);
lean_dec_ref(v___f_2850_);
lean_dec(v_completeness_2849_);
lean_dec(v_inst_2833_);
lean_dec_ref(v_inst_2832_);
lean_dec_ref(v_inst_2830_);
lean_dec_ref(v_inst_2828_);
lean_dec_ref(v_method_2827_);
v_a_2855_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___x_2852_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2852_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2855_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
else
{
lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
lean_dec(v___x_2844_);
lean_dec_ref(v_onDidChange_2835_);
lean_dec_ref(v_handler_2834_);
lean_dec(v_inst_2833_);
lean_dec_ref(v_inst_2832_);
lean_dec_ref(v_inst_2831_);
lean_dec_ref(v_inst_2830_);
lean_dec_ref(v_inst_2829_);
lean_dec_ref(v_inst_2828_);
v___x_2863_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0));
v___x_2864_ = lean_string_append(v___x_2863_, v_method_2827_);
lean_dec_ref(v_method_2827_);
v___x_2865_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__1));
v___x_2866_ = lean_string_append(v___x_2864_, v___x_2865_);
v___x_2867_ = lean_mk_io_user_error(v___x_2866_);
v___x_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2867_);
return v___x_2868_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2869_, lean_object* v_inst_2870_, lean_object* v_inst_2871_, lean_object* v_inst_2872_, lean_object* v_inst_2873_, lean_object* v_inst_2874_, lean_object* v_inst_2875_, lean_object* v_handler_2876_, lean_object* v_onDidChange_2877_, lean_object* v_a_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg(v_method_2869_, v_inst_2870_, v_inst_2871_, v_inst_2872_, v_inst_2873_, v_inst_2874_, v_inst_2875_, v_handler_2876_, v_onDidChange_2877_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler(lean_object* v_method_2880_, lean_object* v_paramType_2881_, lean_object* v_inst_2882_, lean_object* v_inst_2883_, lean_object* v_inst_2884_, lean_object* v_respType_2885_, lean_object* v_inst_2886_, lean_object* v_inst_2887_, lean_object* v_stateType_2888_, lean_object* v_inst_2889_, lean_object* v_handler_2890_, lean_object* v_onDidChange_2891_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg(v_method_2880_, v_inst_2882_, v_inst_2883_, v_inst_2884_, v_inst_2886_, v_inst_2887_, v_inst_2889_, v_handler_2890_, v_onDidChange_2891_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___boxed(lean_object* v_method_2894_, lean_object* v_paramType_2895_, lean_object* v_inst_2896_, lean_object* v_inst_2897_, lean_object* v_inst_2898_, lean_object* v_respType_2899_, lean_object* v_inst_2900_, lean_object* v_inst_2901_, lean_object* v_stateType_2902_, lean_object* v_inst_2903_, lean_object* v_handler_2904_, lean_object* v_onDidChange_2905_, lean_object* v_a_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_Lean_Server_chainStatefulLspRequestHandler(v_method_2894_, v_paramType_2895_, v_inst_2896_, v_inst_2897_, v_inst_2898_, v_respType_2899_, v_inst_2900_, v_inst_2901_, v_stateType_2902_, v_inst_2903_, v_handler_2904_, v_onDidChange_2905_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___lam__0(lean_object* v_p_2908_, lean_object* v_x_2909_, lean_object* v_handler_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v_onDidChange_2913_; lean_object* v___x_2914_; 
v_onDidChange_2913_ = lean_ctor_get(v_handler_2910_, 4);
lean_inc_ref(v_onDidChange_2913_);
lean_dec_ref(v_handler_2910_);
lean_inc_ref(v___y_2911_);
v___x_2914_ = lean_apply_3(v_onDidChange_2913_, v_p_2908_, v___y_2911_, lean_box(0));
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___lam__0___boxed(lean_object* v_p_2915_, lean_object* v_x_2916_, lean_object* v_handler_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l_Lean_Server_handleOnDidChange___lam__0(v_p_2915_, v_x_2916_, v_handler_2917_, v___y_2918_);
lean_dec_ref(v___y_2918_);
lean_dec_ref(v_x_2916_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0(lean_object* v_f_2921_, lean_object* v_x_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
lean_object* v___x_2927_; 
lean_inc_ref(v___y_2925_);
v___x_2927_ = lean_apply_4(v_f_2921_, v___y_2923_, v___y_2924_, v___y_2925_, lean_box(0));
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0___boxed(lean_object* v_f_2928_, lean_object* v_x_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0(v_f_2928_, v_x_2929_, v___y_2930_, v___y_2931_, v___y_2932_);
lean_dec_ref(v___y_2932_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_2935_, lean_object* v_keys_2936_, lean_object* v_vals_2937_, lean_object* v_i_2938_, lean_object* v_acc_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v___x_2942_; uint8_t v___x_2943_; 
v___x_2942_ = lean_array_get_size(v_keys_2936_);
v___x_2943_ = lean_nat_dec_lt(v_i_2938_, v___x_2942_);
if (v___x_2943_ == 0)
{
lean_object* v___x_2944_; 
lean_dec(v_i_2938_);
lean_dec_ref(v_f_2935_);
v___x_2944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2944_, 0, v_acc_2939_);
return v___x_2944_;
}
else
{
lean_object* v_k_2945_; lean_object* v_v_2946_; lean_object* v___x_2947_; 
v_k_2945_ = lean_array_fget_borrowed(v_keys_2936_, v_i_2938_);
v_v_2946_ = lean_array_fget_borrowed(v_vals_2937_, v_i_2938_);
lean_inc_ref(v_f_2935_);
lean_inc_ref(v___y_2940_);
lean_inc(v_v_2946_);
lean_inc(v_k_2945_);
v___x_2947_ = lean_apply_5(v_f_2935_, v_acc_2939_, v_k_2945_, v_v_2946_, v___y_2940_, lean_box(0));
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_a_2948_);
lean_dec_ref_known(v___x_2947_, 1);
v___x_2949_ = lean_unsigned_to_nat(1u);
v___x_2950_ = lean_nat_add(v_i_2938_, v___x_2949_);
lean_dec(v_i_2938_);
v_i_2938_ = v___x_2950_;
v_acc_2939_ = v_a_2948_;
goto _start;
}
else
{
lean_dec(v_i_2938_);
lean_dec_ref(v_f_2935_);
return v___x_2947_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_2952_, lean_object* v_keys_2953_, lean_object* v_vals_2954_, lean_object* v_i_2955_, lean_object* v_acc_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2952_, v_keys_2953_, v_vals_2954_, v_i_2955_, v_acc_2956_, v___y_2957_);
lean_dec_ref(v___y_2957_);
lean_dec_ref(v_vals_2954_);
lean_dec_ref(v_keys_2953_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_2960_, lean_object* v_as_2961_, size_t v_i_2962_, size_t v_stop_2963_, lean_object* v_b_2964_, lean_object* v___y_2965_){
_start:
{
lean_object* v_a_2968_; lean_object* v___y_2973_; uint8_t v___x_2975_; 
v___x_2975_ = lean_usize_dec_eq(v_i_2962_, v_stop_2963_);
if (v___x_2975_ == 0)
{
lean_object* v___x_2976_; 
v___x_2976_ = lean_array_uget_borrowed(v_as_2961_, v_i_2962_);
switch(lean_obj_tag(v___x_2976_))
{
case 0:
{
lean_object* v_key_2977_; lean_object* v_val_2978_; lean_object* v___x_2979_; 
v_key_2977_ = lean_ctor_get(v___x_2976_, 0);
v_val_2978_ = lean_ctor_get(v___x_2976_, 1);
lean_inc_ref(v_f_2960_);
lean_inc_ref(v___y_2965_);
lean_inc(v_val_2978_);
lean_inc(v_key_2977_);
v___x_2979_ = lean_apply_5(v_f_2960_, v_b_2964_, v_key_2977_, v_val_2978_, v___y_2965_, lean_box(0));
v___y_2973_ = v___x_2979_;
goto v___jp_2972_;
}
case 1:
{
lean_object* v_node_2980_; lean_object* v___x_2981_; 
v_node_2980_ = lean_ctor_get(v___x_2976_, 0);
lean_inc(v_node_2980_);
lean_inc_ref(v_f_2960_);
v___x_2981_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_2960_, v_node_2980_, v_b_2964_, v___y_2965_);
v___y_2973_ = v___x_2981_;
goto v___jp_2972_;
}
default: 
{
v_a_2968_ = v_b_2964_;
goto v___jp_2967_;
}
}
}
else
{
lean_object* v___x_2982_; 
lean_dec_ref(v_f_2960_);
v___x_2982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2982_, 0, v_b_2964_);
return v___x_2982_;
}
v___jp_2967_:
{
size_t v___x_2969_; size_t v___x_2970_; 
v___x_2969_ = ((size_t)1ULL);
v___x_2970_ = lean_usize_add(v_i_2962_, v___x_2969_);
v_i_2962_ = v___x_2970_;
v_b_2964_ = v_a_2968_;
goto _start;
}
v___jp_2972_:
{
if (lean_obj_tag(v___y_2973_) == 0)
{
lean_object* v_a_2974_; 
v_a_2974_ = lean_ctor_get(v___y_2973_, 0);
lean_inc(v_a_2974_);
lean_dec_ref_known(v___y_2973_, 1);
v_a_2968_ = v_a_2974_;
goto v___jp_2967_;
}
else
{
lean_dec_ref(v_f_2960_);
return v___y_2973_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2983_, lean_object* v_x_2984_, lean_object* v_x_2985_, lean_object* v___y_2986_){
_start:
{
if (lean_obj_tag(v_x_2984_) == 0)
{
lean_object* v_es_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_3001_; 
v_es_2988_ = lean_ctor_get(v_x_2984_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v_x_2984_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2990_ = v_x_2984_;
v_isShared_2991_ = v_isSharedCheck_3001_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_es_2988_);
lean_dec(v_x_2984_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_3001_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; uint8_t v___x_2994_; 
v___x_2992_ = lean_unsigned_to_nat(0u);
v___x_2993_ = lean_array_get_size(v_es_2988_);
v___x_2994_ = lean_nat_dec_lt(v___x_2992_, v___x_2993_);
if (v___x_2994_ == 0)
{
lean_object* v___x_2996_; 
lean_dec_ref(v_es_2988_);
lean_dec_ref(v_f_2983_);
if (v_isShared_2991_ == 0)
{
lean_ctor_set(v___x_2990_, 0, v_x_2985_);
v___x_2996_ = v___x_2990_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_x_2985_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
else
{
size_t v___x_2998_; size_t v___x_2999_; lean_object* v___x_3000_; 
lean_del_object(v___x_2990_);
v___x_2998_ = ((size_t)0ULL);
v___x_2999_ = lean_usize_of_nat(v___x_2993_);
v___x_3000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2983_, v_es_2988_, v___x_2998_, v___x_2999_, v_x_2985_, v___y_2986_);
lean_dec_ref(v_es_2988_);
return v___x_3000_;
}
}
}
else
{
lean_object* v_ks_3002_; lean_object* v_vs_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v_ks_3002_ = lean_ctor_get(v_x_2984_, 0);
lean_inc_ref(v_ks_3002_);
v_vs_3003_ = lean_ctor_get(v_x_2984_, 1);
lean_inc_ref(v_vs_3003_);
lean_dec_ref_known(v_x_2984_, 2);
v___x_3004_ = lean_unsigned_to_nat(0u);
v___x_3005_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2983_, v_ks_3002_, v_vs_3003_, v___x_3004_, v_x_2985_, v___y_2986_);
lean_dec_ref(v_vs_3003_);
lean_dec_ref(v_ks_3002_);
return v___x_3005_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_3006_, lean_object* v_x_3007_, lean_object* v_x_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3006_, v_x_3007_, v_x_3008_, v___y_3009_);
lean_dec_ref(v___y_3009_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_3012_, lean_object* v_as_3013_, lean_object* v_i_3014_, lean_object* v_stop_3015_, lean_object* v_b_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
size_t v_i_boxed_3019_; size_t v_stop_boxed_3020_; lean_object* v_res_3021_; 
v_i_boxed_3019_ = lean_unbox_usize(v_i_3014_);
lean_dec(v_i_3014_);
v_stop_boxed_3020_ = lean_unbox_usize(v_stop_3015_);
lean_dec(v_stop_3015_);
v_res_3021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3012_, v_as_3013_, v_i_boxed_3019_, v_stop_boxed_3020_, v_b_3016_, v___y_3017_);
lean_dec_ref(v___y_3017_);
lean_dec_ref(v_as_3013_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(lean_object* v_map_3022_, lean_object* v_f_3023_, lean_object* v___y_3024_){
_start:
{
lean_object* v___f_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___f_3026_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3026_, 0, v_f_3023_);
v___x_3027_ = lean_box(0);
v___x_3028_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v___f_3026_, v_map_3022_, v___x_3027_, v___y_3024_);
return v___x_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___boxed(lean_object* v_map_3029_, lean_object* v_f_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(v_map_3029_, v_f_3030_, v___y_3031_);
lean_dec_ref(v___y_3031_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange(lean_object* v_p_3034_, lean_object* v_a_3035_){
_start:
{
lean_object* v___f_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___f_3037_ = lean_alloc_closure((void*)(l_Lean_Server_handleOnDidChange___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3037_, 0, v_p_3034_);
v___x_3038_ = l_Lean_Server_statefulRequestHandlers;
v___x_3039_ = lean_st_ref_get(v___x_3038_);
v___x_3040_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(v___x_3039_, v___f_3037_, v_a_3035_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___boxed(lean_object* v_p_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_Server_handleOnDidChange(v_p_3041_, v_a_3042_);
lean_dec_ref(v_a_3042_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0(lean_object* v_00_u03b2_3045_, lean_object* v_map_3046_, lean_object* v_f_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v___x_3050_; 
v___x_3050_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(v_map_3046_, v_f_3047_, v___y_3048_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___boxed(lean_object* v_00_u03b2_3051_, lean_object* v_map_3052_, lean_object* v_f_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0(v_00_u03b2_3051_, v_map_3052_, v_f_3053_, v___y_3054_);
lean_dec_ref(v___y_3054_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg(lean_object* v_map_3057_, lean_object* v_f_3058_, lean_object* v_init_3059_, lean_object* v___y_3060_){
_start:
{
lean_object* v___x_3062_; 
v___x_3062_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3058_, v_map_3057_, v_init_3059_, v___y_3060_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg___boxed(lean_object* v_map_3063_, lean_object* v_f_3064_, lean_object* v_init_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg(v_map_3063_, v_f_3064_, v_init_3065_, v___y_3066_);
lean_dec_ref(v___y_3066_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0(lean_object* v_00_u03c3_3069_, lean_object* v_00_u03b2_3070_, lean_object* v_map_3071_, lean_object* v_f_3072_, lean_object* v_init_3073_, lean_object* v___y_3074_){
_start:
{
lean_object* v___x_3076_; 
v___x_3076_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3072_, v_map_3071_, v_init_3073_, v___y_3074_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3077_, lean_object* v_00_u03b2_3078_, lean_object* v_map_3079_, lean_object* v_f_3080_, lean_object* v_init_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0(v_00_u03c3_3077_, v_00_u03b2_3078_, v_map_3079_, v_f_3080_, v_init_3081_, v___y_3082_);
lean_dec_ref(v___y_3082_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3085_, lean_object* v_00_u03b1_3086_, lean_object* v_00_u03b2_3087_, lean_object* v_f_3088_, lean_object* v_x_3089_, lean_object* v_x_3090_, lean_object* v___y_3091_){
_start:
{
lean_object* v___x_3093_; 
v___x_3093_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3088_, v_x_3089_, v_x_3090_, v___y_3091_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3094_, lean_object* v_00_u03b1_3095_, lean_object* v_00_u03b2_3096_, lean_object* v_f_3097_, lean_object* v_x_3098_, lean_object* v_x_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1(v_00_u03c3_3094_, v_00_u03b1_3095_, v_00_u03b2_3096_, v_f_3097_, v_x_3098_, v_x_3099_, v___y_3100_);
lean_dec_ref(v___y_3100_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3103_, lean_object* v_00_u03b2_3104_, lean_object* v_00_u03c3_3105_, lean_object* v_f_3106_, lean_object* v_as_3107_, size_t v_i_3108_, size_t v_stop_3109_, lean_object* v_b_3110_, lean_object* v___y_3111_){
_start:
{
lean_object* v___x_3113_; 
v___x_3113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3106_, v_as_3107_, v_i_3108_, v_stop_3109_, v_b_3110_, v___y_3111_);
return v___x_3113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3114_, lean_object* v_00_u03b2_3115_, lean_object* v_00_u03c3_3116_, lean_object* v_f_3117_, lean_object* v_as_3118_, lean_object* v_i_3119_, lean_object* v_stop_3120_, lean_object* v_b_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
size_t v_i_boxed_3124_; size_t v_stop_boxed_3125_; lean_object* v_res_3126_; 
v_i_boxed_3124_ = lean_unbox_usize(v_i_3119_);
lean_dec(v_i_3119_);
v_stop_boxed_3125_ = lean_unbox_usize(v_stop_3120_);
lean_dec(v_stop_3120_);
v_res_3126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3114_, v_00_u03b2_3115_, v_00_u03c3_3116_, v_f_3117_, v_as_3118_, v_i_boxed_3124_, v_stop_boxed_3125_, v_b_3121_, v___y_3122_);
lean_dec_ref(v___y_3122_);
lean_dec_ref(v_as_3118_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3127_, lean_object* v_00_u03b1_3128_, lean_object* v_00_u03b2_3129_, lean_object* v_f_3130_, lean_object* v_keys_3131_, lean_object* v_vals_3132_, lean_object* v_heq_3133_, lean_object* v_i_3134_, lean_object* v_acc_3135_, lean_object* v___y_3136_){
_start:
{
lean_object* v___x_3138_; 
v___x_3138_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3130_, v_keys_3131_, v_vals_3132_, v_i_3134_, v_acc_3135_, v___y_3136_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3139_, lean_object* v_00_u03b1_3140_, lean_object* v_00_u03b2_3141_, lean_object* v_f_3142_, lean_object* v_keys_3143_, lean_object* v_vals_3144_, lean_object* v_heq_3145_, lean_object* v_i_3146_, lean_object* v_acc_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3139_, v_00_u03b1_3140_, v_00_u03b2_3141_, v_f_3142_, v_keys_3143_, v_vals_3144_, v_heq_3145_, v_i_3146_, v_acc_3147_, v___y_3148_);
lean_dec_ref(v___y_3148_);
lean_dec_ref(v_vals_3144_);
lean_dec_ref(v_keys_3143_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest(lean_object* v_method_3153_, lean_object* v_params_3154_, lean_object* v_a_3155_){
_start:
{
uint8_t v___x_3157_; 
v___x_3157_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_3153_);
if (v___x_3157_ == 0)
{
lean_object* v___x_3158_; lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3174_; 
v___x_3158_ = l_Lean_Server_lookupLspRequestHandler(v_method_3153_);
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3161_ = v___x_3158_;
v_isShared_3162_ = v_isSharedCheck_3174_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3158_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3174_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
if (lean_obj_tag(v_a_3159_) == 0)
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3169_; 
lean_dec(v_params_3154_);
v___x_3163_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__0));
v___x_3164_ = lean_string_append(v___x_3163_, v_method_3153_);
v___x_3165_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__1));
v___x_3166_ = lean_string_append(v___x_3164_, v___x_3165_);
v___x_3167_ = l_Lean_Server_RequestError_internalError(v___x_3166_);
if (v_isShared_3162_ == 0)
{
lean_ctor_set_tag(v___x_3161_, 1);
lean_ctor_set(v___x_3161_, 0, v___x_3167_);
v___x_3169_ = v___x_3161_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v___x_3167_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
else
{
lean_object* v_val_3171_; lean_object* v_handle_3172_; lean_object* v___x_3173_; 
lean_del_object(v___x_3161_);
v_val_3171_ = lean_ctor_get(v_a_3159_, 0);
lean_inc(v_val_3171_);
lean_dec_ref_known(v_a_3159_, 1);
v_handle_3172_ = lean_ctor_get(v_val_3171_, 1);
lean_inc_ref(v_handle_3172_);
lean_dec(v_val_3171_);
lean_inc_ref(v_a_3155_);
v___x_3173_ = lean_apply_3(v_handle_3172_, v_params_3154_, v_a_3155_, lean_box(0));
return v___x_3173_;
}
}
}
else
{
lean_object* v___x_3175_; 
v___x_3175_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_3153_);
if (lean_obj_tag(v___x_3175_) == 0)
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
lean_dec(v_params_3154_);
v___x_3176_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__0));
v___x_3177_ = lean_string_append(v___x_3176_, v_method_3153_);
v___x_3178_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__1));
v___x_3179_ = lean_string_append(v___x_3177_, v___x_3178_);
v___x_3180_ = l_Lean_Server_RequestError_internalError(v___x_3179_);
v___x_3181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3180_);
return v___x_3181_;
}
else
{
lean_object* v_val_3182_; lean_object* v_handle_3183_; lean_object* v___x_3184_; 
v_val_3182_ = lean_ctor_get(v___x_3175_, 0);
lean_inc(v_val_3182_);
lean_dec_ref_known(v___x_3175_, 1);
v_handle_3183_ = lean_ctor_get(v_val_3182_, 2);
lean_inc_ref(v_handle_3183_);
lean_dec(v_val_3182_);
lean_inc_ref(v_a_3155_);
v___x_3184_ = lean_apply_3(v_handle_3183_, v_params_3154_, v_a_3155_, lean_box(0));
return v___x_3184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest___boxed(lean_object* v_method_3185_, lean_object* v_params_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_){
_start:
{
lean_object* v_res_3189_; 
v_res_3189_ = l_Lean_Server_handleLspRequest(v_method_3185_, v_params_3186_, v_a_3187_);
lean_dec_ref(v_a_3187_);
lean_dec_ref(v_method_3185_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_routeLspRequest(lean_object* v_method_3190_, lean_object* v_params_3191_){
_start:
{
uint8_t v___x_3193_; 
v___x_3193_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_3190_);
if (v___x_3193_ == 0)
{
lean_object* v___x_3194_; lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3210_; 
v___x_3194_ = l_Lean_Server_lookupLspRequestHandler(v_method_3190_);
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3197_ = v___x_3194_;
v_isShared_3198_ = v_isSharedCheck_3210_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3194_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3210_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
if (lean_obj_tag(v_a_3195_) == 0)
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3202_; 
lean_dec(v_params_3191_);
v___x_3199_ = l_Lean_Server_RequestError_methodNotFound(v_method_3190_);
v___x_3200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3199_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 0, v___x_3200_);
v___x_3202_ = v___x_3197_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3200_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
else
{
lean_object* v_val_3204_; lean_object* v_fileSource_3205_; lean_object* v___x_3206_; lean_object* v___x_3208_; 
v_val_3204_ = lean_ctor_get(v_a_3195_, 0);
lean_inc(v_val_3204_);
lean_dec_ref_known(v_a_3195_, 1);
v_fileSource_3205_ = lean_ctor_get(v_val_3204_, 0);
lean_inc_ref(v_fileSource_3205_);
lean_dec(v_val_3204_);
v___x_3206_ = lean_apply_1(v_fileSource_3205_, v_params_3191_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 0, v___x_3206_);
v___x_3208_ = v___x_3197_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v___x_3206_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
}
else
{
lean_object* v___x_3211_; 
v___x_3211_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_3190_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
lean_dec(v_params_3191_);
v___x_3212_ = l_Lean_Server_RequestError_methodNotFound(v_method_3190_);
v___x_3213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3212_);
v___x_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
return v___x_3214_;
}
else
{
lean_object* v_val_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3224_; 
v_val_3215_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3217_ = v___x_3211_;
v_isShared_3218_ = v_isSharedCheck_3224_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_val_3215_);
lean_dec(v___x_3211_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3224_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v_fileSource_3219_; lean_object* v___x_3220_; lean_object* v___x_3222_; 
v_fileSource_3219_ = lean_ctor_get(v_val_3215_, 0);
lean_inc_ref(v_fileSource_3219_);
lean_dec(v_val_3215_);
v___x_3220_ = lean_apply_1(v_fileSource_3219_, v_params_3191_);
if (v_isShared_3218_ == 0)
{
lean_ctor_set_tag(v___x_3217_, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3220_);
v___x_3222_ = v___x_3217_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v___x_3220_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_routeLspRequest___boxed(lean_object* v_method_3225_, lean_object* v_params_3226_, lean_object* v_a_3227_){
_start:
{
lean_object* v_res_3228_; 
v_res_3228_ = l_Lean_Server_routeLspRequest(v_method_3225_, v_params_3226_);
lean_dec_ref(v_method_3225_);
return v_res_3228_;
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
