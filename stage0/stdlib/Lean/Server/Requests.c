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
lean_object* l_Lean_Server_RequestError_ofException(lean_object* v_e_38_){
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
LEAN_EXPORT void l_Lean_Server_RequestError_ofException_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_38_ = stack[0].m_obj;
lean_object* v_res_44_;
v_res_44_ = l_Lean_Server_RequestError_ofException(v_e_38_);
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_ofException___boxed(lean_object* v_e_45_, lean_object* v_a_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_Server_RequestError_ofException(v_e_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_ofIoError(lean_object* v_e_48_){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_io_error_to_string(v_e_48_);
v___x_50_ = l_Lean_Server_RequestError_internalError(v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_toLspResponseError(lean_object* v_id_51_, lean_object* v_e_52_){
_start:
{
uint8_t v_code_53_; lean_object* v_message_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v_code_53_ = lean_ctor_get_uint8(v_e_52_, sizeof(void*)*1);
v_message_54_ = lean_ctor_get(v_e_52_, 0);
v___x_55_ = lean_box(0);
lean_inc_ref(v_message_54_);
v___x_56_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_56_, 0, v_id_51_);
lean_ctor_set(v___x_56_, 1, v_message_54_);
lean_ctor_set(v___x_56_, 2, v___x_55_);
lean_ctor_set_uint8(v___x_56_, sizeof(void*)*3, v_code_53_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_toLspResponseError___boxed(lean_object* v_id_57_, lean_object* v_e_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_Server_RequestError_toLspResponseError(v_id_57_, v_e_58_);
lean_dec_ref(v_e_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___redArg(lean_object* v_inst_62_, lean_object* v_params_63_){
_start:
{
lean_object* v___x_64_; 
lean_inc(v_params_63_);
v___x_64_ = lean_apply_1(v_inst_62_, v_params_63_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v_a_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_80_; 
v_a_65_ = lean_ctor_get(v___x_64_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_80_ == 0)
{
v___x_67_ = v___x_64_;
v_isShared_68_ = v_isSharedCheck_80_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_a_65_);
lean_dec(v___x_64_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_80_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
uint8_t v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_78_; 
v___x_69_ = 3;
v___x_70_ = ((lean_object*)(l_Lean_Server_parseRequestParams___redArg___closed__0));
v___x_71_ = l_Lean_Json_compress(v_params_63_);
v___x_72_ = lean_string_append(v___x_70_, v___x_71_);
lean_dec_ref(v___x_71_);
v___x_73_ = ((lean_object*)(l_Lean_Server_parseRequestParams___redArg___closed__1));
v___x_74_ = lean_string_append(v___x_72_, v___x_73_);
v___x_75_ = lean_string_append(v___x_74_, v_a_65_);
lean_dec(v_a_65_);
v___x_76_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set_uint8(v___x_76_, sizeof(void*)*1, v___x_69_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 0, v___x_76_);
v___x_78_ = v___x_67_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_76_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
else
{
lean_object* v_a_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_88_; 
lean_dec(v_params_63_);
v_a_81_ = lean_ctor_get(v___x_64_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_88_ == 0)
{
v___x_83_ = v___x_64_;
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_a_81_);
lean_dec(v___x_64_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_86_; 
if (v_isShared_84_ == 0)
{
v___x_86_ = v___x_83_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_a_81_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams(lean_object* v_paramType_89_, lean_object* v_inst_90_, lean_object* v_params_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_Server_parseRequestParams___redArg(v_inst_90_, v_params_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___impl___redArg(lean_object* v_x_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_obj_tag_nat(v_x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___impl___redArg___boxed(lean_object* v_x_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Server_ServerRequestResponse_ctorIdx___impl___redArg(v_x_95_);
lean_dec_ref(v_x_95_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___impl(lean_object* v_00_u03b1_97_, lean_object* v_x_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_obj_tag_nat(v_x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___impl___boxed(lean_object* v_00_u03b1_100_, lean_object* v_x_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_Server_ServerRequestResponse_ctorIdx___impl(v_00_u03b1_100_, v_x_101_);
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
lean_object* l_Lean_Server_instInhabitedServerRequestResponse_default___redArg(){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = ((lean_object*)(l_Lean_Server_instInhabitedServerRequestResponse_default___redArg___closed__0));
return v___x_147_;
}
}
LEAN_EXPORT void l_Lean_Server_instInhabitedServerRequestResponse_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_148_;
v_res_148_ = l_Lean_Server_instInhabitedServerRequestResponse_default___redArg();
stack->m_obj
 = v_res_148_;
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse_default___redArg___boxed(lean_object* v___dummy_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_Server_instInhabitedServerRequestResponse_default___redArg();
return v_res_150_;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0(void){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Server_instInhabitedServerRequestResponse_default___redArg();
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse_default(lean_object* v_00_u03b1_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = lean_obj_once(&l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0, &l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0_once, _init_l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0);
return v___x_153_;
}
}
lean_object* l_Lean_Server_instInhabitedServerRequestResponse___redArg(){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = lean_obj_once(&l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0, &l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0_once, _init_l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0);
return v___x_155_;
}
}
LEAN_EXPORT void l_Lean_Server_instInhabitedServerRequestResponse___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_156_;
v_res_156_ = l_Lean_Server_instInhabitedServerRequestResponse___redArg();
stack->m_obj
 = v_res_156_;
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse___redArg___boxed(lean_object* v___dummy_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_Server_instInhabitedServerRequestResponse___redArg();
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse(lean_object* v_a_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lean_obj_once(&l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0, &l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0_once, _init_l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0);
return v___x_160_;
}
}
lean_object* l_Lean_Server_RequestM_run___redArg(lean_object* v_act_161_, lean_object* v_rc_162_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = lean_apply_2(v_act_161_, v_rc_162_, lean_box(0));
return v___x_164_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_161_ = stack[0].m_obj;
lean_object* v_rc_162_ = stack[1].m_obj;
lean_object* v_res_165_;
v_res_165_ = l_Lean_Server_RequestM_run___redArg(v_act_161_, v_rc_162_);
stack->m_obj
 = v_res_165_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run___redArg___boxed(lean_object* v_act_166_, lean_object* v_rc_167_, lean_object* v_a_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_Server_RequestM_run___redArg(v_act_166_, v_rc_167_);
return v_res_169_;
}
}
lean_object* l_Lean_Server_RequestM_run(lean_object* v_00_u03b1_170_, lean_object* v_act_171_, lean_object* v_rc_172_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lean_apply_2(v_act_171_, v_rc_172_, lean_box(0));
return v___x_174_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_171_ = stack[1].m_obj;
lean_object* v_rc_172_ = stack[2].m_obj;
lean_object* v_res_175_;
v_res_175_ = l_Lean_Server_RequestM_run(lean_box(0), v_act_171_, v_rc_172_);
stack->m_obj
 = v_res_175_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run___boxed(lean_object* v_00_u03b1_176_, lean_object* v_act_177_, lean_object* v_rc_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Server_RequestM_run(v_00_u03b1_176_, v_act_177_, v_rc_178_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestTask_pure___redArg(lean_object* v_a_181_){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_182_, 0, v_a_181_);
v___x_183_ = lean_task_pure(v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestTask_pure(lean_object* v_00_u03b1_184_, lean_object* v_a_185_){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_186_, 0, v_a_185_);
v___x_187_ = lean_task_pure(v___x_186_);
return v___x_187_;
}
}
lean_object* l_Lean_Server_instMonadLiftIORequestM___lam__0(lean_object* v_00_u03b1_188_, lean_object* v_x_189_, lean_object* v___y_190_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_apply_1(v_x_189_, lean_box(0));
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_192_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_192_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
else
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_209_; 
v_a_201_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_209_ == 0)
{
v___x_203_ = v___x_192_;
v_isShared_204_ = v_isSharedCheck_209_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_192_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_209_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v___x_207_; 
v___x_205_ = l_Lean_Server_RequestError_ofIoError(v_a_201_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v___x_205_);
v___x_207_ = v___x_203_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_205_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_instMonadLiftIORequestM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_189_ = stack[1].m_obj;
lean_object* v___y_190_ = stack[2].m_obj;
lean_object* v_res_210_;
v_res_210_ = l_Lean_Server_instMonadLiftIORequestM___lam__0(lean_box(0), v_x_189_, v___y_190_);
stack->m_obj
 = v_res_210_;
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM___lam__0___boxed(lean_object* v_00_u03b1_211_, lean_object* v_x_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_Server_instMonadLiftIORequestM___lam__0(v_00_u03b1_211_, v_x_212_, v___y_213_);
lean_dec_ref(v___y_213_);
return v_res_215_;
}
}
lean_object* l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0(lean_object* v_00_u03b1_218_, lean_object* v_x_219_, lean_object* v___y_220_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = lean_apply_1(v_x_219_, lean_box(0));
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_230_; 
v_a_223_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_230_ == 0)
{
v___x_225_ = v___x_222_;
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_222_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_228_; 
if (v_isShared_226_ == 0)
{
v___x_228_ = v___x_225_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_a_223_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
else
{
lean_object* v_a_231_; lean_object* v___x_232_; lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
v_a_231_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_a_231_);
lean_dec_ref_known(v___x_222_, 1);
v___x_232_ = l_Lean_Server_RequestError_ofException(v_a_231_);
v_a_233_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_232_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_232_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set_tag(v___x_235_, 1);
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_a_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_219_ = stack[1].m_obj;
lean_object* v___y_220_ = stack[2].m_obj;
lean_object* v_res_241_;
v_res_241_ = l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0(lean_box(0), v_x_219_, v___y_220_);
stack->m_obj
 = v_res_241_;
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0___boxed(lean_object* v_00_u03b1_242_, lean_object* v_x_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0(v_00_u03b1_242_, v_x_243_, v___y_244_);
lean_dec_ref(v___y_244_);
return v_res_246_;
}
}
lean_object* l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0(lean_object* v_00_u03b1_249_, lean_object* v_x_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_cancelTk_253_; lean_object* v___x_254_; 
v_cancelTk_253_ = lean_ctor_get(v___y_251_, 4);
lean_inc_ref(v_cancelTk_253_);
v___x_254_ = lean_apply_2(v_x_250_, v_cancelTk_253_, lean_box(0));
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_267_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_267_ == 0)
{
v___x_257_ = v___x_254_;
v_isShared_258_ = v_isSharedCheck_267_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_267_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
if (lean_obj_tag(v_a_255_) == 0)
{
lean_object* v___x_259_; lean_object* v___x_261_; 
lean_dec_ref_known(v_a_255_, 1);
v___x_259_ = ((lean_object*)(l_Lean_Server_RequestError_requestCancelled));
if (v_isShared_258_ == 0)
{
lean_ctor_set_tag(v___x_257_, 1);
lean_ctor_set(v___x_257_, 0, v___x_259_);
v___x_261_ = v___x_257_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; 
v_a_263_ = lean_ctor_get(v_a_255_, 0);
lean_inc(v_a_263_);
lean_dec_ref_known(v_a_255_, 1);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 0, v_a_263_);
v___x_265_ = v___x_257_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
else
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_276_; 
v_a_268_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_276_ == 0)
{
v___x_270_ = v___x_254_;
v_isShared_271_ = v_isSharedCheck_276_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_254_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_276_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_272_ = l_Lean_Server_RequestError_ofIoError(v_a_268_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_272_);
v___x_274_ = v___x_270_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_272_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_250_ = stack[1].m_obj;
lean_object* v___y_251_ = stack[2].m_obj;
lean_object* v_res_277_;
v_res_277_ = l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0(lean_box(0), v_x_250_, v___y_251_);
stack->m_obj
 = v_res_277_;
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0___boxed(lean_object* v_00_u03b1_278_, lean_object* v_x_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0(v_00_u03b1_278_, v_x_279_, v___y_280_);
lean_dec_ref(v___y_280_);
return v_res_282_;
}
}
lean_object* l_Lean_Server_RequestM_runInIO___redArg(lean_object* v_x_285_, lean_object* v_ctx_286_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = lean_apply_2(v_x_285_, v_ctx_286_, lean_box(0));
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
v_a_289_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_288_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
else
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_306_; 
v_a_297_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_306_ == 0)
{
v___x_299_ = v___x_288_;
v_isShared_300_ = v_isSharedCheck_306_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_288_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_306_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v_message_301_; lean_object* v___x_302_; lean_object* v___x_304_; 
v_message_301_ = lean_ctor_get(v_a_297_, 0);
lean_inc_ref(v_message_301_);
lean_dec(v_a_297_);
v___x_302_ = lean_mk_io_user_error(v_message_301_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_302_);
v___x_304_ = v___x_299_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_runInIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_285_ = stack[0].m_obj;
lean_object* v_ctx_286_ = stack[1].m_obj;
lean_object* v_res_307_;
v_res_307_ = l_Lean_Server_RequestM_runInIO___redArg(v_x_285_, v_ctx_286_);
stack->m_obj
 = v_res_307_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO___redArg___boxed(lean_object* v_x_308_, lean_object* v_ctx_309_, lean_object* v_a_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_Server_RequestM_runInIO___redArg(v_x_308_, v_ctx_309_);
return v_res_311_;
}
}
lean_object* l_Lean_Server_RequestM_runInIO(lean_object* v_00_u03b1_312_, lean_object* v_x_313_, lean_object* v_ctx_314_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_Server_RequestM_runInIO___redArg(v_x_313_, v_ctx_314_);
return v___x_316_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_runInIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_313_ = stack[1].m_obj;
lean_object* v_ctx_314_ = stack[2].m_obj;
lean_object* v_res_317_;
v_res_317_ = l_Lean_Server_RequestM_runInIO(lean_box(0), v_x_313_, v_ctx_314_);
stack->m_obj
 = v_res_317_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO___boxed(lean_object* v_00_u03b1_318_, lean_object* v_x_319_, lean_object* v_ctx_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Server_RequestM_runInIO(v_00_u03b1_318_, v_x_319_, v_ctx_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___redArg___lam__0(lean_object* v_toPure_323_, lean_object* v_rc_324_){
_start:
{
lean_object* v_doc_325_; lean_object* v___x_326_; 
v_doc_325_ = lean_ctor_get(v_rc_324_, 1);
lean_inc_ref(v_doc_325_);
lean_dec_ref(v_rc_324_);
v___x_326_ = lean_apply_2(v_toPure_323_, lean_box(0), v_doc_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___redArg(lean_object* v_inst_327_, lean_object* v_inst_328_){
_start:
{
lean_object* v_toApplicative_329_; lean_object* v_toBind_330_; lean_object* v_toPure_331_; lean_object* v___f_332_; lean_object* v___x_333_; 
v_toApplicative_329_ = lean_ctor_get(v_inst_327_, 0);
lean_inc_ref(v_toApplicative_329_);
v_toBind_330_ = lean_ctor_get(v_inst_327_, 1);
lean_inc(v_toBind_330_);
lean_dec_ref(v_inst_327_);
v_toPure_331_ = lean_ctor_get(v_toApplicative_329_, 1);
lean_inc(v_toPure_331_);
lean_dec_ref(v_toApplicative_329_);
v___f_332_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_readDoc___redArg___lam__0), 2, 1);
lean_closure_set(v___f_332_, 0, v_toPure_331_);
v___x_333_ = lean_apply_4(v_toBind_330_, lean_box(0), lean_box(0), v_inst_328_, v___f_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc(lean_object* v_m_334_, lean_object* v_inst_335_, lean_object* v_inst_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_Server_RequestM_readDoc___redArg(v_inst_335_, v_inst_336_);
return v___x_337_;
}
}
lean_object* l_Lean_Server_RequestM_asTask___redArg___lam__0(lean_object* v_t_338_, lean_object* v_a_339_){
_start:
{
lean_object* v___x_341_; 
lean_inc_ref(v_a_339_);
v___x_341_ = lean_apply_2(v_t_338_, v_a_339_, lean_box(0));
return v___x_341_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_asTask___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_338_ = stack[0].m_obj;
lean_object* v_a_339_ = stack[1].m_obj;
lean_object* v_res_342_;
v_res_342_ = l_Lean_Server_RequestM_asTask___redArg___lam__0(v_t_338_, v_a_339_);
stack->m_obj
 = v_res_342_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg___lam__0___boxed(lean_object* v_t_343_, lean_object* v_a_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_Server_RequestM_asTask___redArg___lam__0(v_t_343_, v_a_344_);
lean_dec_ref(v_a_344_);
return v_res_346_;
}
}
lean_object* l_Lean_Server_RequestM_asTask___redArg(lean_object* v_t_347_, lean_object* v_a_348_){
_start:
{
lean_object* v___f_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
lean_inc_ref(v_a_348_);
v___f_350_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_asTask___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_350_, 0, v_t_347_);
lean_closure_set(v___f_350_, 1, v_a_348_);
v___x_351_ = l_Lean_Server_ServerTask_EIO_asTask___redArg(v___f_350_);
v___x_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_asTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_347_ = stack[0].m_obj;
lean_object* v_a_348_ = stack[1].m_obj;
lean_object* v_res_353_;
v_res_353_ = l_Lean_Server_RequestM_asTask___redArg(v_t_347_, v_a_348_);
stack->m_obj
 = v_res_353_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg___boxed(lean_object* v_t_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_Server_RequestM_asTask___redArg(v_t_354_, v_a_355_);
lean_dec_ref(v_a_355_);
return v_res_357_;
}
}
lean_object* l_Lean_Server_RequestM_asTask(lean_object* v_00_u03b1_358_, lean_object* v_t_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_Server_RequestM_asTask___redArg(v_t_359_, v_a_360_);
return v___x_362_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_asTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_359_ = stack[1].m_obj;
lean_object* v_a_360_ = stack[2].m_obj;
lean_object* v_res_363_;
v_res_363_ = l_Lean_Server_RequestM_asTask(lean_box(0), v_t_359_, v_a_360_);
stack->m_obj
 = v_res_363_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___boxed(lean_object* v_00_u03b1_364_, lean_object* v_t_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Server_RequestM_asTask(v_00_u03b1_364_, v_t_365_, v_a_366_);
lean_dec_ref(v_a_366_);
return v_res_368_;
}
}
lean_object* l_Lean_Server_RequestM_pureTask___redArg(lean_object* v_t_369_, lean_object* v_a_370_){
_start:
{
lean_object* v___x_372_; 
lean_inc_ref(v_a_370_);
v___x_372_ = lean_apply_2(v_t_369_, v_a_370_, lean_box(0));
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_382_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_382_ == 0)
{
v___x_375_ = v___x_372_;
v_isShared_376_ = v_isSharedCheck_382_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_382_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_377_, 0, v_a_373_);
v___x_378_ = lean_task_pure(v___x_377_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v___x_378_);
v___x_380_ = v___x_375_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
v_a_383_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_372_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_372_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_pureTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_369_ = stack[0].m_obj;
lean_object* v_a_370_ = stack[1].m_obj;
lean_object* v_res_391_;
v_res_391_ = l_Lean_Server_RequestM_pureTask___redArg(v_t_369_, v_a_370_);
stack->m_obj
 = v_res_391_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask___redArg___boxed(lean_object* v_t_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Server_RequestM_pureTask___redArg(v_t_392_, v_a_393_);
lean_dec_ref(v_a_393_);
return v_res_395_;
}
}
lean_object* l_Lean_Server_RequestM_pureTask(lean_object* v_00_u03b1_396_, lean_object* v_t_397_, lean_object* v_a_398_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_Server_RequestM_pureTask___redArg(v_t_397_, v_a_398_);
return v___x_400_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_pureTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_397_ = stack[1].m_obj;
lean_object* v_a_398_ = stack[2].m_obj;
lean_object* v_res_401_;
v_res_401_ = l_Lean_Server_RequestM_pureTask(lean_box(0), v_t_397_, v_a_398_);
stack->m_obj
 = v_res_401_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask___boxed(lean_object* v_00_u03b1_402_, lean_object* v_t_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_Server_RequestM_pureTask(v_00_u03b1_402_, v_t_403_, v_a_404_);
lean_dec_ref(v_a_404_);
return v_res_406_;
}
}
lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0(lean_object* v_f_407_, lean_object* v_a_408_, lean_object* v_x_409_){
_start:
{
lean_object* v___x_411_; 
lean_inc_ref(v_a_408_);
v___x_411_ = lean_apply_3(v_f_407_, v_x_409_, v_a_408_, lean_box(0));
return v___x_411_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_407_ = stack[0].m_obj;
lean_object* v_a_408_ = stack[1].m_obj;
lean_object* v_x_409_ = stack[2].m_obj;
lean_object* v_res_412_;
v_res_412_ = l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0(v_f_407_, v_a_408_, v_x_409_);
stack->m_obj
 = v_res_412_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0___boxed(lean_object* v_f_413_, lean_object* v_a_414_, lean_object* v_x_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0(v_f_413_, v_a_414_, v_x_415_);
lean_dec_ref(v_a_414_);
return v_res_417_;
}
}
lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg(lean_object* v_t_418_, lean_object* v_f_419_, lean_object* v_a_420_){
_start:
{
lean_object* v___f_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
lean_inc_ref(v_a_420_);
v___f_422_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_422_, 0, v_f_419_);
lean_closure_set(v___f_422_, 1, v_a_420_);
v___x_423_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(v___f_422_, v_t_418_);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_mapTaskCheap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_418_ = stack[0].m_obj;
lean_object* v_f_419_ = stack[1].m_obj;
lean_object* v_a_420_ = stack[2].m_obj;
lean_object* v_res_425_;
v_res_425_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_t_418_, v_f_419_, v_a_420_);
stack->m_obj
 = v_res_425_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg___boxed(lean_object* v_t_426_, lean_object* v_f_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_t_426_, v_f_427_, v_a_428_);
lean_dec_ref(v_a_428_);
return v_res_430_;
}
}
lean_object* l_Lean_Server_RequestM_mapTaskCheap(lean_object* v_00_u03b1_431_, lean_object* v_00_u03b2_432_, lean_object* v_t_433_, lean_object* v_f_434_, lean_object* v_a_435_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_t_433_, v_f_434_, v_a_435_);
return v___x_437_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_mapTaskCheap_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_433_ = stack[2].m_obj;
lean_object* v_f_434_ = stack[3].m_obj;
lean_object* v_a_435_ = stack[4].m_obj;
lean_object* v_res_438_;
v_res_438_ = l_Lean_Server_RequestM_mapTaskCheap(lean_box(0), lean_box(0), v_t_433_, v_f_434_, v_a_435_);
stack->m_obj
 = v_res_438_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___boxed(lean_object* v_00_u03b1_439_, lean_object* v_00_u03b2_440_, lean_object* v_t_441_, lean_object* v_f_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Server_RequestM_mapTaskCheap(v_00_u03b1_439_, v_00_u03b2_440_, v_t_441_, v_f_442_, v_a_443_);
lean_dec_ref(v_a_443_);
return v_res_445_;
}
}
lean_object* l_Lean_Server_RequestM_mapTaskCostly___redArg(lean_object* v_t_446_, lean_object* v_f_447_, lean_object* v_a_448_){
_start:
{
lean_object* v___f_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
lean_inc_ref(v_a_448_);
v___f_450_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_450_, 0, v_f_447_);
lean_closure_set(v___f_450_, 1, v_a_448_);
v___x_451_ = l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(v___f_450_, v_t_446_);
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_mapTaskCostly___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_446_ = stack[0].m_obj;
lean_object* v_f_447_ = stack[1].m_obj;
lean_object* v_a_448_ = stack[2].m_obj;
lean_object* v_res_453_;
v_res_453_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_t_446_, v_f_447_, v_a_448_);
stack->m_obj
 = v_res_453_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly___redArg___boxed(lean_object* v_t_454_, lean_object* v_f_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_t_454_, v_f_455_, v_a_456_);
lean_dec_ref(v_a_456_);
return v_res_458_;
}
}
lean_object* l_Lean_Server_RequestM_mapTaskCostly(lean_object* v_00_u03b1_459_, lean_object* v_00_u03b2_460_, lean_object* v_t_461_, lean_object* v_f_462_, lean_object* v_a_463_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_t_461_, v_f_462_, v_a_463_);
return v___x_465_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_mapTaskCostly_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_461_ = stack[2].m_obj;
lean_object* v_f_462_ = stack[3].m_obj;
lean_object* v_a_463_ = stack[4].m_obj;
lean_object* v_res_466_;
v_res_466_ = l_Lean_Server_RequestM_mapTaskCostly(lean_box(0), lean_box(0), v_t_461_, v_f_462_, v_a_463_);
stack->m_obj
 = v_res_466_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly___boxed(lean_object* v_00_u03b1_467_, lean_object* v_00_u03b2_468_, lean_object* v_t_469_, lean_object* v_f_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_Server_RequestM_mapTaskCostly(v_00_u03b1_467_, v_00_u03b2_468_, v_t_469_, v_f_470_, v_a_471_);
lean_dec_ref(v_a_471_);
return v_res_473_;
}
}
lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0(lean_object* v_f_474_, lean_object* v_a_475_, lean_object* v_x_476_){
_start:
{
lean_object* v___x_478_; 
lean_inc_ref(v_a_475_);
v___x_478_ = lean_apply_3(v_f_474_, v_x_476_, v_a_475_, lean_box(0));
return v___x_478_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_474_ = stack[0].m_obj;
lean_object* v_a_475_ = stack[1].m_obj;
lean_object* v_x_476_ = stack[2].m_obj;
lean_object* v_res_479_;
v_res_479_ = l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0(v_f_474_, v_a_475_, v_x_476_);
stack->m_obj
 = v_res_479_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0___boxed(lean_object* v_f_480_, lean_object* v_a_481_, lean_object* v_x_482_, lean_object* v___y_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0(v_f_480_, v_a_481_, v_x_482_);
lean_dec_ref(v_a_481_);
return v_res_484_;
}
}
lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg(lean_object* v_t_485_, lean_object* v_f_486_, lean_object* v_a_487_){
_start:
{
lean_object* v___f_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
lean_inc_ref(v_a_487_);
v___f_489_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_489_, 0, v_f_486_);
lean_closure_set(v___f_489_, 1, v_a_487_);
v___x_490_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(v_t_485_, v___f_489_);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_bindTaskCheap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_485_ = stack[0].m_obj;
lean_object* v_f_486_ = stack[1].m_obj;
lean_object* v_a_487_ = stack[2].m_obj;
lean_object* v_res_492_;
v_res_492_ = l_Lean_Server_RequestM_bindTaskCheap___redArg(v_t_485_, v_f_486_, v_a_487_);
stack->m_obj
 = v_res_492_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg___boxed(lean_object* v_t_493_, lean_object* v_f_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_Server_RequestM_bindTaskCheap___redArg(v_t_493_, v_f_494_, v_a_495_);
lean_dec_ref(v_a_495_);
return v_res_497_;
}
}
lean_object* l_Lean_Server_RequestM_bindTaskCheap(lean_object* v_00_u03b1_498_, lean_object* v_00_u03b2_499_, lean_object* v_t_500_, lean_object* v_f_501_, lean_object* v_a_502_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_Server_RequestM_bindTaskCheap___redArg(v_t_500_, v_f_501_, v_a_502_);
return v___x_504_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_bindTaskCheap_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_500_ = stack[2].m_obj;
lean_object* v_f_501_ = stack[3].m_obj;
lean_object* v_a_502_ = stack[4].m_obj;
lean_object* v_res_505_;
v_res_505_ = l_Lean_Server_RequestM_bindTaskCheap(lean_box(0), lean_box(0), v_t_500_, v_f_501_, v_a_502_);
stack->m_obj
 = v_res_505_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___boxed(lean_object* v_00_u03b1_506_, lean_object* v_00_u03b2_507_, lean_object* v_t_508_, lean_object* v_f_509_, lean_object* v_a_510_, lean_object* v_a_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lean_Server_RequestM_bindTaskCheap(v_00_u03b1_506_, v_00_u03b2_507_, v_t_508_, v_f_509_, v_a_510_);
lean_dec_ref(v_a_510_);
return v_res_512_;
}
}
lean_object* l_Lean_Server_RequestM_bindTaskCostly___redArg(lean_object* v_t_513_, lean_object* v_f_514_, lean_object* v_a_515_){
_start:
{
lean_object* v___f_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
lean_inc_ref(v_a_515_);
v___f_517_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_517_, 0, v_f_514_);
lean_closure_set(v___f_517_, 1, v_a_515_);
v___x_518_ = l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(v_t_513_, v___f_517_);
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_bindTaskCostly___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_513_ = stack[0].m_obj;
lean_object* v_f_514_ = stack[1].m_obj;
lean_object* v_a_515_ = stack[2].m_obj;
lean_object* v_res_520_;
v_res_520_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_t_513_, v_f_514_, v_a_515_);
stack->m_obj
 = v_res_520_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly___redArg___boxed(lean_object* v_t_521_, lean_object* v_f_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_t_521_, v_f_522_, v_a_523_);
lean_dec_ref(v_a_523_);
return v_res_525_;
}
}
lean_object* l_Lean_Server_RequestM_bindTaskCostly(lean_object* v_00_u03b1_526_, lean_object* v_00_u03b2_527_, lean_object* v_t_528_, lean_object* v_f_529_, lean_object* v_a_530_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_t_528_, v_f_529_, v_a_530_);
return v___x_532_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_bindTaskCostly_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_528_ = stack[2].m_obj;
lean_object* v_f_529_ = stack[3].m_obj;
lean_object* v_a_530_ = stack[4].m_obj;
lean_object* v_res_533_;
v_res_533_ = l_Lean_Server_RequestM_bindTaskCostly(lean_box(0), lean_box(0), v_t_528_, v_f_529_, v_a_530_);
stack->m_obj
 = v_res_533_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly___boxed(lean_object* v_00_u03b1_534_, lean_object* v_00_u03b2_535_, lean_object* v_t_536_, lean_object* v_f_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_Server_RequestM_bindTaskCostly(v_00_u03b1_534_, v_00_u03b2_535_, v_t_536_, v_f_537_, v_a_538_);
lean_dec_ref(v_a_538_);
return v_res_540_;
}
}
lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0(lean_object* v_f_541_, lean_object* v_x_542_, lean_object* v___y_543_){
_start:
{
if (lean_obj_tag(v_x_542_) == 0)
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec_ref(v_f_541_);
v_a_545_ = lean_ctor_get(v_x_542_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v_x_542_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v_x_542_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v_x_542_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
lean_ctor_set_tag(v___x_547_, 1);
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_554_; 
v_a_553_ = lean_ctor_get(v_x_542_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v_x_542_, 1);
lean_inc_ref(v___y_543_);
v___x_554_ = lean_apply_3(v_f_541_, v_a_553_, v___y_543_, lean_box(0));
return v___x_554_;
}
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_541_ = stack[0].m_obj;
lean_object* v_x_542_ = stack[1].m_obj;
lean_object* v___y_543_ = stack[2].m_obj;
lean_object* v_res_555_;
v_res_555_ = l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0(v_f_541_, v_x_542_, v___y_543_);
stack->m_obj
 = v_res_555_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0___boxed(lean_object* v_f_556_, lean_object* v_x_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0(v_f_556_, v_x_557_, v___y_558_);
lean_dec_ref(v___y_558_);
return v_res_560_;
}
}
lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg(lean_object* v_t_561_, lean_object* v_f_562_, lean_object* v_a_563_){
_start:
{
lean_object* v___f_565_; lean_object* v___x_566_; 
v___f_565_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_565_, 0, v_f_562_);
v___x_566_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_t_561_, v___f_565_, v_a_563_);
return v___x_566_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_mapRequestTaskCheap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_561_ = stack[0].m_obj;
lean_object* v_f_562_ = stack[1].m_obj;
lean_object* v_a_563_ = stack[2].m_obj;
lean_object* v_res_567_;
v_res_567_ = l_Lean_Server_RequestM_mapRequestTaskCheap___redArg(v_t_561_, v_f_562_, v_a_563_);
stack->m_obj
 = v_res_567_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___boxed(lean_object* v_t_568_, lean_object* v_f_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_Server_RequestM_mapRequestTaskCheap___redArg(v_t_568_, v_f_569_, v_a_570_);
lean_dec_ref(v_a_570_);
return v_res_572_;
}
}
lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap(lean_object* v_00_u03b1_573_, lean_object* v_00_u03b2_574_, lean_object* v_t_575_, lean_object* v_f_576_, lean_object* v_a_577_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_Server_RequestM_mapRequestTaskCheap___redArg(v_t_575_, v_f_576_, v_a_577_);
return v___x_579_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_mapRequestTaskCheap_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_575_ = stack[2].m_obj;
lean_object* v_f_576_ = stack[3].m_obj;
lean_object* v_a_577_ = stack[4].m_obj;
lean_object* v_res_580_;
v_res_580_ = l_Lean_Server_RequestM_mapRequestTaskCheap(lean_box(0), lean_box(0), v_t_575_, v_f_576_, v_a_577_);
stack->m_obj
 = v_res_580_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___boxed(lean_object* v_00_u03b1_581_, lean_object* v_00_u03b2_582_, lean_object* v_t_583_, lean_object* v_f_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_Server_RequestM_mapRequestTaskCheap(v_00_u03b1_581_, v_00_u03b2_582_, v_t_583_, v_f_584_, v_a_585_);
lean_dec_ref(v_a_585_);
return v_res_587_;
}
}
lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(lean_object* v_t_588_, lean_object* v_f_589_, lean_object* v_a_590_){
_start:
{
lean_object* v___f_592_; lean_object* v___x_593_; 
v___f_592_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_592_, 0, v_f_589_);
v___x_593_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_t_588_, v___f_592_, v_a_590_);
return v___x_593_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_mapRequestTaskCostly___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_588_ = stack[0].m_obj;
lean_object* v_f_589_ = stack[1].m_obj;
lean_object* v_a_590_ = stack[2].m_obj;
lean_object* v_res_594_;
v_res_594_ = l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(v_t_588_, v_f_589_, v_a_590_);
stack->m_obj
 = v_res_594_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly___redArg___boxed(lean_object* v_t_595_, lean_object* v_f_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(v_t_595_, v_f_596_, v_a_597_);
lean_dec_ref(v_a_597_);
return v_res_599_;
}
}
lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly(lean_object* v_00_u03b1_600_, lean_object* v_00_u03b2_601_, lean_object* v_t_602_, lean_object* v_f_603_, lean_object* v_a_604_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(v_t_602_, v_f_603_, v_a_604_);
return v___x_606_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_mapRequestTaskCostly_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_602_ = stack[2].m_obj;
lean_object* v_f_603_ = stack[3].m_obj;
lean_object* v_a_604_ = stack[4].m_obj;
lean_object* v_res_607_;
v_res_607_ = l_Lean_Server_RequestM_mapRequestTaskCostly(lean_box(0), lean_box(0), v_t_602_, v_f_603_, v_a_604_);
stack->m_obj
 = v_res_607_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly___boxed(lean_object* v_00_u03b1_608_, lean_object* v_00_u03b2_609_, lean_object* v_t_610_, lean_object* v_f_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_Server_RequestM_mapRequestTaskCostly(v_00_u03b1_608_, v_00_u03b2_609_, v_t_610_, v_f_611_, v_a_612_);
lean_dec_ref(v_a_612_);
return v_res_614_;
}
}
lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0(lean_object* v_f_615_, lean_object* v_x_616_, lean_object* v___y_617_){
_start:
{
if (lean_obj_tag(v_x_616_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
lean_dec_ref(v_f_615_);
v_a_619_ = lean_ctor_get(v_x_616_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v_x_616_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v_x_616_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v_x_616_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set_tag(v___x_621_, 1);
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
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
lean_object* v_a_627_; lean_object* v___x_628_; 
v_a_627_ = lean_ctor_get(v_x_616_, 0);
lean_inc(v_a_627_);
lean_dec_ref_known(v_x_616_, 1);
lean_inc_ref(v___y_617_);
v___x_628_ = lean_apply_3(v_f_615_, v_a_627_, v___y_617_, lean_box(0));
return v___x_628_;
}
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_615_ = stack[0].m_obj;
lean_object* v_x_616_ = stack[1].m_obj;
lean_object* v___y_617_ = stack[2].m_obj;
lean_object* v_res_629_;
v_res_629_ = l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0(v_f_615_, v_x_616_, v___y_617_);
stack->m_obj
 = v_res_629_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0___boxed(lean_object* v_f_630_, lean_object* v_x_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0(v_f_630_, v_x_631_, v___y_632_);
lean_dec_ref(v___y_632_);
return v_res_634_;
}
}
lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg(lean_object* v_t_635_, lean_object* v_f_636_, lean_object* v_a_637_){
_start:
{
lean_object* v___f_639_; lean_object* v___x_640_; 
v___f_639_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_639_, 0, v_f_636_);
v___x_640_ = l_Lean_Server_RequestM_bindTaskCheap___redArg(v_t_635_, v___f_639_, v_a_637_);
return v___x_640_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_bindRequestTaskCheap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_635_ = stack[0].m_obj;
lean_object* v_f_636_ = stack[1].m_obj;
lean_object* v_a_637_ = stack[2].m_obj;
lean_object* v_res_641_;
v_res_641_ = l_Lean_Server_RequestM_bindRequestTaskCheap___redArg(v_t_635_, v_f_636_, v_a_637_);
stack->m_obj
 = v_res_641_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___boxed(lean_object* v_t_642_, lean_object* v_f_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_Server_RequestM_bindRequestTaskCheap___redArg(v_t_642_, v_f_643_, v_a_644_);
lean_dec_ref(v_a_644_);
return v_res_646_;
}
}
lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap(lean_object* v_00_u03b1_647_, lean_object* v_00_u03b2_648_, lean_object* v_t_649_, lean_object* v_f_650_, lean_object* v_a_651_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_Server_RequestM_bindRequestTaskCheap___redArg(v_t_649_, v_f_650_, v_a_651_);
return v___x_653_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_bindRequestTaskCheap_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_649_ = stack[2].m_obj;
lean_object* v_f_650_ = stack[3].m_obj;
lean_object* v_a_651_ = stack[4].m_obj;
lean_object* v_res_654_;
v_res_654_ = l_Lean_Server_RequestM_bindRequestTaskCheap(lean_box(0), lean_box(0), v_t_649_, v_f_650_, v_a_651_);
stack->m_obj
 = v_res_654_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___boxed(lean_object* v_00_u03b1_655_, lean_object* v_00_u03b2_656_, lean_object* v_t_657_, lean_object* v_f_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_Server_RequestM_bindRequestTaskCheap(v_00_u03b1_655_, v_00_u03b2_656_, v_t_657_, v_f_658_, v_a_659_);
lean_dec_ref(v_a_659_);
return v_res_661_;
}
}
lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly___redArg(lean_object* v_t_662_, lean_object* v_f_663_, lean_object* v_a_664_){
_start:
{
lean_object* v___f_666_; lean_object* v___x_667_; 
v___f_666_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_666_, 0, v_f_663_);
v___x_667_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_t_662_, v___f_666_, v_a_664_);
return v___x_667_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_bindRequestTaskCostly___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_662_ = stack[0].m_obj;
lean_object* v_f_663_ = stack[1].m_obj;
lean_object* v_a_664_ = stack[2].m_obj;
lean_object* v_res_668_;
v_res_668_ = l_Lean_Server_RequestM_bindRequestTaskCostly___redArg(v_t_662_, v_f_663_, v_a_664_);
stack->m_obj
 = v_res_668_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly___redArg___boxed(lean_object* v_t_669_, lean_object* v_f_670_, lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_Server_RequestM_bindRequestTaskCostly___redArg(v_t_669_, v_f_670_, v_a_671_);
lean_dec_ref(v_a_671_);
return v_res_673_;
}
}
lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly(lean_object* v_00_u03b1_674_, lean_object* v_00_u03b2_675_, lean_object* v_t_676_, lean_object* v_f_677_, lean_object* v_a_678_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_Server_RequestM_bindRequestTaskCostly___redArg(v_t_676_, v_f_677_, v_a_678_);
return v___x_680_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_bindRequestTaskCostly_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_676_ = stack[2].m_obj;
lean_object* v_f_677_ = stack[3].m_obj;
lean_object* v_a_678_ = stack[4].m_obj;
lean_object* v_res_681_;
v_res_681_ = l_Lean_Server_RequestM_bindRequestTaskCostly(lean_box(0), lean_box(0), v_t_676_, v_f_677_, v_a_678_);
stack->m_obj
 = v_res_681_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly___boxed(lean_object* v_00_u03b1_682_, lean_object* v_00_u03b2_683_, lean_object* v_t_684_, lean_object* v_f_685_, lean_object* v_a_686_, lean_object* v_a_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_Server_RequestM_bindRequestTaskCostly(v_00_u03b1_682_, v_00_u03b2_683_, v_t_684_, v_f_685_, v_a_686_);
lean_dec_ref(v_a_686_);
return v_res_688_;
}
}
lean_object* l_Lean_Server_RequestM_parseRequestParams___redArg(lean_object* v_inst_689_, lean_object* v_params_690_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_Server_parseRequestParams___redArg(v_inst_689_, v_params_690_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
lean_ctor_set_tag(v___x_695_, 1);
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
v_a_701_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_692_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_692_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set_tag(v___x_703_, 0);
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_parseRequestParams___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_689_ = stack[0].m_obj;
lean_object* v_params_690_ = stack[1].m_obj;
lean_object* v_res_709_;
v_res_709_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_689_, v_params_690_);
stack->m_obj
 = v_res_709_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___redArg___boxed(lean_object* v_inst_710_, lean_object* v_params_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_710_, v_params_711_);
return v_res_713_;
}
}
lean_object* l_Lean_Server_RequestM_parseRequestParams(lean_object* v_paramType_714_, lean_object* v_inst_715_, lean_object* v_params_716_, lean_object* v_a_717_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_715_, v_params_716_);
return v___x_719_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_parseRequestParams_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_715_ = stack[1].m_obj;
lean_object* v_params_716_ = stack[2].m_obj;
lean_object* v_a_717_ = stack[3].m_obj;
lean_object* v_res_720_;
v_res_720_ = l_Lean_Server_RequestM_parseRequestParams(lean_box(0), v_inst_715_, v_params_716_, v_a_717_);
stack->m_obj
 = v_res_720_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___boxed(lean_object* v_paramType_721_, lean_object* v_inst_722_, lean_object* v_params_723_, lean_object* v_a_724_, lean_object* v_a_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_Server_RequestM_parseRequestParams(v_paramType_721_, v_inst_722_, v_params_723_, v_a_724_);
lean_dec_ref(v_a_724_);
return v_res_726_;
}
}
lean_object* l_Lean_Server_RequestM_checkCancelled(lean_object* v_a_727_){
_start:
{
lean_object* v_cancelTk_729_; uint8_t v___x_730_; 
v_cancelTk_729_ = lean_ctor_get(v_a_727_, 4);
v___x_730_ = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_cancelTk_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = lean_box(0);
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
return v___x_732_;
}
else
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = ((lean_object*)(l_Lean_Server_RequestError_requestCancelled));
v___x_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
return v___x_734_;
}
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_checkCancelled_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_727_ = stack[0].m_obj;
lean_object* v_res_735_;
v_res_735_ = l_Lean_Server_RequestM_checkCancelled(v_a_727_);
stack->m_obj
 = v_res_735_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_checkCancelled___boxed(lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_Server_RequestM_checkCancelled(v_a_736_);
lean_dec_ref(v_a_736_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0(lean_object* v_inst_740_, lean_object* v_x_741_){
_start:
{
if (lean_obj_tag(v_x_741_) == 0)
{
lean_object* v_response_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_760_; 
v_response_742_ = lean_ctor_get(v_x_741_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v_x_741_);
if (v_isSharedCheck_760_ == 0)
{
v___x_744_ = v_x_741_;
v_isShared_745_ = v_isSharedCheck_760_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_response_742_);
lean_dec(v_x_741_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_760_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; 
lean_inc(v_response_742_);
v___x_746_ = lean_apply_1(v_inst_740_, v_response_742_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; uint8_t v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
lean_del_object(v___x_744_);
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_746_, 1);
v___x_748_ = 0;
v___x_749_ = ((lean_object*)(l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0___closed__0));
v___x_750_ = l_Lean_Json_compress(v_response_742_);
v___x_751_ = lean_string_append(v___x_749_, v___x_750_);
lean_dec_ref(v___x_750_);
v___x_752_ = ((lean_object*)(l_Lean_Server_parseRequestParams___redArg___closed__1));
v___x_753_ = lean_string_append(v___x_751_, v___x_752_);
v___x_754_ = lean_string_append(v___x_753_, v_a_747_);
lean_dec(v_a_747_);
v___x_755_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_755_, 0, v___x_754_);
lean_ctor_set_uint8(v___x_755_, sizeof(void*)*1, v___x_748_);
return v___x_755_;
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; 
lean_dec(v_response_742_);
v_a_756_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_756_);
lean_dec_ref_known(v___x_746_, 1);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v_a_756_);
v___x_758_ = v___x_744_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
else
{
uint8_t v_code_761_; lean_object* v_message_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_dec_ref(v_inst_740_);
v_code_761_ = lean_ctor_get_uint8(v_x_741_, sizeof(void*)*1);
v_message_762_ = lean_ctor_get(v_x_741_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v_x_741_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v_x_741_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_message_762_);
lean_dec(v_x_741_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_message_762_);
lean_ctor_set_uint8(v_reuseFailAlloc_768_, sizeof(void*)*1, v_code_761_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
lean_object* l_Lean_Server_RequestM_sendServerRequest___redArg(lean_object* v_inst_770_, lean_object* v_inst_771_, lean_object* v_method_772_, lean_object* v_param_773_, lean_object* v_a_774_){
_start:
{
lean_object* v_serverRequestEmitter_776_; lean_object* v___f_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v_serverRequestEmitter_776_ = lean_ctor_get(v_a_774_, 5);
v___f_777_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0), 2, 1);
lean_closure_set(v___f_777_, 0, v_inst_771_);
v___x_778_ = lean_apply_1(v_inst_770_, v_param_773_);
lean_inc_ref(v_serverRequestEmitter_776_);
v___x_779_ = lean_apply_3(v_serverRequestEmitter_776_, v_method_772_, v___x_778_, lean_box(0));
v___x_780_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_777_, v___x_779_);
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_sendServerRequest___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_770_ = stack[0].m_obj;
lean_object* v_inst_771_ = stack[1].m_obj;
lean_object* v_method_772_ = stack[2].m_obj;
lean_object* v_param_773_ = stack[3].m_obj;
lean_object* v_a_774_ = stack[4].m_obj;
lean_object* v_res_782_;
v_res_782_ = l_Lean_Server_RequestM_sendServerRequest___redArg(v_inst_770_, v_inst_771_, v_method_772_, v_param_773_, v_a_774_);
stack->m_obj
 = v_res_782_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___redArg___boxed(lean_object* v_inst_783_, lean_object* v_inst_784_, lean_object* v_method_785_, lean_object* v_param_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_Server_RequestM_sendServerRequest___redArg(v_inst_783_, v_inst_784_, v_method_785_, v_param_786_, v_a_787_);
lean_dec_ref(v_a_787_);
return v_res_789_;
}
}
lean_object* l_Lean_Server_RequestM_sendServerRequest(lean_object* v_paramType_790_, lean_object* v_inst_791_, lean_object* v_responseType_792_, lean_object* v_inst_793_, lean_object* v_inst_794_, lean_object* v_method_795_, lean_object* v_param_796_, lean_object* v_a_797_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_Server_RequestM_sendServerRequest___redArg(v_inst_791_, v_inst_793_, v_method_795_, v_param_796_, v_a_797_);
return v___x_799_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_sendServerRequest_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_791_ = stack[1].m_obj;
lean_object* v_inst_793_ = stack[3].m_obj;
lean_object* v_inst_794_ = stack[4].m_obj;
lean_object* v_method_795_ = stack[5].m_obj;
lean_object* v_param_796_ = stack[6].m_obj;
lean_object* v_a_797_ = stack[7].m_obj;
lean_object* v_res_800_;
v_res_800_ = l_Lean_Server_RequestM_sendServerRequest(lean_box(0), v_inst_791_, lean_box(0), v_inst_793_, v_inst_794_, v_method_795_, v_param_796_, v_a_797_);
stack->m_obj
 = v_res_800_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___boxed(lean_object* v_paramType_801_, lean_object* v_inst_802_, lean_object* v_responseType_803_, lean_object* v_inst_804_, lean_object* v_inst_805_, lean_object* v_method_806_, lean_object* v_param_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_Server_RequestM_sendServerRequest(v_paramType_801_, v_inst_802_, v_responseType_803_, v_inst_804_, v_inst_805_, v_method_806_, v_param_807_, v_a_808_);
lean_dec_ref(v_a_808_);
lean_dec(v_inst_805_);
return v_res_810_;
}
}
lean_object* l_Lean_Server_RequestM_waitFindSnapAux___redArg(lean_object* v_notFoundX_811_, lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v_a_814_){
_start:
{
if (lean_obj_tag(v_x_813_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_824_; 
lean_dec_ref(v_x_812_);
lean_dec_ref(v_notFoundX_811_);
v_a_816_ = lean_ctor_get(v_x_813_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v_x_813_);
if (v_isSharedCheck_824_ == 0)
{
v___x_818_ = v_x_813_;
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v_x_813_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_820_ = l_Lean_Server_RequestError_ofIoError(v_a_816_);
if (v_isShared_819_ == 0)
{
lean_ctor_set_tag(v___x_818_, 1);
lean_ctor_set(v___x_818_, 0, v___x_820_);
v___x_822_ = v___x_818_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
else
{
lean_object* v_a_825_; 
v_a_825_ = lean_ctor_get(v_x_813_, 0);
lean_inc(v_a_825_);
lean_dec_ref_known(v_x_813_, 1);
if (lean_obj_tag(v_a_825_) == 0)
{
lean_object* v___x_826_; 
lean_dec_ref(v_x_812_);
lean_inc_ref(v_a_814_);
v___x_826_ = lean_apply_2(v_notFoundX_811_, v_a_814_, lean_box(0));
return v___x_826_;
}
else
{
lean_object* v_val_827_; lean_object* v___x_828_; 
lean_dec_ref(v_notFoundX_811_);
v_val_827_ = lean_ctor_get(v_a_825_, 0);
lean_inc(v_val_827_);
lean_dec_ref_known(v_a_825_, 1);
lean_inc_ref(v_a_814_);
v___x_828_ = lean_apply_3(v_x_812_, v_val_827_, v_a_814_, lean_box(0));
return v___x_828_;
}
}
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_waitFindSnapAux___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_notFoundX_811_ = stack[0].m_obj;
lean_object* v_x_812_ = stack[1].m_obj;
lean_object* v_x_813_ = stack[2].m_obj;
lean_object* v_a_814_ = stack[3].m_obj;
lean_object* v_res_829_;
v_res_829_ = l_Lean_Server_RequestM_waitFindSnapAux___redArg(v_notFoundX_811_, v_x_812_, v_x_813_, v_a_814_);
stack->m_obj
 = v_res_829_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux___redArg___boxed(lean_object* v_notFoundX_830_, lean_object* v_x_831_, lean_object* v_x_832_, lean_object* v_a_833_, lean_object* v_a_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_Server_RequestM_waitFindSnapAux___redArg(v_notFoundX_830_, v_x_831_, v_x_832_, v_a_833_);
lean_dec_ref(v_a_833_);
return v_res_835_;
}
}
lean_object* l_Lean_Server_RequestM_waitFindSnapAux(lean_object* v_00_u03b1_836_, lean_object* v_notFoundX_837_, lean_object* v_x_838_, lean_object* v_x_839_, lean_object* v_a_840_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Lean_Server_RequestM_waitFindSnapAux___redArg(v_notFoundX_837_, v_x_838_, v_x_839_, v_a_840_);
return v___x_842_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_waitFindSnapAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_notFoundX_837_ = stack[1].m_obj;
lean_object* v_x_838_ = stack[2].m_obj;
lean_object* v_x_839_ = stack[3].m_obj;
lean_object* v_a_840_ = stack[4].m_obj;
lean_object* v_res_843_;
v_res_843_ = l_Lean_Server_RequestM_waitFindSnapAux(lean_box(0), v_notFoundX_837_, v_x_838_, v_x_839_, v_a_840_);
stack->m_obj
 = v_res_843_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux___boxed(lean_object* v_00_u03b1_844_, lean_object* v_notFoundX_845_, lean_object* v_x_846_, lean_object* v_x_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_Server_RequestM_waitFindSnapAux(v_00_u03b1_844_, v_notFoundX_845_, v_x_846_, v_x_847_, v_a_848_);
lean_dec_ref(v_a_848_);
return v_res_850_;
}
}
lean_object* l_Lean_Server_RequestM_withWaitFindSnap___redArg(lean_object* v_doc_851_, lean_object* v_p_852_, lean_object* v_notFoundX_853_, lean_object* v_x_854_, lean_object* v_a_855_){
_start:
{
lean_object* v_toEditableDocumentCore_857_; lean_object* v_cmdSnaps_858_; lean_object* v_findTask_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v_toEditableDocumentCore_857_ = lean_ctor_get(v_doc_851_, 0);
lean_inc_ref(v_toEditableDocumentCore_857_);
lean_dec_ref(v_doc_851_);
v_cmdSnaps_858_ = lean_ctor_get(v_toEditableDocumentCore_857_, 2);
lean_inc(v_cmdSnaps_858_);
lean_dec_ref(v_toEditableDocumentCore_857_);
v_findTask_859_ = l_Lean_AsyncList_waitFind_x3f___redArg(v_p_852_, v_cmdSnaps_858_);
v___x_860_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_waitFindSnapAux___boxed), 6, 3);
lean_closure_set(v___x_860_, 0, lean_box(0));
lean_closure_set(v___x_860_, 1, v_notFoundX_853_);
lean_closure_set(v___x_860_, 2, v_x_854_);
v___x_861_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_findTask_859_, v___x_860_, v_a_855_);
return v___x_861_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_withWaitFindSnap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_doc_851_ = stack[0].m_obj;
lean_object* v_p_852_ = stack[1].m_obj;
lean_object* v_notFoundX_853_ = stack[2].m_obj;
lean_object* v_x_854_ = stack[3].m_obj;
lean_object* v_a_855_ = stack[4].m_obj;
lean_object* v_res_862_;
v_res_862_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_doc_851_, v_p_852_, v_notFoundX_853_, v_x_854_, v_a_855_);
stack->m_obj
 = v_res_862_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___redArg___boxed(lean_object* v_doc_863_, lean_object* v_p_864_, lean_object* v_notFoundX_865_, lean_object* v_x_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_doc_863_, v_p_864_, v_notFoundX_865_, v_x_866_, v_a_867_);
lean_dec_ref(v_a_867_);
return v_res_869_;
}
}
lean_object* l_Lean_Server_RequestM_withWaitFindSnap(lean_object* v_00_u03b2_870_, lean_object* v_doc_871_, lean_object* v_p_872_, lean_object* v_notFoundX_873_, lean_object* v_x_874_, lean_object* v_a_875_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_doc_871_, v_p_872_, v_notFoundX_873_, v_x_874_, v_a_875_);
return v___x_877_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_withWaitFindSnap_0interp(lean_interpreter_value* stack)
{
lean_object* v_doc_871_ = stack[1].m_obj;
lean_object* v_p_872_ = stack[2].m_obj;
lean_object* v_notFoundX_873_ = stack[3].m_obj;
lean_object* v_x_874_ = stack[4].m_obj;
lean_object* v_a_875_ = stack[5].m_obj;
lean_object* v_res_878_;
v_res_878_ = l_Lean_Server_RequestM_withWaitFindSnap(lean_box(0), v_doc_871_, v_p_872_, v_notFoundX_873_, v_x_874_, v_a_875_);
stack->m_obj
 = v_res_878_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___boxed(lean_object* v_00_u03b2_879_, lean_object* v_doc_880_, lean_object* v_p_881_, lean_object* v_notFoundX_882_, lean_object* v_x_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_Server_RequestM_withWaitFindSnap(v_00_u03b2_879_, v_doc_880_, v_p_881_, v_notFoundX_882_, v_x_883_, v_a_884_);
lean_dec_ref(v_a_884_);
return v_res_886_;
}
}
lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___redArg(lean_object* v_doc_887_, lean_object* v_p_888_, lean_object* v_notFoundX_889_, lean_object* v_x_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_toEditableDocumentCore_893_; lean_object* v_cmdSnaps_894_; lean_object* v_findTask_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_toEditableDocumentCore_893_ = lean_ctor_get(v_doc_887_, 0);
lean_inc_ref(v_toEditableDocumentCore_893_);
lean_dec_ref(v_doc_887_);
v_cmdSnaps_894_ = lean_ctor_get(v_toEditableDocumentCore_893_, 2);
lean_inc(v_cmdSnaps_894_);
lean_dec_ref(v_toEditableDocumentCore_893_);
v_findTask_895_ = l_Lean_AsyncList_waitFind_x3f___redArg(v_p_888_, v_cmdSnaps_894_);
v___x_896_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_waitFindSnapAux___boxed), 6, 3);
lean_closure_set(v___x_896_, 0, lean_box(0));
lean_closure_set(v___x_896_, 1, v_notFoundX_889_);
lean_closure_set(v___x_896_, 2, v_x_890_);
v___x_897_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_findTask_895_, v___x_896_, v_a_891_);
return v___x_897_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_bindWaitFindSnap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_doc_887_ = stack[0].m_obj;
lean_object* v_p_888_ = stack[1].m_obj;
lean_object* v_notFoundX_889_ = stack[2].m_obj;
lean_object* v_x_890_ = stack[3].m_obj;
lean_object* v_a_891_ = stack[4].m_obj;
lean_object* v_res_898_;
v_res_898_ = l_Lean_Server_RequestM_bindWaitFindSnap___redArg(v_doc_887_, v_p_888_, v_notFoundX_889_, v_x_890_, v_a_891_);
stack->m_obj
 = v_res_898_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___redArg___boxed(lean_object* v_doc_899_, lean_object* v_p_900_, lean_object* v_notFoundX_901_, lean_object* v_x_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_Server_RequestM_bindWaitFindSnap___redArg(v_doc_899_, v_p_900_, v_notFoundX_901_, v_x_902_, v_a_903_);
lean_dec_ref(v_a_903_);
return v_res_905_;
}
}
lean_object* l_Lean_Server_RequestM_bindWaitFindSnap(lean_object* v_00_u03b2_906_, lean_object* v_doc_907_, lean_object* v_p_908_, lean_object* v_notFoundX_909_, lean_object* v_x_910_, lean_object* v_a_911_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_Lean_Server_RequestM_bindWaitFindSnap___redArg(v_doc_907_, v_p_908_, v_notFoundX_909_, v_x_910_, v_a_911_);
return v___x_913_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_bindWaitFindSnap_0interp(lean_interpreter_value* stack)
{
lean_object* v_doc_907_ = stack[1].m_obj;
lean_object* v_p_908_ = stack[2].m_obj;
lean_object* v_notFoundX_909_ = stack[3].m_obj;
lean_object* v_x_910_ = stack[4].m_obj;
lean_object* v_a_911_ = stack[5].m_obj;
lean_object* v_res_914_;
v_res_914_ = l_Lean_Server_RequestM_bindWaitFindSnap(lean_box(0), v_doc_907_, v_p_908_, v_notFoundX_909_, v_x_910_, v_a_911_);
stack->m_obj
 = v_res_914_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___boxed(lean_object* v_00_u03b2_915_, lean_object* v_doc_916_, lean_object* v_p_917_, lean_object* v_notFoundX_918_, lean_object* v_x_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_Server_RequestM_bindWaitFindSnap(v_00_u03b2_915_, v_doc_916_, v_p_917_, v_notFoundX_918_, v_x_919_, v_a_920_);
lean_dec_ref(v_a_920_);
return v_res_922_;
}
}
lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(lean_object* v___y_923_){
_start:
{
lean_object* v_doc_925_; lean_object* v___x_926_; 
v_doc_925_ = lean_ctor_get(v___y_923_, 1);
lean_inc_ref(v_doc_925_);
v___x_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_926_, 0, v_doc_925_);
return v___x_926_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_923_ = stack[0].m_obj;
lean_object* v_res_927_;
v_res_927_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(v___y_923_);
stack->m_obj
 = v_res_927_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0___boxed(lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(v___y_928_);
lean_dec_ref(v___y_928_);
return v_res_930_;
}
}
uint8_t l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0(lean_object* v___x_931_, lean_object* v_s_932_){
_start:
{
lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_933_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_s_932_);
v___x_934_ = lean_nat_dec_le(v___x_931_, v___x_933_);
lean_dec(v___x_933_);
return v___x_934_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_931_ = stack[0].m_obj;
lean_object* v_s_932_ = stack[1].m_obj;
uint8_t v_res_935_;
v_res_935_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0(v___x_931_, v_s_932_);
stack->m_num = v_res_935_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0___boxed(lean_object* v___x_936_, lean_object* v_s_937_){
_start:
{
uint8_t v_res_938_; lean_object* v_r_939_; 
v_res_938_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0(v___x_936_, v_s_937_);
lean_dec_ref(v_s_937_);
lean_dec(v___x_936_);
v_r_939_ = lean_box(v_res_938_);
return v_r_939_;
}
}
lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1(lean_object* v___x_940_, lean_object* v___y_941_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_940_);
return v___x_943_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_940_ = stack[0].m_obj;
lean_object* v___y_941_ = stack[1].m_obj;
lean_object* v_res_944_;
v_res_944_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1(v___x_940_, v___y_941_);
stack->m_obj
 = v_res_944_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1___boxed(lean_object* v___x_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1(v___x_945_, v___y_946_);
lean_dec_ref(v___y_946_);
return v_res_948_;
}
}
lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg(lean_object* v_lspPos_953_, lean_object* v_f_954_, lean_object* v_a_955_){
_start:
{
lean_object* v___x_957_; lean_object* v_a_958_; lean_object* v_toEditableDocumentCore_959_; lean_object* v_meta_960_; lean_object* v_text_961_; lean_object* v_line_962_; lean_object* v_character_963_; lean_object* v___x_964_; lean_object* v___f_965_; uint8_t v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___f_979_; lean_object* v___x_980_; 
v___x_957_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(v_a_955_);
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
lean_dec_ref(v___x_957_);
v_toEditableDocumentCore_959_ = lean_ctor_get(v_a_958_, 0);
v_meta_960_ = lean_ctor_get(v_toEditableDocumentCore_959_, 0);
v_text_961_ = lean_ctor_get(v_meta_960_, 3);
v_line_962_ = lean_ctor_get(v_lspPos_953_, 0);
lean_inc(v_line_962_);
v_character_963_ = lean_ctor_get(v_lspPos_953_, 1);
lean_inc(v_character_963_);
v___x_964_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_961_, v_lspPos_953_);
v___f_965_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_965_, 0, v___x_964_);
v___x_966_ = 3;
v___x_967_ = ((lean_object*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__0));
v___x_968_ = ((lean_object*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__1));
v___x_969_ = l_Nat_reprFast(v_line_962_);
v___x_970_ = lean_string_append(v___x_968_, v___x_969_);
lean_dec_ref(v___x_969_);
v___x_971_ = ((lean_object*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__2));
v___x_972_ = lean_string_append(v___x_970_, v___x_971_);
v___x_973_ = l_Nat_reprFast(v_character_963_);
v___x_974_ = lean_string_append(v___x_972_, v___x_973_);
lean_dec_ref(v___x_973_);
v___x_975_ = ((lean_object*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__3));
v___x_976_ = lean_string_append(v___x_974_, v___x_975_);
v___x_977_ = lean_string_append(v___x_967_, v___x_976_);
lean_dec_ref(v___x_976_);
v___x_978_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set_uint8(v___x_978_, sizeof(void*)*1, v___x_966_);
v___f_979_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_979_, 0, v___x_978_);
v___x_980_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_a_958_, v___f_965_, v___f_979_, v_f_954_, v_a_955_);
return v___x_980_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lspPos_953_ = stack[0].m_obj;
lean_object* v_f_954_ = stack[1].m_obj;
lean_object* v_a_955_ = stack[2].m_obj;
lean_object* v_res_981_;
v_res_981_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg(v_lspPos_953_, v_f_954_, v_a_955_);
stack->m_obj
 = v_res_981_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___boxed(lean_object* v_lspPos_982_, lean_object* v_f_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg(v_lspPos_982_, v_f_983_, v_a_984_);
lean_dec_ref(v_a_984_);
return v_res_986_;
}
}
lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos(lean_object* v_00_u03b1_987_, lean_object* v_lspPos_988_, lean_object* v_f_989_, lean_object* v_a_990_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg(v_lspPos_988_, v_f_989_, v_a_990_);
return v___x_992_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_withWaitFindSnapAtPos_0interp(lean_interpreter_value* stack)
{
lean_object* v_lspPos_988_ = stack[1].m_obj;
lean_object* v_f_989_ = stack[2].m_obj;
lean_object* v_a_990_ = stack[3].m_obj;
lean_object* v_res_993_;
v_res_993_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos(lean_box(0), v_lspPos_988_, v_f_989_, v_a_990_);
stack->m_obj
 = v_res_993_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___boxed(lean_object* v_00_u03b1_994_, lean_object* v_lspPos_995_, lean_object* v_f_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos(v_00_u03b1_994_, v_lspPos_995_, v_f_996_, v_a_997_);
lean_dec_ref(v_a_997_);
return v_res_999_;
}
}
lean_object* l_Lean_Server_RequestM_runCommandElabM___redArg(lean_object* v_snap_1000_, lean_object* v_c_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v_doc_1004_; lean_object* v_toEditableDocumentCore_1005_; lean_object* v_meta_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_doc_1004_ = lean_ctor_get(v_a_1002_, 1);
v_toEditableDocumentCore_1005_ = lean_ctor_get(v_doc_1004_, 0);
v_meta_1006_ = lean_ctor_get(v_toEditableDocumentCore_1005_, 0);
lean_inc_ref(v_a_1002_);
v___x_1007_ = lean_apply_1(v_c_1001_, v_a_1002_);
v___x_1008_ = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(v_snap_1000_, v_meta_1006_, v___x_1007_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1021_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1011_ = v___x_1008_;
v_isShared_1012_ = v_isSharedCheck_1021_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1021_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
if (lean_obj_tag(v_a_1009_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1015_; 
v_a_1013_ = lean_ctor_get(v_a_1009_, 0);
lean_inc(v_a_1013_);
lean_dec_ref_known(v_a_1009_, 1);
if (v_isShared_1012_ == 0)
{
lean_ctor_set_tag(v___x_1011_, 1);
lean_ctor_set(v___x_1011_, 0, v_a_1013_);
v___x_1015_ = v___x_1011_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; 
v_a_1017_ = lean_ctor_get(v_a_1009_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v_a_1009_, 1);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v_a_1017_);
v___x_1019_ = v___x_1011_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1023_; lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
v_a_1022_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1008_, 1);
v___x_1023_ = l_Lean_Server_RequestError_ofException(v_a_1022_);
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1023_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1023_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
lean_ctor_set_tag(v___x_1026_, 1);
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_runCommandElabM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_snap_1000_ = stack[0].m_obj;
lean_object* v_c_1001_ = stack[1].m_obj;
lean_object* v_a_1002_ = stack[2].m_obj;
lean_object* v_res_1032_;
v_res_1032_ = l_Lean_Server_RequestM_runCommandElabM___redArg(v_snap_1000_, v_c_1001_, v_a_1002_);
stack->m_obj
 = v_res_1032_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___redArg___boxed(lean_object* v_snap_1033_, lean_object* v_c_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_Server_RequestM_runCommandElabM___redArg(v_snap_1033_, v_c_1034_, v_a_1035_);
lean_dec_ref(v_a_1035_);
return v_res_1037_;
}
}
lean_object* l_Lean_Server_RequestM_runCommandElabM(lean_object* v_00_u03b1_1038_, lean_object* v_snap_1039_, lean_object* v_c_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lean_Server_RequestM_runCommandElabM___redArg(v_snap_1039_, v_c_1040_, v_a_1041_);
return v___x_1043_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_runCommandElabM_0interp(lean_interpreter_value* stack)
{
lean_object* v_snap_1039_ = stack[1].m_obj;
lean_object* v_c_1040_ = stack[2].m_obj;
lean_object* v_a_1041_ = stack[3].m_obj;
lean_object* v_res_1044_;
v_res_1044_ = l_Lean_Server_RequestM_runCommandElabM(lean_box(0), v_snap_1039_, v_c_1040_, v_a_1041_);
stack->m_obj
 = v_res_1044_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___boxed(lean_object* v_00_u03b1_1045_, lean_object* v_snap_1046_, lean_object* v_c_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_Server_RequestM_runCommandElabM(v_00_u03b1_1045_, v_snap_1046_, v_c_1047_, v_a_1048_);
lean_dec_ref(v_a_1048_);
return v_res_1050_;
}
}
lean_object* l_Lean_Server_RequestM_runCoreM___redArg(lean_object* v_snap_1051_, lean_object* v_c_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v_doc_1055_; lean_object* v_toEditableDocumentCore_1056_; lean_object* v_meta_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v_doc_1055_ = lean_ctor_get(v_a_1053_, 1);
v_toEditableDocumentCore_1056_ = lean_ctor_get(v_doc_1055_, 0);
v_meta_1057_ = lean_ctor_get(v_toEditableDocumentCore_1056_, 0);
lean_inc_ref(v_a_1053_);
v___x_1058_ = lean_apply_1(v_c_1052_, v_a_1053_);
v___x_1059_ = l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(v_snap_1051_, v_meta_1057_, v___x_1058_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1072_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1062_ = v___x_1059_;
v_isShared_1063_ = v_isSharedCheck_1072_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1059_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1072_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
if (lean_obj_tag(v_a_1060_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1066_; 
v_a_1064_ = lean_ctor_get(v_a_1060_, 0);
lean_inc(v_a_1064_);
lean_dec_ref_known(v_a_1060_, 1);
if (v_isShared_1063_ == 0)
{
lean_ctor_set_tag(v___x_1062_, 1);
lean_ctor_set(v___x_1062_, 0, v_a_1064_);
v___x_1066_ = v___x_1062_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; 
v_a_1068_ = lean_ctor_get(v_a_1060_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v_a_1060_, 1);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 0, v_a_1068_);
v___x_1070_ = v___x_1062_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1068_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1074_; lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
v_a_1073_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1073_);
lean_dec_ref_known(v___x_1059_, 1);
v___x_1074_ = l_Lean_Server_RequestError_ofException(v_a_1073_);
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1074_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1074_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set_tag(v___x_1077_, 1);
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_runCoreM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_snap_1051_ = stack[0].m_obj;
lean_object* v_c_1052_ = stack[1].m_obj;
lean_object* v_a_1053_ = stack[2].m_obj;
lean_object* v_res_1083_;
v_res_1083_ = l_Lean_Server_RequestM_runCoreM___redArg(v_snap_1051_, v_c_1052_, v_a_1053_);
stack->m_obj
 = v_res_1083_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___redArg___boxed(lean_object* v_snap_1084_, lean_object* v_c_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_Server_RequestM_runCoreM___redArg(v_snap_1084_, v_c_1085_, v_a_1086_);
lean_dec_ref(v_a_1086_);
return v_res_1088_;
}
}
lean_object* l_Lean_Server_RequestM_runCoreM(lean_object* v_00_u03b1_1089_, lean_object* v_snap_1090_, lean_object* v_c_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Lean_Server_RequestM_runCoreM___redArg(v_snap_1090_, v_c_1091_, v_a_1092_);
return v___x_1094_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_runCoreM_0interp(lean_interpreter_value* stack)
{
lean_object* v_snap_1090_ = stack[1].m_obj;
lean_object* v_c_1091_ = stack[2].m_obj;
lean_object* v_a_1092_ = stack[3].m_obj;
lean_object* v_res_1095_;
v_res_1095_ = l_Lean_Server_RequestM_runCoreM(lean_box(0), v_snap_1090_, v_c_1091_, v_a_1092_);
stack->m_obj
 = v_res_1095_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___boxed(lean_object* v_00_u03b1_1096_, lean_object* v_snap_1097_, lean_object* v_c_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_Server_RequestM_runCoreM(v_00_u03b1_1096_, v_snap_1097_, v_c_1098_, v_a_1099_);
lean_dec_ref(v_a_1099_);
return v_res_1101_;
}
}
lean_object* l_Lean_Server_RequestM_runTermElabM___redArg(lean_object* v_snap_1102_, lean_object* v_c_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v_doc_1106_; lean_object* v_toEditableDocumentCore_1107_; lean_object* v_meta_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v_doc_1106_ = lean_ctor_get(v_a_1104_, 1);
v_toEditableDocumentCore_1107_ = lean_ctor_get(v_doc_1106_, 0);
v_meta_1108_ = lean_ctor_get(v_toEditableDocumentCore_1107_, 0);
lean_inc_ref(v_a_1104_);
v___x_1109_ = lean_apply_1(v_c_1103_, v_a_1104_);
v___x_1110_ = l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg(v_snap_1102_, v_meta_1108_, v___x_1109_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1123_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1113_ = v___x_1110_;
v_isShared_1114_ = v_isSharedCheck_1123_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1110_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1123_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
if (lean_obj_tag(v_a_1111_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1117_; 
v_a_1115_ = lean_ctor_get(v_a_1111_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v_a_1111_, 1);
if (v_isShared_1114_ == 0)
{
lean_ctor_set_tag(v___x_1113_, 1);
lean_ctor_set(v___x_1113_, 0, v_a_1115_);
v___x_1117_ = v___x_1113_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1115_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; 
v_a_1119_ = lean_ctor_get(v_a_1111_, 0);
lean_inc(v_a_1119_);
lean_dec_ref_known(v_a_1111_, 1);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v_a_1119_);
v___x_1121_ = v___x_1113_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1119_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1125_; lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
v_a_1124_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1124_);
lean_dec_ref_known(v___x_1110_, 1);
v___x_1125_ = l_Lean_Server_RequestError_ofException(v_a_1124_);
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1125_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1125_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set_tag(v___x_1128_, 1);
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
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
LEAN_EXPORT void l_Lean_Server_RequestM_runTermElabM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_snap_1102_ = stack[0].m_obj;
lean_object* v_c_1103_ = stack[1].m_obj;
lean_object* v_a_1104_ = stack[2].m_obj;
lean_object* v_res_1134_;
v_res_1134_ = l_Lean_Server_RequestM_runTermElabM___redArg(v_snap_1102_, v_c_1103_, v_a_1104_);
stack->m_obj
 = v_res_1134_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___redArg___boxed(lean_object* v_snap_1135_, lean_object* v_c_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_Server_RequestM_runTermElabM___redArg(v_snap_1135_, v_c_1136_, v_a_1137_);
lean_dec_ref(v_a_1137_);
return v_res_1139_;
}
}
lean_object* l_Lean_Server_RequestM_runTermElabM(lean_object* v_00_u03b1_1140_, lean_object* v_snap_1141_, lean_object* v_c_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Lean_Server_RequestM_runTermElabM___redArg(v_snap_1141_, v_c_1142_, v_a_1143_);
return v___x_1145_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_runTermElabM_0interp(lean_interpreter_value* stack)
{
lean_object* v_snap_1141_ = stack[1].m_obj;
lean_object* v_c_1142_ = stack[2].m_obj;
lean_object* v_a_1143_ = stack[3].m_obj;
lean_object* v_res_1146_;
v_res_1146_ = l_Lean_Server_RequestM_runTermElabM(lean_box(0), v_snap_1141_, v_c_1142_, v_a_1143_);
stack->m_obj
 = v_res_1146_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___boxed(lean_object* v_00_u03b1_1147_, lean_object* v_snap_1148_, lean_object* v_c_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_Server_RequestM_runTermElabM(v_00_u03b1_1147_, v_snap_1148_, v_c_1149_, v_a_1150_);
lean_dec_ref(v_a_1150_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage(lean_object* v_id_1159_, lean_object* v_r_1160_){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___y_1164_; 
v___x_1161_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__0));
v___x_1162_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__1));
switch(lean_obj_tag(v_id_1159_))
{
case 0:
{
lean_object* v_s_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
v_s_1178_ = lean_ctor_get(v_id_1159_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_id_1159_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v_id_1159_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_s_1178_);
lean_dec(v_id_1159_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
lean_ctor_set_tag(v___x_1180_, 3);
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_s_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
v___y_1164_ = v___x_1183_;
goto v___jp_1163_;
}
}
}
case 1:
{
lean_object* v_n_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
v_n_1186_ = lean_ctor_get(v_id_1159_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_id_1159_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v_id_1159_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_n_1186_);
lean_dec(v_id_1159_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set_tag(v___x_1188_, 2);
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_n_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
v___y_1164_ = v___x_1191_;
goto v___jp_1163_;
}
}
}
default: 
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_box(0);
v___y_1164_ = v___x_1194_;
goto v___jp_1163_;
}
}
v___jp_1163_:
{
lean_object* v_serialized_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v_serialized_1165_ = lean_ctor_get(v_r_1160_, 1);
v___x_1166_ = l_Lean_Json_compress(v___y_1164_);
v___x_1167_ = lean_string_append(v___x_1162_, v___x_1166_);
lean_dec_ref(v___x_1166_);
v___x_1168_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__2));
v___x_1169_ = lean_string_append(v___x_1167_, v___x_1168_);
v___x_1170_ = lean_string_append(v___x_1161_, v___x_1169_);
lean_dec_ref(v___x_1169_);
v___x_1171_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__3));
v___x_1172_ = lean_string_append(v___x_1170_, v___x_1171_);
v___x_1173_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__4));
v___x_1174_ = lean_string_append(v___x_1173_, v_serialized_1165_);
v___x_1175_ = lean_string_append(v___x_1172_, v___x_1174_);
lean_dec_ref(v___x_1174_);
v___x_1176_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__5));
v___x_1177_ = lean_string_append(v___x_1175_, v___x_1176_);
return v___x_1177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage___boxed(lean_object* v_id_1195_, lean_object* v_r_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_Server_SerializedLspResponse_toSerializedMessage(v_id_1195_, v_r_1196_);
lean_dec_ref(v_r_1196_);
return v_res_1197_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1198_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_);
v___x_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
return v___x_1200_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1202_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_);
v___x_1203_ = lean_st_mk_ref(v___x_1202_);
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1205_;
v_res_1205_ = l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1205_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2____boxed(lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_();
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__0(lean_object* v_inst_1208_, lean_object* v_inst_1209_, lean_object* v_j_1210_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Lean_Server_parseRequestParams___redArg(v_inst_1208_, v_j_1210_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
lean_dec_ref(v_inst_1209_);
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1211_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1211_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1228_; 
v_a_1220_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1222_ = v___x_1211_;
v_isShared_1223_ = v_isSharedCheck_1228_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1211_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1228_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1224_; lean_object* v___x_1226_; 
v___x_1224_ = lean_apply_1(v_inst_1209_, v_a_1220_);
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 0, v___x_1224_);
v___x_1226_ = v___x_1222_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__1(lean_object* v_serialize_x3f_1229_, uint8_t v_val_1230_, lean_object* v_inst_1231_, lean_object* v_r_1232_){
_start:
{
if (lean_obj_tag(v_serialize_x3f_1229_) == 1)
{
lean_object* v_val_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_dec_ref(v_inst_1231_);
v_val_1233_ = lean_ctor_get(v_serialize_x3f_1229_, 0);
lean_inc(v_val_1233_);
lean_dec_ref_known(v_serialize_x3f_1229_, 1);
v___x_1234_ = lean_box(0);
v___x_1235_ = lean_apply_1(v_val_1233_, v_r_1232_);
v___x_1236_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1236_, 0, v___x_1234_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
lean_ctor_set_uint8(v___x_1236_, sizeof(void*)*2, v_val_1230_);
return v___x_1236_;
}
else
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
lean_dec(v_serialize_x3f_1229_);
v___x_1237_ = lean_apply_1(v_inst_1231_, v_r_1232_);
lean_inc(v___x_1237_);
v___x_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
v___x_1239_ = l_Lean_Json_compress(v___x_1237_);
v___x_1240_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1240_, 0, v___x_1238_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
lean_ctor_set_uint8(v___x_1240_, sizeof(void*)*2, v_val_1230_);
return v___x_1240_;
}
}
}
LEAN_EXPORT void l_Lean_Server_registerLspRequestHandler___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_serialize_x3f_1229_ = stack[0].m_obj;
uint8_t v_val_1230_ = stack[1].m_num;
lean_object* v_inst_1231_ = stack[2].m_obj;
lean_object* v_r_1232_ = stack[3].m_obj;
lean_object* v_res_1241_;
v_res_1241_ = l_Lean_Server_registerLspRequestHandler___redArg___lam__1(v_serialize_x3f_1229_, v_val_1230_, v_inst_1231_, v_r_1232_);
stack->m_obj
 = v_res_1241_;
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__1___boxed(lean_object* v_serialize_x3f_1242_, lean_object* v_val_1243_, lean_object* v_inst_1244_, lean_object* v_r_1245_){
_start:
{
uint8_t v_val_1382__boxed_1246_; lean_object* v_res_1247_; 
v_val_1382__boxed_1246_ = lean_unbox(v_val_1243_);
v_res_1247_ = l_Lean_Server_registerLspRequestHandler___redArg___lam__1(v_serialize_x3f_1242_, v_val_1382__boxed_1246_, v_inst_1244_, v_r_1245_);
return v_res_1247_;
}
}
lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__2(lean_object* v_inst_1248_, lean_object* v_handler_1249_, lean_object* v___f_1250_, lean_object* v_j_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_1248_, v_j_1251_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v___x_1256_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
lean_dec_ref_known(v___x_1254_, 1);
lean_inc_ref(v___y_1252_);
v___x_1256_ = lean_apply_3(v_handler_1249_, v_a_1255_, v___y_1252_, lean_box(0));
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1266_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1259_ = v___x_1256_;
v_isShared_1260_ = v_isSharedCheck_1266_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1256_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1266_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1264_; 
v___x_1261_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_1261_, 0, lean_box(0));
lean_closure_set(v___x_1261_, 1, lean_box(0));
lean_closure_set(v___x_1261_, 2, lean_box(0));
lean_closure_set(v___x_1261_, 3, v___f_1250_);
v___x_1262_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___x_1261_, v_a_1257_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1262_);
v___x_1264_ = v___x_1259_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1262_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec_ref(v___f_1250_);
v_a_1267_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1256_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1256_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_dec_ref(v___f_1250_);
lean_dec_ref(v_handler_1249_);
v_a_1275_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1254_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1254_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_registerLspRequestHandler___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1248_ = stack[0].m_obj;
lean_object* v_handler_1249_ = stack[1].m_obj;
lean_object* v___f_1250_ = stack[2].m_obj;
lean_object* v_j_1251_ = stack[3].m_obj;
lean_object* v___y_1252_ = stack[4].m_obj;
lean_object* v_res_1283_;
v_res_1283_ = l_Lean_Server_registerLspRequestHandler___redArg___lam__2(v_inst_1248_, v_handler_1249_, v___f_1250_, v_j_1251_, v___y_1252_);
stack->m_obj
 = v_res_1283_;
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__2___boxed(lean_object* v_inst_1284_, lean_object* v_handler_1285_, lean_object* v___f_1286_, lean_object* v_j_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_Server_registerLspRequestHandler___redArg___lam__2(v_inst_1284_, v_handler_1285_, v___f_1286_, v_j_1287_, v___y_1288_);
lean_dec_ref(v___y_1288_);
return v_res_1290_;
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___f_1295_; 
v___x_1294_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___f_1295_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1295_, 0, v___x_1294_);
return v___f_1295_;
}
}
lean_object* l_Lean_Server_registerLspRequestHandler___redArg(lean_object* v_method_1297_, lean_object* v_inst_1298_, lean_object* v_inst_1299_, lean_object* v_inst_1300_, lean_object* v_handler_1301_, lean_object* v_serialize_x3f_1302_){
_start:
{
lean_object* v___f_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
lean_inc_ref(v_inst_1298_);
v___f_1304_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1304_, 0, v_inst_1298_);
lean_closure_set(v___f_1304_, 1, v_inst_1299_);
v___x_1305_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__0));
v___x_1306_ = l_Lean_initializing();
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
lean_dec_ref(v___f_1304_);
lean_dec(v_serialize_x3f_1302_);
lean_dec_ref(v_handler_1301_);
lean_dec_ref(v_inst_1300_);
lean_dec_ref(v_inst_1298_);
v___x_1307_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__1));
v___x_1308_ = lean_string_append(v___x_1307_, v_method_1297_);
lean_dec_ref(v_method_1297_);
v___x_1309_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___x_1310_ = lean_string_append(v___x_1308_, v___x_1309_);
v___x_1311_ = lean_mk_io_user_error(v___x_1310_);
v___x_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
return v___x_1312_;
}
else
{
lean_object* v___x_1313_; lean_object* v___f_1314_; lean_object* v___f_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___f_1318_; uint8_t v___x_1319_; 
v___x_1313_ = lean_box(v___x_1306_);
v___f_1314_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1314_, 0, v_serialize_x3f_1302_);
lean_closure_set(v___f_1314_, 1, v___x_1313_);
lean_closure_set(v___f_1314_, 2, v_inst_1300_);
v___f_1315_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1315_, 0, v_inst_1298_);
lean_closure_set(v___f_1315_, 1, v_handler_1301_);
lean_closure_set(v___f_1315_, 2, v___f_1314_);
v___x_1316_ = l_Lean_Server_requestHandlers;
v___x_1317_ = lean_st_ref_get(v___x_1316_);
v___f_1318_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
lean_inc_ref(v_method_1297_);
v___x_1319_ = l_Lean_PersistentHashMap_contains___redArg(v___f_1318_, v___x_1305_, v___x_1317_, v_method_1297_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1320_ = lean_st_ref_take(v___x_1316_);
v___x_1321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1321_, 0, v___f_1304_);
lean_ctor_set(v___x_1321_, 1, v___f_1315_);
v___x_1322_ = l_Lean_PersistentHashMap_insert___redArg(v___f_1318_, v___x_1305_, v___x_1320_, v_method_1297_, v___x_1321_);
v___x_1323_ = lean_st_ref_put(v___x_1316_, v___x_1322_);
v___x_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
return v___x_1324_;
}
else
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
lean_dec_ref(v___f_1315_);
lean_dec_ref(v___f_1304_);
v___x_1325_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__1));
v___x_1326_ = lean_string_append(v___x_1325_, v_method_1297_);
lean_dec_ref(v_method_1297_);
v___x_1327_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__4));
v___x_1328_ = lean_string_append(v___x_1326_, v___x_1327_);
v___x_1329_ = lean_mk_io_user_error(v___x_1328_);
v___x_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
return v___x_1330_;
}
}
}
}
LEAN_EXPORT void l_Lean_Server_registerLspRequestHandler___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_1297_ = stack[0].m_obj;
lean_object* v_inst_1298_ = stack[1].m_obj;
lean_object* v_inst_1299_ = stack[2].m_obj;
lean_object* v_inst_1300_ = stack[3].m_obj;
lean_object* v_handler_1301_ = stack[4].m_obj;
lean_object* v_serialize_x3f_1302_ = stack[5].m_obj;
lean_object* v_res_1331_;
v_res_1331_ = l_Lean_Server_registerLspRequestHandler___redArg(v_method_1297_, v_inst_1298_, v_inst_1299_, v_inst_1300_, v_handler_1301_, v_serialize_x3f_1302_);
stack->m_obj
 = v_res_1331_;
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___boxed(lean_object* v_method_1332_, lean_object* v_inst_1333_, lean_object* v_inst_1334_, lean_object* v_inst_1335_, lean_object* v_handler_1336_, lean_object* v_serialize_x3f_1337_, lean_object* v_a_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_Server_registerLspRequestHandler___redArg(v_method_1332_, v_inst_1333_, v_inst_1334_, v_inst_1335_, v_handler_1336_, v_serialize_x3f_1337_);
return v_res_1339_;
}
}
lean_object* l_Lean_Server_registerLspRequestHandler(lean_object* v_method_1340_, lean_object* v_paramType_1341_, lean_object* v_inst_1342_, lean_object* v_inst_1343_, lean_object* v_respType_1344_, lean_object* v_inst_1345_, lean_object* v_handler_1346_, lean_object* v_serialize_x3f_1347_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_Server_registerLspRequestHandler___redArg(v_method_1340_, v_inst_1342_, v_inst_1343_, v_inst_1345_, v_handler_1346_, v_serialize_x3f_1347_);
return v___x_1349_;
}
}
LEAN_EXPORT void l_Lean_Server_registerLspRequestHandler_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_1340_ = stack[0].m_obj;
lean_object* v_inst_1342_ = stack[2].m_obj;
lean_object* v_inst_1343_ = stack[3].m_obj;
lean_object* v_inst_1345_ = stack[5].m_obj;
lean_object* v_handler_1346_ = stack[6].m_obj;
lean_object* v_serialize_x3f_1347_ = stack[7].m_obj;
lean_object* v_res_1350_;
v_res_1350_ = l_Lean_Server_registerLspRequestHandler(v_method_1340_, lean_box(0), v_inst_1342_, v_inst_1343_, lean_box(0), v_inst_1345_, v_handler_1346_, v_serialize_x3f_1347_);
stack->m_obj
 = v_res_1350_;
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___boxed(lean_object* v_method_1351_, lean_object* v_paramType_1352_, lean_object* v_inst_1353_, lean_object* v_inst_1354_, lean_object* v_respType_1355_, lean_object* v_inst_1356_, lean_object* v_handler_1357_, lean_object* v_serialize_x3f_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_Server_registerLspRequestHandler(v_method_1351_, v_paramType_1352_, v_inst_1353_, v_inst_1354_, v_respType_1355_, v_inst_1356_, v_handler_1357_, v_serialize_x3f_1358_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1361_, lean_object* v_vals_1362_, lean_object* v_i_1363_, lean_object* v_k_1364_){
_start:
{
lean_object* v___x_1365_; uint8_t v___x_1366_; 
v___x_1365_ = lean_array_get_size(v_keys_1361_);
v___x_1366_ = lean_nat_dec_lt(v_i_1363_, v___x_1365_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; 
lean_dec(v_i_1363_);
v___x_1367_ = lean_box(0);
return v___x_1367_;
}
else
{
lean_object* v_k_x27_1368_; uint8_t v___x_1369_; 
v_k_x27_1368_ = lean_array_fget_borrowed(v_keys_1361_, v_i_1363_);
v___x_1369_ = lean_string_dec_eq(v_k_1364_, v_k_x27_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = lean_unsigned_to_nat(1u);
v___x_1371_ = lean_nat_add(v_i_1363_, v___x_1370_);
lean_dec(v_i_1363_);
v_i_1363_ = v___x_1371_;
goto _start;
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = lean_array_fget_borrowed(v_vals_1362_, v_i_1363_);
lean_dec(v_i_1363_);
lean_inc(v___x_1373_);
v___x_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
return v___x_1374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1375_, lean_object* v_vals_1376_, lean_object* v_i_1377_, lean_object* v_k_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(v_keys_1375_, v_vals_1376_, v_i_1377_, v_k_1378_);
lean_dec_ref(v_k_1378_);
lean_dec_ref(v_vals_1376_);
lean_dec_ref(v_keys_1375_);
return v_res_1379_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(lean_object* v_x_1380_, size_t v_x_1381_, lean_object* v_x_1382_){
_start:
{
if (lean_obj_tag(v_x_1380_) == 0)
{
lean_object* v_es_1383_; lean_object* v___x_1384_; size_t v___x_1385_; size_t v___x_1386_; lean_object* v_j_1387_; lean_object* v___x_1388_; 
v_es_1383_ = lean_ctor_get(v_x_1380_, 0);
v___x_1384_ = lean_box(2);
v___x_1385_ = ((size_t)31ULL);
v___x_1386_ = lean_usize_land(v_x_1381_, v___x_1385_);
v_j_1387_ = lean_usize_to_nat(v___x_1386_);
v___x_1388_ = lean_array_get_borrowed(v___x_1384_, v_es_1383_, v_j_1387_);
lean_dec(v_j_1387_);
switch(lean_obj_tag(v___x_1388_))
{
case 0:
{
lean_object* v_key_1389_; lean_object* v_val_1390_; uint8_t v___x_1391_; 
v_key_1389_ = lean_ctor_get(v___x_1388_, 0);
v_val_1390_ = lean_ctor_get(v___x_1388_, 1);
v___x_1391_ = lean_string_dec_eq(v_x_1382_, v_key_1389_);
if (v___x_1391_ == 0)
{
lean_object* v___x_1392_; 
v___x_1392_ = lean_box(0);
return v___x_1392_;
}
else
{
lean_object* v___x_1393_; 
lean_inc(v_val_1390_);
v___x_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1393_, 0, v_val_1390_);
return v___x_1393_;
}
}
case 1:
{
lean_object* v_node_1394_; size_t v___x_1395_; size_t v___x_1396_; 
v_node_1394_ = lean_ctor_get(v___x_1388_, 0);
v___x_1395_ = ((size_t)5ULL);
v___x_1396_ = lean_usize_shift_right(v_x_1381_, v___x_1395_);
v_x_1380_ = v_node_1394_;
v_x_1381_ = v___x_1396_;
goto _start;
}
default: 
{
lean_object* v___x_1398_; 
v___x_1398_ = lean_box(0);
return v___x_1398_;
}
}
}
else
{
lean_object* v_ks_1399_; lean_object* v_vs_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v_ks_1399_ = lean_ctor_get(v_x_1380_, 0);
v_vs_1400_ = lean_ctor_get(v_x_1380_, 1);
v___x_1401_ = lean_unsigned_to_nat(0u);
v___x_1402_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(v_ks_1399_, v_vs_1400_, v___x_1401_, v_x_1382_);
return v___x_1402_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1380_ = stack[0].m_obj;
size_t v_x_1381_ = stack[1].m_num;
lean_object* v_x_1382_ = stack[2].m_obj;
lean_object* v_res_1403_;
v_res_1403_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_1380_, v_x_1381_, v_x_1382_);
stack->m_obj
 = v_res_1403_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___boxed(lean_object* v_x_1404_, lean_object* v_x_1405_, lean_object* v_x_1406_){
_start:
{
size_t v_x_286__boxed_1407_; lean_object* v_res_1408_; 
v_x_286__boxed_1407_ = lean_unbox_usize(v_x_1405_);
lean_dec(v_x_1405_);
v_res_1408_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_1404_, v_x_286__boxed_1407_, v_x_1406_);
lean_dec_ref(v_x_1406_);
lean_dec_ref(v_x_1404_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(lean_object* v_x_1409_, lean_object* v_x_1410_){
_start:
{
uint64_t v___x_1411_; size_t v___x_1412_; lean_object* v___x_1413_; 
v___x_1411_ = lean_string_hash(v_x_1410_);
v___x_1412_ = lean_uint64_to_usize(v___x_1411_);
v___x_1413_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_1409_, v___x_1412_, v_x_1410_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg___boxed(lean_object* v_x_1414_, lean_object* v_x_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v_x_1414_, v_x_1415_);
lean_dec_ref(v_x_1415_);
lean_dec_ref(v_x_1414_);
return v_res_1416_;
}
}
lean_object* l_Lean_Server_lookupLspRequestHandler(lean_object* v_method_1417_){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1419_ = l_Lean_Server_requestHandlers;
v___x_1420_ = lean_st_ref_get(v___x_1419_);
v___x_1421_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v___x_1420_, v_method_1417_);
lean_dec(v___x_1420_);
v___x_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT void l_Lean_Server_lookupLspRequestHandler_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_1417_ = stack[0].m_obj;
lean_object* v_res_1423_;
v_res_1423_ = l_Lean_Server_lookupLspRequestHandler(v_method_1417_);
stack->m_obj
 = v_res_1423_;
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupLspRequestHandler___boxed(lean_object* v_method_1424_, lean_object* v_a_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_Server_lookupLspRequestHandler(v_method_1424_);
lean_dec_ref(v_method_1424_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0(lean_object* v_00_u03b2_1427_, lean_object* v_x_1428_, lean_object* v_x_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v_x_1428_, v_x_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___boxed(lean_object* v_00_u03b2_1431_, lean_object* v_x_1432_, lean_object* v_x_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0(v_00_u03b2_1431_, v_x_1432_, v_x_1433_);
lean_dec_ref(v_x_1433_);
lean_dec_ref(v_x_1432_);
return v_res_1434_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0(lean_object* v_00_u03b2_1435_, lean_object* v_x_1436_, size_t v_x_1437_, lean_object* v_x_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_1436_, v_x_1437_, v_x_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1436_ = stack[1].m_obj;
size_t v_x_1437_ = stack[2].m_num;
lean_object* v_x_1438_ = stack[3].m_obj;
lean_object* v_res_1440_;
v_res_1440_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0(lean_box(0), v_x_1436_, v_x_1437_, v_x_1438_);
stack->m_obj
 = v_res_1440_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1441_, lean_object* v_x_1442_, lean_object* v_x_1443_, lean_object* v_x_1444_){
_start:
{
size_t v_x_407__boxed_1445_; lean_object* v_res_1446_; 
v_x_407__boxed_1445_ = lean_unbox_usize(v_x_1443_);
lean_dec(v_x_1443_);
v_res_1446_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0(v_00_u03b2_1441_, v_x_1442_, v_x_407__boxed_1445_, v_x_1444_);
lean_dec_ref(v_x_1444_);
lean_dec_ref(v_x_1442_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1447_, lean_object* v_keys_1448_, lean_object* v_vals_1449_, lean_object* v_heq_1450_, lean_object* v_i_1451_, lean_object* v_k_1452_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(v_keys_1448_, v_vals_1449_, v_i_1451_, v_k_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1454_, lean_object* v_keys_1455_, lean_object* v_vals_1456_, lean_object* v_heq_1457_, lean_object* v_i_1458_, lean_object* v_k_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1(v_00_u03b2_1454_, v_keys_1455_, v_vals_1456_, v_heq_1457_, v_i_1458_, v_k_1459_);
lean_dec_ref(v_k_1459_);
lean_dec_ref(v_vals_1456_);
lean_dec_ref(v_keys_1455_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__0(lean_object* v_inst_1464_, lean_object* v_method_1465_, lean_object* v_x_1466_){
_start:
{
lean_object* v_response_1468_; 
if (lean_obj_tag(v_x_1466_) == 0)
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec_ref(v_inst_1464_);
v_a_1492_ = lean_ctor_get(v_x_1466_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_x_1466_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v_x_1466_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v_x_1466_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v_response_x3f_1501_; 
v_a_1500_ = lean_ctor_get(v_x_1466_, 0);
lean_inc(v_a_1500_);
lean_dec_ref_known(v_x_1466_, 1);
v_response_x3f_1501_ = lean_ctor_get(v_a_1500_, 0);
if (lean_obj_tag(v_response_x3f_1501_) == 0)
{
lean_object* v_serialized_1502_; lean_object* v___x_1503_; 
v_serialized_1502_ = lean_ctor_get(v_a_1500_, 1);
lean_inc_ref(v_serialized_1502_);
lean_dec(v_a_1500_);
v___x_1503_ = l_Lean_Json_parse(v_serialized_1502_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1517_; 
lean_dec_ref(v_inst_1464_);
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1506_ = v___x_1503_;
v_isShared_1507_ = v_isSharedCheck_1517_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1503_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1517_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; 
v___x_1508_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__2));
v___x_1509_ = lean_string_append(v___x_1508_, v_method_1465_);
v___x_1510_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1));
v___x_1511_ = lean_string_append(v___x_1509_, v___x_1510_);
v___x_1512_ = lean_string_append(v___x_1511_, v_a_1504_);
lean_dec(v_a_1504_);
v___x_1513_ = l_Lean_Server_RequestError_internalError(v___x_1512_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 0, v___x_1513_);
v___x_1515_ = v___x_1506_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
else
{
lean_object* v_a_1518_; 
v_a_1518_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v___x_1503_, 1);
v_response_1468_ = v_a_1518_;
goto v___jp_1467_;
}
}
else
{
lean_object* v_val_1519_; 
lean_inc_ref(v_response_x3f_1501_);
lean_dec(v_a_1500_);
v_val_1519_ = lean_ctor_get(v_response_x3f_1501_, 0);
lean_inc(v_val_1519_);
lean_dec_ref_known(v_response_x3f_1501_, 1);
v_response_1468_ = v_val_1519_;
goto v___jp_1467_;
}
}
v___jp_1467_:
{
lean_object* v___x_1469_; 
v___x_1469_ = lean_apply_1(v_inst_1464_, v_response_1468_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1483_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1472_ = v___x_1469_;
v_isShared_1473_ = v_isSharedCheck_1483_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1469_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1483_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1481_; 
v___x_1474_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__0));
v___x_1475_ = lean_string_append(v___x_1474_, v_method_1465_);
v___x_1476_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1));
v___x_1477_ = lean_string_append(v___x_1475_, v___x_1476_);
v___x_1478_ = lean_string_append(v___x_1477_, v_a_1470_);
lean_dec(v_a_1470_);
v___x_1479_ = l_Lean_Server_RequestError_internalError(v___x_1478_);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 0, v___x_1479_);
v___x_1481_ = v___x_1472_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1479_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
v_a_1484_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1469_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1469_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__0___boxed(lean_object* v_inst_1520_, lean_object* v_method_1521_, lean_object* v_x_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__0(v_inst_1520_, v_method_1521_, v_x_1522_);
lean_dec_ref(v_method_1521_);
return v_res_1523_;
}
}
lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__1(lean_object* v_inst_1524_, uint8_t v_val_1525_, lean_object* v_r_1526_){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1527_ = lean_apply_1(v_inst_1524_, v_r_1526_);
lean_inc(v___x_1527_);
v___x_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
v___x_1529_ = l_Lean_Json_compress(v___x_1527_);
v___x_1530_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1530_, 0, v___x_1528_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
lean_ctor_set_uint8(v___x_1530_, sizeof(void*)*2, v_val_1525_);
return v___x_1530_;
}
}
LEAN_EXPORT void l_Lean_Server_chainLspRequestHandler___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1524_ = stack[0].m_obj;
uint8_t v_val_1525_ = stack[1].m_num;
lean_object* v_r_1526_ = stack[2].m_obj;
lean_object* v_res_1531_;
v_res_1531_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__1(v_inst_1524_, v_val_1525_, v_r_1526_);
stack->m_obj
 = v_res_1531_;
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__1___boxed(lean_object* v_inst_1532_, lean_object* v_val_1533_, lean_object* v_r_1534_){
_start:
{
uint8_t v_val_2337__boxed_1535_; lean_object* v_res_1536_; 
v_val_2337__boxed_1535_ = lean_unbox(v_val_1533_);
v_res_1536_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__1(v_inst_1532_, v_val_2337__boxed_1535_, v_r_1534_);
return v_res_1536_;
}
}
lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__2(lean_object* v_val_1537_, lean_object* v___f_1538_, lean_object* v_inst_1539_, lean_object* v_handler_1540_, lean_object* v___f_1541_, lean_object* v_j_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v_handle_1545_; lean_object* v___x_1546_; 
v_handle_1545_ = lean_ctor_get(v_val_1537_, 1);
lean_inc_ref(v_handle_1545_);
lean_dec_ref(v_val_1537_);
lean_inc_ref(v___y_1543_);
lean_inc(v_j_1542_);
v___x_1546_ = lean_apply_3(v_handle_1545_, v_j_1542_, v___y_1543_, lean_box(0));
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref_known(v___x_1546_, 1);
v___x_1548_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_1538_, v_a_1547_);
v___x_1549_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_1539_, v_j_1542_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1551_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1549_, 1);
lean_inc_ref(v___y_1543_);
v___x_1551_ = lean_apply_4(v_handler_1540_, v_a_1550_, v___x_1548_, v___y_1543_, lean_box(0));
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1561_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1554_ = v___x_1551_;
v_isShared_1555_ = v_isSharedCheck_1561_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1551_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1561_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1556_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_1556_, 0, lean_box(0));
lean_closure_set(v___x_1556_, 1, lean_box(0));
lean_closure_set(v___x_1556_, 2, lean_box(0));
lean_closure_set(v___x_1556_, 3, v___f_1541_);
v___x_1557_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___x_1556_, v_a_1552_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 0, v___x_1557_);
v___x_1559_ = v___x_1554_;
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
else
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1569_; 
lean_dec_ref(v___f_1541_);
v_a_1562_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1564_ = v___x_1551_;
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1551_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1565_ == 0)
{
v___x_1567_ = v___x_1564_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_a_1562_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_dec_ref(v___x_1548_);
lean_dec_ref(v___f_1541_);
lean_dec_ref(v_handler_1540_);
v_a_1570_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1549_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1549_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
else
{
lean_dec(v_j_1542_);
lean_dec_ref(v___f_1541_);
lean_dec_ref(v_handler_1540_);
lean_dec_ref(v_inst_1539_);
lean_dec_ref(v___f_1538_);
return v___x_1546_;
}
}
}
LEAN_EXPORT void l_Lean_Server_chainLspRequestHandler___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1537_ = stack[0].m_obj;
lean_object* v___f_1538_ = stack[1].m_obj;
lean_object* v_inst_1539_ = stack[2].m_obj;
lean_object* v_handler_1540_ = stack[3].m_obj;
lean_object* v___f_1541_ = stack[4].m_obj;
lean_object* v_j_1542_ = stack[5].m_obj;
lean_object* v___y_1543_ = stack[6].m_obj;
lean_object* v_res_1578_;
v_res_1578_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__2(v_val_1537_, v___f_1538_, v_inst_1539_, v_handler_1540_, v___f_1541_, v_j_1542_, v___y_1543_);
stack->m_obj
 = v_res_1578_;
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__2___boxed(lean_object* v_val_1579_, lean_object* v___f_1580_, lean_object* v_inst_1581_, lean_object* v_handler_1582_, lean_object* v___f_1583_, lean_object* v_j_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__2(v_val_1579_, v___f_1580_, v_inst_1581_, v_handler_1582_, v___f_1583_, v_j_1584_, v___y_1585_);
lean_dec_ref(v___y_1585_);
return v_res_1587_;
}
}
lean_object* l_Lean_Server_chainLspRequestHandler___redArg(lean_object* v_method_1590_, lean_object* v_inst_1591_, lean_object* v_inst_1592_, lean_object* v_inst_1593_, lean_object* v_handler_1594_){
_start:
{
lean_object* v___f_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; 
lean_inc_ref(v_method_1590_);
v___f_1596_ = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1596_, 0, v_inst_1592_);
lean_closure_set(v___f_1596_, 1, v_method_1590_);
v___x_1597_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__0));
v___x_1598_ = l_Lean_initializing();
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
lean_dec_ref(v___f_1596_);
lean_dec_ref(v_handler_1594_);
lean_dec_ref(v_inst_1593_);
lean_dec_ref(v_inst_1591_);
v___x_1599_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__0));
v___x_1600_ = lean_string_append(v___x_1599_, v_method_1590_);
lean_dec_ref(v_method_1590_);
v___x_1601_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___x_1602_ = lean_string_append(v___x_1600_, v___x_1601_);
v___x_1603_ = lean_mk_io_user_error(v___x_1602_);
v___x_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
return v___x_1604_;
}
else
{
lean_object* v___x_1605_; lean_object* v___f_1606_; lean_object* v___x_1607_; lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1639_; 
v___x_1605_ = lean_box(v___x_1598_);
v___f_1606_ = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_1606_, 0, v_inst_1593_);
lean_closure_set(v___f_1606_, 1, v___x_1605_);
v___x_1607_ = l_Lean_Server_lookupLspRequestHandler(v_method_1590_);
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1610_ = v___x_1607_;
v_isShared_1611_ = v_isSharedCheck_1639_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1607_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1639_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
if (lean_obj_tag(v_a_1608_) == 1)
{
lean_object* v_val_1612_; lean_object* v___f_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v_fileSource_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1629_; 
v_val_1612_ = lean_ctor_get(v_a_1608_, 0);
lean_inc_n(v_val_1612_, 2);
lean_dec_ref_known(v_a_1608_, 1);
v___f_1613_ = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_1613_, 0, v_val_1612_);
lean_closure_set(v___f_1613_, 1, v___f_1596_);
lean_closure_set(v___f_1613_, 2, v_inst_1591_);
lean_closure_set(v___f_1613_, 3, v_handler_1594_);
lean_closure_set(v___f_1613_, 4, v___f_1606_);
v___x_1614_ = l_Lean_Server_requestHandlers;
v___x_1615_ = lean_st_ref_take(v___x_1614_);
v_fileSource_1616_ = lean_ctor_get(v_val_1612_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v_val_1612_);
if (v_isSharedCheck_1629_ == 0)
{
lean_object* v_unused_1630_; 
v_unused_1630_ = lean_ctor_get(v_val_1612_, 1);
lean_dec(v_unused_1630_);
v___x_1618_ = v_val_1612_;
v_isShared_1619_ = v_isSharedCheck_1629_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_fileSource_1616_);
lean_dec(v_val_1612_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1629_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___f_1620_; lean_object* v___x_1622_; 
v___f_1620_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 1, v___f_1613_);
v___x_1622_ = v___x_1618_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_fileSource_1616_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v___f_1613_);
v___x_1622_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1626_; 
v___x_1623_ = l_Lean_PersistentHashMap_insert___redArg(v___f_1620_, v___x_1597_, v___x_1615_, v_method_1590_, v___x_1622_);
v___x_1624_ = lean_st_ref_put(v___x_1614_, v___x_1623_);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v___x_1624_);
v___x_1626_ = v___x_1610_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1624_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
else
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1637_; 
lean_dec(v_a_1608_);
lean_dec_ref(v___f_1606_);
lean_dec_ref(v___f_1596_);
lean_dec_ref(v_handler_1594_);
lean_dec_ref(v_inst_1591_);
v___x_1631_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__0));
v___x_1632_ = lean_string_append(v___x_1631_, v_method_1590_);
lean_dec_ref(v_method_1590_);
v___x_1633_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__1));
v___x_1634_ = lean_string_append(v___x_1632_, v___x_1633_);
v___x_1635_ = lean_mk_io_user_error(v___x_1634_);
if (v_isShared_1611_ == 0)
{
lean_ctor_set_tag(v___x_1610_, 1);
lean_ctor_set(v___x_1610_, 0, v___x_1635_);
v___x_1637_ = v___x_1610_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1635_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_chainLspRequestHandler___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_1590_ = stack[0].m_obj;
lean_object* v_inst_1591_ = stack[1].m_obj;
lean_object* v_inst_1592_ = stack[2].m_obj;
lean_object* v_inst_1593_ = stack[3].m_obj;
lean_object* v_handler_1594_ = stack[4].m_obj;
lean_object* v_res_1640_;
v_res_1640_ = l_Lean_Server_chainLspRequestHandler___redArg(v_method_1590_, v_inst_1591_, v_inst_1592_, v_inst_1593_, v_handler_1594_);
stack->m_obj
 = v_res_1640_;
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___boxed(lean_object* v_method_1641_, lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v_inst_1644_, lean_object* v_handler_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_Server_chainLspRequestHandler___redArg(v_method_1641_, v_inst_1642_, v_inst_1643_, v_inst_1644_, v_handler_1645_);
return v_res_1647_;
}
}
lean_object* l_Lean_Server_chainLspRequestHandler(lean_object* v_method_1648_, lean_object* v_paramType_1649_, lean_object* v_inst_1650_, lean_object* v_respType_1651_, lean_object* v_inst_1652_, lean_object* v_inst_1653_, lean_object* v_handler_1654_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_Server_chainLspRequestHandler___redArg(v_method_1648_, v_inst_1650_, v_inst_1652_, v_inst_1653_, v_handler_1654_);
return v___x_1656_;
}
}
LEAN_EXPORT void l_Lean_Server_chainLspRequestHandler_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_1648_ = stack[0].m_obj;
lean_object* v_inst_1650_ = stack[2].m_obj;
lean_object* v_inst_1652_ = stack[4].m_obj;
lean_object* v_inst_1653_ = stack[5].m_obj;
lean_object* v_handler_1654_ = stack[6].m_obj;
lean_object* v_res_1657_;
v_res_1657_ = l_Lean_Server_chainLspRequestHandler(v_method_1648_, lean_box(0), v_inst_1650_, lean_box(0), v_inst_1652_, v_inst_1653_, v_handler_1654_);
stack->m_obj
 = v_res_1657_;
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___boxed(lean_object* v_method_1658_, lean_object* v_paramType_1659_, lean_object* v_inst_1660_, lean_object* v_respType_1661_, lean_object* v_inst_1662_, lean_object* v_inst_1663_, lean_object* v_handler_1664_, lean_object* v_a_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_Server_chainLspRequestHandler(v_method_1658_, v_paramType_1659_, v_inst_1660_, v_respType_1661_, v_inst_1662_, v_inst_1663_, v_handler_1664_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorIdx___impl(lean_object* v_x_1667_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = lean_obj_tag_nat(v_x_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorIdx___impl___boxed(lean_object* v_x_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Lean_Server_RequestHandlerCompleteness_ctorIdx___impl(v_x_1669_);
lean_dec(v_x_1669_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(lean_object* v_t_1671_, lean_object* v_k_1672_){
_start:
{
if (lean_obj_tag(v_t_1671_) == 0)
{
return v_k_1672_;
}
else
{
lean_object* v_refreshMethod_1673_; lean_object* v_refreshIntervalMs_1674_; lean_object* v___x_1675_; 
v_refreshMethod_1673_ = lean_ctor_get(v_t_1671_, 0);
lean_inc_ref(v_refreshMethod_1673_);
v_refreshIntervalMs_1674_ = lean_ctor_get(v_t_1671_, 1);
lean_inc(v_refreshIntervalMs_1674_);
lean_dec_ref_known(v_t_1671_, 2);
v___x_1675_ = lean_apply_2(v_k_1672_, v_refreshMethod_1673_, v_refreshIntervalMs_1674_);
return v___x_1675_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim(lean_object* v_motive_1676_, lean_object* v_ctorIdx_1677_, lean_object* v_t_1678_, lean_object* v_h_1679_, lean_object* v_k_1680_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_1678_, v_k_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim___boxed(lean_object* v_motive_1682_, lean_object* v_ctorIdx_1683_, lean_object* v_t_1684_, lean_object* v_h_1685_, lean_object* v_k_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim(v_motive_1682_, v_ctorIdx_1683_, v_t_1684_, v_h_1685_, v_k_1686_);
lean_dec(v_ctorIdx_1683_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_complete_elim___redArg(lean_object* v_t_1688_, lean_object* v_complete_1689_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_1688_, v_complete_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_complete_elim(lean_object* v_motive_1691_, lean_object* v_t_1692_, lean_object* v_h_1693_, lean_object* v_complete_1694_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_1692_, v_complete_1694_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_partial_elim___redArg(lean_object* v_t_1696_, lean_object* v_partial_1697_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_1696_, v_partial_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_partial_elim(lean_object* v_motive_1699_, lean_object* v_t_1700_, lean_object* v_h_1701_, lean_object* v_partial_1702_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_1700_, v_partial_1702_);
return v___x_1703_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_);
v___x_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1704_);
return v___x_1705_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1707_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_);
v___x_1708_ = lean_st_mk_ref(v___x_1707_);
v___x_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1710_;
v_res_1710_ = l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1710_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2____boxed(lean_object* v_a_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_();
return v_res_1712_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(lean_object* v_method_1714_, lean_object* v_state_1715_, lean_object* v_inst_1716_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_state_1715_, v_inst_1716_);
if (lean_obj_tag(v___x_1718_) == 1)
{
lean_object* v_val_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
v_val_1719_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1718_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_val_1719_);
lean_dec(v___x_1718_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
lean_ctor_set_tag(v___x_1721_, 0);
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_val_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
else
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_dec(v___x_1718_);
v___x_1727_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0));
v___x_1728_ = lean_string_append(v___x_1727_, v_method_1714_);
v___x_1729_ = l_Lean_Server_RequestError_internalError(v___x_1728_);
v___x_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
return v___x_1730_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_1714_ = stack[0].m_obj;
lean_object* v_state_1715_ = stack[1].m_obj;
lean_object* v_inst_1716_ = stack[2].m_obj;
lean_object* v_res_1731_;
v_res_1731_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_1714_, v_state_1715_, v_inst_1716_);
stack->m_obj
 = v_res_1731_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___boxed(lean_object* v_method_1732_, lean_object* v_state_1733_, lean_object* v_inst_1734_, lean_object* v_a_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_1732_, v_state_1733_, v_inst_1734_);
lean_dec(v_inst_1734_);
lean_dec(v_state_1733_);
lean_dec_ref(v_method_1732_);
return v_res_1736_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(lean_object* v_method_1737_, lean_object* v_state_1738_, lean_object* v_stateType_1739_, lean_object* v_inst_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_1737_, v_state_1738_, v_inst_1740_);
return v___x_1743_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_getState_x21_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_1737_ = stack[0].m_obj;
lean_object* v_state_1738_ = stack[1].m_obj;
lean_object* v_inst_1740_ = stack[3].m_obj;
lean_object* v_a_1741_ = stack[4].m_obj;
lean_object* v_res_1744_;
v_res_1744_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_1737_, v_state_1738_, lean_box(0), v_inst_1740_, v_a_1741_);
stack->m_obj
 = v_res_1744_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___boxed(lean_object* v_method_1745_, lean_object* v_state_1746_, lean_object* v_stateType_1747_, lean_object* v_inst_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_1745_, v_state_1746_, v_stateType_1747_, v_inst_1748_, v_a_1749_);
lean_dec_ref(v_a_1749_);
lean_dec(v_inst_1748_);
lean_dec(v_state_1746_);
lean_dec_ref(v_method_1745_);
return v_res_1751_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(lean_object* v_method_1752_, lean_object* v_state_1753_, lean_object* v_inst_1754_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_state_1753_, v_inst_1754_);
if (lean_obj_tag(v___x_1756_) == 1)
{
lean_object* v_val_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
v_val_1757_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1756_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_val_1757_);
lean_dec(v___x_1756_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
lean_ctor_set_tag(v___x_1759_, 0);
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_val_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
else
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
lean_dec(v___x_1756_);
v___x_1765_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0));
v___x_1766_ = lean_string_append(v___x_1765_, v_method_1752_);
v___x_1767_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
v___x_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
return v___x_1768_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_1752_ = stack[0].m_obj;
lean_object* v_state_1753_ = stack[1].m_obj;
lean_object* v_inst_1754_ = stack[2].m_obj;
lean_object* v_res_1769_;
v_res_1769_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(v_method_1752_, v_state_1753_, v_inst_1754_);
stack->m_obj
 = v_res_1769_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg___boxed(lean_object* v_method_1770_, lean_object* v_state_1771_, lean_object* v_inst_1772_, lean_object* v_a_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(v_method_1770_, v_state_1771_, v_inst_1772_);
lean_dec(v_inst_1772_);
lean_dec(v_state_1771_);
lean_dec_ref(v_method_1770_);
return v_res_1774_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21(lean_object* v_method_1775_, lean_object* v_state_1776_, lean_object* v_stateType_1777_, lean_object* v_inst_1778_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(v_method_1775_, v_state_1776_, v_inst_1778_);
return v___x_1780_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_1775_ = stack[0].m_obj;
lean_object* v_state_1776_ = stack[1].m_obj;
lean_object* v_inst_1778_ = stack[3].m_obj;
lean_object* v_res_1781_;
v_res_1781_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21(v_method_1775_, v_state_1776_, lean_box(0), v_inst_1778_);
stack->m_obj
 = v_res_1781_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___boxed(lean_object* v_method_1782_, lean_object* v_state_1783_, lean_object* v_stateType_1784_, lean_object* v_inst_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21(v_method_1782_, v_state_1783_, v_stateType_1784_, v_inst_1785_);
lean_dec(v_inst_1785_);
lean_dec(v_state_1783_);
lean_dec_ref(v_method_1782_);
return v_res_1787_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1(lean_object* v_inst_1788_, lean_object* v_method_1789_, lean_object* v_inst_1790_, lean_object* v_handler_1791_, lean_object* v_inst_1792_, lean_object* v_param_1793_, lean_object* v_state_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_1788_, v_param_1793_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1799_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_a_1798_);
lean_dec_ref_known(v___x_1797_, 1);
v___x_1799_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_1789_, v_state_1794_, v_inst_1790_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v___x_1801_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_a_1800_);
lean_dec_ref_known(v___x_1799_, 1);
lean_inc_ref(v___y_1795_);
v___x_1801_ = lean_apply_4(v_handler_1791_, v_a_1798_, v_a_1800_, v___y_1795_, lean_box(0));
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1825_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1804_ = v___x_1801_;
v_isShared_1805_ = v_isSharedCheck_1825_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1801_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1825_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v_fst_1806_; lean_object* v_snd_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1824_; 
v_fst_1806_ = lean_ctor_get(v_a_1802_, 0);
v_snd_1807_ = lean_ctor_get(v_a_1802_, 1);
v_isSharedCheck_1824_ = !lean_is_exclusive(v_a_1802_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1809_ = v_a_1802_;
v_isShared_1810_ = v_isSharedCheck_1824_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_snd_1807_);
lean_inc(v_fst_1806_);
lean_dec(v_a_1802_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1824_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v_response_1811_; uint8_t v_isComplete_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1818_; 
v_response_1811_ = lean_ctor_get(v_fst_1806_, 0);
lean_inc(v_response_1811_);
v_isComplete_1812_ = lean_ctor_get_uint8(v_fst_1806_, sizeof(void*)*1);
lean_dec(v_fst_1806_);
v___x_1813_ = lean_apply_1(v_inst_1792_, v_response_1811_);
lean_inc(v___x_1813_);
v___x_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
v___x_1815_ = l_Lean_Json_compress(v___x_1813_);
v___x_1816_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1816_, 0, v___x_1814_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
lean_ctor_set_uint8(v___x_1816_, sizeof(void*)*2, v_isComplete_1812_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v_inst_1790_);
v___x_1818_ = v___x_1809_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_inst_1790_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_snd_1807_);
v___x_1818_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1816_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1819_);
v___x_1821_ = v___x_1804_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
lean_dec_ref(v_inst_1792_);
lean_dec(v_inst_1790_);
v_a_1826_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1801_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1801_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
lean_dec(v_a_1798_);
lean_dec_ref(v_inst_1792_);
lean_dec_ref(v_handler_1791_);
lean_dec(v_inst_1790_);
v_a_1834_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1799_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1799_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
else
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
lean_dec_ref(v_inst_1792_);
lean_dec_ref(v_handler_1791_);
lean_dec(v_inst_1790_);
v_a_1842_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1797_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1797_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1788_ = stack[0].m_obj;
lean_object* v_method_1789_ = stack[1].m_obj;
lean_object* v_inst_1790_ = stack[2].m_obj;
lean_object* v_handler_1791_ = stack[3].m_obj;
lean_object* v_inst_1792_ = stack[4].m_obj;
lean_object* v_param_1793_ = stack[5].m_obj;
lean_object* v_state_1794_ = stack[6].m_obj;
lean_object* v___y_1795_ = stack[7].m_obj;
lean_object* v_res_1850_;
v_res_1850_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1(v_inst_1788_, v_method_1789_, v_inst_1790_, v_handler_1791_, v_inst_1792_, v_param_1793_, v_state_1794_, v___y_1795_);
stack->m_obj
 = v_res_1850_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1___boxed(lean_object* v_inst_1851_, lean_object* v_method_1852_, lean_object* v_inst_1853_, lean_object* v_handler_1854_, lean_object* v_inst_1855_, lean_object* v_param_1856_, lean_object* v_state_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1(v_inst_1851_, v_method_1852_, v_inst_1853_, v_handler_1854_, v_inst_1855_, v_param_1856_, v_state_1857_, v___y_1858_);
lean_dec_ref(v___y_1858_);
lean_dec(v_state_1857_);
lean_dec_ref(v_method_1852_);
return v_res_1860_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0(lean_object* v_method_1861_, lean_object* v_inst_1862_, lean_object* v_onDidChange_1863_, lean_object* v_param_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_1861_, v___y_1865_, v_inst_1862_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1870_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1869_);
lean_dec_ref_known(v___x_1868_, 1);
lean_inc_ref(v___y_1866_);
v___x_1870_ = lean_apply_4(v_onDidChange_1863_, v_param_1864_, v_a_1869_, v___y_1866_, lean_box(0));
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1889_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1873_ = v___x_1870_;
v_isShared_1874_ = v_isSharedCheck_1889_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1889_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v_snd_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1887_; 
v_snd_1875_ = lean_ctor_get(v_a_1871_, 1);
v_isSharedCheck_1887_ = !lean_is_exclusive(v_a_1871_);
if (v_isSharedCheck_1887_ == 0)
{
lean_object* v_unused_1888_; 
v_unused_1888_ = lean_ctor_get(v_a_1871_, 0);
lean_dec(v_unused_1888_);
v___x_1877_ = v_a_1871_;
v_isShared_1878_ = v_isSharedCheck_1887_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_snd_1875_);
lean_dec(v_a_1871_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1887_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v_inst_1862_);
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_inst_1862_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_snd_1875_);
v___x_1880_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1884_; 
v___x_1881_ = lean_box(0);
v___x_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
lean_ctor_set(v___x_1882_, 1, v___x_1880_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v___x_1882_);
v___x_1884_ = v___x_1873_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1882_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_dec(v_inst_1862_);
v_a_1890_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1870_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1870_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec_ref(v_param_1864_);
lean_dec_ref(v_onDidChange_1863_);
lean_dec(v_inst_1862_);
v_a_1898_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1868_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1868_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_1861_ = stack[0].m_obj;
lean_object* v_inst_1862_ = stack[1].m_obj;
lean_object* v_onDidChange_1863_ = stack[2].m_obj;
lean_object* v_param_1864_ = stack[3].m_obj;
lean_object* v___y_1865_ = stack[4].m_obj;
lean_object* v___y_1866_ = stack[5].m_obj;
lean_object* v_res_1906_;
v_res_1906_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0(v_method_1861_, v_inst_1862_, v_onDidChange_1863_, v_param_1864_, v___y_1865_, v___y_1866_);
stack->m_obj
 = v_res_1906_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object* v_method_1907_, lean_object* v_inst_1908_, lean_object* v_onDidChange_1909_, lean_object* v_param_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0(v_method_1907_, v_inst_1908_, v_onDidChange_1909_, v_param_1910_, v___y_1911_, v___y_1912_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v_method_1907_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2(lean_object* v___x_1915_, lean_object* v_x_1916_){
_start:
{
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2___boxed(lean_object* v___x_1917_, lean_object* v_x_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2(v___x_1917_, v_x_1918_);
lean_dec_ref(v_x_1918_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3(lean_object* v___x_1920_, lean_object* v_x_1921_){
_start:
{
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3___boxed(lean_object* v___x_1922_, lean_object* v_x_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3(v___x_1922_, v_x_1923_);
lean_dec_ref(v_x_1923_);
return v_res_1924_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4(lean_object* v_val_1925_, lean_object* v___f_1926_, lean_object* v_param_1927_, lean_object* v_x_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1931_ = lean_st_ref_get(v_val_1925_);
lean_inc_ref(v___y_1929_);
v___x_1932_ = lean_apply_4(v___f_1926_, v_param_1927_, v___x_1931_, v___y_1929_, lean_box(0));
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1943_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1935_ = v___x_1932_;
v_isShared_1936_ = v_isSharedCheck_1943_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1932_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1943_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v_fst_1937_; lean_object* v_snd_1938_; lean_object* v___x_1939_; lean_object* v___x_1941_; 
v_fst_1937_ = lean_ctor_get(v_a_1933_, 0);
lean_inc(v_fst_1937_);
v_snd_1938_ = lean_ctor_get(v_a_1933_, 1);
lean_inc(v_snd_1938_);
lean_dec(v_a_1933_);
v___x_1939_ = lean_st_ref_swap(v_val_1925_, v_snd_1938_);
lean_dec(v___x_1939_);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 0, v_fst_1937_);
v___x_1941_ = v___x_1935_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_fst_1937_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
v_a_1944_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1932_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1932_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1925_ = stack[0].m_obj;
lean_object* v___f_1926_ = stack[1].m_obj;
lean_object* v_param_1927_ = stack[2].m_obj;
lean_object* v_x_1928_ = stack[3].m_obj;
lean_object* v___y_1929_ = stack[4].m_obj;
lean_object* v_res_1952_;
v_res_1952_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4(v_val_1925_, v___f_1926_, v_param_1927_, v_x_1928_, v___y_1929_);
stack->m_obj
 = v_res_1952_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4___boxed(lean_object* v_val_1953_, lean_object* v___f_1954_, lean_object* v_param_1955_, lean_object* v_x_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4(v_val_1953_, v___f_1954_, v_param_1955_, v_x_1956_, v___y_1957_);
lean_dec_ref(v___y_1957_);
lean_dec(v_val_1953_);
return v_res_1959_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5(lean_object* v___f_1960_, lean_object* v___f_1961_, lean_object* v_lastTask_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v___x_1966_; lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1976_; 
v___x_1966_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_lastTask_1962_, v___f_1960_, v___y_1964_);
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1969_ = v___x_1966_;
v_isShared_1970_ = v_isSharedCheck_1976_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1966_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1976_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1974_; 
lean_inc(v_a_1967_);
v___x_1971_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_1961_, v_a_1967_);
v___x_1972_ = lean_st_ref_swap(v___y_1963_, v___x_1971_);
lean_dec(v___x_1972_);
if (v_isShared_1970_ == 0)
{
v___x_1974_ = v___x_1969_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1967_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1960_ = stack[0].m_obj;
lean_object* v___f_1961_ = stack[1].m_obj;
lean_object* v_lastTask_1962_ = stack[2].m_obj;
lean_object* v___y_1963_ = stack[3].m_obj;
lean_object* v___y_1964_ = stack[4].m_obj;
lean_object* v_res_1977_;
v_res_1977_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5(v___f_1960_, v___f_1961_, v_lastTask_1962_, v___y_1963_, v___y_1964_);
stack->m_obj
 = v_res_1977_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5___boxed(lean_object* v___f_1978_, lean_object* v___f_1979_, lean_object* v_lastTask_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5(v___f_1978_, v___f_1979_, v_lastTask_1980_, v___y_1981_, v___y_1982_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
return v_res_1984_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6(lean_object* v_val_1985_, lean_object* v___f_1986_, lean_object* v___f_1987_, lean_object* v___f_1988_, lean_object* v___x_1989_, lean_object* v___f_1990_, lean_object* v___f_1991_, lean_object* v_val_1992_, lean_object* v_param_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v___f_1996_; lean_object* v___f_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_6224__overap_2000_; lean_object* v___x_2001_; 
v___f_1996_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_1996_, 0, v_val_1985_);
lean_closure_set(v___f_1996_, 1, v___f_1986_);
lean_closure_set(v___f_1996_, 2, v_param_1993_);
v___f_1997_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5___boxed), 6, 2);
lean_closure_set(v___f_1997_, 0, v___f_1996_);
lean_closure_set(v___f_1997_, 1, v___f_1987_);
v___x_1998_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_1998_, 0, lean_box(0));
lean_closure_set(v___x_1998_, 1, lean_box(0));
lean_closure_set(v___x_1998_, 2, lean_box(0));
lean_closure_set(v___x_1998_, 3, v___f_1988_);
lean_inc_ref(v___x_1989_);
v___x_1999_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_1999_, 0, lean_box(0));
lean_closure_set(v___x_1999_, 1, lean_box(0));
lean_closure_set(v___x_1999_, 2, v___x_1989_);
lean_closure_set(v___x_1999_, 3, lean_box(0));
lean_closure_set(v___x_1999_, 4, lean_box(0));
lean_closure_set(v___x_1999_, 5, v___x_1998_);
lean_closure_set(v___x_1999_, 6, v___f_1997_);
v___x_6224__overap_2000_ = l_Std_Mutex_atomically___redArg(v___x_1989_, v___f_1990_, v___f_1991_, v_val_1992_, v___x_1999_);
lean_inc_ref(v___y_1994_);
v___x_2001_ = lean_apply_2(v___x_6224__overap_2000_, v___y_1994_, lean_box(0));
return v___x_2001_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1985_ = stack[0].m_obj;
lean_object* v___f_1986_ = stack[1].m_obj;
lean_object* v___f_1987_ = stack[2].m_obj;
lean_object* v___f_1988_ = stack[3].m_obj;
lean_object* v___x_1989_ = stack[4].m_obj;
lean_object* v___f_1990_ = stack[5].m_obj;
lean_object* v___f_1991_ = stack[6].m_obj;
lean_object* v_val_1992_ = stack[7].m_obj;
lean_object* v_param_1993_ = stack[8].m_obj;
lean_object* v___y_1994_ = stack[9].m_obj;
lean_object* v_res_2002_;
v_res_2002_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6(v_val_1985_, v___f_1986_, v___f_1987_, v___f_1988_, v___x_1989_, v___f_1990_, v___f_1991_, v_val_1992_, v_param_1993_, v___y_1994_);
stack->m_obj
 = v_res_2002_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6___boxed(lean_object* v_val_2003_, lean_object* v___f_2004_, lean_object* v___f_2005_, lean_object* v___f_2006_, lean_object* v___x_2007_, lean_object* v___f_2008_, lean_object* v___f_2009_, lean_object* v_val_2010_, lean_object* v_param_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6(v_val_2003_, v___f_2004_, v___f_2005_, v___f_2006_, v___x_2007_, v___f_2008_, v___f_2009_, v_val_2010_, v_param_2011_, v___y_2012_);
lean_dec_ref(v___y_2012_);
return v_res_2014_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7(lean_object* v_val_2015_, lean_object* v___f_2016_, lean_object* v_param_2017_, lean_object* v___x_2018_, lean_object* v_x_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2022_ = lean_st_ref_get(v_val_2015_);
lean_inc_ref(v___y_2020_);
v___x_2023_ = lean_apply_4(v___f_2016_, v_param_2017_, v___x_2022_, v___y_2020_, lean_box(0));
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2033_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2026_ = v___x_2023_;
v_isShared_2027_ = v_isSharedCheck_2033_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2033_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v_snd_2028_; lean_object* v___x_2029_; lean_object* v___x_2031_; 
v_snd_2028_ = lean_ctor_get(v_a_2024_, 1);
lean_inc(v_snd_2028_);
lean_dec(v_a_2024_);
v___x_2029_ = lean_st_ref_swap(v_val_2015_, v_snd_2028_);
lean_dec(v___x_2029_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2018_);
v___x_2031_ = v___x_2026_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2018_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
v_a_2034_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_2023_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2023_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2015_ = stack[0].m_obj;
lean_object* v___f_2016_ = stack[1].m_obj;
lean_object* v_param_2017_ = stack[2].m_obj;
lean_object* v___x_2018_ = stack[3].m_obj;
lean_object* v_x_2019_ = stack[4].m_obj;
lean_object* v___y_2020_ = stack[5].m_obj;
lean_object* v_res_2042_;
v_res_2042_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7(v_val_2015_, v___f_2016_, v_param_2017_, v___x_2018_, v_x_2019_, v___y_2020_);
stack->m_obj
 = v_res_2042_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7___boxed(lean_object* v_val_2043_, lean_object* v___f_2044_, lean_object* v_param_2045_, lean_object* v___x_2046_, lean_object* v_x_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7(v_val_2043_, v___f_2044_, v_param_2045_, v___x_2046_, v_x_2047_, v___y_2048_);
lean_dec_ref(v___y_2048_);
lean_dec(v_val_2043_);
return v_res_2050_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8(lean_object* v___f_2051_, lean_object* v___f_2052_, lean_object* v___x_2053_, lean_object* v_lastTask_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v___x_2058_; lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2068_; 
v___x_2058_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_lastTask_2054_, v___f_2051_, v___y_2056_);
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2061_ = v___x_2058_;
v_isShared_2062_ = v_isSharedCheck_2068_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2058_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2068_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2066_; 
v___x_2063_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2052_, v_a_2059_);
v___x_2064_ = lean_st_ref_swap(v___y_2055_, v___x_2063_);
lean_dec(v___x_2064_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v___x_2053_);
v___x_2066_ = v___x_2061_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2053_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2051_ = stack[0].m_obj;
lean_object* v___f_2052_ = stack[1].m_obj;
lean_object* v___x_2053_ = stack[2].m_obj;
lean_object* v_lastTask_2054_ = stack[3].m_obj;
lean_object* v___y_2055_ = stack[4].m_obj;
lean_object* v___y_2056_ = stack[5].m_obj;
lean_object* v_res_2069_;
v_res_2069_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8(v___f_2051_, v___f_2052_, v___x_2053_, v_lastTask_2054_, v___y_2055_, v___y_2056_);
stack->m_obj
 = v_res_2069_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8___boxed(lean_object* v___f_2070_, lean_object* v___f_2071_, lean_object* v___x_2072_, lean_object* v_lastTask_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8(v___f_2070_, v___f_2071_, v___x_2072_, v_lastTask_2073_, v___y_2074_, v___y_2075_);
lean_dec_ref(v___y_2075_);
lean_dec(v___y_2074_);
return v_res_2077_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9(lean_object* v_val_2078_, lean_object* v___f_2079_, lean_object* v___x_2080_, lean_object* v___f_2081_, lean_object* v___f_2082_, lean_object* v___x_2083_, lean_object* v___f_2084_, lean_object* v___f_2085_, lean_object* v_val_2086_, lean_object* v_param_2087_, lean_object* v___y_2088_){
_start:
{
lean_object* v___f_2090_; lean_object* v___f_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_6278__overap_2094_; lean_object* v___x_2095_; 
v___f_2090_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_2090_, 0, v_val_2078_);
lean_closure_set(v___f_2090_, 1, v___f_2079_);
lean_closure_set(v___f_2090_, 2, v_param_2087_);
lean_closure_set(v___f_2090_, 3, v___x_2080_);
v___f_2091_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8___boxed), 7, 3);
lean_closure_set(v___f_2091_, 0, v___f_2090_);
lean_closure_set(v___f_2091_, 1, v___f_2081_);
lean_closure_set(v___f_2091_, 2, v___x_2080_);
v___x_2092_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_2092_, 0, lean_box(0));
lean_closure_set(v___x_2092_, 1, lean_box(0));
lean_closure_set(v___x_2092_, 2, lean_box(0));
lean_closure_set(v___x_2092_, 3, v___f_2082_);
lean_inc_ref(v___x_2083_);
v___x_2093_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2093_, 0, lean_box(0));
lean_closure_set(v___x_2093_, 1, lean_box(0));
lean_closure_set(v___x_2093_, 2, v___x_2083_);
lean_closure_set(v___x_2093_, 3, lean_box(0));
lean_closure_set(v___x_2093_, 4, lean_box(0));
lean_closure_set(v___x_2093_, 5, v___x_2092_);
lean_closure_set(v___x_2093_, 6, v___f_2091_);
v___x_6278__overap_2094_ = l_Std_Mutex_atomically___redArg(v___x_2083_, v___f_2084_, v___f_2085_, v_val_2086_, v___x_2093_);
lean_inc_ref(v___y_2088_);
v___x_2095_ = lean_apply_2(v___x_6278__overap_2094_, v___y_2088_, lean_box(0));
return v___x_2095_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2078_ = stack[0].m_obj;
lean_object* v___f_2079_ = stack[1].m_obj;
lean_object* v___x_2080_ = stack[2].m_obj;
lean_object* v___f_2081_ = stack[3].m_obj;
lean_object* v___f_2082_ = stack[4].m_obj;
lean_object* v___x_2083_ = stack[5].m_obj;
lean_object* v___f_2084_ = stack[6].m_obj;
lean_object* v___f_2085_ = stack[7].m_obj;
lean_object* v_val_2086_ = stack[8].m_obj;
lean_object* v_param_2087_ = stack[9].m_obj;
lean_object* v___y_2088_ = stack[10].m_obj;
lean_object* v_res_2096_;
v_res_2096_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9(v_val_2078_, v___f_2079_, v___x_2080_, v___f_2081_, v___f_2082_, v___x_2083_, v___f_2084_, v___f_2085_, v_val_2086_, v_param_2087_, v___y_2088_);
stack->m_obj
 = v_res_2096_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9___boxed(lean_object* v_val_2097_, lean_object* v___f_2098_, lean_object* v___x_2099_, lean_object* v___f_2100_, lean_object* v___f_2101_, lean_object* v___x_2102_, lean_object* v___f_2103_, lean_object* v___f_2104_, lean_object* v_val_2105_, lean_object* v_param_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9(v_val_2097_, v___f_2098_, v___x_2099_, v___f_2100_, v___f_2101_, v___x_2102_, v___f_2103_, v___f_2104_, v_val_2105_, v_param_2106_, v___y_2107_);
lean_dec_ref(v___y_2107_);
return v_res_2109_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1(void){
_start:
{
lean_object* v___x_2111_; 
v___x_2111_ = l_instMonadEIO___redArg();
return v___x_2111_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1);
v___x_2113_ = l_ReaderT_instMonad___redArg(v___x_2112_);
return v___x_2113_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15(void){
_start:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2139_ = lean_box(0);
v___x_2140_ = lean_task_pure(v___x_2139_);
return v___x_2140_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(lean_object* v_method_2141_, lean_object* v_completeness_2142_, lean_object* v_inst_2143_, lean_object* v_inst_2144_, lean_object* v_inst_2145_, lean_object* v_inst_2146_, lean_object* v_initState_2147_, lean_object* v_handler_2148_, lean_object* v_onDidChange_2149_){
_start:
{
lean_object* v___f_2151_; lean_object* v___f_2152_; lean_object* v___f_2153_; lean_object* v___x_2154_; lean_object* v___f_2155_; lean_object* v___f_2156_; lean_object* v___f_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; 
lean_inc_ref(v_inst_2143_);
v___f_2151_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2151_, 0, v_inst_2143_);
lean_closure_set(v___f_2151_, 1, v_inst_2144_);
lean_inc_n(v_inst_2146_, 2);
lean_inc_ref_n(v_method_2141_, 2);
v___f_2152_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1___boxed), 9, 5);
lean_closure_set(v___f_2152_, 0, v_inst_2143_);
lean_closure_set(v___f_2152_, 1, v_method_2141_);
lean_closure_set(v___f_2152_, 2, v_inst_2146_);
lean_closure_set(v___f_2152_, 3, v_handler_2148_);
lean_closure_set(v___f_2152_, 4, v_inst_2145_);
v___f_2153_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0___boxed), 7, 3);
lean_closure_set(v___f_2153_, 0, v_method_2141_);
lean_closure_set(v___f_2153_, 1, v_inst_2146_);
lean_closure_set(v___f_2153_, 2, v_onDidChange_2149_);
v___x_2154_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2);
v___f_2155_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__5));
v___f_2156_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__7));
v___f_2157_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__11));
v___x_2158_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__0));
v___x_2159_ = l_Lean_initializing();
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
lean_dec_ref(v___f_2153_);
lean_dec_ref(v___f_2152_);
lean_dec_ref(v___f_2151_);
lean_dec(v_initState_2147_);
lean_dec(v_inst_2146_);
lean_dec(v_completeness_2142_);
v___x_2160_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__12));
v___x_2161_ = lean_string_append(v___x_2160_, v_method_2141_);
lean_dec_ref(v_method_2141_);
v___x_2162_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___x_2163_ = lean_string_append(v___x_2161_, v___x_2162_);
v___x_2164_ = lean_mk_io_user_error(v___x_2163_);
v___x_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
return v___x_2165_;
}
else
{
lean_object* v___x_2166_; lean_object* v___f_2167_; lean_object* v___f_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___f_2173_; lean_object* v___f_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___f_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2166_ = lean_box(0);
v___f_2167_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__13));
v___f_2168_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__14));
v___x_2169_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15);
v___x_2170_ = l_Std_Mutex_new___redArg(v___x_2169_);
v___x_2171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2171_, 0, v_inst_2146_);
lean_ctor_set(v___x_2171_, 1, v_initState_2147_);
lean_inc_ref(v___x_2171_);
v___x_2172_ = lean_st_mk_ref(v___x_2171_);
lean_inc_ref_n(v___x_2170_, 2);
lean_inc_ref(v___f_2152_);
lean_inc_n(v___x_2172_, 2);
v___f_2173_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6___boxed), 11, 8);
lean_closure_set(v___f_2173_, 0, v___x_2172_);
lean_closure_set(v___f_2173_, 1, v___f_2152_);
lean_closure_set(v___f_2173_, 2, v___f_2167_);
lean_closure_set(v___f_2173_, 3, v___f_2157_);
lean_closure_set(v___f_2173_, 4, v___x_2154_);
lean_closure_set(v___f_2173_, 5, v___f_2155_);
lean_closure_set(v___f_2173_, 6, v___f_2156_);
lean_closure_set(v___f_2173_, 7, v___x_2170_);
lean_inc_ref(v___f_2153_);
v___f_2174_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9___boxed), 12, 9);
lean_closure_set(v___f_2174_, 0, v___x_2172_);
lean_closure_set(v___f_2174_, 1, v___f_2153_);
lean_closure_set(v___f_2174_, 2, v___x_2166_);
lean_closure_set(v___f_2174_, 3, v___f_2168_);
lean_closure_set(v___f_2174_, 4, v___f_2157_);
lean_closure_set(v___f_2174_, 5, v___x_2154_);
lean_closure_set(v___f_2174_, 6, v___f_2155_);
lean_closure_set(v___f_2174_, 7, v___f_2156_);
lean_closure_set(v___f_2174_, 8, v___x_2170_);
v___x_2175_ = l_Lean_Server_statefulRequestHandlers;
v___x_2176_ = lean_st_ref_take(v___x_2175_);
v___f_2177_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
v___x_2178_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2178_, 0, v___f_2151_);
lean_ctor_set(v___x_2178_, 1, v___f_2152_);
lean_ctor_set(v___x_2178_, 2, v___f_2173_);
lean_ctor_set(v___x_2178_, 3, v___f_2153_);
lean_ctor_set(v___x_2178_, 4, v___f_2174_);
lean_ctor_set(v___x_2178_, 5, v___x_2170_);
lean_ctor_set(v___x_2178_, 6, v___x_2171_);
lean_ctor_set(v___x_2178_, 7, v___x_2172_);
lean_ctor_set(v___x_2178_, 8, v_completeness_2142_);
v___x_2179_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2177_, v___x_2158_, v___x_2176_, v_method_2141_, v___x_2178_);
v___x_2180_ = lean_st_ref_put(v___x_2175_, v___x_2179_);
v___x_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2180_);
return v___x_2181_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_2141_ = stack[0].m_obj;
lean_object* v_completeness_2142_ = stack[1].m_obj;
lean_object* v_inst_2143_ = stack[2].m_obj;
lean_object* v_inst_2144_ = stack[3].m_obj;
lean_object* v_inst_2145_ = stack[4].m_obj;
lean_object* v_inst_2146_ = stack[5].m_obj;
lean_object* v_initState_2147_ = stack[6].m_obj;
lean_object* v_handler_2148_ = stack[7].m_obj;
lean_object* v_onDidChange_2149_ = stack[8].m_obj;
lean_object* v_res_2182_;
v_res_2182_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2141_, v_completeness_2142_, v_inst_2143_, v_inst_2144_, v_inst_2145_, v_inst_2146_, v_initState_2147_, v_handler_2148_, v_onDidChange_2149_);
stack->m_obj
 = v_res_2182_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2183_, lean_object* v_completeness_2184_, lean_object* v_inst_2185_, lean_object* v_inst_2186_, lean_object* v_inst_2187_, lean_object* v_inst_2188_, lean_object* v_initState_2189_, lean_object* v_handler_2190_, lean_object* v_onDidChange_2191_, lean_object* v_a_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2183_, v_completeness_2184_, v_inst_2185_, v_inst_2186_, v_inst_2187_, v_inst_2188_, v_initState_2189_, v_handler_2190_, v_onDidChange_2191_);
return v_res_2193_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(lean_object* v_method_2194_, lean_object* v_completeness_2195_, lean_object* v_paramType_2196_, lean_object* v_inst_2197_, lean_object* v_inst_2198_, lean_object* v_respType_2199_, lean_object* v_inst_2200_, lean_object* v_stateType_2201_, lean_object* v_inst_2202_, lean_object* v_initState_2203_, lean_object* v_handler_2204_, lean_object* v_onDidChange_2205_){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2194_, v_completeness_2195_, v_inst_2197_, v_inst_2198_, v_inst_2200_, v_inst_2202_, v_initState_2203_, v_handler_2204_, v_onDidChange_2205_);
return v___x_2207_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_2194_ = stack[0].m_obj;
lean_object* v_completeness_2195_ = stack[1].m_obj;
lean_object* v_inst_2197_ = stack[3].m_obj;
lean_object* v_inst_2198_ = stack[4].m_obj;
lean_object* v_inst_2200_ = stack[6].m_obj;
lean_object* v_inst_2202_ = stack[8].m_obj;
lean_object* v_initState_2203_ = stack[9].m_obj;
lean_object* v_handler_2204_ = stack[10].m_obj;
lean_object* v_onDidChange_2205_ = stack[11].m_obj;
lean_object* v_res_2208_;
v_res_2208_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(v_method_2194_, v_completeness_2195_, lean_box(0), v_inst_2197_, v_inst_2198_, lean_box(0), v_inst_2200_, lean_box(0), v_inst_2202_, v_initState_2203_, v_handler_2204_, v_onDidChange_2205_);
stack->m_obj
 = v_res_2208_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___boxed(lean_object* v_method_2209_, lean_object* v_completeness_2210_, lean_object* v_paramType_2211_, lean_object* v_inst_2212_, lean_object* v_inst_2213_, lean_object* v_respType_2214_, lean_object* v_inst_2215_, lean_object* v_stateType_2216_, lean_object* v_inst_2217_, lean_object* v_initState_2218_, lean_object* v_handler_2219_, lean_object* v_onDidChange_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(v_method_2209_, v_completeness_2210_, v_paramType_2211_, v_inst_2212_, v_inst_2213_, v_respType_2214_, v_inst_2215_, v_stateType_2216_, v_inst_2217_, v_initState_2218_, v_handler_2219_, v_onDidChange_2220_);
return v_res_2222_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(lean_object* v_method_2223_, lean_object* v_completeness_2224_, lean_object* v_inst_2225_, lean_object* v_inst_2226_, lean_object* v_inst_2227_, lean_object* v_inst_2228_, lean_object* v_initState_2229_, lean_object* v_handler_2230_, lean_object* v_onDidChange_2231_){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___f_2236_; uint8_t v___x_2237_; 
v___x_2233_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__0));
v___x_2234_ = l_Lean_Server_requestHandlers;
v___x_2235_ = lean_st_ref_get(v___x_2234_);
v___f_2236_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
lean_inc_ref(v_method_2223_);
v___x_2237_ = l_Lean_PersistentHashMap_contains___redArg(v___f_2236_, v___x_2233_, v___x_2235_, v_method_2223_);
if (v___x_2237_ == 0)
{
lean_object* v___x_2238_; 
v___x_2238_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2223_, v_completeness_2224_, v_inst_2225_, v_inst_2226_, v_inst_2227_, v_inst_2228_, v_initState_2229_, v_handler_2230_, v_onDidChange_2231_);
return v___x_2238_;
}
else
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
lean_dec_ref(v_onDidChange_2231_);
lean_dec_ref(v_handler_2230_);
lean_dec(v_initState_2229_);
lean_dec(v_inst_2228_);
lean_dec_ref(v_inst_2227_);
lean_dec_ref(v_inst_2226_);
lean_dec_ref(v_inst_2225_);
lean_dec(v_completeness_2224_);
v___x_2239_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__12));
v___x_2240_ = lean_string_append(v___x_2239_, v_method_2223_);
lean_dec_ref(v_method_2223_);
v___x_2241_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__4));
v___x_2242_ = lean_string_append(v___x_2240_, v___x_2241_);
v___x_2243_ = lean_mk_io_user_error(v___x_2242_);
v___x_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
return v___x_2244_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_2223_ = stack[0].m_obj;
lean_object* v_completeness_2224_ = stack[1].m_obj;
lean_object* v_inst_2225_ = stack[2].m_obj;
lean_object* v_inst_2226_ = stack[3].m_obj;
lean_object* v_inst_2227_ = stack[4].m_obj;
lean_object* v_inst_2228_ = stack[5].m_obj;
lean_object* v_initState_2229_ = stack[6].m_obj;
lean_object* v_handler_2230_ = stack[7].m_obj;
lean_object* v_onDidChange_2231_ = stack[8].m_obj;
lean_object* v_res_2245_;
v_res_2245_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2223_, v_completeness_2224_, v_inst_2225_, v_inst_2226_, v_inst_2227_, v_inst_2228_, v_initState_2229_, v_handler_2230_, v_onDidChange_2231_);
stack->m_obj
 = v_res_2245_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2246_, lean_object* v_completeness_2247_, lean_object* v_inst_2248_, lean_object* v_inst_2249_, lean_object* v_inst_2250_, lean_object* v_inst_2251_, lean_object* v_initState_2252_, lean_object* v_handler_2253_, lean_object* v_onDidChange_2254_, lean_object* v_a_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2246_, v_completeness_2247_, v_inst_2248_, v_inst_2249_, v_inst_2250_, v_inst_2251_, v_initState_2252_, v_handler_2253_, v_onDidChange_2254_);
return v_res_2256_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler(lean_object* v_method_2257_, lean_object* v_completeness_2258_, lean_object* v_paramType_2259_, lean_object* v_inst_2260_, lean_object* v_inst_2261_, lean_object* v_respType_2262_, lean_object* v_inst_2263_, lean_object* v_stateType_2264_, lean_object* v_inst_2265_, lean_object* v_initState_2266_, lean_object* v_handler_2267_, lean_object* v_onDidChange_2268_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2257_, v_completeness_2258_, v_inst_2260_, v_inst_2261_, v_inst_2263_, v_inst_2265_, v_initState_2266_, v_handler_2267_, v_onDidChange_2268_);
return v___x_2270_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_2257_ = stack[0].m_obj;
lean_object* v_completeness_2258_ = stack[1].m_obj;
lean_object* v_inst_2260_ = stack[3].m_obj;
lean_object* v_inst_2261_ = stack[4].m_obj;
lean_object* v_inst_2263_ = stack[6].m_obj;
lean_object* v_inst_2265_ = stack[8].m_obj;
lean_object* v_initState_2266_ = stack[9].m_obj;
lean_object* v_handler_2267_ = stack[10].m_obj;
lean_object* v_onDidChange_2268_ = stack[11].m_obj;
lean_object* v_res_2271_;
v_res_2271_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler(v_method_2257_, v_completeness_2258_, lean_box(0), v_inst_2260_, v_inst_2261_, lean_box(0), v_inst_2263_, lean_box(0), v_inst_2265_, v_initState_2266_, v_handler_2267_, v_onDidChange_2268_);
stack->m_obj
 = v_res_2271_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___boxed(lean_object* v_method_2272_, lean_object* v_completeness_2273_, lean_object* v_paramType_2274_, lean_object* v_inst_2275_, lean_object* v_inst_2276_, lean_object* v_respType_2277_, lean_object* v_inst_2278_, lean_object* v_stateType_2279_, lean_object* v_inst_2280_, lean_object* v_initState_2281_, lean_object* v_handler_2282_, lean_object* v_onDidChange_2283_, lean_object* v_a_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler(v_method_2272_, v_completeness_2273_, v_paramType_2274_, v_inst_2275_, v_inst_2276_, v_respType_2277_, v_inst_2278_, v_stateType_2279_, v_inst_2280_, v_initState_2281_, v_handler_2282_, v_onDidChange_2283_);
return v_res_2285_;
}
}
lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0(lean_object* v_handler_2286_, lean_object* v_p_2287_, lean_object* v_s_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v___x_2291_; 
lean_inc_ref(v___y_2289_);
v___x_2291_ = lean_apply_4(v_handler_2286_, v_p_2287_, v_s_2288_, v___y_2289_, lean_box(0));
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2310_; 
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2294_ = v___x_2291_;
v_isShared_2295_ = v_isSharedCheck_2310_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2291_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2310_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v_fst_2296_; lean_object* v_snd_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2309_; 
v_fst_2296_ = lean_ctor_get(v_a_2292_, 0);
v_snd_2297_ = lean_ctor_get(v_a_2292_, 1);
v_isSharedCheck_2309_ = !lean_is_exclusive(v_a_2292_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2299_ = v_a_2292_;
v_isShared_2300_ = v_isSharedCheck_2309_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_snd_2297_);
lean_inc(v_fst_2296_);
lean_dec(v_a_2292_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2309_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
uint8_t v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2304_; 
v___x_2301_ = 1;
v___x_2302_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2302_, 0, v_fst_2296_);
lean_ctor_set_uint8(v___x_2302_, sizeof(void*)*1, v___x_2301_);
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 0, v___x_2302_);
v___x_2304_ = v___x_2299_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2302_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_snd_2297_);
v___x_2304_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
lean_object* v___x_2306_; 
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 0, v___x_2304_);
v___x_2306_ = v___x_2294_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
v_a_2311_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2291_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2291_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_handler_2286_ = stack[0].m_obj;
lean_object* v_p_2287_ = stack[1].m_obj;
lean_object* v_s_2288_ = stack[2].m_obj;
lean_object* v___y_2289_ = stack[3].m_obj;
lean_object* v_res_2319_;
v_res_2319_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0(v_handler_2286_, v_p_2287_, v_s_2288_, v___y_2289_);
stack->m_obj
 = v_res_2319_;
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object* v_handler_2320_, lean_object* v_p_2321_, lean_object* v_s_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0(v_handler_2320_, v_p_2321_, v_s_2322_, v___y_2323_);
lean_dec_ref(v___y_2323_);
return v_res_2325_;
}
}
lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(lean_object* v_method_2326_, lean_object* v_inst_2327_, lean_object* v_inst_2328_, lean_object* v_inst_2329_, lean_object* v_inst_2330_, lean_object* v_initState_2331_, lean_object* v_handler_2332_, lean_object* v_onDidChange_2333_){
_start:
{
lean_object* v_handler_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v_handler_2335_ = lean_alloc_closure((void*)(l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v_handler_2335_, 0, v_handler_2332_);
v___x_2336_ = lean_box(0);
v___x_2337_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2326_, v___x_2336_, v_inst_2327_, v_inst_2328_, v_inst_2329_, v_inst_2330_, v_initState_2331_, v_handler_2335_, v_onDidChange_2333_);
return v___x_2337_;
}
}
LEAN_EXPORT void l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_2326_ = stack[0].m_obj;
lean_object* v_inst_2327_ = stack[1].m_obj;
lean_object* v_inst_2328_ = stack[2].m_obj;
lean_object* v_inst_2329_ = stack[3].m_obj;
lean_object* v_inst_2330_ = stack[4].m_obj;
lean_object* v_initState_2331_ = stack[5].m_obj;
lean_object* v_handler_2332_ = stack[6].m_obj;
lean_object* v_onDidChange_2333_ = stack[7].m_obj;
lean_object* v_res_2338_;
v_res_2338_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(v_method_2326_, v_inst_2327_, v_inst_2328_, v_inst_2329_, v_inst_2330_, v_initState_2331_, v_handler_2332_, v_onDidChange_2333_);
stack->m_obj
 = v_res_2338_;
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2339_, lean_object* v_inst_2340_, lean_object* v_inst_2341_, lean_object* v_inst_2342_, lean_object* v_inst_2343_, lean_object* v_initState_2344_, lean_object* v_handler_2345_, lean_object* v_onDidChange_2346_, lean_object* v_a_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(v_method_2339_, v_inst_2340_, v_inst_2341_, v_inst_2342_, v_inst_2343_, v_initState_2344_, v_handler_2345_, v_onDidChange_2346_);
return v_res_2348_;
}
}
lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler(lean_object* v_method_2349_, lean_object* v_paramType_2350_, lean_object* v_inst_2351_, lean_object* v_inst_2352_, lean_object* v_respType_2353_, lean_object* v_inst_2354_, lean_object* v_stateType_2355_, lean_object* v_inst_2356_, lean_object* v_initState_2357_, lean_object* v_handler_2358_, lean_object* v_onDidChange_2359_){
_start:
{
lean_object* v___x_2361_; 
v___x_2361_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(v_method_2349_, v_inst_2351_, v_inst_2352_, v_inst_2354_, v_inst_2356_, v_initState_2357_, v_handler_2358_, v_onDidChange_2359_);
return v___x_2361_;
}
}
LEAN_EXPORT void l_Lean_Server_registerCompleteStatefulLspRequestHandler_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_2349_ = stack[0].m_obj;
lean_object* v_inst_2351_ = stack[2].m_obj;
lean_object* v_inst_2352_ = stack[3].m_obj;
lean_object* v_inst_2354_ = stack[5].m_obj;
lean_object* v_inst_2356_ = stack[7].m_obj;
lean_object* v_initState_2357_ = stack[8].m_obj;
lean_object* v_handler_2358_ = stack[9].m_obj;
lean_object* v_onDidChange_2359_ = stack[10].m_obj;
lean_object* v_res_2362_;
v_res_2362_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler(v_method_2349_, lean_box(0), v_inst_2351_, v_inst_2352_, lean_box(0), v_inst_2354_, lean_box(0), v_inst_2356_, v_initState_2357_, v_handler_2358_, v_onDidChange_2359_);
stack->m_obj
 = v_res_2362_;
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___boxed(lean_object* v_method_2363_, lean_object* v_paramType_2364_, lean_object* v_inst_2365_, lean_object* v_inst_2366_, lean_object* v_respType_2367_, lean_object* v_inst_2368_, lean_object* v_stateType_2369_, lean_object* v_inst_2370_, lean_object* v_initState_2371_, lean_object* v_handler_2372_, lean_object* v_onDidChange_2373_, lean_object* v_a_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler(v_method_2363_, v_paramType_2364_, v_inst_2365_, v_inst_2366_, v_respType_2367_, v_inst_2368_, v_stateType_2369_, v_inst_2370_, v_initState_2371_, v_handler_2372_, v_onDidChange_2373_);
return v_res_2375_;
}
}
lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(lean_object* v_method_2376_, lean_object* v_refreshMethod_2377_, lean_object* v_refreshIntervalMs_2378_, lean_object* v_inst_2379_, lean_object* v_inst_2380_, lean_object* v_inst_2381_, lean_object* v_inst_2382_, lean_object* v_initState_2383_, lean_object* v_handler_2384_, lean_object* v_onDidChange_2385_){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2387_, 0, v_refreshMethod_2377_);
lean_ctor_set(v___x_2387_, 1, v_refreshIntervalMs_2378_);
v___x_2388_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2376_, v___x_2387_, v_inst_2379_, v_inst_2380_, v_inst_2381_, v_inst_2382_, v_initState_2383_, v_handler_2384_, v_onDidChange_2385_);
return v___x_2388_;
}
}
LEAN_EXPORT void l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_2376_ = stack[0].m_obj;
lean_object* v_refreshMethod_2377_ = stack[1].m_obj;
lean_object* v_refreshIntervalMs_2378_ = stack[2].m_obj;
lean_object* v_inst_2379_ = stack[3].m_obj;
lean_object* v_inst_2380_ = stack[4].m_obj;
lean_object* v_inst_2381_ = stack[5].m_obj;
lean_object* v_inst_2382_ = stack[6].m_obj;
lean_object* v_initState_2383_ = stack[7].m_obj;
lean_object* v_handler_2384_ = stack[8].m_obj;
lean_object* v_onDidChange_2385_ = stack[9].m_obj;
lean_object* v_res_2389_;
v_res_2389_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(v_method_2376_, v_refreshMethod_2377_, v_refreshIntervalMs_2378_, v_inst_2379_, v_inst_2380_, v_inst_2381_, v_inst_2382_, v_initState_2383_, v_handler_2384_, v_onDidChange_2385_);
stack->m_obj
 = v_res_2389_;
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2390_, lean_object* v_refreshMethod_2391_, lean_object* v_refreshIntervalMs_2392_, lean_object* v_inst_2393_, lean_object* v_inst_2394_, lean_object* v_inst_2395_, lean_object* v_inst_2396_, lean_object* v_initState_2397_, lean_object* v_handler_2398_, lean_object* v_onDidChange_2399_, lean_object* v_a_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(v_method_2390_, v_refreshMethod_2391_, v_refreshIntervalMs_2392_, v_inst_2393_, v_inst_2394_, v_inst_2395_, v_inst_2396_, v_initState_2397_, v_handler_2398_, v_onDidChange_2399_);
return v_res_2401_;
}
}
lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler(lean_object* v_method_2402_, lean_object* v_refreshMethod_2403_, lean_object* v_refreshIntervalMs_2404_, lean_object* v_paramType_2405_, lean_object* v_inst_2406_, lean_object* v_inst_2407_, lean_object* v_respType_2408_, lean_object* v_inst_2409_, lean_object* v_stateType_2410_, lean_object* v_inst_2411_, lean_object* v_initState_2412_, lean_object* v_handler_2413_, lean_object* v_onDidChange_2414_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(v_method_2402_, v_refreshMethod_2403_, v_refreshIntervalMs_2404_, v_inst_2406_, v_inst_2407_, v_inst_2409_, v_inst_2411_, v_initState_2412_, v_handler_2413_, v_onDidChange_2414_);
return v___x_2416_;
}
}
LEAN_EXPORT void l_Lean_Server_registerPartialStatefulLspRequestHandler_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_2402_ = stack[0].m_obj;
lean_object* v_refreshMethod_2403_ = stack[1].m_obj;
lean_object* v_refreshIntervalMs_2404_ = stack[2].m_obj;
lean_object* v_inst_2406_ = stack[4].m_obj;
lean_object* v_inst_2407_ = stack[5].m_obj;
lean_object* v_inst_2409_ = stack[7].m_obj;
lean_object* v_inst_2411_ = stack[9].m_obj;
lean_object* v_initState_2412_ = stack[10].m_obj;
lean_object* v_handler_2413_ = stack[11].m_obj;
lean_object* v_onDidChange_2414_ = stack[12].m_obj;
lean_object* v_res_2417_;
v_res_2417_ = l_Lean_Server_registerPartialStatefulLspRequestHandler(v_method_2402_, v_refreshMethod_2403_, v_refreshIntervalMs_2404_, lean_box(0), v_inst_2406_, v_inst_2407_, lean_box(0), v_inst_2409_, lean_box(0), v_inst_2411_, v_initState_2412_, v_handler_2413_, v_onDidChange_2414_);
stack->m_obj
 = v_res_2417_;
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___boxed(lean_object* v_method_2418_, lean_object* v_refreshMethod_2419_, lean_object* v_refreshIntervalMs_2420_, lean_object* v_paramType_2421_, lean_object* v_inst_2422_, lean_object* v_inst_2423_, lean_object* v_respType_2424_, lean_object* v_inst_2425_, lean_object* v_stateType_2426_, lean_object* v_inst_2427_, lean_object* v_initState_2428_, lean_object* v_handler_2429_, lean_object* v_onDidChange_2430_, lean_object* v_a_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Lean_Server_registerPartialStatefulLspRequestHandler(v_method_2418_, v_refreshMethod_2419_, v_refreshIntervalMs_2420_, v_paramType_2421_, v_inst_2422_, v_inst_2423_, v_respType_2424_, v_inst_2425_, v_stateType_2426_, v_inst_2427_, v_initState_2428_, v_handler_2429_, v_onDidChange_2430_);
return v_res_2432_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2433_, lean_object* v_i_2434_, lean_object* v_k_2435_){
_start:
{
lean_object* v___x_2436_; uint8_t v___x_2437_; 
v___x_2436_ = lean_array_get_size(v_keys_2433_);
v___x_2437_ = lean_nat_dec_lt(v_i_2434_, v___x_2436_);
if (v___x_2437_ == 0)
{
lean_dec(v_i_2434_);
return v___x_2437_;
}
else
{
lean_object* v_k_x27_2438_; uint8_t v___x_2439_; 
v_k_x27_2438_ = lean_array_fget_borrowed(v_keys_2433_, v_i_2434_);
v___x_2439_ = lean_string_dec_eq(v_k_2435_, v_k_x27_2438_);
if (v___x_2439_ == 0)
{
lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2440_ = lean_unsigned_to_nat(1u);
v___x_2441_ = lean_nat_add(v_i_2434_, v___x_2440_);
lean_dec(v_i_2434_);
v_i_2434_ = v___x_2441_;
goto _start;
}
else
{
lean_dec(v_i_2434_);
return v___x_2437_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2433_ = stack[0].m_obj;
lean_object* v_i_2434_ = stack[1].m_obj;
lean_object* v_k_2435_ = stack[2].m_obj;
uint8_t v_res_2443_;
v_res_2443_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_keys_2433_, v_i_2434_, v_k_2435_);
stack->m_num = v_res_2443_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2444_, lean_object* v_i_2445_, lean_object* v_k_2446_){
_start:
{
uint8_t v_res_2447_; lean_object* v_r_2448_; 
v_res_2447_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_keys_2444_, v_i_2445_, v_k_2446_);
lean_dec_ref(v_k_2446_);
lean_dec_ref(v_keys_2444_);
v_r_2448_ = lean_box(v_res_2447_);
return v_r_2448_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(lean_object* v_x_2449_, size_t v_x_2450_, lean_object* v_x_2451_){
_start:
{
if (lean_obj_tag(v_x_2449_) == 0)
{
lean_object* v_es_2452_; lean_object* v___x_2453_; size_t v___x_2454_; size_t v___x_2455_; lean_object* v_j_2456_; lean_object* v___x_2457_; 
v_es_2452_ = lean_ctor_get(v_x_2449_, 0);
v___x_2453_ = lean_box(2);
v___x_2454_ = ((size_t)31ULL);
v___x_2455_ = lean_usize_land(v_x_2450_, v___x_2454_);
v_j_2456_ = lean_usize_to_nat(v___x_2455_);
v___x_2457_ = lean_array_get_borrowed(v___x_2453_, v_es_2452_, v_j_2456_);
lean_dec(v_j_2456_);
switch(lean_obj_tag(v___x_2457_))
{
case 0:
{
lean_object* v_key_2458_; uint8_t v___x_2459_; 
v_key_2458_ = lean_ctor_get(v___x_2457_, 0);
v___x_2459_ = lean_string_dec_eq(v_x_2451_, v_key_2458_);
return v___x_2459_;
}
case 1:
{
lean_object* v_node_2460_; size_t v___x_2461_; size_t v___x_2462_; 
v_node_2460_ = lean_ctor_get(v___x_2457_, 0);
v___x_2461_ = ((size_t)5ULL);
v___x_2462_ = lean_usize_shift_right(v_x_2450_, v___x_2461_);
v_x_2449_ = v_node_2460_;
v_x_2450_ = v___x_2462_;
goto _start;
}
default: 
{
uint8_t v___x_2464_; 
v___x_2464_ = 0;
return v___x_2464_;
}
}
}
else
{
lean_object* v_ks_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; 
v_ks_2465_ = lean_ctor_get(v_x_2449_, 0);
v___x_2466_ = lean_unsigned_to_nat(0u);
v___x_2467_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_ks_2465_, v___x_2466_, v_x_2451_);
return v___x_2467_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2449_ = stack[0].m_obj;
size_t v_x_2450_ = stack[1].m_num;
lean_object* v_x_2451_ = stack[2].m_obj;
uint8_t v_res_2468_;
v_res_2468_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_2449_, v_x_2450_, v_x_2451_);
stack->m_num = v_res_2468_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg___boxed(lean_object* v_x_2469_, lean_object* v_x_2470_, lean_object* v_x_2471_){
_start:
{
size_t v_x_232__boxed_2472_; uint8_t v_res_2473_; lean_object* v_r_2474_; 
v_x_232__boxed_2472_ = lean_unbox_usize(v_x_2470_);
lean_dec(v_x_2470_);
v_res_2473_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_2469_, v_x_232__boxed_2472_, v_x_2471_);
lean_dec_ref(v_x_2471_);
lean_dec_ref(v_x_2469_);
v_r_2474_ = lean_box(v_res_2473_);
return v_r_2474_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(lean_object* v_x_2475_, lean_object* v_x_2476_){
_start:
{
uint64_t v___x_2477_; size_t v___x_2478_; uint8_t v___x_2479_; 
v___x_2477_ = lean_string_hash(v_x_2476_);
v___x_2478_ = lean_uint64_to_usize(v___x_2477_);
v___x_2479_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_2475_, v___x_2478_, v_x_2476_);
return v___x_2479_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2475_ = stack[0].m_obj;
lean_object* v_x_2476_ = stack[1].m_obj;
uint8_t v_res_2480_;
v_res_2480_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v_x_2475_, v_x_2476_);
stack->m_num = v_res_2480_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg___boxed(lean_object* v_x_2481_, lean_object* v_x_2482_){
_start:
{
uint8_t v_res_2483_; lean_object* v_r_2484_; 
v_res_2483_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v_x_2481_, v_x_2482_);
lean_dec_ref(v_x_2482_);
lean_dec_ref(v_x_2481_);
v_r_2484_ = lean_box(v_res_2483_);
return v_r_2484_;
}
}
uint8_t l_Lean_Server_isStatefulLspRequestMethod(lean_object* v_method_2485_){
_start:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; uint8_t v___x_2489_; 
v___x_2487_ = l_Lean_Server_statefulRequestHandlers;
v___x_2488_ = lean_st_ref_get(v___x_2487_);
v___x_2489_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v___x_2488_, v_method_2485_);
lean_dec(v___x_2488_);
return v___x_2489_;
}
}
LEAN_EXPORT void l_Lean_Server_isStatefulLspRequestMethod_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_2485_ = stack[0].m_obj;
uint8_t v_res_2490_;
v_res_2490_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_2485_);
stack->m_num = v_res_2490_;
}
LEAN_EXPORT lean_object* l_Lean_Server_isStatefulLspRequestMethod___boxed(lean_object* v_method_2491_, lean_object* v_a_2492_){
_start:
{
uint8_t v_res_2493_; lean_object* v_r_2494_; 
v_res_2493_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_2491_);
lean_dec_ref(v_method_2491_);
v_r_2494_ = lean_box(v_res_2493_);
return v_r_2494_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0(lean_object* v_00_u03b2_2495_, lean_object* v_x_2496_, lean_object* v_x_2497_){
_start:
{
uint8_t v___x_2498_; 
v___x_2498_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v_x_2496_, v_x_2497_);
return v___x_2498_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2496_ = stack[1].m_obj;
lean_object* v_x_2497_ = stack[2].m_obj;
uint8_t v_res_2499_;
v_res_2499_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0(lean_box(0), v_x_2496_, v_x_2497_);
stack->m_num = v_res_2499_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___boxed(lean_object* v_00_u03b2_2500_, lean_object* v_x_2501_, lean_object* v_x_2502_){
_start:
{
uint8_t v_res_2503_; lean_object* v_r_2504_; 
v_res_2503_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0(v_00_u03b2_2500_, v_x_2501_, v_x_2502_);
lean_dec_ref(v_x_2502_);
lean_dec_ref(v_x_2501_);
v_r_2504_ = lean_box(v_res_2503_);
return v_r_2504_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0(lean_object* v_00_u03b2_2505_, lean_object* v_x_2506_, size_t v_x_2507_, lean_object* v_x_2508_){
_start:
{
uint8_t v___x_2509_; 
v___x_2509_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_2506_, v_x_2507_, v_x_2508_);
return v___x_2509_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2506_ = stack[1].m_obj;
size_t v_x_2507_ = stack[2].m_num;
lean_object* v_x_2508_ = stack[3].m_obj;
uint8_t v_res_2510_;
v_res_2510_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0(lean_box(0), v_x_2506_, v_x_2507_, v_x_2508_);
stack->m_num = v_res_2510_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2511_, lean_object* v_x_2512_, lean_object* v_x_2513_, lean_object* v_x_2514_){
_start:
{
size_t v_x_340__boxed_2515_; uint8_t v_res_2516_; lean_object* v_r_2517_; 
v_x_340__boxed_2515_ = lean_unbox_usize(v_x_2513_);
lean_dec(v_x_2513_);
v_res_2516_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0(v_00_u03b2_2511_, v_x_2512_, v_x_340__boxed_2515_, v_x_2514_);
lean_dec_ref(v_x_2514_);
lean_dec_ref(v_x_2512_);
v_r_2517_ = lean_box(v_res_2516_);
return v_r_2517_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2518_, lean_object* v_keys_2519_, lean_object* v_vals_2520_, lean_object* v_heq_2521_, lean_object* v_i_2522_, lean_object* v_k_2523_){
_start:
{
uint8_t v___x_2524_; 
v___x_2524_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_keys_2519_, v_i_2522_, v_k_2523_);
return v___x_2524_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2519_ = stack[1].m_obj;
lean_object* v_vals_2520_ = stack[2].m_obj;
lean_object* v_i_2522_ = stack[4].m_obj;
lean_object* v_k_2523_ = stack[5].m_obj;
uint8_t v_res_2525_;
v_res_2525_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1(lean_box(0), v_keys_2519_, v_vals_2520_, lean_box(0), v_i_2522_, v_k_2523_);
stack->m_num = v_res_2525_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2526_, lean_object* v_keys_2527_, lean_object* v_vals_2528_, lean_object* v_heq_2529_, lean_object* v_i_2530_, lean_object* v_k_2531_){
_start:
{
uint8_t v_res_2532_; lean_object* v_r_2533_; 
v_res_2532_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1(v_00_u03b2_2526_, v_keys_2527_, v_vals_2528_, v_heq_2529_, v_i_2530_, v_k_2531_);
lean_dec_ref(v_k_2531_);
lean_dec_ref(v_vals_2528_);
lean_dec_ref(v_keys_2527_);
v_r_2533_ = lean_box(v_res_2532_);
return v_r_2533_;
}
}
lean_object* l_Lean_Server_lookupStatefulLspRequestHandler(lean_object* v_method_2534_){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2536_ = l_Lean_Server_statefulRequestHandlers;
v___x_2537_ = lean_st_ref_get(v___x_2536_);
v___x_2538_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v___x_2537_, v_method_2534_);
lean_dec(v___x_2537_);
return v___x_2538_;
}
}
LEAN_EXPORT void l_Lean_Server_lookupStatefulLspRequestHandler_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_2534_ = stack[0].m_obj;
lean_object* v_res_2539_;
v_res_2539_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_2534_);
stack->m_obj
 = v_res_2539_;
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupStatefulLspRequestHandler___boxed(lean_object* v_method_2540_, lean_object* v_a_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_2540_);
lean_dec_ref(v_method_2540_);
return v_res_2542_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(lean_object* v_as_2543_, size_t v_i_2544_, size_t v_stop_2545_, lean_object* v_b_2546_){
_start:
{
lean_object* v___y_2548_; uint8_t v___x_2552_; 
v___x_2552_ = lean_usize_dec_eq(v_i_2544_, v_stop_2545_);
if (v___x_2552_ == 0)
{
lean_object* v___x_2553_; lean_object* v_snd_2554_; lean_object* v_completeness_2555_; 
v___x_2553_ = lean_array_uget(v_as_2543_, v_i_2544_);
v_snd_2554_ = lean_ctor_get(v___x_2553_, 1);
v_completeness_2555_ = lean_ctor_get(v_snd_2554_, 8);
lean_inc(v_completeness_2555_);
if (lean_obj_tag(v_completeness_2555_) == 1)
{
lean_object* v_fst_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2573_; 
v_fst_2556_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2573_ == 0)
{
lean_object* v_unused_2574_; 
v_unused_2574_ = lean_ctor_get(v___x_2553_, 1);
lean_dec(v_unused_2574_);
v___x_2558_ = v___x_2553_;
v_isShared_2559_ = v_isSharedCheck_2573_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_fst_2556_);
lean_dec(v___x_2553_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2573_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v_refreshMethod_2560_; lean_object* v_refreshIntervalMs_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2572_; 
v_refreshMethod_2560_ = lean_ctor_get(v_completeness_2555_, 0);
v_refreshIntervalMs_2561_ = lean_ctor_get(v_completeness_2555_, 1);
v_isSharedCheck_2572_ = !lean_is_exclusive(v_completeness_2555_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2563_ = v_completeness_2555_;
v_isShared_2564_ = v_isSharedCheck_2572_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_refreshIntervalMs_2561_);
lean_inc(v_refreshMethod_2560_);
lean_dec(v_completeness_2555_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2572_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 1, v_refreshIntervalMs_2561_);
lean_ctor_set(v___x_2558_, 0, v_refreshMethod_2560_);
v___x_2566_ = v___x_2558_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_refreshMethod_2560_);
lean_ctor_set(v_reuseFailAlloc_2571_, 1, v_refreshIntervalMs_2561_);
v___x_2566_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
lean_object* v___x_2568_; 
if (v_isShared_2564_ == 0)
{
lean_ctor_set_tag(v___x_2563_, 0);
lean_ctor_set(v___x_2563_, 1, v___x_2566_);
lean_ctor_set(v___x_2563_, 0, v_fst_2556_);
v___x_2568_ = v___x_2563_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_fst_2556_);
lean_ctor_set(v_reuseFailAlloc_2570_, 1, v___x_2566_);
v___x_2568_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
lean_object* v___x_2569_; 
v___x_2569_ = lean_array_push(v_b_2546_, v___x_2568_);
v___y_2548_ = v___x_2569_;
goto v___jp_2547_;
}
}
}
}
}
else
{
lean_dec(v_completeness_2555_);
lean_dec(v___x_2553_);
v___y_2548_ = v_b_2546_;
goto v___jp_2547_;
}
}
else
{
return v_b_2546_;
}
v___jp_2547_:
{
size_t v___x_2549_; size_t v___x_2550_; 
v___x_2549_ = ((size_t)1ULL);
v___x_2550_ = lean_usize_add(v_i_2544_, v___x_2549_);
v_i_2544_ = v___x_2550_;
v_b_2546_ = v___y_2548_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2543_ = stack[0].m_obj;
size_t v_i_2544_ = stack[1].m_num;
size_t v_stop_2545_ = stack[2].m_num;
lean_object* v_b_2546_ = stack[3].m_obj;
lean_object* v_res_2575_;
v_res_2575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_2543_, v_i_2544_, v_stop_2545_, v_b_2546_);
stack->m_obj
 = v_res_2575_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2___boxed(lean_object* v_as_2576_, lean_object* v_i_2577_, lean_object* v_stop_2578_, lean_object* v_b_2579_){
_start:
{
size_t v_i_boxed_2580_; size_t v_stop_boxed_2581_; lean_object* v_res_2582_; 
v_i_boxed_2580_ = lean_unbox_usize(v_i_2577_);
lean_dec(v_i_2577_);
v_stop_boxed_2581_ = lean_unbox_usize(v_stop_2578_);
lean_dec(v_stop_2578_);
v_res_2582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_2576_, v_i_boxed_2580_, v_stop_boxed_2581_, v_b_2579_);
lean_dec_ref(v_as_2576_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(lean_object* v_as_2585_, lean_object* v_start_2586_, lean_object* v_stop_2587_){
_start:
{
lean_object* v___x_2588_; uint8_t v___x_2589_; 
v___x_2588_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___closed__0));
v___x_2589_ = lean_nat_dec_lt(v_start_2586_, v_stop_2587_);
if (v___x_2589_ == 0)
{
return v___x_2588_;
}
else
{
lean_object* v___x_2590_; uint8_t v___x_2591_; 
v___x_2590_ = lean_array_get_size(v_as_2585_);
v___x_2591_ = lean_nat_dec_le(v_stop_2587_, v___x_2590_);
if (v___x_2591_ == 0)
{
uint8_t v___x_2592_; 
v___x_2592_ = lean_nat_dec_lt(v_start_2586_, v___x_2590_);
if (v___x_2592_ == 0)
{
return v___x_2588_;
}
else
{
size_t v___x_2593_; size_t v___x_2594_; lean_object* v___x_2595_; 
v___x_2593_ = lean_usize_of_nat(v_start_2586_);
v___x_2594_ = lean_usize_of_nat(v___x_2590_);
v___x_2595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_2585_, v___x_2593_, v___x_2594_, v___x_2588_);
return v___x_2595_;
}
}
else
{
size_t v___x_2596_; size_t v___x_2597_; lean_object* v___x_2598_; 
v___x_2596_ = lean_usize_of_nat(v_start_2586_);
v___x_2597_ = lean_usize_of_nat(v_stop_2587_);
v___x_2598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_2585_, v___x_2596_, v___x_2597_, v___x_2588_);
return v___x_2598_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___boxed(lean_object* v_as_2599_, lean_object* v_start_2600_, lean_object* v_stop_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(v_as_2599_, v_start_2600_, v_stop_2601_);
lean_dec(v_stop_2601_);
lean_dec(v_start_2600_);
lean_dec_ref(v_as_2599_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_f_2603_, lean_object* v_keys_2604_, lean_object* v_vals_2605_, lean_object* v_i_2606_, lean_object* v_acc_2607_){
_start:
{
lean_object* v___x_2608_; uint8_t v___x_2609_; 
v___x_2608_ = lean_array_get_size(v_keys_2604_);
v___x_2609_ = lean_nat_dec_lt(v_i_2606_, v___x_2608_);
if (v___x_2609_ == 0)
{
lean_dec(v_i_2606_);
lean_dec(v_f_2603_);
return v_acc_2607_;
}
else
{
lean_object* v_k_2610_; lean_object* v_v_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v_k_2610_ = lean_array_fget_borrowed(v_keys_2604_, v_i_2606_);
v_v_2611_ = lean_array_fget_borrowed(v_vals_2605_, v_i_2606_);
lean_inc(v_f_2603_);
lean_inc(v_v_2611_);
lean_inc(v_k_2610_);
v___x_2612_ = lean_apply_3(v_f_2603_, v_acc_2607_, v_k_2610_, v_v_2611_);
v___x_2613_ = lean_unsigned_to_nat(1u);
v___x_2614_ = lean_nat_add(v_i_2606_, v___x_2613_);
lean_dec(v_i_2606_);
v_i_2606_ = v___x_2614_;
v_acc_2607_ = v___x_2612_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_f_2616_, lean_object* v_keys_2617_, lean_object* v_vals_2618_, lean_object* v_i_2619_, lean_object* v_acc_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_2616_, v_keys_2617_, v_vals_2618_, v_i_2619_, v_acc_2620_);
lean_dec_ref(v_vals_2618_);
lean_dec_ref(v_keys_2617_);
return v_res_2621_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_f_2622_, lean_object* v_as_2623_, size_t v_i_2624_, size_t v_stop_2625_, lean_object* v_b_2626_){
_start:
{
lean_object* v___y_2628_; uint8_t v___x_2632_; 
v___x_2632_ = lean_usize_dec_eq(v_i_2624_, v_stop_2625_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; 
v___x_2633_ = lean_array_uget_borrowed(v_as_2623_, v_i_2624_);
switch(lean_obj_tag(v___x_2633_))
{
case 0:
{
lean_object* v_key_2634_; lean_object* v_val_2635_; lean_object* v___x_2636_; 
v_key_2634_ = lean_ctor_get(v___x_2633_, 0);
v_val_2635_ = lean_ctor_get(v___x_2633_, 1);
lean_inc(v_f_2622_);
lean_inc(v_val_2635_);
lean_inc(v_key_2634_);
v___x_2636_ = lean_apply_3(v_f_2622_, v_b_2626_, v_key_2634_, v_val_2635_);
v___y_2628_ = v___x_2636_;
goto v___jp_2627_;
}
case 1:
{
lean_object* v_node_2637_; lean_object* v___x_2638_; 
v_node_2637_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_f_2622_);
v___x_2638_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2622_, v_node_2637_, v_b_2626_);
v___y_2628_ = v___x_2638_;
goto v___jp_2627_;
}
default: 
{
v___y_2628_ = v_b_2626_;
goto v___jp_2627_;
}
}
}
else
{
lean_dec(v_f_2622_);
return v_b_2626_;
}
v___jp_2627_:
{
size_t v___x_2629_; size_t v___x_2630_; 
v___x_2629_ = ((size_t)1ULL);
v___x_2630_ = lean_usize_add(v_i_2624_, v___x_2629_);
v_i_2624_ = v___x_2630_;
v_b_2626_ = v___y_2628_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2622_ = stack[0].m_obj;
lean_object* v_as_2623_ = stack[1].m_obj;
size_t v_i_2624_ = stack[2].m_num;
size_t v_stop_2625_ = stack[3].m_num;
lean_object* v_b_2626_ = stack[4].m_obj;
lean_object* v_res_2639_;
v_res_2639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_2622_, v_as_2623_, v_i_2624_, v_stop_2625_, v_b_2626_);
stack->m_obj
 = v_res_2639_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_2640_, lean_object* v_x_2641_, lean_object* v_x_2642_){
_start:
{
if (lean_obj_tag(v_x_2641_) == 0)
{
lean_object* v_es_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; uint8_t v___x_2646_; 
v_es_2643_ = lean_ctor_get(v_x_2641_, 0);
v___x_2644_ = lean_unsigned_to_nat(0u);
v___x_2645_ = lean_array_get_size(v_es_2643_);
v___x_2646_ = lean_nat_dec_lt(v___x_2644_, v___x_2645_);
if (v___x_2646_ == 0)
{
lean_dec(v_f_2640_);
return v_x_2642_;
}
else
{
size_t v___x_2647_; size_t v___x_2648_; lean_object* v___x_2649_; 
v___x_2647_ = ((size_t)0ULL);
v___x_2648_ = lean_usize_of_nat(v___x_2645_);
v___x_2649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_2640_, v_es_2643_, v___x_2647_, v___x_2648_, v_x_2642_);
return v___x_2649_;
}
}
else
{
lean_object* v_ks_2650_; lean_object* v_vs_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v_ks_2650_ = lean_ctor_get(v_x_2641_, 0);
v_vs_2651_ = lean_ctor_get(v_x_2641_, 1);
v___x_2652_ = lean_unsigned_to_nat(0u);
v___x_2653_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_2640_, v_ks_2650_, v_vs_2651_, v___x_2652_, v_x_2642_);
return v___x_2653_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_2654_, lean_object* v_x_2655_, lean_object* v_x_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2654_, v_x_2655_, v_x_2656_);
lean_dec_ref(v_x_2655_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_f_2658_, lean_object* v_as_2659_, lean_object* v_i_2660_, lean_object* v_stop_2661_, lean_object* v_b_2662_){
_start:
{
size_t v_i_boxed_2663_; size_t v_stop_boxed_2664_; lean_object* v_res_2665_; 
v_i_boxed_2663_ = lean_unbox_usize(v_i_2660_);
lean_dec(v_i_2660_);
v_stop_boxed_2664_ = lean_unbox_usize(v_stop_2661_);
lean_dec(v_stop_2661_);
v_res_2665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_2658_, v_as_2659_, v_i_boxed_2663_, v_stop_boxed_2664_, v_b_2662_);
lean_dec_ref(v_as_2659_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___lam__0(lean_object* v_f_2666_, lean_object* v_x1_2667_, lean_object* v_x2_2668_, lean_object* v_x3_2669_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = lean_apply_3(v_f_2666_, v_x1_2667_, v_x2_2668_, v_x3_2669_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(lean_object* v_map_2671_, lean_object* v_f_2672_, lean_object* v_init_2673_){
_start:
{
lean_object* v___f_2674_; lean_object* v___x_2675_; 
v___f_2674_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2674_, 0, v_f_2672_);
v___x_2675_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v___f_2674_, v_map_2671_, v_init_2673_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___boxed(lean_object* v_map_2676_, lean_object* v_f_2677_, lean_object* v_init_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_map_2676_, v_f_2677_, v_init_2678_);
lean_dec_ref(v_map_2676_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___lam__0(lean_object* v_ps_2680_, lean_object* v_k_2681_, lean_object* v_v_2682_){
_start:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2683_, 0, v_k_2681_);
lean_ctor_set(v___x_2683_, 1, v_v_2682_);
v___x_2684_ = lean_array_push(v_ps_2680_, v___x_2683_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(lean_object* v_m_2688_){
_start:
{
lean_object* v___f_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___f_2689_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__0));
v___x_2690_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__1));
v___x_2691_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_m_2688_, v___f_2689_, v___x_2690_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___boxed(lean_object* v_m_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v_m_2692_);
lean_dec_ref(v_m_2692_);
return v_res_2693_;
}
}
lean_object* l_Lean_Server_partialLspRequestHandlerMethods(){
_start:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2695_ = l_Lean_Server_statefulRequestHandlers;
v___x_2696_ = lean_st_ref_get(v___x_2695_);
v___x_2697_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v___x_2696_);
lean_dec(v___x_2696_);
v___x_2698_ = lean_unsigned_to_nat(0u);
v___x_2699_ = lean_array_get_size(v___x_2697_);
v___x_2700_ = l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(v___x_2697_, v___x_2698_, v___x_2699_);
lean_dec_ref(v___x_2697_);
v___x_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2700_);
return v___x_2701_;
}
}
LEAN_EXPORT void l_Lean_Server_partialLspRequestHandlerMethods_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2702_;
v_res_2702_ = l_Lean_Server_partialLspRequestHandlerMethods();
stack->m_obj
 = v_res_2702_;
}
LEAN_EXPORT lean_object* l_Lean_Server_partialLspRequestHandlerMethods___boxed(lean_object* v_a_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l_Lean_Server_partialLspRequestHandlerMethods();
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0(lean_object* v_00_u03b2_2705_, lean_object* v_m_2706_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v_m_2706_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___boxed(lean_object* v_00_u03b2_2708_, lean_object* v_m_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0(v_00_u03b2_2708_, v_m_2709_);
lean_dec_ref(v_m_2709_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0(lean_object* v_00_u03c3_2711_, lean_object* v_00_u03b2_2712_, lean_object* v_map_2713_, lean_object* v_f_2714_, lean_object* v_init_2715_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_map_2713_, v_f_2714_, v_init_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___boxed(lean_object* v_00_u03c3_2717_, lean_object* v_00_u03b2_2718_, lean_object* v_map_2719_, lean_object* v_f_2720_, lean_object* v_init_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0(v_00_u03c3_2717_, v_00_u03b2_2718_, v_map_2719_, v_f_2720_, v_init_2721_);
lean_dec_ref(v_map_2719_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg(lean_object* v_map_2723_, lean_object* v_f_2724_, lean_object* v_init_2725_){
_start:
{
lean_object* v___x_2726_; 
v___x_2726_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2724_, v_map_2723_, v_init_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_2727_, lean_object* v_f_2728_, lean_object* v_init_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg(v_map_2727_, v_f_2728_, v_init_2729_);
lean_dec_ref(v_map_2727_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_2731_, lean_object* v_00_u03b2_2732_, lean_object* v_map_2733_, lean_object* v_f_2734_, lean_object* v_init_2735_){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2734_, v_map_2733_, v_init_2735_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_2737_, lean_object* v_00_u03b2_2738_, lean_object* v_map_2739_, lean_object* v_f_2740_, lean_object* v_init_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1(v_00_u03c3_2737_, v_00_u03b2_2738_, v_map_2739_, v_f_2740_, v_init_2741_);
lean_dec_ref(v_map_2739_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_2743_, lean_object* v_00_u03b1_2744_, lean_object* v_00_u03b2_2745_, lean_object* v_f_2746_, lean_object* v_x_2747_, lean_object* v_x_2748_){
_start:
{
lean_object* v___x_2749_; 
v___x_2749_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2746_, v_x_2747_, v_x_2748_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_2750_, lean_object* v_00_u03b1_2751_, lean_object* v_00_u03b2_2752_, lean_object* v_f_2753_, lean_object* v_x_2754_, lean_object* v_x_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_2750_, v_00_u03b1_2751_, v_00_u03b2_2752_, v_f_2753_, v_x_2754_, v_x_2755_);
lean_dec_ref(v_x_2754_);
return v_res_2756_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_2757_, lean_object* v_00_u03b2_2758_, lean_object* v_00_u03c3_2759_, lean_object* v_f_2760_, lean_object* v_as_2761_, size_t v_i_2762_, size_t v_stop_2763_, lean_object* v_b_2764_){
_start:
{
lean_object* v___x_2765_; 
v___x_2765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_2760_, v_as_2761_, v_i_2762_, v_stop_2763_, v_b_2764_);
return v___x_2765_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2760_ = stack[3].m_obj;
lean_object* v_as_2761_ = stack[4].m_obj;
size_t v_i_2762_ = stack[5].m_num;
size_t v_stop_2763_ = stack[6].m_num;
lean_object* v_b_2764_ = stack[7].m_obj;
lean_object* v_res_2766_;
v_res_2766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5(lean_box(0), lean_box(0), lean_box(0), v_f_2760_, v_as_2761_, v_i_2762_, v_stop_2763_, v_b_2764_);
stack->m_obj
 = v_res_2766_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2767_, lean_object* v_00_u03b2_2768_, lean_object* v_00_u03c3_2769_, lean_object* v_f_2770_, lean_object* v_as_2771_, lean_object* v_i_2772_, lean_object* v_stop_2773_, lean_object* v_b_2774_){
_start:
{
size_t v_i_boxed_2775_; size_t v_stop_boxed_2776_; lean_object* v_res_2777_; 
v_i_boxed_2775_ = lean_unbox_usize(v_i_2772_);
lean_dec(v_i_2772_);
v_stop_boxed_2776_ = lean_unbox_usize(v_stop_2773_);
lean_dec(v_stop_2773_);
v_res_2777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_2767_, v_00_u03b2_2768_, v_00_u03c3_2769_, v_f_2770_, v_as_2771_, v_i_boxed_2775_, v_stop_boxed_2776_, v_b_2774_);
lean_dec_ref(v_as_2771_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03c3_2778_, lean_object* v_00_u03b1_2779_, lean_object* v_00_u03b2_2780_, lean_object* v_f_2781_, lean_object* v_keys_2782_, lean_object* v_vals_2783_, lean_object* v_heq_2784_, lean_object* v_i_2785_, lean_object* v_acc_2786_){
_start:
{
lean_object* v___x_2787_; 
v___x_2787_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_2781_, v_keys_2782_, v_vals_2783_, v_i_2785_, v_acc_2786_);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03c3_2788_, lean_object* v_00_u03b1_2789_, lean_object* v_00_u03b2_2790_, lean_object* v_f_2791_, lean_object* v_keys_2792_, lean_object* v_vals_2793_, lean_object* v_heq_2794_, lean_object* v_i_2795_, lean_object* v_acc_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6(v_00_u03c3_2788_, v_00_u03b1_2789_, v_00_u03b2_2790_, v_f_2791_, v_keys_2792_, v_vals_2793_, v_heq_2794_, v_i_2795_, v_acc_2796_);
lean_dec_ref(v_vals_2793_);
lean_dec_ref(v_keys_2792_);
return v_res_2797_;
}
}
lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0(lean_object* v_inst_2798_, lean_object* v_pureOnDidChange_2799_, lean_object* v_method_2800_, lean_object* v_onDidChange_2801_, lean_object* v_p_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
lean_inc(v_inst_2798_);
v___x_2806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2806_, 0, v_inst_2798_);
lean_ctor_set(v___x_2806_, 1, v___y_2803_);
lean_inc_ref(v___y_2804_);
lean_inc_ref(v_p_2802_);
v___x_2807_ = lean_apply_4(v_pureOnDidChange_2799_, v_p_2802_, v___x_2806_, v___y_2804_, lean_box(0));
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v_snd_2809_; lean_object* v___x_2810_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2807_, 1);
v_snd_2809_ = lean_ctor_get(v_a_2808_, 1);
lean_inc(v_snd_2809_);
lean_dec(v_a_2808_);
v___x_2810_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_2800_, v_snd_2809_, v_inst_2798_);
lean_dec(v_inst_2798_);
lean_dec(v_snd_2809_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; lean_object* v___x_2812_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2811_);
lean_dec_ref_known(v___x_2810_, 1);
lean_inc_ref(v___y_2804_);
v___x_2812_ = lean_apply_4(v_onDidChange_2801_, v_p_2802_, v_a_2811_, v___y_2804_, lean_box(0));
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2830_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2815_ = v___x_2812_;
v_isShared_2816_ = v_isSharedCheck_2830_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2812_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2830_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v_snd_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2828_; 
v_snd_2817_ = lean_ctor_get(v_a_2813_, 1);
v_isSharedCheck_2828_ = !lean_is_exclusive(v_a_2813_);
if (v_isSharedCheck_2828_ == 0)
{
lean_object* v_unused_2829_; 
v_unused_2829_ = lean_ctor_get(v_a_2813_, 0);
lean_dec(v_unused_2829_);
v___x_2819_ = v_a_2813_;
v_isShared_2820_ = v_isSharedCheck_2828_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_snd_2817_);
lean_dec(v_a_2813_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2828_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2821_; lean_object* v___x_2823_; 
v___x_2821_ = lean_box(0);
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 0, v___x_2821_);
v___x_2823_ = v___x_2819_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2821_);
lean_ctor_set(v_reuseFailAlloc_2827_, 1, v_snd_2817_);
v___x_2823_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
lean_object* v___x_2825_; 
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 0, v___x_2823_);
v___x_2825_ = v___x_2815_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2823_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
}
else
{
return v___x_2812_;
}
}
else
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2838_; 
lean_dec_ref(v_p_2802_);
lean_dec_ref(v_onDidChange_2801_);
v_a_2831_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2833_ = v___x_2810_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2810_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2831_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
}
else
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
lean_dec_ref(v_p_2802_);
lean_dec_ref(v_onDidChange_2801_);
lean_dec(v_inst_2798_);
v_a_2839_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v___x_2807_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2807_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2842_ == 0)
{
v___x_2844_ = v___x_2841_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2798_ = stack[0].m_obj;
lean_object* v_pureOnDidChange_2799_ = stack[1].m_obj;
lean_object* v_method_2800_ = stack[2].m_obj;
lean_object* v_onDidChange_2801_ = stack[3].m_obj;
lean_object* v_p_2802_ = stack[4].m_obj;
lean_object* v___y_2803_ = stack[5].m_obj;
lean_object* v___y_2804_ = stack[6].m_obj;
lean_object* v_res_2847_;
v_res_2847_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0(v_inst_2798_, v_pureOnDidChange_2799_, v_method_2800_, v_onDidChange_2801_, v_p_2802_, v___y_2803_, v___y_2804_);
stack->m_obj
 = v_res_2847_;
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object* v_inst_2848_, lean_object* v_pureOnDidChange_2849_, lean_object* v_method_2850_, lean_object* v_onDidChange_2851_, lean_object* v_p_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0(v_inst_2848_, v_pureOnDidChange_2849_, v_method_2850_, v_onDidChange_2851_, v_p_2852_, v___y_2853_, v___y_2854_);
lean_dec_ref(v___y_2854_);
lean_dec_ref(v_method_2850_);
return v_res_2856_;
}
}
static lean_object* _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2858_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__0));
v___x_2859_ = l_Lean_Server_RequestError_internalError(v___x_2858_);
return v___x_2859_;
}
}
static lean_object* _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2861_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__2));
v___x_2862_ = l_Lean_Server_RequestError_internalError(v___x_2861_);
return v___x_2862_;
}
}
lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1(lean_object* v_inst_2863_, lean_object* v_inst_2864_, lean_object* v_pureHandle_2865_, lean_object* v_inst_2866_, lean_object* v_method_2867_, lean_object* v_handler_2868_, lean_object* v_p_2869_, lean_object* v_s_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
lean_inc(v_p_2869_);
v___x_2873_ = lean_apply_1(v_inst_2863_, v_p_2869_);
lean_inc(v_inst_2864_);
v___x_2874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2874_, 0, v_inst_2864_);
lean_ctor_set(v___x_2874_, 1, v_s_2870_);
lean_inc_ref(v___y_2871_);
v___x_2875_ = lean_apply_4(v_pureHandle_2865_, v___x_2873_, v___x_2874_, v___y_2871_, lean_box(0));
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2910_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2878_ = v___x_2875_;
v_isShared_2879_ = v_isSharedCheck_2910_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2875_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2910_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v_fst_2880_; lean_object* v_snd_2881_; lean_object* v_response_x3f_2882_; lean_object* v_serialized_2883_; uint8_t v_isComplete_2884_; lean_object* v_a_2886_; 
v_fst_2880_ = lean_ctor_get(v_a_2876_, 0);
lean_inc(v_fst_2880_);
v_snd_2881_ = lean_ctor_get(v_a_2876_, 1);
lean_inc(v_snd_2881_);
lean_dec(v_a_2876_);
v_response_x3f_2882_ = lean_ctor_get(v_fst_2880_, 0);
lean_inc(v_response_x3f_2882_);
v_serialized_2883_ = lean_ctor_get(v_fst_2880_, 1);
lean_inc_ref(v_serialized_2883_);
v_isComplete_2884_ = lean_ctor_get_uint8(v_fst_2880_, sizeof(void*)*2);
lean_dec(v_fst_2880_);
if (lean_obj_tag(v_response_x3f_2882_) == 0)
{
lean_object* v___x_2905_; 
v___x_2905_ = l_Lean_Json_parse(v_serialized_2883_);
if (lean_obj_tag(v___x_2905_) == 1)
{
lean_object* v_a_2906_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_a_2906_);
lean_dec_ref_known(v___x_2905_, 1);
v_a_2886_ = v_a_2906_;
goto v___jp_2885_;
}
else
{
lean_object* v___x_2907_; lean_object* v___x_2908_; 
lean_dec_ref(v___x_2905_);
lean_dec(v_snd_2881_);
lean_del_object(v___x_2878_);
lean_dec(v_p_2869_);
lean_dec_ref(v_handler_2868_);
lean_dec_ref(v_inst_2866_);
lean_dec(v_inst_2864_);
v___x_2907_ = lean_obj_once(&l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3, &l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3_once, _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3);
v___x_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2907_);
return v___x_2908_;
}
}
else
{
lean_object* v_val_2909_; 
lean_dec_ref(v_serialized_2883_);
v_val_2909_ = lean_ctor_get(v_response_x3f_2882_, 0);
lean_inc(v_val_2909_);
lean_dec_ref_known(v_response_x3f_2882_, 1);
v_a_2886_ = v_val_2909_;
goto v___jp_2885_;
}
v___jp_2885_:
{
lean_object* v___x_2887_; 
v___x_2887_ = lean_apply_1(v_inst_2866_, v_a_2886_);
if (lean_obj_tag(v___x_2887_) == 1)
{
lean_object* v_a_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
lean_del_object(v___x_2878_);
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref_known(v___x_2887_, 1);
v___x_2889_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2889_, 0, v_a_2888_);
lean_ctor_set_uint8(v___x_2889_, sizeof(void*)*1, v_isComplete_2884_);
v___x_2890_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_2867_, v_snd_2881_, v_inst_2864_);
lean_dec(v_inst_2864_);
lean_dec(v_snd_2881_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2892_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc(v_a_2891_);
lean_dec_ref_known(v___x_2890_, 1);
lean_inc_ref(v___y_2871_);
v___x_2892_ = lean_apply_5(v_handler_2868_, v_p_2869_, v___x_2889_, v_a_2891_, v___y_2871_, lean_box(0));
return v___x_2892_;
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
lean_dec_ref_known(v___x_2889_, 1);
lean_dec(v_p_2869_);
lean_dec_ref(v_handler_2868_);
v_a_2893_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___x_2890_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2890_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2893_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
else
{
lean_object* v___x_2901_; lean_object* v___x_2903_; 
lean_dec_ref(v___x_2887_);
lean_dec(v_snd_2881_);
lean_dec(v_p_2869_);
lean_dec_ref(v_handler_2868_);
lean_dec(v_inst_2864_);
v___x_2901_ = lean_obj_once(&l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1, &l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1_once, _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1);
if (v_isShared_2879_ == 0)
{
lean_ctor_set_tag(v___x_2878_, 1);
lean_ctor_set(v___x_2878_, 0, v___x_2901_);
v___x_2903_ = v___x_2878_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v___x_2901_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
}
else
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
lean_dec(v_p_2869_);
lean_dec_ref(v_handler_2868_);
lean_dec_ref(v_inst_2866_);
lean_dec(v_inst_2864_);
v_a_2911_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2875_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2875_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2863_ = stack[0].m_obj;
lean_object* v_inst_2864_ = stack[1].m_obj;
lean_object* v_pureHandle_2865_ = stack[2].m_obj;
lean_object* v_inst_2866_ = stack[3].m_obj;
lean_object* v_method_2867_ = stack[4].m_obj;
lean_object* v_handler_2868_ = stack[5].m_obj;
lean_object* v_p_2869_ = stack[6].m_obj;
lean_object* v_s_2870_ = stack[7].m_obj;
lean_object* v___y_2871_ = stack[8].m_obj;
lean_object* v_res_2919_;
v_res_2919_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1(v_inst_2863_, v_inst_2864_, v_pureHandle_2865_, v_inst_2866_, v_method_2867_, v_handler_2868_, v_p_2869_, v_s_2870_, v___y_2871_);
stack->m_obj
 = v_res_2919_;
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___boxed(lean_object* v_inst_2920_, lean_object* v_inst_2921_, lean_object* v_pureHandle_2922_, lean_object* v_inst_2923_, lean_object* v_method_2924_, lean_object* v_handler_2925_, lean_object* v_p_2926_, lean_object* v_s_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1(v_inst_2920_, v_inst_2921_, v_pureHandle_2922_, v_inst_2923_, v_method_2924_, v_handler_2925_, v_p_2926_, v_s_2927_, v___y_2928_);
lean_dec_ref(v___y_2928_);
lean_dec_ref(v_method_2924_);
return v_res_2930_;
}
}
lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg(lean_object* v_method_2932_, lean_object* v_inst_2933_, lean_object* v_inst_2934_, lean_object* v_inst_2935_, lean_object* v_inst_2936_, lean_object* v_inst_2937_, lean_object* v_inst_2938_, lean_object* v_handler_2939_, lean_object* v_onDidChange_2940_){
_start:
{
uint8_t v___x_2942_; 
v___x_2942_ = l_Lean_initializing();
if (v___x_2942_ == 0)
{
lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
lean_dec_ref(v_onDidChange_2940_);
lean_dec_ref(v_handler_2939_);
lean_dec(v_inst_2938_);
lean_dec_ref(v_inst_2937_);
lean_dec_ref(v_inst_2936_);
lean_dec_ref(v_inst_2935_);
lean_dec_ref(v_inst_2934_);
lean_dec_ref(v_inst_2933_);
v___x_2943_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0));
v___x_2944_ = lean_string_append(v___x_2943_, v_method_2932_);
lean_dec_ref(v_method_2932_);
v___x_2945_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___x_2946_ = lean_string_append(v___x_2944_, v___x_2945_);
v___x_2947_ = lean_mk_io_user_error(v___x_2946_);
v___x_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
return v___x_2948_;
}
else
{
lean_object* v___x_2949_; 
v___x_2949_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_2932_);
if (lean_obj_tag(v___x_2949_) == 1)
{
lean_object* v_val_2950_; lean_object* v_pureHandle_2951_; lean_object* v_pureOnDidChange_2952_; lean_object* v_initState_2953_; lean_object* v_completeness_2954_; lean_object* v___f_2955_; lean_object* v___f_2956_; lean_object* v___x_2957_; 
v_val_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_val_2950_);
lean_dec_ref_known(v___x_2949_, 1);
v_pureHandle_2951_ = lean_ctor_get(v_val_2950_, 1);
lean_inc_ref(v_pureHandle_2951_);
v_pureOnDidChange_2952_ = lean_ctor_get(v_val_2950_, 3);
lean_inc_ref(v_pureOnDidChange_2952_);
v_initState_2953_ = lean_ctor_get(v_val_2950_, 6);
lean_inc(v_initState_2953_);
v_completeness_2954_ = lean_ctor_get(v_val_2950_, 8);
lean_inc(v_completeness_2954_);
lean_dec(v_val_2950_);
lean_inc_ref_n(v_method_2932_, 2);
lean_inc_n(v_inst_2938_, 2);
v___f_2955_ = lean_alloc_closure((void*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_2955_, 0, v_inst_2938_);
lean_closure_set(v___f_2955_, 1, v_pureOnDidChange_2952_);
lean_closure_set(v___f_2955_, 2, v_method_2932_);
lean_closure_set(v___f_2955_, 3, v_onDidChange_2940_);
v___f_2956_ = lean_alloc_closure((void*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___boxed), 10, 6);
lean_closure_set(v___f_2956_, 0, v_inst_2934_);
lean_closure_set(v___f_2956_, 1, v_inst_2938_);
lean_closure_set(v___f_2956_, 2, v_pureHandle_2951_);
lean_closure_set(v___f_2956_, 3, v_inst_2936_);
lean_closure_set(v___f_2956_, 4, v_method_2932_);
lean_closure_set(v___f_2956_, 5, v_handler_2939_);
v___x_2957_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(v_method_2932_, v_initState_2953_, v_inst_2938_);
lean_dec(v_initState_2953_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___x_2959_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_a_2958_);
lean_dec_ref_known(v___x_2957_, 1);
v___x_2959_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2932_, v_completeness_2954_, v_inst_2933_, v_inst_2935_, v_inst_2937_, v_inst_2938_, v_a_2958_, v___f_2956_, v___f_2955_);
return v___x_2959_;
}
else
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2967_; 
lean_dec_ref(v___f_2956_);
lean_dec_ref(v___f_2955_);
lean_dec(v_completeness_2954_);
lean_dec(v_inst_2938_);
lean_dec_ref(v_inst_2937_);
lean_dec_ref(v_inst_2935_);
lean_dec_ref(v_inst_2933_);
lean_dec_ref(v_method_2932_);
v_a_2960_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2962_ = v___x_2957_;
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2957_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2965_; 
if (v_isShared_2963_ == 0)
{
v___x_2965_ = v___x_2962_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2960_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
}
else
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
lean_dec(v___x_2949_);
lean_dec_ref(v_onDidChange_2940_);
lean_dec_ref(v_handler_2939_);
lean_dec(v_inst_2938_);
lean_dec_ref(v_inst_2937_);
lean_dec_ref(v_inst_2936_);
lean_dec_ref(v_inst_2935_);
lean_dec_ref(v_inst_2934_);
lean_dec_ref(v_inst_2933_);
v___x_2968_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0));
v___x_2969_ = lean_string_append(v___x_2968_, v_method_2932_);
lean_dec_ref(v_method_2932_);
v___x_2970_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__1));
v___x_2971_ = lean_string_append(v___x_2969_, v___x_2970_);
v___x_2972_ = lean_mk_io_user_error(v___x_2971_);
v___x_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2972_);
return v___x_2973_;
}
}
}
}
LEAN_EXPORT void l_Lean_Server_chainStatefulLspRequestHandler___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_2932_ = stack[0].m_obj;
lean_object* v_inst_2933_ = stack[1].m_obj;
lean_object* v_inst_2934_ = stack[2].m_obj;
lean_object* v_inst_2935_ = stack[3].m_obj;
lean_object* v_inst_2936_ = stack[4].m_obj;
lean_object* v_inst_2937_ = stack[5].m_obj;
lean_object* v_inst_2938_ = stack[6].m_obj;
lean_object* v_handler_2939_ = stack[7].m_obj;
lean_object* v_onDidChange_2940_ = stack[8].m_obj;
lean_object* v_res_2974_;
v_res_2974_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg(v_method_2932_, v_inst_2933_, v_inst_2934_, v_inst_2935_, v_inst_2936_, v_inst_2937_, v_inst_2938_, v_handler_2939_, v_onDidChange_2940_);
stack->m_obj
 = v_res_2974_;
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2975_, lean_object* v_inst_2976_, lean_object* v_inst_2977_, lean_object* v_inst_2978_, lean_object* v_inst_2979_, lean_object* v_inst_2980_, lean_object* v_inst_2981_, lean_object* v_handler_2982_, lean_object* v_onDidChange_2983_, lean_object* v_a_2984_){
_start:
{
lean_object* v_res_2985_; 
v_res_2985_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg(v_method_2975_, v_inst_2976_, v_inst_2977_, v_inst_2978_, v_inst_2979_, v_inst_2980_, v_inst_2981_, v_handler_2982_, v_onDidChange_2983_);
return v_res_2985_;
}
}
lean_object* l_Lean_Server_chainStatefulLspRequestHandler(lean_object* v_method_2986_, lean_object* v_paramType_2987_, lean_object* v_inst_2988_, lean_object* v_inst_2989_, lean_object* v_inst_2990_, lean_object* v_respType_2991_, lean_object* v_inst_2992_, lean_object* v_inst_2993_, lean_object* v_stateType_2994_, lean_object* v_inst_2995_, lean_object* v_handler_2996_, lean_object* v_onDidChange_2997_){
_start:
{
lean_object* v___x_2999_; 
v___x_2999_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg(v_method_2986_, v_inst_2988_, v_inst_2989_, v_inst_2990_, v_inst_2992_, v_inst_2993_, v_inst_2995_, v_handler_2996_, v_onDidChange_2997_);
return v___x_2999_;
}
}
LEAN_EXPORT void l_Lean_Server_chainStatefulLspRequestHandler_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_2986_ = stack[0].m_obj;
lean_object* v_inst_2988_ = stack[2].m_obj;
lean_object* v_inst_2989_ = stack[3].m_obj;
lean_object* v_inst_2990_ = stack[4].m_obj;
lean_object* v_inst_2992_ = stack[6].m_obj;
lean_object* v_inst_2993_ = stack[7].m_obj;
lean_object* v_inst_2995_ = stack[9].m_obj;
lean_object* v_handler_2996_ = stack[10].m_obj;
lean_object* v_onDidChange_2997_ = stack[11].m_obj;
lean_object* v_res_3000_;
v_res_3000_ = l_Lean_Server_chainStatefulLspRequestHandler(v_method_2986_, lean_box(0), v_inst_2988_, v_inst_2989_, v_inst_2990_, lean_box(0), v_inst_2992_, v_inst_2993_, lean_box(0), v_inst_2995_, v_handler_2996_, v_onDidChange_2997_);
stack->m_obj
 = v_res_3000_;
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___boxed(lean_object* v_method_3001_, lean_object* v_paramType_3002_, lean_object* v_inst_3003_, lean_object* v_inst_3004_, lean_object* v_inst_3005_, lean_object* v_respType_3006_, lean_object* v_inst_3007_, lean_object* v_inst_3008_, lean_object* v_stateType_3009_, lean_object* v_inst_3010_, lean_object* v_handler_3011_, lean_object* v_onDidChange_3012_, lean_object* v_a_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l_Lean_Server_chainStatefulLspRequestHandler(v_method_3001_, v_paramType_3002_, v_inst_3003_, v_inst_3004_, v_inst_3005_, v_respType_3006_, v_inst_3007_, v_inst_3008_, v_stateType_3009_, v_inst_3010_, v_handler_3011_, v_onDidChange_3012_);
return v_res_3014_;
}
}
lean_object* l_Lean_Server_handleOnDidChange___lam__0(lean_object* v_p_3015_, lean_object* v_x_3016_, lean_object* v_handler_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v_onDidChange_3020_; lean_object* v___x_3021_; 
v_onDidChange_3020_ = lean_ctor_get(v_handler_3017_, 4);
lean_inc_ref(v_onDidChange_3020_);
lean_dec_ref(v_handler_3017_);
lean_inc_ref(v___y_3018_);
v___x_3021_ = lean_apply_3(v_onDidChange_3020_, v_p_3015_, v___y_3018_, lean_box(0));
return v___x_3021_;
}
}
LEAN_EXPORT void l_Lean_Server_handleOnDidChange___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3015_ = stack[0].m_obj;
lean_object* v_x_3016_ = stack[1].m_obj;
lean_object* v_handler_3017_ = stack[2].m_obj;
lean_object* v___y_3018_ = stack[3].m_obj;
lean_object* v_res_3022_;
v_res_3022_ = l_Lean_Server_handleOnDidChange___lam__0(v_p_3015_, v_x_3016_, v_handler_3017_, v___y_3018_);
stack->m_obj
 = v_res_3022_;
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___lam__0___boxed(lean_object* v_p_3023_, lean_object* v_x_3024_, lean_object* v_handler_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Lean_Server_handleOnDidChange___lam__0(v_p_3023_, v_x_3024_, v_handler_3025_, v___y_3026_);
lean_dec_ref(v___y_3026_);
lean_dec_ref(v_x_3024_);
return v_res_3028_;
}
}
lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0(lean_object* v_f_3029_, lean_object* v_x_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_){
_start:
{
lean_object* v___x_3035_; 
lean_inc_ref(v___y_3033_);
v___x_3035_ = lean_apply_4(v_f_3029_, v___y_3031_, v___y_3032_, v___y_3033_, lean_box(0));
return v___x_3035_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3029_ = stack[0].m_obj;
lean_object* v_x_3030_ = stack[1].m_obj;
lean_object* v___y_3031_ = stack[2].m_obj;
lean_object* v___y_3032_ = stack[3].m_obj;
lean_object* v___y_3033_ = stack[4].m_obj;
lean_object* v_res_3036_;
v_res_3036_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0(v_f_3029_, v_x_3030_, v___y_3031_, v___y_3032_, v___y_3033_);
stack->m_obj
 = v_res_3036_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0___boxed(lean_object* v_f_3037_, lean_object* v_x_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0(v_f_3037_, v_x_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
lean_dec_ref(v___y_3041_);
return v_res_3043_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_3044_, lean_object* v_keys_3045_, lean_object* v_vals_3046_, lean_object* v_i_3047_, lean_object* v_acc_3048_, lean_object* v___y_3049_){
_start:
{
lean_object* v___x_3051_; uint8_t v___x_3052_; 
v___x_3051_ = lean_array_get_size(v_keys_3045_);
v___x_3052_ = lean_nat_dec_lt(v_i_3047_, v___x_3051_);
if (v___x_3052_ == 0)
{
lean_object* v___x_3053_; 
lean_dec(v_i_3047_);
lean_dec_ref(v_f_3044_);
v___x_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3053_, 0, v_acc_3048_);
return v___x_3053_;
}
else
{
lean_object* v_k_3054_; lean_object* v_v_3055_; lean_object* v___x_3056_; 
v_k_3054_ = lean_array_fget_borrowed(v_keys_3045_, v_i_3047_);
v_v_3055_ = lean_array_fget_borrowed(v_vals_3046_, v_i_3047_);
lean_inc_ref(v_f_3044_);
lean_inc_ref(v___y_3049_);
lean_inc(v_v_3055_);
lean_inc(v_k_3054_);
v___x_3056_ = lean_apply_5(v_f_3044_, v_acc_3048_, v_k_3054_, v_v_3055_, v___y_3049_, lean_box(0));
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v_a_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_a_3057_);
lean_dec_ref_known(v___x_3056_, 1);
v___x_3058_ = lean_unsigned_to_nat(1u);
v___x_3059_ = lean_nat_add(v_i_3047_, v___x_3058_);
lean_dec(v_i_3047_);
v_i_3047_ = v___x_3059_;
v_acc_3048_ = v_a_3057_;
goto _start;
}
else
{
lean_dec(v_i_3047_);
lean_dec_ref(v_f_3044_);
return v___x_3056_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3044_ = stack[0].m_obj;
lean_object* v_keys_3045_ = stack[1].m_obj;
lean_object* v_vals_3046_ = stack[2].m_obj;
lean_object* v_i_3047_ = stack[3].m_obj;
lean_object* v_acc_3048_ = stack[4].m_obj;
lean_object* v___y_3049_ = stack[5].m_obj;
lean_object* v_res_3061_;
v_res_3061_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3044_, v_keys_3045_, v_vals_3046_, v_i_3047_, v_acc_3048_, v___y_3049_);
stack->m_obj
 = v_res_3061_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_3062_, lean_object* v_keys_3063_, lean_object* v_vals_3064_, lean_object* v_i_3065_, lean_object* v_acc_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3062_, v_keys_3063_, v_vals_3064_, v_i_3065_, v_acc_3066_, v___y_3067_);
lean_dec_ref(v___y_3067_);
lean_dec_ref(v_vals_3064_);
lean_dec_ref(v_keys_3063_);
return v_res_3069_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_3070_, lean_object* v_as_3071_, size_t v_i_3072_, size_t v_stop_3073_, lean_object* v_b_3074_, lean_object* v___y_3075_){
_start:
{
lean_object* v_a_3078_; lean_object* v___y_3083_; uint8_t v___x_3085_; 
v___x_3085_ = lean_usize_dec_eq(v_i_3072_, v_stop_3073_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; 
v___x_3086_ = lean_array_uget_borrowed(v_as_3071_, v_i_3072_);
switch(lean_obj_tag(v___x_3086_))
{
case 0:
{
lean_object* v_key_3087_; lean_object* v_val_3088_; lean_object* v___x_3089_; 
v_key_3087_ = lean_ctor_get(v___x_3086_, 0);
v_val_3088_ = lean_ctor_get(v___x_3086_, 1);
lean_inc_ref(v_f_3070_);
lean_inc_ref(v___y_3075_);
lean_inc(v_val_3088_);
lean_inc(v_key_3087_);
v___x_3089_ = lean_apply_5(v_f_3070_, v_b_3074_, v_key_3087_, v_val_3088_, v___y_3075_, lean_box(0));
v___y_3083_ = v___x_3089_;
goto v___jp_3082_;
}
case 1:
{
lean_object* v_node_3090_; lean_object* v___x_3091_; 
v_node_3090_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_node_3090_);
lean_inc_ref(v_f_3070_);
v___x_3091_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3070_, v_node_3090_, v_b_3074_, v___y_3075_);
v___y_3083_ = v___x_3091_;
goto v___jp_3082_;
}
default: 
{
v_a_3078_ = v_b_3074_;
goto v___jp_3077_;
}
}
}
else
{
lean_object* v___x_3092_; 
lean_dec_ref(v_f_3070_);
v___x_3092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3092_, 0, v_b_3074_);
return v___x_3092_;
}
v___jp_3077_:
{
size_t v___x_3079_; size_t v___x_3080_; 
v___x_3079_ = ((size_t)1ULL);
v___x_3080_ = lean_usize_add(v_i_3072_, v___x_3079_);
v_i_3072_ = v___x_3080_;
v_b_3074_ = v_a_3078_;
goto _start;
}
v___jp_3082_:
{
if (lean_obj_tag(v___y_3083_) == 0)
{
lean_object* v_a_3084_; 
v_a_3084_ = lean_ctor_get(v___y_3083_, 0);
lean_inc(v_a_3084_);
lean_dec_ref_known(v___y_3083_, 1);
v_a_3078_ = v_a_3084_;
goto v___jp_3077_;
}
else
{
lean_dec_ref(v_f_3070_);
return v___y_3083_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3070_ = stack[0].m_obj;
lean_object* v_as_3071_ = stack[1].m_obj;
size_t v_i_3072_ = stack[2].m_num;
size_t v_stop_3073_ = stack[3].m_num;
lean_object* v_b_3074_ = stack[4].m_obj;
lean_object* v___y_3075_ = stack[5].m_obj;
lean_object* v_res_3093_;
v_res_3093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3070_, v_as_3071_, v_i_3072_, v_stop_3073_, v_b_3074_, v___y_3075_);
stack->m_obj
 = v_res_3093_;
}
lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(lean_object* v_f_3094_, lean_object* v_x_3095_, lean_object* v_x_3096_, lean_object* v___y_3097_){
_start:
{
if (lean_obj_tag(v_x_3095_) == 0)
{
lean_object* v_es_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3112_; 
v_es_3099_ = lean_ctor_get(v_x_3095_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v_x_3095_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3101_ = v_x_3095_;
v_isShared_3102_ = v_isSharedCheck_3112_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_es_3099_);
lean_dec(v_x_3095_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3112_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; uint8_t v___x_3105_; 
v___x_3103_ = lean_unsigned_to_nat(0u);
v___x_3104_ = lean_array_get_size(v_es_3099_);
v___x_3105_ = lean_nat_dec_lt(v___x_3103_, v___x_3104_);
if (v___x_3105_ == 0)
{
lean_object* v___x_3107_; 
lean_dec_ref(v_es_3099_);
lean_dec_ref(v_f_3094_);
if (v_isShared_3102_ == 0)
{
lean_ctor_set(v___x_3101_, 0, v_x_3096_);
v___x_3107_ = v___x_3101_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_x_3096_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
else
{
size_t v___x_3109_; size_t v___x_3110_; lean_object* v___x_3111_; 
lean_del_object(v___x_3101_);
v___x_3109_ = ((size_t)0ULL);
v___x_3110_ = lean_usize_of_nat(v___x_3104_);
v___x_3111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3094_, v_es_3099_, v___x_3109_, v___x_3110_, v_x_3096_, v___y_3097_);
lean_dec_ref(v_es_3099_);
return v___x_3111_;
}
}
}
else
{
lean_object* v_ks_3113_; lean_object* v_vs_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v_ks_3113_ = lean_ctor_get(v_x_3095_, 0);
lean_inc_ref(v_ks_3113_);
v_vs_3114_ = lean_ctor_get(v_x_3095_, 1);
lean_inc_ref(v_vs_3114_);
lean_dec_ref_known(v_x_3095_, 2);
v___x_3115_ = lean_unsigned_to_nat(0u);
v___x_3116_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3094_, v_ks_3113_, v_vs_3114_, v___x_3115_, v_x_3096_, v___y_3097_);
lean_dec_ref(v_vs_3114_);
lean_dec_ref(v_ks_3113_);
return v___x_3116_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3094_ = stack[0].m_obj;
lean_object* v_x_3095_ = stack[1].m_obj;
lean_object* v_x_3096_ = stack[2].m_obj;
lean_object* v___y_3097_ = stack[3].m_obj;
lean_object* v_res_3117_;
v_res_3117_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3094_, v_x_3095_, v_x_3096_, v___y_3097_);
stack->m_obj
 = v_res_3117_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_3118_, lean_object* v_x_3119_, lean_object* v_x_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3118_, v_x_3119_, v_x_3120_, v___y_3121_);
lean_dec_ref(v___y_3121_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_3124_, lean_object* v_as_3125_, lean_object* v_i_3126_, lean_object* v_stop_3127_, lean_object* v_b_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_){
_start:
{
size_t v_i_boxed_3131_; size_t v_stop_boxed_3132_; lean_object* v_res_3133_; 
v_i_boxed_3131_ = lean_unbox_usize(v_i_3126_);
lean_dec(v_i_3126_);
v_stop_boxed_3132_ = lean_unbox_usize(v_stop_3127_);
lean_dec(v_stop_3127_);
v_res_3133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3124_, v_as_3125_, v_i_boxed_3131_, v_stop_boxed_3132_, v_b_3128_, v___y_3129_);
lean_dec_ref(v___y_3129_);
lean_dec_ref(v_as_3125_);
return v_res_3133_;
}
}
lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(lean_object* v_map_3134_, lean_object* v_f_3135_, lean_object* v___y_3136_){
_start:
{
lean_object* v___f_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___f_3138_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3138_, 0, v_f_3135_);
v___x_3139_ = lean_box(0);
v___x_3140_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v___f_3138_, v_map_3134_, v___x_3139_, v___y_3136_);
return v___x_3140_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_3134_ = stack[0].m_obj;
lean_object* v_f_3135_ = stack[1].m_obj;
lean_object* v___y_3136_ = stack[2].m_obj;
lean_object* v_res_3141_;
v_res_3141_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(v_map_3134_, v_f_3135_, v___y_3136_);
stack->m_obj
 = v_res_3141_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___boxed(lean_object* v_map_3142_, lean_object* v_f_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(v_map_3142_, v_f_3143_, v___y_3144_);
lean_dec_ref(v___y_3144_);
return v_res_3146_;
}
}
lean_object* l_Lean_Server_handleOnDidChange(lean_object* v_p_3147_, lean_object* v_a_3148_){
_start:
{
lean_object* v___f_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___f_3150_ = lean_alloc_closure((void*)(l_Lean_Server_handleOnDidChange___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3150_, 0, v_p_3147_);
v___x_3151_ = l_Lean_Server_statefulRequestHandlers;
v___x_3152_ = lean_st_ref_get(v___x_3151_);
v___x_3153_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(v___x_3152_, v___f_3150_, v_a_3148_);
return v___x_3153_;
}
}
LEAN_EXPORT void l_Lean_Server_handleOnDidChange_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3147_ = stack[0].m_obj;
lean_object* v_a_3148_ = stack[1].m_obj;
lean_object* v_res_3154_;
v_res_3154_ = l_Lean_Server_handleOnDidChange(v_p_3147_, v_a_3148_);
stack->m_obj
 = v_res_3154_;
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___boxed(lean_object* v_p_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l_Lean_Server_handleOnDidChange(v_p_3155_, v_a_3156_);
lean_dec_ref(v_a_3156_);
return v_res_3158_;
}
}
lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0(lean_object* v_00_u03b2_3159_, lean_object* v_map_3160_, lean_object* v_f_3161_, lean_object* v___y_3162_){
_start:
{
lean_object* v___x_3164_; 
v___x_3164_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(v_map_3160_, v_f_3161_, v___y_3162_);
return v___x_3164_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_3160_ = stack[1].m_obj;
lean_object* v_f_3161_ = stack[2].m_obj;
lean_object* v___y_3162_ = stack[3].m_obj;
lean_object* v_res_3165_;
v_res_3165_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0(lean_box(0), v_map_3160_, v_f_3161_, v___y_3162_);
stack->m_obj
 = v_res_3165_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___boxed(lean_object* v_00_u03b2_3166_, lean_object* v_map_3167_, lean_object* v_f_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0(v_00_u03b2_3166_, v_map_3167_, v_f_3168_, v___y_3169_);
lean_dec_ref(v___y_3169_);
return v_res_3171_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg(lean_object* v_map_3172_, lean_object* v_f_3173_, lean_object* v_init_3174_, lean_object* v___y_3175_){
_start:
{
lean_object* v___x_3177_; 
v___x_3177_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3173_, v_map_3172_, v_init_3174_, v___y_3175_);
return v___x_3177_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_3172_ = stack[0].m_obj;
lean_object* v_f_3173_ = stack[1].m_obj;
lean_object* v_init_3174_ = stack[2].m_obj;
lean_object* v___y_3175_ = stack[3].m_obj;
lean_object* v_res_3178_;
v_res_3178_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg(v_map_3172_, v_f_3173_, v_init_3174_, v___y_3175_);
stack->m_obj
 = v_res_3178_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg___boxed(lean_object* v_map_3179_, lean_object* v_f_3180_, lean_object* v_init_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v_res_3184_; 
v_res_3184_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg(v_map_3179_, v_f_3180_, v_init_3181_, v___y_3182_);
lean_dec_ref(v___y_3182_);
return v_res_3184_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0(lean_object* v_00_u03c3_3185_, lean_object* v_00_u03b2_3186_, lean_object* v_map_3187_, lean_object* v_f_3188_, lean_object* v_init_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v___x_3192_; 
v___x_3192_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3188_, v_map_3187_, v_init_3189_, v___y_3190_);
return v___x_3192_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_3187_ = stack[2].m_obj;
lean_object* v_f_3188_ = stack[3].m_obj;
lean_object* v_init_3189_ = stack[4].m_obj;
lean_object* v___y_3190_ = stack[5].m_obj;
lean_object* v_res_3193_;
v_res_3193_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0(lean_box(0), lean_box(0), v_map_3187_, v_f_3188_, v_init_3189_, v___y_3190_);
stack->m_obj
 = v_res_3193_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3194_, lean_object* v_00_u03b2_3195_, lean_object* v_map_3196_, lean_object* v_f_3197_, lean_object* v_init_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0(v_00_u03c3_3194_, v_00_u03b2_3195_, v_map_3196_, v_f_3197_, v_init_3198_, v___y_3199_);
lean_dec_ref(v___y_3199_);
return v_res_3201_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3202_, lean_object* v_00_u03b1_3203_, lean_object* v_00_u03b2_3204_, lean_object* v_f_3205_, lean_object* v_x_3206_, lean_object* v_x_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v___x_3210_; 
v___x_3210_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3205_, v_x_3206_, v_x_3207_, v___y_3208_);
return v___x_3210_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3205_ = stack[3].m_obj;
lean_object* v_x_3206_ = stack[4].m_obj;
lean_object* v_x_3207_ = stack[5].m_obj;
lean_object* v___y_3208_ = stack[6].m_obj;
lean_object* v_res_3211_;
v_res_3211_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1(lean_box(0), lean_box(0), lean_box(0), v_f_3205_, v_x_3206_, v_x_3207_, v___y_3208_);
stack->m_obj
 = v_res_3211_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3212_, lean_object* v_00_u03b1_3213_, lean_object* v_00_u03b2_3214_, lean_object* v_f_3215_, lean_object* v_x_3216_, lean_object* v_x_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v_res_3220_; 
v_res_3220_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1(v_00_u03c3_3212_, v_00_u03b1_3213_, v_00_u03b2_3214_, v_f_3215_, v_x_3216_, v_x_3217_, v___y_3218_);
lean_dec_ref(v___y_3218_);
return v_res_3220_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3221_, lean_object* v_00_u03b2_3222_, lean_object* v_00_u03c3_3223_, lean_object* v_f_3224_, lean_object* v_as_3225_, size_t v_i_3226_, size_t v_stop_3227_, lean_object* v_b_3228_, lean_object* v___y_3229_){
_start:
{
lean_object* v___x_3231_; 
v___x_3231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3224_, v_as_3225_, v_i_3226_, v_stop_3227_, v_b_3228_, v___y_3229_);
return v___x_3231_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3224_ = stack[3].m_obj;
lean_object* v_as_3225_ = stack[4].m_obj;
size_t v_i_3226_ = stack[5].m_num;
size_t v_stop_3227_ = stack[6].m_num;
lean_object* v_b_3228_ = stack[7].m_obj;
lean_object* v___y_3229_ = stack[8].m_obj;
lean_object* v_res_3232_;
v_res_3232_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2(lean_box(0), lean_box(0), lean_box(0), v_f_3224_, v_as_3225_, v_i_3226_, v_stop_3227_, v_b_3228_, v___y_3229_);
stack->m_obj
 = v_res_3232_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3233_, lean_object* v_00_u03b2_3234_, lean_object* v_00_u03c3_3235_, lean_object* v_f_3236_, lean_object* v_as_3237_, lean_object* v_i_3238_, lean_object* v_stop_3239_, lean_object* v_b_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
size_t v_i_boxed_3243_; size_t v_stop_boxed_3244_; lean_object* v_res_3245_; 
v_i_boxed_3243_ = lean_unbox_usize(v_i_3238_);
lean_dec(v_i_3238_);
v_stop_boxed_3244_ = lean_unbox_usize(v_stop_3239_);
lean_dec(v_stop_3239_);
v_res_3245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3233_, v_00_u03b2_3234_, v_00_u03c3_3235_, v_f_3236_, v_as_3237_, v_i_boxed_3243_, v_stop_boxed_3244_, v_b_3240_, v___y_3241_);
lean_dec_ref(v___y_3241_);
lean_dec_ref(v_as_3237_);
return v_res_3245_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3246_, lean_object* v_00_u03b1_3247_, lean_object* v_00_u03b2_3248_, lean_object* v_f_3249_, lean_object* v_keys_3250_, lean_object* v_vals_3251_, lean_object* v_heq_3252_, lean_object* v_i_3253_, lean_object* v_acc_3254_, lean_object* v___y_3255_){
_start:
{
lean_object* v___x_3257_; 
v___x_3257_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3249_, v_keys_3250_, v_vals_3251_, v_i_3253_, v_acc_3254_, v___y_3255_);
return v___x_3257_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3249_ = stack[3].m_obj;
lean_object* v_keys_3250_ = stack[4].m_obj;
lean_object* v_vals_3251_ = stack[5].m_obj;
lean_object* v_i_3253_ = stack[7].m_obj;
lean_object* v_acc_3254_ = stack[8].m_obj;
lean_object* v___y_3255_ = stack[9].m_obj;
lean_object* v_res_3258_;
v_res_3258_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3(lean_box(0), lean_box(0), lean_box(0), v_f_3249_, v_keys_3250_, v_vals_3251_, lean_box(0), v_i_3253_, v_acc_3254_, v___y_3255_);
stack->m_obj
 = v_res_3258_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3259_, lean_object* v_00_u03b1_3260_, lean_object* v_00_u03b2_3261_, lean_object* v_f_3262_, lean_object* v_keys_3263_, lean_object* v_vals_3264_, lean_object* v_heq_3265_, lean_object* v_i_3266_, lean_object* v_acc_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
_start:
{
lean_object* v_res_3270_; 
v_res_3270_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3259_, v_00_u03b1_3260_, v_00_u03b2_3261_, v_f_3262_, v_keys_3263_, v_vals_3264_, v_heq_3265_, v_i_3266_, v_acc_3267_, v___y_3268_);
lean_dec_ref(v___y_3268_);
lean_dec_ref(v_vals_3264_);
lean_dec_ref(v_keys_3263_);
return v_res_3270_;
}
}
lean_object* l_Lean_Server_handleLspRequest(lean_object* v_method_3273_, lean_object* v_params_3274_, lean_object* v_a_3275_){
_start:
{
uint8_t v___x_3277_; 
v___x_3277_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_3273_);
if (v___x_3277_ == 0)
{
lean_object* v___x_3278_; lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3294_; 
v___x_3278_ = l_Lean_Server_lookupLspRequestHandler(v_method_3273_);
v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___x_3278_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3281_ = v___x_3278_;
v_isShared_3282_ = v_isSharedCheck_3294_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3278_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3294_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
if (lean_obj_tag(v_a_3279_) == 0)
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3289_; 
lean_dec(v_params_3274_);
v___x_3283_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__0));
v___x_3284_ = lean_string_append(v___x_3283_, v_method_3273_);
v___x_3285_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__1));
v___x_3286_ = lean_string_append(v___x_3284_, v___x_3285_);
v___x_3287_ = l_Lean_Server_RequestError_internalError(v___x_3286_);
if (v_isShared_3282_ == 0)
{
lean_ctor_set_tag(v___x_3281_, 1);
lean_ctor_set(v___x_3281_, 0, v___x_3287_);
v___x_3289_ = v___x_3281_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v___x_3287_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
else
{
lean_object* v_val_3291_; lean_object* v_handle_3292_; lean_object* v___x_3293_; 
lean_del_object(v___x_3281_);
v_val_3291_ = lean_ctor_get(v_a_3279_, 0);
lean_inc(v_val_3291_);
lean_dec_ref_known(v_a_3279_, 1);
v_handle_3292_ = lean_ctor_get(v_val_3291_, 1);
lean_inc_ref(v_handle_3292_);
lean_dec(v_val_3291_);
lean_inc_ref(v_a_3275_);
v___x_3293_ = lean_apply_3(v_handle_3292_, v_params_3274_, v_a_3275_, lean_box(0));
return v___x_3293_;
}
}
}
else
{
lean_object* v___x_3295_; 
v___x_3295_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_3273_);
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
lean_dec(v_params_3274_);
v___x_3296_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__0));
v___x_3297_ = lean_string_append(v___x_3296_, v_method_3273_);
v___x_3298_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__1));
v___x_3299_ = lean_string_append(v___x_3297_, v___x_3298_);
v___x_3300_ = l_Lean_Server_RequestError_internalError(v___x_3299_);
v___x_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3300_);
return v___x_3301_;
}
else
{
lean_object* v_val_3302_; lean_object* v_handle_3303_; lean_object* v___x_3304_; 
v_val_3302_ = lean_ctor_get(v___x_3295_, 0);
lean_inc(v_val_3302_);
lean_dec_ref_known(v___x_3295_, 1);
v_handle_3303_ = lean_ctor_get(v_val_3302_, 2);
lean_inc_ref(v_handle_3303_);
lean_dec(v_val_3302_);
lean_inc_ref(v_a_3275_);
v___x_3304_ = lean_apply_3(v_handle_3303_, v_params_3274_, v_a_3275_, lean_box(0));
return v___x_3304_;
}
}
}
}
LEAN_EXPORT void l_Lean_Server_handleLspRequest_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_3273_ = stack[0].m_obj;
lean_object* v_params_3274_ = stack[1].m_obj;
lean_object* v_a_3275_ = stack[2].m_obj;
lean_object* v_res_3305_;
v_res_3305_ = l_Lean_Server_handleLspRequest(v_method_3273_, v_params_3274_, v_a_3275_);
stack->m_obj
 = v_res_3305_;
}
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest___boxed(lean_object* v_method_3306_, lean_object* v_params_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Lean_Server_handleLspRequest(v_method_3306_, v_params_3307_, v_a_3308_);
lean_dec_ref(v_a_3308_);
lean_dec_ref(v_method_3306_);
return v_res_3310_;
}
}
lean_object* l_Lean_Server_routeLspRequest(lean_object* v_method_3311_, lean_object* v_params_3312_){
_start:
{
uint8_t v___x_3314_; 
v___x_3314_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_3311_);
if (v___x_3314_ == 0)
{
lean_object* v___x_3315_; lean_object* v_a_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3331_; 
v___x_3315_ = l_Lean_Server_lookupLspRequestHandler(v_method_3311_);
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3318_ = v___x_3315_;
v_isShared_3319_ = v_isSharedCheck_3331_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_a_3316_);
lean_dec(v___x_3315_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3331_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
if (lean_obj_tag(v_a_3316_) == 0)
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3323_; 
lean_dec(v_params_3312_);
v___x_3320_ = l_Lean_Server_RequestError_methodNotFound(v_method_3311_);
v___x_3321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3320_);
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 0, v___x_3321_);
v___x_3323_ = v___x_3318_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v___x_3321_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
else
{
lean_object* v_val_3325_; lean_object* v_fileSource_3326_; lean_object* v___x_3327_; lean_object* v___x_3329_; 
v_val_3325_ = lean_ctor_get(v_a_3316_, 0);
lean_inc(v_val_3325_);
lean_dec_ref_known(v_a_3316_, 1);
v_fileSource_3326_ = lean_ctor_get(v_val_3325_, 0);
lean_inc_ref(v_fileSource_3326_);
lean_dec(v_val_3325_);
v___x_3327_ = lean_apply_1(v_fileSource_3326_, v_params_3312_);
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 0, v___x_3327_);
v___x_3329_ = v___x_3318_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v___x_3327_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
}
else
{
lean_object* v___x_3332_; 
v___x_3332_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_3311_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
lean_dec(v_params_3312_);
v___x_3333_ = l_Lean_Server_RequestError_methodNotFound(v_method_3311_);
v___x_3334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3333_);
v___x_3335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3334_);
return v___x_3335_;
}
else
{
lean_object* v_val_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3345_; 
v_val_3336_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3338_ = v___x_3332_;
v_isShared_3339_ = v_isSharedCheck_3345_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_val_3336_);
lean_dec(v___x_3332_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3345_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v_fileSource_3340_; lean_object* v___x_3341_; lean_object* v___x_3343_; 
v_fileSource_3340_ = lean_ctor_get(v_val_3336_, 0);
lean_inc_ref(v_fileSource_3340_);
lean_dec(v_val_3336_);
v___x_3341_ = lean_apply_1(v_fileSource_3340_, v_params_3312_);
if (v_isShared_3339_ == 0)
{
lean_ctor_set_tag(v___x_3338_, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3341_);
v___x_3343_ = v___x_3338_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v___x_3341_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_routeLspRequest_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_3311_ = stack[0].m_obj;
lean_object* v_params_3312_ = stack[1].m_obj;
lean_object* v_res_3346_;
v_res_3346_ = l_Lean_Server_routeLspRequest(v_method_3311_, v_params_3312_);
stack->m_obj
 = v_res_3346_;
}
LEAN_EXPORT lean_object* l_Lean_Server_routeLspRequest___boxed(lean_object* v_method_3347_, lean_object* v_params_3348_, lean_object* v_a_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l_Lean_Server_routeLspRequest(v_method_3347_, v_params_3348_);
lean_dec_ref(v_method_3347_);
return v_res_3350_;
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
