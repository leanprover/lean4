// Lean compiler output
// Module: Std.Http.Server
// Imports: public import Std.Async public import Std.Async.TCP public import Std.Sync.CancellationToken public import Std.Sync.Semaphore public import Std.Http.Server.Config public import Std.Http.Server.Handler public import Std.Http.Server.Connection
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
lean_object* l_Std_Semaphore_release(lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Std_CancellationToken_isCancelled(lean_object*);
lean_object* l_Std_Channel_send___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Std_CancellationContext_cancel(lean_object*, lean_object*);
lean_object* l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_ContextAsync_instMonadFinally___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Mutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Server_serveConnection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_BaseAsync_toRawBaseIO___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* l_Std_CancellationContext_fork(lean_object*);
extern lean_object* l_Std_Http_Extensions_empty;
lean_object* l_Std_Http_Extensions_compareName___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_tcp_getpeername(lean_object*);
lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Async_Selectable_one___redArg(lean_object*);
lean_object* l_Std_Semaphore_acquire(lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* l___private_Init_While_0__repeatM_erased___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Async_ContextAsync_instMonad;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_CancellationContext_new();
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* l_Std_CloseableChannel_new___redArg(lean_object*);
lean_object* l_Std_Semaphore_new(lean_object*);
lean_object* lean_uv_tcp_getsockname(lean_object*);
lean_object* lean_uv_tcp_nodelay(lean_object*);
lean_object* lean_uv_tcp_listen(lean_object*, uint32_t);
lean_object* lean_uv_tcp_bind(lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_selector(lean_object*);
extern lean_object* l_Std_Http_instTransportClient;
extern lean_object* l_Std_Http_Server_instImpl_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8_;
lean_object* lean_uv_tcp_new();
lean_object* l_Std_Channel_recv___redArg(lean_object*, lean_object*);
lean_object* l_Std_Channel_recvSelector___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_new(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_new___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdown(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdown___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Server_waitShutdown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_waitShutdown___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_waitShutdown___closed__0 = (const lean_object*)&l_Std_Http_Server_waitShutdown___closed__0_value;
static const lean_closure_object l_Std_Http_Server_waitShutdown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_waitShutdown___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Server_waitShutdown___closed__0_value)} };
static const lean_object* l_Std_Http_Server_waitShutdown___closed__1 = (const lean_object*)&l_Std_Http_Server_waitShutdown___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdownSelector(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1_value;
static const lean_closure_object l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2 = (const lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2_value;
static const lean_closure_object l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2_value),((lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1_value)} };
static const lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3 = (const lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3_value;
static const lean_closure_object l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_instMonadFinally___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4 = (const lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4_value;
static const lean_closure_object l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5 = (const lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5_value;
static const lean_closure_object l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6 = (const lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2___boxed(lean_object*);
static const lean_ctor_object l_Std_Http_Server_serve___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Server_serve___redArg___lam__5___closed__0 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__5___closed__0_value;
static const lean_ctor_object l_Std_Http_Server_serve___redArg___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Server_serve___redArg___lam__5___closed__0_value)}};
static const lean_object* l_Std_Http_Server_serve___redArg___lam__5___closed__1 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__5___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Server_serve___redArg___lam__19___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Server_serve___redArg___lam__19___closed__0;
static lean_once_cell_t l_Std_Http_Server_serve___redArg___lam__19___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Server_serve___redArg___lam__19___closed__1;
static const lean_closure_object l_Std_Http_Server_serve___redArg___lam__19___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Extensions_compareName___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___lam__19___closed__2 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__19___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__19(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Server_serve___redArg___lam__28___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__10___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Server_serve___redArg___lam__28___closed__0 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__28___closed__0_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___lam__28___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__6___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Server_serve___redArg___lam__28___closed__1 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__28___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32(lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__33___boxed(lean_object**);
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__0 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__0_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__1 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__1_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__2 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__2_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__5___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__3 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__3_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__4 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__4_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__4___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__5 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_new(lean_object* v_config_1_, lean_object* v_localAddr_2_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v_connectionLimit_8_; lean_object* v_maxConnections_13_; uint8_t v___x_14_; 
v___x_4_ = l_Std_CancellationContext_new();
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = l_Std_Mutex_new___redArg(v___x_5_);
v_maxConnections_13_ = lean_ctor_get(v_config_1_, 0);
v___x_14_ = lean_nat_dec_eq(v_maxConnections_13_, v___x_5_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; lean_object* v___x_16_; 
lean_inc(v_maxConnections_13_);
v___x_15_ = l_Std_Semaphore_new(v_maxConnections_13_);
v___x_16_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
v_connectionLimit_8_ = v___x_16_;
goto v___jp_7_;
}
else
{
lean_object* v___x_17_; 
v___x_17_ = lean_box(0);
v_connectionLimit_8_ = v___x_17_;
goto v___jp_7_;
}
v___jp_7_:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_9_ = lean_box(0);
v___x_10_ = l_Std_CloseableChannel_new___redArg(v___x_9_);
v___x_11_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_11_, 0, v___x_4_);
lean_ctor_set(v___x_11_, 1, v___x_6_);
lean_ctor_set(v___x_11_, 2, v_connectionLimit_8_);
lean_ctor_set(v___x_11_, 3, v___x_10_);
lean_ctor_set(v___x_11_, 4, v_config_1_);
lean_ctor_set(v___x_11_, 5, v_localAddr_2_);
v___x_12_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_new___boxed(lean_object* v_config_18_, lean_object* v_localAddr_19_, lean_object* v_a_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Std_Http_Server_new(v_config_18_, v_localAddr_19_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdown(lean_object* v_s_22_){
_start:
{
lean_object* v_context_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v_context_24_ = lean_ctor_get(v_s_22_, 0);
lean_inc_ref(v_context_24_);
lean_dec_ref(v_s_22_);
v___x_25_ = lean_box(1);
v___x_26_ = l_Std_CancellationContext_cancel(v_context_24_, v___x_25_);
v___x_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
v___x_28_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdown___boxed(lean_object* v_s_29_, lean_object* v_a_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Std_Http_Server_shutdown(v_s_29_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___lam__0(lean_object* v_a_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_33_, 0, v_a_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___lam__1(lean_object* v___f_34_, lean_object* v_x_35_){
_start:
{
if (lean_obj_tag(v_x_35_) == 0)
{
lean_object* v_a_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_45_; 
lean_dec_ref(v___f_34_);
v_a_37_ = lean_ctor_get(v_x_35_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v_x_35_);
if (v_isSharedCheck_45_ == 0)
{
v___x_39_ = v_x_35_;
v_isShared_40_ = v_isSharedCheck_45_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_a_37_);
lean_dec(v_x_35_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_45_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_42_; 
if (v_isShared_40_ == 0)
{
v___x_42_ = v___x_39_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_a_37_);
v___x_42_ = v_reuseFailAlloc_44_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
lean_object* v___x_43_; 
v___x_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
return v___x_43_;
}
}
}
else
{
lean_object* v_a_46_; lean_object* v___x_47_; uint8_t v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_a_46_ = lean_ctor_get(v_x_35_, 0);
lean_inc(v_a_46_);
lean_dec_ref_known(v_x_35_, 1);
v___x_47_ = lean_unsigned_to_nat(0u);
v___x_48_ = 0;
v___x_49_ = lean_task_map(v___f_34_, v_a_46_, v___x_47_, v___x_48_);
v___x_50_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___lam__1___boxed(lean_object* v___f_51_, lean_object* v_x_52_, lean_object* v___y_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Std_Http_Server_waitShutdown___lam__1(v___f_51_, v_x_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown(lean_object* v_s_58_){
_start:
{
lean_object* v_shutdownPromise_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___f_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; lean_object* v___x_68_; 
v_shutdownPromise_60_ = lean_ctor_get(v_s_58_, 3);
lean_inc_ref(v_shutdownPromise_60_);
lean_dec_ref(v_s_58_);
v___x_61_ = lean_box(0);
v___x_62_ = l_Std_Channel_recv___redArg(v___x_61_, v_shutdownPromise_60_);
v___f_63_ = ((lean_object*)(l_Std_Http_Server_waitShutdown___closed__1));
v___x_64_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_62_);
v___x_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
v___x_66_ = lean_unsigned_to_nat(0u);
v___x_67_ = 0;
v___x_68_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_66_, v___x_67_, v___x_65_, v___f_63_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___boxed(lean_object* v_s_69_, lean_object* v_a_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Std_Http_Server_waitShutdown(v_s_69_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdownSelector(lean_object* v_s_72_){
_start:
{
lean_object* v_shutdownPromise_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v_shutdownPromise_73_ = lean_ctor_get(v_s_72_, 3);
lean_inc_ref(v_shutdownPromise_73_);
lean_dec_ref(v_s_72_);
v___x_74_ = lean_box(0);
v___x_75_ = l_Std_Channel_recvSelector___redArg(v___x_74_, v_shutdownPromise_73_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait___lam__2(lean_object* v_shutdownPromise_76_, lean_object* v___f_77_, lean_object* v_x_78_){
_start:
{
if (lean_obj_tag(v_x_78_) == 0)
{
lean_object* v___x_80_; 
lean_dec_ref(v___f_77_);
lean_dec_ref(v_shutdownPromise_76_);
v___x_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_80_, 0, v_x_78_);
return v___x_80_;
}
else
{
lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_93_; 
v_isSharedCheck_93_ = !lean_is_exclusive(v_x_78_);
if (v_isSharedCheck_93_ == 0)
{
lean_object* v_unused_94_; 
v_unused_94_ = lean_ctor_get(v_x_78_, 0);
lean_dec(v_unused_94_);
v___x_82_ = v_x_78_;
v_isShared_83_ = v_isSharedCheck_93_;
goto v_resetjp_81_;
}
else
{
lean_dec(v_x_78_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_93_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_84_ = lean_box(0);
v___x_85_ = l_Std_Channel_recv___redArg(v___x_84_, v_shutdownPromise_76_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 0, v___x_85_);
v___x_87_ = v___x_82_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_85_);
v___x_87_ = v_reuseFailAlloc_92_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; 
v___x_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = 0;
v___x_91_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_89_, v___x_90_, v___x_88_, v___f_77_);
return v___x_91_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait___lam__2___boxed(lean_object* v_shutdownPromise_95_, lean_object* v___f_96_, lean_object* v_x_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Std_Http_Server_shutdownAndWait___lam__2(v_shutdownPromise_95_, v___f_96_, v_x_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait(lean_object* v_s_100_){
_start:
{
lean_object* v_context_102_; lean_object* v_shutdownPromise_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___f_106_; lean_object* v___f_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; lean_object* v___x_112_; 
v_context_102_ = lean_ctor_get(v_s_100_, 0);
lean_inc_ref(v_context_102_);
v_shutdownPromise_103_ = lean_ctor_get(v_s_100_, 3);
lean_inc_ref(v_shutdownPromise_103_);
lean_dec_ref(v_s_100_);
v___x_104_ = lean_box(1);
v___x_105_ = l_Std_CancellationContext_cancel(v_context_102_, v___x_104_);
v___f_106_ = ((lean_object*)(l_Std_Http_Server_waitShutdown___closed__1));
v___f_107_ = lean_alloc_closure((void*)(l_Std_Http_Server_shutdownAndWait___lam__2___boxed), 4, 2);
lean_closure_set(v___f_107_, 0, v_shutdownPromise_103_);
lean_closure_set(v___f_107_, 1, v___f_106_);
v___x_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_105_);
v___x_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
v___x_110_ = lean_unsigned_to_nat(0u);
v___x_111_ = 0;
v___x_112_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_110_, v___x_111_, v___x_109_, v___f_107_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait___boxed(lean_object* v_s_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Std_Http_Server_shutdownAndWait(v_s_113_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0(lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_123_ = lean_st_ref_take(v___y_120_);
v___x_124_ = lean_unsigned_to_nat(1u);
v___x_125_ = lean_nat_add(v___x_123_, v___x_124_);
lean_dec(v___x_123_);
v___x_126_ = lean_st_ref_put(v___y_120_, v___x_125_);
v___x_127_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___boxed(lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0(v___y_128_, v___y_129_);
lean_dec_ref(v___y_129_);
lean_dec(v___y_128_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1(lean_object* v_x_132_){
_start:
{
lean_object* v_fst_133_; 
v_fst_133_ = lean_ctor_get(v_x_132_, 0);
lean_inc(v_fst_133_);
return v_fst_133_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1___boxed(lean_object* v_x_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1(v_x_134_);
lean_dec_ref(v_x_134_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2(lean_object* v_shutdownPromise_136_, lean_object* v_a_137_, lean_object* v_x_138_){
_start:
{
uint8_t v___y_141_; 
if (lean_obj_tag(v_x_138_) == 0)
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_154_; 
lean_dec_ref(v_shutdownPromise_136_);
v_a_146_ = lean_ctor_get(v_x_138_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v_x_138_);
if (v_isSharedCheck_154_ == 0)
{
v___x_148_ = v_x_138_;
v_isShared_149_ = v_isSharedCheck_154_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v_x_138_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_154_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_153_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_152_; 
v___x_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
return v___x_152_;
}
}
}
else
{
lean_object* v_a_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v_a_155_ = lean_ctor_get(v_x_138_, 0);
lean_inc(v_a_155_);
lean_dec_ref_known(v_x_138_, 1);
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = lean_nat_dec_eq(v_a_137_, v___x_156_);
if (v___x_157_ == 0)
{
lean_dec(v_a_155_);
v___y_141_ = v___x_157_;
goto v___jp_140_;
}
else
{
uint8_t v___x_158_; 
v___x_158_ = lean_unbox(v_a_155_);
lean_dec(v_a_155_);
v___y_141_ = v___x_158_;
goto v___jp_140_;
}
}
v___jp_140_:
{
if (v___y_141_ == 0)
{
lean_object* v___x_142_; 
lean_dec_ref(v_shutdownPromise_136_);
v___x_142_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_142_;
}
else
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_143_ = lean_box(0);
v___x_144_ = l_Std_Channel_send___redArg(v_shutdownPromise_136_, v___x_143_);
lean_dec_ref(v___x_144_);
v___x_145_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_145_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2___boxed(lean_object* v_shutdownPromise_159_, lean_object* v_a_160_, lean_object* v_x_161_, lean_object* v___y_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2(v_shutdownPromise_159_, v_a_160_, v_x_161_);
lean_dec(v_a_160_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3(lean_object* v_context_164_, lean_object* v_shutdownPromise_165_, lean_object* v_x_166_){
_start:
{
if (lean_obj_tag(v_x_166_) == 0)
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_176_; 
lean_dec_ref(v_shutdownPromise_165_);
lean_dec_ref(v_context_164_);
v_a_168_ = lean_ctor_get(v_x_166_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v_x_166_);
if (v_isSharedCheck_176_ == 0)
{
v___x_170_ = v_x_166_;
v_isShared_171_ = v_isSharedCheck_176_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v_x_166_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_176_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_a_168_);
v___x_173_ = v_reuseFailAlloc_175_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
lean_object* v___x_174_; 
v___x_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
return v___x_174_;
}
}
}
else
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_192_; 
v_a_177_ = lean_ctor_get(v_x_166_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v_x_166_);
if (v_isSharedCheck_192_ == 0)
{
v___x_179_ = v_x_166_;
v_isShared_180_ = v_isSharedCheck_192_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v_x_166_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_192_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v_token_181_; uint8_t v___x_182_; lean_object* v___f_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
v_token_181_ = lean_ctor_get(v_context_164_, 1);
lean_inc_ref(v_token_181_);
lean_dec_ref(v_context_164_);
v___x_182_ = l_Std_CancellationToken_isCancelled(v_token_181_);
v___f_183_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_183_, 0, v_shutdownPromise_165_);
lean_closure_set(v___f_183_, 1, v_a_177_);
v___x_184_ = lean_box(v___x_182_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_184_);
v___x_186_ = v___x_179_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_184_);
v___x_186_ = v_reuseFailAlloc_191_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; lean_object* v___x_190_; 
v___x_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = 0;
v___x_190_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_188_, v___x_189_, v___x_187_, v___f_183_);
return v___x_190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed(lean_object* v_context_193_, lean_object* v_shutdownPromise_194_, lean_object* v_x_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3(v_context_193_, v_shutdownPromise_194_, v_x_195_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4(lean_object* v___f_198_, lean_object* v_____r_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; lean_object* v___x_208_; 
v___x_203_ = lean_st_ref_get(v___y_200_);
v___x_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
v___x_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = 0;
v___x_208_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_206_, v___x_207_, v___x_205_, v___f_198_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed(lean_object* v___f_209_, lean_object* v_____r_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4(v___f_209_, v_____r_210_, v___y_211_, v___y_212_);
lean_dec_ref(v___y_212_);
lean_dec(v___y_211_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5(lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_218_ = lean_st_ref_take(v___y_215_);
v___x_219_ = lean_unsigned_to_nat(1u);
v___x_220_ = lean_nat_sub(v___x_218_, v___x_219_);
lean_dec(v___x_218_);
v___x_221_ = lean_st_ref_put(v___y_215_, v___x_220_);
v___x_222_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5___boxed(lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5(v___y_223_, v___y_224_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6(lean_object* v___x_227_, lean_object* v___f_228_, lean_object* v___f_229_, lean_object* v___f_230_, lean_object* v___f_231_, lean_object* v_activeConnections_232_, lean_object* v_____r_233_, lean_object* v___y_234_){
_start:
{
lean_object* v___x_236_; lean_object* v___x_2161__overap_237_; lean_object* v___x_238_; 
lean_inc_ref(v___x_227_);
v___x_236_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_236_, 0, lean_box(0));
lean_closure_set(v___x_236_, 1, lean_box(0));
lean_closure_set(v___x_236_, 2, v___x_227_);
lean_closure_set(v___x_236_, 3, lean_box(0));
lean_closure_set(v___x_236_, 4, lean_box(0));
lean_closure_set(v___x_236_, 5, v___f_228_);
lean_closure_set(v___x_236_, 6, v___f_229_);
v___x_2161__overap_237_ = l_Std_Mutex_atomically___redArg(v___x_227_, v___f_230_, v___f_231_, v_activeConnections_232_, v___x_236_);
lean_inc_ref(v___y_234_);
v___x_238_ = lean_apply_2(v___x_2161__overap_237_, v___y_234_, lean_box(0));
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed(lean_object* v___x_239_, lean_object* v___f_240_, lean_object* v___f_241_, lean_object* v___f_242_, lean_object* v___f_243_, lean_object* v_activeConnections_244_, lean_object* v_____r_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6(v___x_239_, v___f_240_, v___f_241_, v___f_242_, v___f_243_, v_activeConnections_244_, v_____r_245_, v___y_246_);
lean_dec_ref(v___y_246_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7(lean_object* v___f_249_, lean_object* v_a_250_, lean_object* v_x_251_){
_start:
{
if (lean_obj_tag(v_x_251_) == 0)
{
lean_object* v___x_253_; 
lean_dec_ref(v___f_249_);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v_x_251_);
return v___x_253_;
}
else
{
lean_object* v_a_254_; lean_object* v___x_255_; 
v_a_254_ = lean_ctor_get(v_x_251_, 0);
lean_inc(v_a_254_);
lean_dec_ref_known(v_x_251_, 1);
lean_inc_ref(v_a_250_);
v___x_255_ = lean_apply_3(v___f_249_, v_a_254_, v_a_250_, lean_box(0));
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed(lean_object* v___f_256_, lean_object* v_a_257_, lean_object* v_x_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7(v___f_256_, v_a_257_, v_x_258_);
lean_dec_ref(v_a_257_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8(uint8_t v_releaseConnectionPermit_261_, lean_object* v___f_262_, lean_object* v_a_263_, lean_object* v_connectionLimit_264_, lean_object* v___f_265_, lean_object* v_opt_266_){
_start:
{
if (v_releaseConnectionPermit_261_ == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec_ref(v___f_265_);
lean_dec(v_connectionLimit_264_);
v___x_268_ = lean_box(0);
lean_inc_ref(v_a_263_);
v___x_269_ = lean_apply_3(v___f_262_, v___x_268_, v_a_263_, lean_box(0));
return v___x_269_;
}
else
{
if (lean_obj_tag(v_connectionLimit_264_) == 1)
{
lean_object* v_val_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_282_; 
lean_dec_ref(v___f_262_);
v_val_270_ = lean_ctor_get(v_connectionLimit_264_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v_connectionLimit_264_);
if (v_isSharedCheck_282_ == 0)
{
v___x_272_ = v_connectionLimit_264_;
v_isShared_273_ = v_isSharedCheck_282_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_val_270_);
lean_dec(v_connectionLimit_264_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_282_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_274_ = l_Std_Semaphore_release(v_val_270_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_274_);
v___x_276_ = v___x_272_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_281_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; lean_object* v___x_280_; 
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
v___x_278_ = lean_unsigned_to_nat(0u);
v___x_279_ = 0;
v___x_280_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_278_, v___x_279_, v___x_277_, v___f_265_);
return v___x_280_;
}
}
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; 
lean_dec_ref(v___f_265_);
lean_dec(v_connectionLimit_264_);
v___x_283_ = lean_box(0);
lean_inc_ref(v_a_263_);
v___x_284_ = lean_apply_3(v___f_262_, v___x_283_, v_a_263_, lean_box(0));
return v___x_284_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed(lean_object* v_releaseConnectionPermit_285_, lean_object* v___f_286_, lean_object* v_a_287_, lean_object* v_connectionLimit_288_, lean_object* v___f_289_, lean_object* v_opt_290_, lean_object* v___y_291_){
_start:
{
uint8_t v_releaseConnectionPermit_boxed_292_; lean_object* v_res_293_; 
v_releaseConnectionPermit_boxed_292_ = lean_unbox(v_releaseConnectionPermit_285_);
v_res_293_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8(v_releaseConnectionPermit_boxed_292_, v___f_286_, v_a_287_, v_connectionLimit_288_, v___f_289_, v_opt_290_);
lean_dec(v_opt_290_);
lean_dec_ref(v_a_287_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9(lean_object* v_action_294_, lean_object* v_a_295_, lean_object* v___f_296_, lean_object* v___f_297_, lean_object* v_x_298_){
_start:
{
if (lean_obj_tag(v_x_298_) == 0)
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_308_; 
lean_dec(v___f_297_);
lean_dec_ref(v___f_296_);
lean_dec_ref(v_action_294_);
v_a_300_ = lean_ctor_get(v_x_298_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v_x_298_);
if (v_isSharedCheck_308_ == 0)
{
v___x_302_ = v_x_298_;
v_isShared_303_ = v_isSharedCheck_308_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v_x_298_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_308_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_307_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_306_; 
v___x_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
return v___x_306_;
}
}
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; lean_object* v___x_312_; lean_object* v___y_314_; 
lean_dec_ref_known(v_x_298_, 1);
lean_inc_ref(v_a_295_);
v___x_309_ = lean_apply_1(v_action_294_, v_a_295_);
v___x_310_ = lean_unsigned_to_nat(0u);
v___x_311_ = 0;
v___x_312_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_309_, v___f_296_, v___x_310_, v___x_311_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_316_; 
lean_dec(v___f_297_);
v_a_316_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_a_316_);
lean_dec_ref_known(v___x_312_, 1);
if (lean_obj_tag(v_a_316_) == 0)
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
v_a_317_ = lean_ctor_get(v_a_316_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v_a_316_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v_a_316_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v_a_316_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
v___y_314_ = v___x_322_;
goto v___jp_313_;
}
}
}
else
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_333_; 
v_a_325_ = lean_ctor_get(v_a_316_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v_a_316_);
if (v_isSharedCheck_333_ == 0)
{
v___x_327_ = v_a_316_;
v_isShared_328_ = v_isSharedCheck_333_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v_a_316_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_333_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v_fst_329_; lean_object* v___x_331_; 
v_fst_329_ = lean_ctor_get(v_a_325_, 0);
lean_inc(v_fst_329_);
lean_dec(v_a_325_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v_fst_329_);
v___x_331_ = v___x_327_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_fst_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
v___y_314_ = v___x_331_;
goto v___jp_313_;
}
}
}
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_343_; 
v_a_334_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_343_ == 0)
{
v___x_336_ = v___x_312_;
v_isShared_337_ = v_isSharedCheck_343_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_312_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_343_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_341_; 
v___x_338_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_338_, 0, lean_box(0));
lean_closure_set(v___x_338_, 1, lean_box(0));
lean_closure_set(v___x_338_, 2, lean_box(0));
lean_closure_set(v___x_338_, 3, v___f_297_);
v___x_339_ = lean_task_map(v___x_338_, v_a_334_, v___x_310_, v___x_311_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_339_);
v___x_341_ = v___x_336_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
v___jp_313_:
{
lean_object* v___x_315_; 
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___y_314_);
return v___x_315_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed(lean_object* v_action_344_, lean_object* v_a_345_, lean_object* v___f_346_, lean_object* v___f_347_, lean_object* v_x_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9(v_action_344_, v_a_345_, v___f_346_, v___f_347_, v_x_348_);
lean_dec_ref(v_a_345_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg(lean_object* v_s_360_, uint8_t v_releaseConnectionPermit_361_, lean_object* v_action_362_, lean_object* v_a_363_){
_start:
{
lean_object* v___x_365_; lean_object* v_context_366_; lean_object* v_activeConnections_367_; lean_object* v_connectionLimit_368_; lean_object* v_shutdownPromise_369_; lean_object* v___f_370_; lean_object* v___f_371_; lean_object* v___f_372_; lean_object* v___x_1398__overap_373_; lean_object* v___x_374_; lean_object* v___f_375_; lean_object* v___f_376_; lean_object* v___f_377_; lean_object* v___f_378_; lean_object* v___f_379_; lean_object* v___f_380_; lean_object* v___x_381_; lean_object* v___f_382_; lean_object* v___f_383_; lean_object* v___x_384_; uint8_t v___x_385_; lean_object* v___x_386_; 
v___x_365_ = l_Std_Async_ContextAsync_instMonad;
v_context_366_ = lean_ctor_get(v_s_360_, 0);
lean_inc_ref(v_context_366_);
v_activeConnections_367_ = lean_ctor_get(v_s_360_, 1);
lean_inc_ref_n(v_activeConnections_367_, 2);
v_connectionLimit_368_ = lean_ctor_get(v_s_360_, 2);
lean_inc(v_connectionLimit_368_);
v_shutdownPromise_369_ = lean_ctor_get(v_s_360_, 3);
lean_inc_ref(v_shutdownPromise_369_);
lean_dec_ref(v_s_360_);
v___f_370_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0));
v___f_371_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3));
v___f_372_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4));
v___x_1398__overap_373_ = l_Std_Mutex_atomically___redArg(v___x_365_, v___f_371_, v___f_372_, v_activeConnections_367_, v___f_370_);
lean_inc_ref_n(v_a_363_, 4);
v___x_374_ = lean_apply_2(v___x_1398__overap_373_, v_a_363_, lean_box(0));
v___f_375_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5));
v___f_376_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_376_, 0, v_context_366_);
lean_closure_set(v___f_376_, 1, v_shutdownPromise_369_);
v___f_377_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed), 5, 1);
lean_closure_set(v___f_377_, 0, v___f_376_);
v___f_378_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6));
v___f_379_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed), 9, 6);
lean_closure_set(v___f_379_, 0, v___x_365_);
lean_closure_set(v___f_379_, 1, v___f_378_);
lean_closure_set(v___f_379_, 2, v___f_377_);
lean_closure_set(v___f_379_, 3, v___f_371_);
lean_closure_set(v___f_379_, 4, v___f_372_);
lean_closure_set(v___f_379_, 5, v_activeConnections_367_);
lean_inc_ref(v___f_379_);
v___f_380_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_380_, 0, v___f_379_);
lean_closure_set(v___f_380_, 1, v_a_363_);
v___x_381_ = lean_box(v_releaseConnectionPermit_361_);
v___f_382_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed), 7, 5);
lean_closure_set(v___f_382_, 0, v___x_381_);
lean_closure_set(v___f_382_, 1, v___f_379_);
lean_closure_set(v___f_382_, 2, v_a_363_);
lean_closure_set(v___f_382_, 3, v_connectionLimit_368_);
lean_closure_set(v___f_382_, 4, v___f_380_);
v___f_383_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed), 6, 4);
lean_closure_set(v___f_383_, 0, v_action_362_);
lean_closure_set(v___f_383_, 1, v_a_363_);
lean_closure_set(v___f_383_, 2, v___f_382_);
lean_closure_set(v___f_383_, 3, v___f_375_);
v___x_384_ = lean_unsigned_to_nat(0u);
v___x_385_ = 0;
v___x_386_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_384_, v___x_385_, v___x_374_, v___f_383_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___boxed(lean_object* v_s_387_, lean_object* v_releaseConnectionPermit_388_, lean_object* v_action_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
uint8_t v_releaseConnectionPermit_boxed_392_; lean_object* v_res_393_; 
v_releaseConnectionPermit_boxed_392_ = lean_unbox(v_releaseConnectionPermit_388_);
v_res_393_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg(v_s_387_, v_releaseConnectionPermit_boxed_392_, v_action_389_, v_a_390_);
lean_dec_ref(v_a_390_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation(lean_object* v_00_u03b1_394_, lean_object* v_s_395_, uint8_t v_releaseConnectionPermit_396_, lean_object* v_action_397_, lean_object* v_a_398_){
_start:
{
lean_object* v___x_400_; lean_object* v_context_401_; lean_object* v_activeConnections_402_; lean_object* v_connectionLimit_403_; lean_object* v_shutdownPromise_404_; lean_object* v___f_405_; lean_object* v___f_406_; lean_object* v___f_407_; lean_object* v___x_1936__overap_408_; lean_object* v___x_409_; lean_object* v___f_410_; lean_object* v___f_411_; lean_object* v___f_412_; lean_object* v___f_413_; lean_object* v___f_414_; lean_object* v___f_415_; lean_object* v___x_416_; lean_object* v___f_417_; lean_object* v___f_418_; lean_object* v___x_419_; uint8_t v___x_420_; lean_object* v___x_421_; 
v___x_400_ = l_Std_Async_ContextAsync_instMonad;
v_context_401_ = lean_ctor_get(v_s_395_, 0);
lean_inc_ref(v_context_401_);
v_activeConnections_402_ = lean_ctor_get(v_s_395_, 1);
lean_inc_ref_n(v_activeConnections_402_, 2);
v_connectionLimit_403_ = lean_ctor_get(v_s_395_, 2);
lean_inc(v_connectionLimit_403_);
v_shutdownPromise_404_ = lean_ctor_get(v_s_395_, 3);
lean_inc_ref(v_shutdownPromise_404_);
lean_dec_ref(v_s_395_);
v___f_405_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0));
v___f_406_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3));
v___f_407_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4));
v___x_1936__overap_408_ = l_Std_Mutex_atomically___redArg(v___x_400_, v___f_406_, v___f_407_, v_activeConnections_402_, v___f_405_);
lean_inc_ref_n(v_a_398_, 4);
v___x_409_ = lean_apply_2(v___x_1936__overap_408_, v_a_398_, lean_box(0));
v___f_410_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5));
v___f_411_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_411_, 0, v_context_401_);
lean_closure_set(v___f_411_, 1, v_shutdownPromise_404_);
v___f_412_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed), 5, 1);
lean_closure_set(v___f_412_, 0, v___f_411_);
v___f_413_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6));
v___f_414_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed), 9, 6);
lean_closure_set(v___f_414_, 0, v___x_400_);
lean_closure_set(v___f_414_, 1, v___f_413_);
lean_closure_set(v___f_414_, 2, v___f_412_);
lean_closure_set(v___f_414_, 3, v___f_406_);
lean_closure_set(v___f_414_, 4, v___f_407_);
lean_closure_set(v___f_414_, 5, v_activeConnections_402_);
lean_inc_ref(v___f_414_);
v___f_415_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_415_, 0, v___f_414_);
lean_closure_set(v___f_415_, 1, v_a_398_);
v___x_416_ = lean_box(v_releaseConnectionPermit_396_);
v___f_417_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed), 7, 5);
lean_closure_set(v___f_417_, 0, v___x_416_);
lean_closure_set(v___f_417_, 1, v___f_414_);
lean_closure_set(v___f_417_, 2, v_a_398_);
lean_closure_set(v___f_417_, 3, v_connectionLimit_403_);
lean_closure_set(v___f_417_, 4, v___f_415_);
v___f_418_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed), 6, 4);
lean_closure_set(v___f_418_, 0, v_action_397_);
lean_closure_set(v___f_418_, 1, v_a_398_);
lean_closure_set(v___f_418_, 2, v___f_417_);
lean_closure_set(v___f_418_, 3, v___f_410_);
v___x_419_ = lean_unsigned_to_nat(0u);
v___x_420_ = 0;
v___x_421_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_419_, v___x_420_, v___x_409_, v___f_418_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___boxed(lean_object* v_00_u03b1_422_, lean_object* v_s_423_, lean_object* v_releaseConnectionPermit_424_, lean_object* v_action_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
uint8_t v_releaseConnectionPermit_boxed_428_; lean_object* v_res_429_; 
v_releaseConnectionPermit_boxed_428_ = lean_unbox(v_releaseConnectionPermit_424_);
v_res_429_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation(v_00_u03b1_422_, v_s_423_, v_releaseConnectionPermit_boxed_428_, v_action_425_, v_a_426_);
lean_dec_ref(v_a_426_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__0(lean_object* v_x_430_){
_start:
{
if (lean_obj_tag(v_x_430_) == 0)
{
lean_object* v___x_432_; 
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v_x_430_);
return v___x_432_;
}
else
{
lean_object* v___x_433_; 
lean_dec_ref_known(v_x_430_, 1);
v___x_433_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_433_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__0___boxed(lean_object* v_x_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Std_Http_Server_serve___redArg___lam__0(v_x_434_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1(lean_object* v_x_437_){
_start:
{
if (lean_obj_tag(v_x_437_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_447_; 
v_a_439_ = lean_ctor_get(v_x_437_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v_x_437_);
if (v_isSharedCheck_447_ == 0)
{
v___x_441_ = v_x_437_;
v_isShared_442_ = v_isSharedCheck_447_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v_x_437_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_447_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_439_);
v___x_444_ = v_reuseFailAlloc_446_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_445_; 
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
return v___x_445_;
}
}
}
else
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_476_; 
v_a_448_ = lean_ctor_get(v_x_437_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v_x_437_);
if (v_isSharedCheck_476_ == 0)
{
v___x_450_ = v_x_437_;
v_isShared_451_ = v_isSharedCheck_476_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v_x_437_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_476_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
if (lean_obj_tag(v_a_448_) == 0)
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_463_; 
v_a_452_ = lean_ctor_get(v_a_448_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v_a_448_);
if (v_isSharedCheck_463_ == 0)
{
v___x_454_ = v_a_448_;
v_isShared_455_ = v_isSharedCheck_463_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v_a_448_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_463_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
lean_ctor_set_tag(v___x_454_, 1);
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_462_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_459_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_457_);
v___x_459_ = v___x_450_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_461_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
lean_object* v___x_460_; 
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
return v___x_460_;
}
}
}
}
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_475_; 
v_a_464_ = lean_ctor_get(v_a_448_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v_a_448_);
if (v_isSharedCheck_475_ == 0)
{
v___x_466_ = v_a_448_;
v_isShared_467_ = v_isSharedCheck_475_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v_a_448_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_475_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
lean_ctor_set_tag(v___x_466_, 0);
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_474_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_471_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_469_);
v___x_471_ = v___x_450_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_469_);
v___x_471_ = v_reuseFailAlloc_473_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; 
v___x_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1___boxed(lean_object* v_x_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Std_Http_Server_serve___redArg___lam__1(v_x_477_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2(lean_object* v_x_480_){
_start:
{
lean_object* v_fst_481_; 
v_fst_481_ = lean_ctor_get(v_x_480_, 0);
lean_inc(v_fst_481_);
return v_fst_481_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2___boxed(lean_object* v_x_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Std_Http_Server_serve___redArg___lam__2(v_x_482_);
lean_dec_ref(v_x_482_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5(lean_object* v_x_488_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__5___closed__1));
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5___boxed(lean_object* v_x_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Std_Http_Server_serve___redArg___lam__5(v_x_491_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3(lean_object* v_x_494_){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_496_, 0, v_x_494_);
v___x_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3___boxed(lean_object* v_x_499_, lean_object* v___y_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Std_Http_Server_serve___redArg___lam__3(v_x_499_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4(lean_object* v_x_502_){
_start:
{
if (lean_obj_tag(v_x_502_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_512_; 
v_a_504_ = lean_ctor_get(v_x_502_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v_x_502_);
if (v_isSharedCheck_512_ == 0)
{
v___x_506_ = v_x_502_;
v_isShared_507_ = v_isSharedCheck_512_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v_x_502_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_512_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_511_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
lean_object* v___x_510_; 
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
}
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_523_; 
v_a_513_ = lean_ctor_get(v_x_502_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v_x_502_);
if (v_isSharedCheck_523_ == 0)
{
v___x_515_ = v_x_502_;
v_isShared_516_ = v_isSharedCheck_523_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v_x_502_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_523_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v_token_517_; lean_object* v___x_518_; lean_object* v___x_520_; 
v_token_517_ = lean_ctor_get(v_a_513_, 1);
lean_inc_ref(v_token_517_);
lean_dec(v_a_513_);
v___x_518_ = l_Std_CancellationToken_selector(v_token_517_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 0, v___x_518_);
v___x_520_ = v___x_515_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_518_);
v___x_520_ = v_reuseFailAlloc_522_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_521_; 
v___x_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
return v___x_521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4___boxed(lean_object* v_x_524_, lean_object* v___y_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Std_Http_Server_serve___redArg___lam__4(v_x_524_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10(lean_object* v___x_527_, lean_object* v_____r_528_, lean_object* v___y_529_){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_527_);
v___x_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10___boxed(lean_object* v___x_534_, lean_object* v_____r_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Std_Http_Server_serve___redArg___lam__10(v___x_534_, v_____r_535_, v___y_536_);
lean_dec_ref(v___y_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6(lean_object* v___x_539_, lean_object* v_x_540_){
_start:
{
if (lean_obj_tag(v_x_540_) == 0)
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_550_; 
v_a_542_ = lean_ctor_get(v_x_540_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v_x_540_);
if (v_isSharedCheck_550_ == 0)
{
v___x_544_ = v_x_540_;
v_isShared_545_ = v_isSharedCheck_550_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v_x_540_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_550_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_549_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_548_; 
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
}
}
else
{
lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_559_; 
v_isSharedCheck_559_ = !lean_is_exclusive(v_x_540_);
if (v_isSharedCheck_559_ == 0)
{
lean_object* v_unused_560_; 
v_unused_560_ = lean_ctor_get(v_x_540_, 0);
lean_dec(v_unused_560_);
v___x_552_ = v_x_540_;
v_isShared_553_ = v_isSharedCheck_559_;
goto v_resetjp_551_;
}
else
{
lean_dec(v_x_540_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_559_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_539_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_554_);
v___x_556_ = v___x_552_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_558_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_557_; 
v___x_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
return v___x_557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6___boxed(lean_object* v___x_561_, lean_object* v_x_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Std_Http_Server_serve___redArg___lam__6(v___x_561_, v_x_562_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7(lean_object* v___f_565_, lean_object* v___y_566_, lean_object* v_x_567_){
_start:
{
if (lean_obj_tag(v_x_567_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_577_; 
lean_dec_ref(v___f_565_);
v_a_569_ = lean_ctor_get(v_x_567_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v_x_567_);
if (v_isSharedCheck_577_ == 0)
{
v___x_571_ = v_x_567_;
v_isShared_572_ = v_isSharedCheck_577_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v_x_567_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_577_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_569_);
v___x_574_ = v_reuseFailAlloc_576_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_575_; 
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_579_; 
v_a_578_ = lean_ctor_get(v_x_567_, 0);
lean_inc(v_a_578_);
lean_dec_ref_known(v_x_567_, 1);
lean_inc_ref(v___y_566_);
v___x_579_ = lean_apply_3(v___f_565_, v_a_578_, v___y_566_, lean_box(0));
return v___x_579_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7___boxed(lean_object* v___f_580_, lean_object* v___y_581_, lean_object* v_x_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Std_Http_Server_serve___redArg___lam__7(v___f_580_, v___y_581_, v_x_582_);
lean_dec_ref(v___y_581_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8(lean_object* v_a_585_, lean_object* v_x_586_){
_start:
{
if (lean_obj_tag(v_x_586_) == 0)
{
lean_object* v___x_588_; 
lean_dec_ref(v_a_585_);
v___x_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_588_, 0, v_x_586_);
return v___x_588_;
}
else
{
lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_598_; 
v_isSharedCheck_598_ = !lean_is_exclusive(v_x_586_);
if (v_isSharedCheck_598_ == 0)
{
lean_object* v_unused_599_; 
v_unused_599_ = lean_ctor_get(v_x_586_, 0);
lean_dec(v_unused_599_);
v___x_590_ = v_x_586_;
v_isShared_591_ = v_isSharedCheck_598_;
goto v_resetjp_589_;
}
else
{
lean_dec(v_x_586_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_598_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_592_ = lean_box(2);
v___x_593_ = l_Std_CancellationContext_cancel(v_a_585_, v___x_592_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_593_);
v___x_595_ = v___x_590_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_593_);
v___x_595_ = v_reuseFailAlloc_597_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_596_; 
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
return v___x_596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8___boxed(lean_object* v_a_600_, lean_object* v_x_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Std_Http_Server_serve___redArg___lam__8(v_a_600_, v_x_601_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11(lean_object* v___f_604_, lean_object* v_a_605_, lean_object* v_x_606_){
_start:
{
if (lean_obj_tag(v_x_606_) == 0)
{
lean_object* v___x_608_; 
lean_dec_ref(v_a_605_);
lean_dec_ref(v___f_604_);
v___x_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_608_, 0, v_x_606_);
return v___x_608_;
}
else
{
lean_object* v_a_609_; lean_object* v___x_610_; 
v_a_609_ = lean_ctor_get(v_x_606_, 0);
lean_inc(v_a_609_);
lean_dec_ref_known(v_x_606_, 1);
v___x_610_ = lean_apply_3(v___f_604_, v_a_609_, v_a_605_, lean_box(0));
return v___x_610_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11___boxed(lean_object* v___f_611_, lean_object* v_a_612_, lean_object* v_x_613_, lean_object* v___y_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Std_Http_Server_serve___redArg___lam__11(v___f_611_, v_a_612_, v_x_613_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9(uint8_t v_permitAcquired_616_, lean_object* v___f_617_, lean_object* v___x_618_, lean_object* v_a_619_, lean_object* v_connectionLimit_620_, lean_object* v___x_621_, uint8_t v___x_622_, lean_object* v___f_623_, lean_object* v_opt_624_){
_start:
{
if (v_permitAcquired_616_ == 0)
{
lean_object* v___x_626_; 
lean_dec_ref(v___f_623_);
lean_dec(v___x_621_);
lean_dec(v_connectionLimit_620_);
v___x_626_ = lean_apply_3(v___f_617_, v___x_618_, v_a_619_, lean_box(0));
return v___x_626_;
}
else
{
if (lean_obj_tag(v_connectionLimit_620_) == 1)
{
lean_object* v_val_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_637_; 
lean_dec_ref(v_a_619_);
lean_dec_ref(v___f_617_);
v_val_627_ = lean_ctor_get(v_connectionLimit_620_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v_connectionLimit_620_);
if (v_isSharedCheck_637_ == 0)
{
v___x_629_ = v_connectionLimit_620_;
v_isShared_630_ = v_isSharedCheck_637_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_val_627_);
lean_dec(v_connectionLimit_620_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_637_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_631_ = l_Std_Semaphore_release(v_val_627_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v___x_631_);
v___x_633_ = v___x_629_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_631_);
v___x_633_ = v_reuseFailAlloc_636_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
v___x_635_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_621_, v___x_622_, v___x_634_, v___f_623_);
return v___x_635_;
}
}
}
else
{
lean_object* v___x_638_; 
lean_dec_ref(v___f_623_);
lean_dec(v___x_621_);
lean_dec(v_connectionLimit_620_);
v___x_638_ = lean_apply_3(v___f_617_, v___x_618_, v_a_619_, lean_box(0));
return v___x_638_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9___boxed(lean_object* v_permitAcquired_639_, lean_object* v___f_640_, lean_object* v___x_641_, lean_object* v_a_642_, lean_object* v_connectionLimit_643_, lean_object* v___x_644_, lean_object* v___x_645_, lean_object* v___f_646_, lean_object* v_opt_647_, lean_object* v___y_648_){
_start:
{
uint8_t v_permitAcquired_boxed_649_; uint8_t v___x_13525__boxed_650_; lean_object* v_res_651_; 
v_permitAcquired_boxed_649_ = lean_unbox(v_permitAcquired_639_);
v___x_13525__boxed_650_ = lean_unbox(v___x_645_);
v_res_651_ = l_Std_Http_Server_serve___redArg___lam__9(v_permitAcquired_boxed_649_, v___f_640_, v___x_641_, v_a_642_, v_connectionLimit_643_, v___x_644_, v___x_13525__boxed_650_, v___f_646_, v_opt_647_);
lean_dec(v_opt_647_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12(lean_object* v___x_652_, lean_object* v_inst_653_, lean_object* v_val_654_, lean_object* v_handler_655_, lean_object* v_config_656_, lean_object* v_extensions_657_, lean_object* v_a_658_, lean_object* v___f_659_, lean_object* v___x_660_, uint8_t v___x_661_, lean_object* v___f_662_, lean_object* v_x_663_){
_start:
{
if (lean_obj_tag(v_x_663_) == 0)
{
lean_object* v___x_665_; 
lean_dec_ref(v___f_662_);
lean_dec(v___x_660_);
lean_dec_ref(v___f_659_);
lean_dec_ref(v_a_658_);
lean_dec(v_extensions_657_);
lean_dec_ref(v_config_656_);
lean_dec(v_handler_655_);
lean_dec(v_val_654_);
lean_dec_ref(v_inst_653_);
lean_dec_ref(v___x_652_);
v___x_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_665_, 0, v_x_663_);
return v___x_665_;
}
else
{
lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_704_; 
v_isSharedCheck_704_ = !lean_is_exclusive(v_x_663_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; 
v_unused_705_ = lean_ctor_get(v_x_663_, 0);
lean_dec(v_unused_705_);
v___x_667_ = v_x_663_;
v_isShared_668_ = v_isSharedCheck_704_;
goto v_resetjp_666_;
}
else
{
lean_dec(v_x_663_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_704_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___y_672_; 
v___x_669_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___boxed), 10, 9);
lean_closure_set(v___x_669_, 0, lean_box(0));
lean_closure_set(v___x_669_, 1, lean_box(0));
lean_closure_set(v___x_669_, 2, v___x_652_);
lean_closure_set(v___x_669_, 3, v_inst_653_);
lean_closure_set(v___x_669_, 4, v_val_654_);
lean_closure_set(v___x_669_, 5, v_handler_655_);
lean_closure_set(v___x_669_, 6, v_config_656_);
lean_closure_set(v___x_669_, 7, v_extensions_657_);
lean_closure_set(v___x_669_, 8, v_a_658_);
lean_inc(v___x_660_);
v___x_670_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_669_, v___f_659_, v___x_660_, v___x_661_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_676_; 
lean_dec_ref(v___f_662_);
lean_dec(v___x_660_);
v_a_676_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_676_);
lean_dec_ref_known(v___x_670_, 1);
if (lean_obj_tag(v_a_676_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
v_a_677_ = lean_ctor_get(v_a_676_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v_a_676_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v_a_676_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v_a_676_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
v___y_672_ = v___x_682_;
goto v___jp_671_;
}
}
}
else
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_693_; 
v_a_685_ = lean_ctor_get(v_a_676_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v_a_676_);
if (v_isSharedCheck_693_ == 0)
{
v___x_687_ = v_a_676_;
v_isShared_688_ = v_isSharedCheck_693_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v_a_676_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_693_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v_fst_689_; lean_object* v___x_691_; 
v_fst_689_ = lean_ctor_get(v_a_685_, 0);
lean_inc(v_fst_689_);
lean_dec(v_a_685_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v_fst_689_);
v___x_691_ = v___x_687_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_fst_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
v___y_672_ = v___x_691_;
goto v___jp_671_;
}
}
}
}
else
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_703_; 
lean_del_object(v___x_667_);
v_a_694_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_703_ == 0)
{
v___x_696_ = v___x_670_;
v_isShared_697_ = v_isSharedCheck_703_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_670_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_703_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_701_; 
v___x_698_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_698_, 0, lean_box(0));
lean_closure_set(v___x_698_, 1, lean_box(0));
lean_closure_set(v___x_698_, 2, lean_box(0));
lean_closure_set(v___x_698_, 3, v___f_662_);
v___x_699_ = lean_task_map(v___x_698_, v_a_694_, v___x_660_, v___x_661_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v___x_699_);
v___x_701_ = v___x_696_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
v___jp_671_:
{
lean_object* v___x_674_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set_tag(v___x_667_, 0);
lean_ctor_set(v___x_667_, 0, v___y_672_);
v___x_674_ = v___x_667_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___y_672_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12___boxed(lean_object* v___x_706_, lean_object* v_inst_707_, lean_object* v_val_708_, lean_object* v_handler_709_, lean_object* v_config_710_, lean_object* v_extensions_711_, lean_object* v_a_712_, lean_object* v___f_713_, lean_object* v___x_714_, lean_object* v___x_715_, lean_object* v___f_716_, lean_object* v_x_717_, lean_object* v___y_718_){
_start:
{
uint8_t v___x_13574__boxed_719_; lean_object* v_res_720_; 
v___x_13574__boxed_719_ = lean_unbox(v___x_715_);
v_res_720_ = l_Std_Http_Server_serve___redArg___lam__12(v___x_706_, v_inst_707_, v_val_708_, v_handler_709_, v_config_710_, v_extensions_711_, v_a_712_, v___f_713_, v___x_714_, v___x_13574__boxed_719_, v___f_716_, v_x_717_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13(lean_object* v___x_721_, lean_object* v_activeConnections_722_, lean_object* v___f_723_, lean_object* v_a_724_, lean_object* v___f_725_, lean_object* v___f_726_, uint8_t v_permitAcquired_727_, lean_object* v___x_728_, lean_object* v_connectionLimit_729_, lean_object* v___x_730_, uint8_t v___x_731_, lean_object* v___x_732_, lean_object* v_inst_733_, lean_object* v_val_734_, lean_object* v_handler_735_, lean_object* v_config_736_, lean_object* v_extensions_737_, lean_object* v___f_738_, lean_object* v___f_739_){
_start:
{
lean_object* v___f_741_; lean_object* v___f_742_; lean_object* v___x_12697__overap_743_; lean_object* v___x_744_; lean_object* v___f_745_; lean_object* v___f_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___f_749_; lean_object* v___x_750_; lean_object* v___f_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___f_741_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3));
v___f_742_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4));
lean_inc_ref(v_activeConnections_722_);
lean_inc_ref(v___x_721_);
v___x_12697__overap_743_ = l_Std_Mutex_atomically___redArg(v___x_721_, v___f_741_, v___f_742_, v_activeConnections_722_, v___f_723_);
lean_inc_ref_n(v_a_724_, 3);
v___x_744_ = lean_apply_2(v___x_12697__overap_743_, v_a_724_, lean_box(0));
v___f_745_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed), 9, 6);
lean_closure_set(v___f_745_, 0, v___x_721_);
lean_closure_set(v___f_745_, 1, v___f_725_);
lean_closure_set(v___f_745_, 2, v___f_726_);
lean_closure_set(v___f_745_, 3, v___f_741_);
lean_closure_set(v___f_745_, 4, v___f_742_);
lean_closure_set(v___f_745_, 5, v_activeConnections_722_);
lean_inc_ref(v___f_745_);
v___f_746_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__11___boxed), 4, 2);
lean_closure_set(v___f_746_, 0, v___f_745_);
lean_closure_set(v___f_746_, 1, v_a_724_);
v___x_747_ = lean_box(v_permitAcquired_727_);
v___x_748_ = lean_box(v___x_731_);
lean_inc_n(v___x_730_, 3);
v___f_749_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__9___boxed), 10, 8);
lean_closure_set(v___f_749_, 0, v___x_747_);
lean_closure_set(v___f_749_, 1, v___f_745_);
lean_closure_set(v___f_749_, 2, v___x_728_);
lean_closure_set(v___f_749_, 3, v_a_724_);
lean_closure_set(v___f_749_, 4, v_connectionLimit_729_);
lean_closure_set(v___f_749_, 5, v___x_730_);
lean_closure_set(v___f_749_, 6, v___x_748_);
lean_closure_set(v___f_749_, 7, v___f_746_);
v___x_750_ = lean_box(v___x_731_);
v___f_751_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__12___boxed), 13, 11);
lean_closure_set(v___f_751_, 0, v___x_732_);
lean_closure_set(v___f_751_, 1, v_inst_733_);
lean_closure_set(v___f_751_, 2, v_val_734_);
lean_closure_set(v___f_751_, 3, v_handler_735_);
lean_closure_set(v___f_751_, 4, v_config_736_);
lean_closure_set(v___f_751_, 5, v_extensions_737_);
lean_closure_set(v___f_751_, 6, v_a_724_);
lean_closure_set(v___f_751_, 7, v___f_749_);
lean_closure_set(v___f_751_, 8, v___x_730_);
lean_closure_set(v___f_751_, 9, v___x_750_);
lean_closure_set(v___f_751_, 10, v___f_738_);
v___x_752_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_730_, v___x_731_, v___x_744_, v___f_751_);
v___x_753_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_730_, v___x_731_, v___x_752_, v___f_739_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13___boxed(lean_object** _args){
lean_object* v___x_754_ = _args[0];
lean_object* v_activeConnections_755_ = _args[1];
lean_object* v___f_756_ = _args[2];
lean_object* v_a_757_ = _args[3];
lean_object* v___f_758_ = _args[4];
lean_object* v___f_759_ = _args[5];
lean_object* v_permitAcquired_760_ = _args[6];
lean_object* v___x_761_ = _args[7];
lean_object* v_connectionLimit_762_ = _args[8];
lean_object* v___x_763_ = _args[9];
lean_object* v___x_764_ = _args[10];
lean_object* v___x_765_ = _args[11];
lean_object* v_inst_766_ = _args[12];
lean_object* v_val_767_ = _args[13];
lean_object* v_handler_768_ = _args[14];
lean_object* v_config_769_ = _args[15];
lean_object* v_extensions_770_ = _args[16];
lean_object* v___f_771_ = _args[17];
lean_object* v___f_772_ = _args[18];
lean_object* v___y_773_ = _args[19];
_start:
{
uint8_t v_permitAcquired_boxed_774_; uint8_t v___x_13693__boxed_775_; lean_object* v_res_776_; 
v_permitAcquired_boxed_774_ = lean_unbox(v_permitAcquired_760_);
v___x_13693__boxed_775_ = lean_unbox(v___x_764_);
v_res_776_ = l_Std_Http_Server_serve___redArg___lam__13(v___x_754_, v_activeConnections_755_, v___f_756_, v_a_757_, v___f_758_, v___f_759_, v_permitAcquired_boxed_774_, v___x_761_, v_connectionLimit_762_, v___x_763_, v___x_13693__boxed_775_, v___x_765_, v_inst_766_, v_val_767_, v_handler_768_, v_config_769_, v_extensions_770_, v___f_771_, v___f_772_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14(lean_object* v___x_777_, lean_object* v_activeConnections_778_, lean_object* v___f_779_, lean_object* v___f_780_, lean_object* v___f_781_, uint8_t v_permitAcquired_782_, lean_object* v___x_783_, lean_object* v_connectionLimit_784_, lean_object* v___x_785_, uint8_t v___x_786_, lean_object* v___x_787_, lean_object* v_inst_788_, lean_object* v_val_789_, lean_object* v_handler_790_, lean_object* v_config_791_, lean_object* v_extensions_792_, lean_object* v___f_793_, lean_object* v_x_794_){
_start:
{
if (lean_obj_tag(v_x_794_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_804_; 
lean_dec_ref(v___f_793_);
lean_dec(v_extensions_792_);
lean_dec_ref(v_config_791_);
lean_dec(v_handler_790_);
lean_dec(v_val_789_);
lean_dec_ref(v_inst_788_);
lean_dec_ref(v___x_787_);
lean_dec(v___x_785_);
lean_dec(v_connectionLimit_784_);
lean_dec_ref(v___f_781_);
lean_dec_ref(v___f_780_);
lean_dec_ref(v___f_779_);
lean_dec_ref(v_activeConnections_778_);
lean_dec_ref(v___x_777_);
v_a_796_ = lean_ctor_get(v_x_794_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v_x_794_);
if (v_isSharedCheck_804_ == 0)
{
v___x_798_ = v_x_794_;
v_isShared_799_ = v_isSharedCheck_804_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v_x_794_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_804_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_803_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_802_; 
v___x_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
return v___x_802_;
}
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_819_; 
v_a_805_ = lean_ctor_get(v_x_794_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v_x_794_);
if (v_isSharedCheck_819_ == 0)
{
v___x_807_ = v_x_794_;
v_isShared_808_ = v_isSharedCheck_819_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v_x_794_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_819_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___f_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___f_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_816_; 
lean_inc(v_a_805_);
v___f_809_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__8___boxed), 3, 1);
lean_closure_set(v___f_809_, 0, v_a_805_);
v___x_810_ = lean_box(v_permitAcquired_782_);
v___x_811_ = lean_box(v___x_786_);
lean_inc(v___x_785_);
v___f_812_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__13___boxed), 20, 19);
lean_closure_set(v___f_812_, 0, v___x_777_);
lean_closure_set(v___f_812_, 1, v_activeConnections_778_);
lean_closure_set(v___f_812_, 2, v___f_779_);
lean_closure_set(v___f_812_, 3, v_a_805_);
lean_closure_set(v___f_812_, 4, v___f_780_);
lean_closure_set(v___f_812_, 5, v___f_781_);
lean_closure_set(v___f_812_, 6, v___x_810_);
lean_closure_set(v___f_812_, 7, v___x_783_);
lean_closure_set(v___f_812_, 8, v_connectionLimit_784_);
lean_closure_set(v___f_812_, 9, v___x_785_);
lean_closure_set(v___f_812_, 10, v___x_811_);
lean_closure_set(v___f_812_, 11, v___x_787_);
lean_closure_set(v___f_812_, 12, v_inst_788_);
lean_closure_set(v___f_812_, 13, v_val_789_);
lean_closure_set(v___f_812_, 14, v_handler_790_);
lean_closure_set(v___f_812_, 15, v_config_791_);
lean_closure_set(v___f_812_, 16, v_extensions_792_);
lean_closure_set(v___f_812_, 17, v___f_793_);
lean_closure_set(v___f_812_, 18, v___f_809_);
v___x_813_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_813_, 0, lean_box(0));
lean_closure_set(v___x_813_, 1, v___f_812_);
v___x_814_ = lean_io_as_task(v___x_813_, v___x_785_);
lean_dec_ref(v___x_814_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_783_);
v___x_816_ = v___x_807_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_783_);
v___x_816_ = v_reuseFailAlloc_818_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_817_; 
v___x_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
return v___x_817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14___boxed(lean_object** _args){
lean_object* v___x_820_ = _args[0];
lean_object* v_activeConnections_821_ = _args[1];
lean_object* v___f_822_ = _args[2];
lean_object* v___f_823_ = _args[3];
lean_object* v___f_824_ = _args[4];
lean_object* v_permitAcquired_825_ = _args[5];
lean_object* v___x_826_ = _args[6];
lean_object* v_connectionLimit_827_ = _args[7];
lean_object* v___x_828_ = _args[8];
lean_object* v___x_829_ = _args[9];
lean_object* v___x_830_ = _args[10];
lean_object* v_inst_831_ = _args[11];
lean_object* v_val_832_ = _args[12];
lean_object* v_handler_833_ = _args[13];
lean_object* v_config_834_ = _args[14];
lean_object* v_extensions_835_ = _args[15];
lean_object* v___f_836_ = _args[16];
lean_object* v_x_837_ = _args[17];
lean_object* v___y_838_ = _args[18];
_start:
{
uint8_t v_permitAcquired_boxed_839_; uint8_t v___x_13760__boxed_840_; lean_object* v_res_841_; 
v_permitAcquired_boxed_839_ = lean_unbox(v_permitAcquired_825_);
v___x_13760__boxed_840_ = lean_unbox(v___x_829_);
v_res_841_ = l_Std_Http_Server_serve___redArg___lam__14(v___x_820_, v_activeConnections_821_, v___f_822_, v___f_823_, v___f_824_, v_permitAcquired_boxed_839_, v___x_826_, v_connectionLimit_827_, v___x_828_, v___x_13760__boxed_840_, v___x_830_, v_inst_831_, v_val_832_, v_handler_833_, v_config_834_, v_extensions_835_, v___f_836_, v_x_837_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15(lean_object* v___x_842_, uint8_t v___x_843_, lean_object* v___f_844_, lean_object* v_x_845_){
_start:
{
if (lean_obj_tag(v_x_845_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_855_; 
lean_dec_ref(v___f_844_);
lean_dec(v___x_842_);
v_a_847_ = lean_ctor_get(v_x_845_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v_x_845_);
if (v_isSharedCheck_855_ == 0)
{
v___x_849_ = v_x_845_;
v_isShared_850_ = v_isSharedCheck_855_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v_x_845_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_855_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_847_);
v___x_852_ = v_reuseFailAlloc_854_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_853_; 
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
return v___x_853_;
}
}
}
else
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_866_; 
v_a_856_ = lean_ctor_get(v_x_845_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v_x_845_);
if (v_isSharedCheck_866_ == 0)
{
v___x_858_ = v_x_845_;
v_isShared_859_ = v_isSharedCheck_866_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v_x_845_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_866_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_860_; lean_object* v___x_862_; 
v___x_860_ = l_Std_CancellationContext_fork(v_a_856_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_860_);
v___x_862_ = v___x_858_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_860_);
v___x_862_ = v_reuseFailAlloc_865_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
v___x_864_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_842_, v___x_843_, v___x_863_, v___f_844_);
return v___x_864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15___boxed(lean_object* v___x_867_, lean_object* v___x_868_, lean_object* v___f_869_, lean_object* v_x_870_, lean_object* v___y_871_){
_start:
{
uint8_t v___x_13842__boxed_872_; lean_object* v_res_873_; 
v___x_13842__boxed_872_ = lean_unbox(v___x_868_);
v_res_873_ = l_Std_Http_Server_serve___redArg___lam__15(v___x_867_, v___x_13842__boxed_872_, v___f_869_, v_x_870_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16(lean_object* v___x_874_, lean_object* v_activeConnections_875_, lean_object* v___f_876_, lean_object* v___f_877_, lean_object* v___f_878_, uint8_t v_permitAcquired_879_, lean_object* v___x_880_, lean_object* v_connectionLimit_881_, uint8_t v___x_882_, lean_object* v___x_883_, lean_object* v_inst_884_, lean_object* v_val_885_, lean_object* v_handler_886_, lean_object* v_config_887_, lean_object* v___f_888_, lean_object* v___f_889_, lean_object* v_extensions_890_, lean_object* v___y_891_){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___f_896_; lean_object* v___x_897_; lean_object* v___f_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_893_ = lean_unsigned_to_nat(0u);
v___x_894_ = lean_box(v_permitAcquired_879_);
v___x_895_ = lean_box(v___x_882_);
v___f_896_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__14___boxed), 19, 17);
lean_closure_set(v___f_896_, 0, v___x_874_);
lean_closure_set(v___f_896_, 1, v_activeConnections_875_);
lean_closure_set(v___f_896_, 2, v___f_876_);
lean_closure_set(v___f_896_, 3, v___f_877_);
lean_closure_set(v___f_896_, 4, v___f_878_);
lean_closure_set(v___f_896_, 5, v___x_894_);
lean_closure_set(v___f_896_, 6, v___x_880_);
lean_closure_set(v___f_896_, 7, v_connectionLimit_881_);
lean_closure_set(v___f_896_, 8, v___x_893_);
lean_closure_set(v___f_896_, 9, v___x_895_);
lean_closure_set(v___f_896_, 10, v___x_883_);
lean_closure_set(v___f_896_, 11, v_inst_884_);
lean_closure_set(v___f_896_, 12, v_val_885_);
lean_closure_set(v___f_896_, 13, v_handler_886_);
lean_closure_set(v___f_896_, 14, v_config_887_);
lean_closure_set(v___f_896_, 15, v_extensions_890_);
lean_closure_set(v___f_896_, 16, v___f_888_);
v___x_897_ = lean_box(v___x_882_);
v___f_898_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__15___boxed), 5, 3);
lean_closure_set(v___f_898_, 0, v___x_893_);
lean_closure_set(v___f_898_, 1, v___x_897_);
lean_closure_set(v___f_898_, 2, v___f_896_);
lean_inc_ref(v___y_891_);
v___x_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_899_, 0, v___y_891_);
v___x_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
v___x_901_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_893_, v___x_882_, v___x_900_, v___f_898_);
v___x_902_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_893_, v___x_882_, v___x_901_, v___f_889_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16___boxed(lean_object** _args){
lean_object* v___x_903_ = _args[0];
lean_object* v_activeConnections_904_ = _args[1];
lean_object* v___f_905_ = _args[2];
lean_object* v___f_906_ = _args[3];
lean_object* v___f_907_ = _args[4];
lean_object* v_permitAcquired_908_ = _args[5];
lean_object* v___x_909_ = _args[6];
lean_object* v_connectionLimit_910_ = _args[7];
lean_object* v___x_911_ = _args[8];
lean_object* v___x_912_ = _args[9];
lean_object* v_inst_913_ = _args[10];
lean_object* v_val_914_ = _args[11];
lean_object* v_handler_915_ = _args[12];
lean_object* v_config_916_ = _args[13];
lean_object* v___f_917_ = _args[14];
lean_object* v___f_918_ = _args[15];
lean_object* v_extensions_919_ = _args[16];
lean_object* v___y_920_ = _args[17];
lean_object* v___y_921_ = _args[18];
_start:
{
uint8_t v_permitAcquired_boxed_922_; uint8_t v___x_13901__boxed_923_; lean_object* v_res_924_; 
v_permitAcquired_boxed_922_ = lean_unbox(v_permitAcquired_908_);
v___x_13901__boxed_923_ = lean_unbox(v___x_911_);
v_res_924_ = l_Std_Http_Server_serve___redArg___lam__16(v___x_903_, v_activeConnections_904_, v___f_905_, v___f_906_, v___f_907_, v_permitAcquired_boxed_922_, v___x_909_, v_connectionLimit_910_, v___x_13901__boxed_923_, v___x_912_, v_inst_913_, v_val_914_, v_handler_915_, v_config_916_, v___f_917_, v___f_918_, v_extensions_919_, v___y_920_);
lean_dec_ref(v___y_920_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17(lean_object* v___f_925_, lean_object* v___y_926_, lean_object* v_x_927_){
_start:
{
if (lean_obj_tag(v_x_927_) == 0)
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_937_; 
lean_dec_ref(v___f_925_);
v_a_929_ = lean_ctor_get(v_x_927_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v_x_927_);
if (v_isSharedCheck_937_ == 0)
{
v___x_931_ = v_x_927_;
v_isShared_932_ = v_isSharedCheck_937_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v_x_927_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_937_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_936_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_935_; 
v___x_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
return v___x_935_;
}
}
}
else
{
lean_object* v_a_938_; lean_object* v___x_939_; 
v_a_938_ = lean_ctor_get(v_x_927_, 0);
lean_inc(v_a_938_);
lean_dec_ref_known(v_x_927_, 1);
lean_inc_ref(v___y_926_);
v___x_939_ = lean_apply_3(v___f_925_, v_a_938_, v___y_926_, lean_box(0));
return v___x_939_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17___boxed(lean_object* v___f_940_, lean_object* v___y_941_, lean_object* v_x_942_, lean_object* v___y_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Std_Http_Server_serve___redArg___lam__17(v___f_940_, v___y_941_, v_x_942_);
lean_dec_ref(v___y_941_);
return v_res_944_;
}
}
static lean_object* _init_l_Std_Http_Server_serve___redArg___lam__19___closed__0(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = l_Std_Http_Extensions_empty;
v___x_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
return v___x_946_;
}
}
static lean_object* _init_l_Std_Http_Server_serve___redArg___lam__19___closed__1(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_obj_once(&l_Std_Http_Server_serve___redArg___lam__19___closed__0, &l_Std_Http_Server_serve___redArg___lam__19___closed__0_once, _init_l_Std_Http_Server_serve___redArg___lam__19___closed__0);
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__19(uint8_t v___x_950_, lean_object* v___f_951_, lean_object* v___x_952_, lean_object* v___f_953_, lean_object* v_x_954_){
_start:
{
if (lean_obj_tag(v_x_954_) == 0)
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_964_; 
lean_dec_ref(v___f_953_);
lean_dec(v___x_952_);
lean_dec_ref(v___f_951_);
v_a_956_ = lean_ctor_get(v_x_954_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v_x_954_);
if (v_isSharedCheck_964_ == 0)
{
v___x_958_ = v_x_954_;
v_isShared_959_ = v_isSharedCheck_964_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v_x_954_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_964_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_963_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_962_; 
v___x_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
return v___x_962_;
}
}
}
else
{
lean_object* v_a_965_; 
v_a_965_ = lean_ctor_get(v_x_954_, 0);
lean_inc(v_a_965_);
lean_dec_ref_known(v_x_954_, 1);
if (lean_obj_tag(v_a_965_) == 0)
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
lean_dec_ref_known(v_a_965_, 1);
lean_dec_ref(v___f_953_);
lean_dec(v___x_952_);
v___x_966_ = lean_obj_once(&l_Std_Http_Server_serve___redArg___lam__19___closed__1, &l_Std_Http_Server_serve___redArg___lam__19___closed__1_once, _init_l_Std_Http_Server_serve___redArg___lam__19___closed__1);
v___x_967_ = lean_unsigned_to_nat(0u);
v___x_968_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_967_, v___x_950_, v___x_966_, v___f_951_);
return v___x_968_;
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_984_; 
lean_dec_ref(v___f_951_);
v_a_969_ = lean_ctor_get(v_a_965_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v_a_965_);
if (v_isSharedCheck_984_ == 0)
{
v___x_971_ = v_a_965_;
v_isShared_972_ = v_isSharedCheck_984_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v_a_965_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_984_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v_dyn_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_979_; 
v___x_973_ = l_Std_Http_Extensions_empty;
v_dyn_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_974_, 0, v___x_952_);
lean_ctor_set(v_dyn_974_, 1, v_a_969_);
v___x_975_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__19___closed__2));
v___x_976_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_974_);
v___x_977_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_975_, v___x_976_, v_dyn_974_, v___x_973_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_977_);
v___x_979_ = v___x_971_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_977_);
v___x_979_ = v_reuseFailAlloc_983_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
v___x_981_ = lean_unsigned_to_nat(0u);
v___x_982_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_981_, v___x_950_, v___x_980_, v___f_953_);
return v___x_982_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__19___boxed(lean_object* v___x_985_, lean_object* v___f_986_, lean_object* v___x_987_, lean_object* v___f_988_, lean_object* v_x_989_, lean_object* v___y_990_){
_start:
{
uint8_t v___x_13999__boxed_991_; lean_object* v_res_992_; 
v___x_13999__boxed_991_ = lean_unbox(v___x_985_);
v_res_992_ = l_Std_Http_Server_serve___redArg___lam__19(v___x_13999__boxed_991_, v___f_986_, v___x_987_, v___f_988_, v_x_989_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18(uint8_t v_permitAcquired_993_, lean_object* v___f_994_, lean_object* v___x_995_, lean_object* v___y_996_, lean_object* v_connectionLimit_997_, uint8_t v___x_998_, lean_object* v___f_999_, lean_object* v___x_1000_, lean_object* v_activeConnections_1001_, lean_object* v___f_1002_, lean_object* v___f_1003_, lean_object* v___f_1004_, lean_object* v___x_1005_, lean_object* v_inst_1006_, lean_object* v_handler_1007_, lean_object* v_config_1008_, lean_object* v___f_1009_, lean_object* v___f_1010_, lean_object* v___x_1011_, lean_object* v_x_1012_){
_start:
{
if (lean_obj_tag(v_x_1012_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1022_; 
lean_dec(v___x_1011_);
lean_dec_ref(v___f_1010_);
lean_dec_ref(v___f_1009_);
lean_dec_ref(v_config_1008_);
lean_dec(v_handler_1007_);
lean_dec_ref(v_inst_1006_);
lean_dec_ref(v___x_1005_);
lean_dec_ref(v___f_1004_);
lean_dec_ref(v___f_1003_);
lean_dec_ref(v___f_1002_);
lean_dec_ref(v_activeConnections_1001_);
lean_dec_ref(v___x_1000_);
lean_dec_ref(v___f_999_);
lean_dec(v_connectionLimit_997_);
lean_dec_ref(v___f_994_);
v_a_1014_ = lean_ctor_get(v_x_1012_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_x_1012_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1016_ = v_x_1012_;
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v_x_1012_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
return v___x_1020_;
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1081_; 
v_a_1023_ = lean_ctor_get(v_x_1012_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_x_1012_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1025_ = v_x_1012_;
v_isShared_1026_ = v_isSharedCheck_1081_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v_x_1012_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1081_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
if (lean_obj_tag(v_a_1023_) == 0)
{
lean_dec(v___x_1011_);
lean_dec_ref(v___f_1010_);
lean_dec_ref(v___f_1009_);
lean_dec_ref(v_config_1008_);
lean_dec(v_handler_1007_);
lean_dec_ref(v_inst_1006_);
lean_dec_ref(v___x_1005_);
lean_dec_ref(v___f_1004_);
lean_dec_ref(v___f_1003_);
lean_dec_ref(v___f_1002_);
lean_dec_ref(v_activeConnections_1001_);
lean_dec_ref(v___x_1000_);
if (v_permitAcquired_993_ == 0)
{
lean_object* v___x_1027_; 
lean_del_object(v___x_1025_);
lean_dec_ref(v___f_999_);
lean_dec(v_connectionLimit_997_);
lean_inc_ref(v___y_996_);
v___x_1027_ = lean_apply_3(v___f_994_, v___x_995_, v___y_996_, lean_box(0));
return v___x_1027_;
}
else
{
if (lean_obj_tag(v_connectionLimit_997_) == 1)
{
lean_object* v_val_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1041_; 
lean_dec_ref(v___f_994_);
v_val_1028_ = lean_ctor_get(v_connectionLimit_997_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_connectionLimit_997_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1030_ = v_connectionLimit_997_;
v_isShared_1031_ = v_isSharedCheck_1041_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_val_1028_);
lean_dec(v_connectionLimit_997_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1041_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1032_ = l_Std_Semaphore_release(v_val_1028_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1032_);
v___x_1034_ = v___x_1025_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1036_; 
if (v_isShared_1031_ == 0)
{
lean_ctor_set_tag(v___x_1030_, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1034_);
v___x_1036_ = v___x_1030_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1034_);
v___x_1036_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = lean_unsigned_to_nat(0u);
v___x_1038_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1037_, v___x_998_, v___x_1036_, v___f_999_);
return v___x_1038_;
}
}
}
}
else
{
lean_object* v___x_1042_; 
lean_del_object(v___x_1025_);
lean_dec_ref(v___f_999_);
lean_dec(v_connectionLimit_997_);
lean_inc_ref(v___y_996_);
v___x_1042_ = lean_apply_3(v___f_994_, v___x_995_, v___y_996_, lean_box(0));
return v___x_1042_;
}
}
}
else
{
lean_object* v_val_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1080_; 
lean_dec_ref(v___f_999_);
lean_dec_ref(v___f_994_);
v_val_1043_ = lean_ctor_get(v_a_1023_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_a_1023_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1045_ = v_a_1023_;
v_isShared_1046_ = v_isSharedCheck_1080_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_val_1043_);
lean_dec(v_a_1023_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1080_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___f_1049_; lean_object* v___f_1050_; lean_object* v___x_1051_; lean_object* v___f_1052_; lean_object* v_val_1054_; lean_object* v___x_1063_; 
v___x_1047_ = lean_box(v_permitAcquired_993_);
v___x_1048_ = lean_box(v___x_998_);
lean_inc(v_val_1043_);
v___f_1049_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__16___boxed), 19, 16);
lean_closure_set(v___f_1049_, 0, v___x_1000_);
lean_closure_set(v___f_1049_, 1, v_activeConnections_1001_);
lean_closure_set(v___f_1049_, 2, v___f_1002_);
lean_closure_set(v___f_1049_, 3, v___f_1003_);
lean_closure_set(v___f_1049_, 4, v___f_1004_);
lean_closure_set(v___f_1049_, 5, v___x_1047_);
lean_closure_set(v___f_1049_, 6, v___x_995_);
lean_closure_set(v___f_1049_, 7, v_connectionLimit_997_);
lean_closure_set(v___f_1049_, 8, v___x_1048_);
lean_closure_set(v___f_1049_, 9, v___x_1005_);
lean_closure_set(v___f_1049_, 10, v_inst_1006_);
lean_closure_set(v___f_1049_, 11, v_val_1043_);
lean_closure_set(v___f_1049_, 12, v_handler_1007_);
lean_closure_set(v___f_1049_, 13, v_config_1008_);
lean_closure_set(v___f_1049_, 14, v___f_1009_);
lean_closure_set(v___f_1049_, 15, v___f_1010_);
lean_inc_ref(v___y_996_);
v___f_1050_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__17___boxed), 4, 2);
lean_closure_set(v___f_1050_, 0, v___f_1049_);
lean_closure_set(v___f_1050_, 1, v___y_996_);
v___x_1051_ = lean_box(v___x_998_);
lean_inc_ref(v___f_1050_);
v___f_1052_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__19___boxed), 6, 4);
lean_closure_set(v___f_1052_, 0, v___x_1051_);
lean_closure_set(v___f_1052_, 1, v___f_1050_);
lean_closure_set(v___f_1052_, 2, v___x_1011_);
lean_closure_set(v___f_1052_, 3, v___f_1050_);
v___x_1063_ = lean_uv_tcp_getpeername(v_val_1043_);
lean_dec(v_val_1043_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 1);
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
v_val_1054_ = v___x_1069_;
goto v___jp_1053_;
}
}
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
v_a_1072_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1063_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1063_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
lean_ctor_set_tag(v___x_1074_, 0);
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
v_val_1054_ = v___x_1077_;
goto v___jp_1053_;
}
}
}
v___jp_1053_:
{
lean_object* v___x_1056_; 
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v_val_1054_);
v___x_1056_ = v___x_1025_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_val_1054_);
v___x_1056_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
lean_object* v___x_1058_; 
if (v_isShared_1046_ == 0)
{
lean_ctor_set_tag(v___x_1045_, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1056_);
v___x_1058_ = v___x_1045_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1056_);
v___x_1058_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_unsigned_to_nat(0u);
v___x_1060_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1059_, v___x_998_, v___x_1058_, v___f_1052_);
return v___x_1060_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18___boxed(lean_object** _args){
lean_object* v_permitAcquired_1082_ = _args[0];
lean_object* v___f_1083_ = _args[1];
lean_object* v___x_1084_ = _args[2];
lean_object* v___y_1085_ = _args[3];
lean_object* v_connectionLimit_1086_ = _args[4];
lean_object* v___x_1087_ = _args[5];
lean_object* v___f_1088_ = _args[6];
lean_object* v___x_1089_ = _args[7];
lean_object* v_activeConnections_1090_ = _args[8];
lean_object* v___f_1091_ = _args[9];
lean_object* v___f_1092_ = _args[10];
lean_object* v___f_1093_ = _args[11];
lean_object* v___x_1094_ = _args[12];
lean_object* v_inst_1095_ = _args[13];
lean_object* v_handler_1096_ = _args[14];
lean_object* v_config_1097_ = _args[15];
lean_object* v___f_1098_ = _args[16];
lean_object* v___f_1099_ = _args[17];
lean_object* v___x_1100_ = _args[18];
lean_object* v_x_1101_ = _args[19];
lean_object* v___y_1102_ = _args[20];
_start:
{
uint8_t v_permitAcquired_boxed_1103_; uint8_t v___x_14082__boxed_1104_; lean_object* v_res_1105_; 
v_permitAcquired_boxed_1103_ = lean_unbox(v_permitAcquired_1082_);
v___x_14082__boxed_1104_ = lean_unbox(v___x_1087_);
v_res_1105_ = l_Std_Http_Server_serve___redArg___lam__18(v_permitAcquired_boxed_1103_, v___f_1083_, v___x_1084_, v___y_1085_, v_connectionLimit_1086_, v___x_14082__boxed_1104_, v___f_1088_, v___x_1089_, v_activeConnections_1090_, v___f_1091_, v___f_1092_, v___f_1093_, v___x_1094_, v_inst_1095_, v_handler_1096_, v_config_1097_, v___f_1098_, v___f_1099_, v___x_1100_, v_x_1101_);
lean_dec_ref(v___y_1085_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20(lean_object* v_a_1106_, lean_object* v___f_1107_, lean_object* v___f_1108_, uint8_t v___x_1109_, lean_object* v___f_1110_, lean_object* v_x_1111_){
_start:
{
if (lean_obj_tag(v_x_1111_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1121_; 
lean_dec_ref(v___f_1110_);
lean_dec_ref(v___f_1108_);
lean_dec_ref(v___f_1107_);
lean_dec(v_a_1106_);
v_a_1113_ = lean_ctor_get(v_x_1111_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_x_1111_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1115_ = v_x_1111_;
v_isShared_1116_ = v_isSharedCheck_1121_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v_x_1111_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1121_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
return v___x_1119_;
}
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v_a_1122_ = lean_ctor_get(v_x_1111_, 0);
lean_inc(v_a_1122_);
lean_dec_ref_known(v_x_1111_, 1);
v___x_1123_ = l_Std_Async_TCP_Socket_Server_acceptSelector(v_a_1106_);
v___x_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
lean_ctor_set(v___x_1124_, 1, v___f_1107_);
v___x_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1125_, 0, v_a_1122_);
lean_ctor_set(v___x_1125_, 1, v___f_1108_);
v___x_1126_ = lean_unsigned_to_nat(2u);
v___x_1127_ = lean_mk_empty_array_with_capacity(v___x_1126_);
v___x_1128_ = lean_array_push(v___x_1127_, v___x_1124_);
v___x_1129_ = lean_array_push(v___x_1128_, v___x_1125_);
v___x_1130_ = l_Std_Async_Selectable_one___redArg(v___x_1129_);
v___x_1131_ = lean_unsigned_to_nat(0u);
v___x_1132_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1131_, v___x_1109_, v___x_1130_, v___f_1110_);
return v___x_1132_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20___boxed(lean_object* v_a_1133_, lean_object* v___f_1134_, lean_object* v___f_1135_, lean_object* v___x_1136_, lean_object* v___f_1137_, lean_object* v_x_1138_, lean_object* v___y_1139_){
_start:
{
uint8_t v___x_14266__boxed_1140_; lean_object* v_res_1141_; 
v___x_14266__boxed_1140_ = lean_unbox(v___x_1136_);
v_res_1141_ = l_Std_Http_Server_serve___redArg___lam__20(v_a_1133_, v___f_1134_, v___f_1135_, v___x_14266__boxed_1140_, v___f_1137_, v_x_1138_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21(uint8_t v___x_1142_, lean_object* v___f_1143_, lean_object* v___f_1144_, lean_object* v___x_1145_, lean_object* v_connectionLimit_1146_, lean_object* v___x_1147_, lean_object* v_activeConnections_1148_, lean_object* v___f_1149_, lean_object* v___f_1150_, lean_object* v___f_1151_, lean_object* v___x_1152_, lean_object* v_inst_1153_, lean_object* v_handler_1154_, lean_object* v_config_1155_, lean_object* v___f_1156_, lean_object* v___f_1157_, lean_object* v___x_1158_, lean_object* v_a_1159_, lean_object* v___f_1160_, lean_object* v___f_1161_, uint8_t v_permitAcquired_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___f_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___f_1172_; lean_object* v___x_1173_; lean_object* v___f_1174_; lean_object* v___x_1175_; 
lean_inc_ref_n(v___y_1163_, 3);
v___x_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1165_, 0, v___y_1163_);
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
v___x_1167_ = lean_unsigned_to_nat(0u);
v___x_1168_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1167_, v___x_1142_, v___x_1166_, v___f_1143_);
lean_inc_ref(v___f_1144_);
v___f_1169_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_1169_, 0, v___f_1144_);
lean_closure_set(v___f_1169_, 1, v___y_1163_);
v___x_1170_ = lean_box(v_permitAcquired_1162_);
v___x_1171_ = lean_box(v___x_1142_);
v___f_1172_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__18___boxed), 21, 19);
lean_closure_set(v___f_1172_, 0, v___x_1170_);
lean_closure_set(v___f_1172_, 1, v___f_1144_);
lean_closure_set(v___f_1172_, 2, v___x_1145_);
lean_closure_set(v___f_1172_, 3, v___y_1163_);
lean_closure_set(v___f_1172_, 4, v_connectionLimit_1146_);
lean_closure_set(v___f_1172_, 5, v___x_1171_);
lean_closure_set(v___f_1172_, 6, v___f_1169_);
lean_closure_set(v___f_1172_, 7, v___x_1147_);
lean_closure_set(v___f_1172_, 8, v_activeConnections_1148_);
lean_closure_set(v___f_1172_, 9, v___f_1149_);
lean_closure_set(v___f_1172_, 10, v___f_1150_);
lean_closure_set(v___f_1172_, 11, v___f_1151_);
lean_closure_set(v___f_1172_, 12, v___x_1152_);
lean_closure_set(v___f_1172_, 13, v_inst_1153_);
lean_closure_set(v___f_1172_, 14, v_handler_1154_);
lean_closure_set(v___f_1172_, 15, v_config_1155_);
lean_closure_set(v___f_1172_, 16, v___f_1156_);
lean_closure_set(v___f_1172_, 17, v___f_1157_);
lean_closure_set(v___f_1172_, 18, v___x_1158_);
v___x_1173_ = lean_box(v___x_1142_);
v___f_1174_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__20___boxed), 7, 5);
lean_closure_set(v___f_1174_, 0, v_a_1159_);
lean_closure_set(v___f_1174_, 1, v___f_1160_);
lean_closure_set(v___f_1174_, 2, v___f_1161_);
lean_closure_set(v___f_1174_, 3, v___x_1173_);
lean_closure_set(v___f_1174_, 4, v___f_1172_);
v___x_1175_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1167_, v___x_1142_, v___x_1168_, v___f_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21___boxed(lean_object** _args){
lean_object* v___x_1176_ = _args[0];
lean_object* v___f_1177_ = _args[1];
lean_object* v___f_1178_ = _args[2];
lean_object* v___x_1179_ = _args[3];
lean_object* v_connectionLimit_1180_ = _args[4];
lean_object* v___x_1181_ = _args[5];
lean_object* v_activeConnections_1182_ = _args[6];
lean_object* v___f_1183_ = _args[7];
lean_object* v___f_1184_ = _args[8];
lean_object* v___f_1185_ = _args[9];
lean_object* v___x_1186_ = _args[10];
lean_object* v_inst_1187_ = _args[11];
lean_object* v_handler_1188_ = _args[12];
lean_object* v_config_1189_ = _args[13];
lean_object* v___f_1190_ = _args[14];
lean_object* v___f_1191_ = _args[15];
lean_object* v___x_1192_ = _args[16];
lean_object* v_a_1193_ = _args[17];
lean_object* v___f_1194_ = _args[18];
lean_object* v___f_1195_ = _args[19];
lean_object* v_permitAcquired_1196_ = _args[20];
lean_object* v___y_1197_ = _args[21];
lean_object* v___y_1198_ = _args[22];
_start:
{
uint8_t v___x_14324__boxed_1199_; uint8_t v_permitAcquired_boxed_1200_; lean_object* v_res_1201_; 
v___x_14324__boxed_1199_ = lean_unbox(v___x_1176_);
v_permitAcquired_boxed_1200_ = lean_unbox(v_permitAcquired_1196_);
v_res_1201_ = l_Std_Http_Server_serve___redArg___lam__21(v___x_14324__boxed_1199_, v___f_1177_, v___f_1178_, v___x_1179_, v_connectionLimit_1180_, v___x_1181_, v_activeConnections_1182_, v___f_1183_, v___f_1184_, v___f_1185_, v___x_1186_, v_inst_1187_, v_handler_1188_, v_config_1189_, v___f_1190_, v___f_1191_, v___x_1192_, v_a_1193_, v___f_1194_, v___f_1195_, v_permitAcquired_boxed_1200_, v___y_1197_);
lean_dec_ref(v___y_1197_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22(lean_object* v___f_1202_, lean_object* v___y_1203_, lean_object* v_x_1204_){
_start:
{
if (lean_obj_tag(v_x_1204_) == 0)
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1214_; 
lean_dec_ref(v___f_1202_);
v_a_1206_ = lean_ctor_get(v_x_1204_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_x_1204_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1208_ = v_x_1204_;
v_isShared_1209_ = v_isSharedCheck_1214_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v_x_1204_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1214_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1212_; 
v___x_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
return v___x_1212_;
}
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1216_; 
v_a_1215_ = lean_ctor_get(v_x_1204_, 0);
lean_inc(v_a_1215_);
lean_dec_ref_known(v_x_1204_, 1);
lean_inc_ref(v___y_1203_);
v___x_1216_ = lean_apply_3(v___f_1202_, v_a_1215_, v___y_1203_, lean_box(0));
return v___x_1216_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22___boxed(lean_object* v___f_1217_, lean_object* v___y_1218_, lean_object* v_x_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Std_Http_Server_serve___redArg___lam__22(v___f_1217_, v___y_1218_, v_x_1219_);
lean_dec_ref(v___y_1218_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23(uint8_t v___x_1222_, uint8_t v___x_1223_, lean_object* v___f_1224_, lean_object* v_x_1225_){
_start:
{
if (lean_obj_tag(v_x_1225_) == 0)
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1235_; 
lean_dec_ref(v___f_1224_);
v_a_1227_ = lean_ctor_get(v_x_1225_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_x_1225_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1229_ = v_x_1225_;
v_isShared_1230_ = v_isSharedCheck_1235_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v_x_1225_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1235_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_object* v___x_1233_; 
v___x_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
return v___x_1233_;
}
}
}
else
{
lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1246_; 
v_isSharedCheck_1246_ = !lean_is_exclusive(v_x_1225_);
if (v_isSharedCheck_1246_ == 0)
{
lean_object* v_unused_1247_; 
v_unused_1247_ = lean_ctor_get(v_x_1225_, 0);
lean_dec(v_unused_1247_);
v___x_1237_ = v_x_1225_;
v_isShared_1238_ = v_isSharedCheck_1246_;
goto v_resetjp_1236_;
}
else
{
lean_dec(v_x_1225_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1246_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1239_ = lean_box(v___x_1222_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v___x_1239_);
v___x_1241_ = v___x_1237_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1239_);
v___x_1241_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
v___x_1243_ = lean_unsigned_to_nat(0u);
v___x_1244_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1243_, v___x_1223_, v___x_1242_, v___f_1224_);
return v___x_1244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23___boxed(lean_object* v___x_1248_, lean_object* v___x_1249_, lean_object* v___f_1250_, lean_object* v_x_1251_, lean_object* v___y_1252_){
_start:
{
uint8_t v___x_14434__boxed_1253_; uint8_t v___x_14435__boxed_1254_; lean_object* v_res_1255_; 
v___x_14434__boxed_1253_ = lean_unbox(v___x_1248_);
v___x_14435__boxed_1254_ = lean_unbox(v___x_1249_);
v_res_1255_ = l_Std_Http_Server_serve___redArg___lam__23(v___x_14434__boxed_1253_, v___x_14435__boxed_1254_, v___f_1250_, v_x_1251_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24(lean_object* v___f_1256_, uint8_t v___x_1257_, lean_object* v___f_1258_, lean_object* v_x_1259_){
_start:
{
if (lean_obj_tag(v_x_1259_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1269_; 
lean_dec_ref(v___f_1258_);
lean_dec_ref(v___f_1256_);
v_a_1261_ = lean_ctor_get(v_x_1259_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v_x_1259_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1263_ = v_x_1259_;
v_isShared_1264_ = v_isSharedCheck_1269_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v_x_1259_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1269_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1267_; 
v___x_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
return v___x_1267_;
}
}
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v_a_1270_ = lean_ctor_get(v_x_1259_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v_x_1259_, 1);
v___x_1271_ = l_IO_Promise_result_x21___redArg(v_a_1270_);
lean_dec(v_a_1270_);
v___x_1272_ = lean_unsigned_to_nat(0u);
v___x_1273_ = lean_task_map(v___f_1256_, v___x_1271_, v___x_1272_, v___x_1257_);
v___x_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
v___x_1275_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1272_, v___x_1257_, v___x_1274_, v___f_1258_);
return v___x_1275_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24___boxed(lean_object* v___f_1276_, lean_object* v___x_1277_, lean_object* v___f_1278_, lean_object* v_x_1279_, lean_object* v___y_1280_){
_start:
{
uint8_t v___x_14493__boxed_1281_; lean_object* v_res_1282_; 
v___x_14493__boxed_1281_ = lean_unbox(v___x_1277_);
v_res_1282_ = l_Std_Http_Server_serve___redArg___lam__24(v___f_1276_, v___x_14493__boxed_1281_, v___f_1278_, v_x_1279_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26(uint8_t v___x_1283_, lean_object* v___f_1284_, lean_object* v_connectionLimit_1285_, lean_object* v___f_1286_, lean_object* v___f_1287_, lean_object* v_b_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___y_1292_; 
if (lean_obj_tag(v_connectionLimit_1285_) == 1)
{
lean_object* v_val_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1313_; 
v_val_1295_ = lean_ctor_get(v_connectionLimit_1285_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v_connectionLimit_1285_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1297_ = v_connectionLimit_1285_;
v_isShared_1298_ = v_isSharedCheck_1313_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_val_1295_);
lean_dec(v_connectionLimit_1285_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1313_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1299_; lean_object* v___f_1300_; uint8_t v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___f_1304_; lean_object* v___x_1305_; lean_object* v___f_1306_; lean_object* v___x_1308_; 
v___x_1299_ = l_Std_Semaphore_acquire(v_val_1295_);
lean_inc_ref(v___y_1289_);
v___f_1300_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__22___boxed), 4, 2);
lean_closure_set(v___f_1300_, 0, v___f_1286_);
lean_closure_set(v___f_1300_, 1, v___y_1289_);
v___x_1301_ = 1;
v___x_1302_ = lean_box(v___x_1301_);
v___x_1303_ = lean_box(v___x_1283_);
v___f_1304_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__23___boxed), 5, 3);
lean_closure_set(v___f_1304_, 0, v___x_1302_);
lean_closure_set(v___f_1304_, 1, v___x_1303_);
lean_closure_set(v___f_1304_, 2, v___f_1300_);
v___x_1305_ = lean_box(v___x_1283_);
v___f_1306_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__24___boxed), 5, 3);
lean_closure_set(v___f_1306_, 0, v___f_1287_);
lean_closure_set(v___f_1306_, 1, v___x_1305_);
lean_closure_set(v___f_1306_, 2, v___f_1304_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v___x_1299_);
v___x_1308_ = v___x_1297_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1299_);
v___x_1308_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
v___x_1310_ = lean_unsigned_to_nat(0u);
v___x_1311_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1310_, v___x_1283_, v___x_1309_, v___f_1306_);
v___y_1292_ = v___x_1311_;
goto v___jp_1291_;
}
}
}
else
{
lean_object* v___f_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
lean_dec_ref(v___f_1287_);
lean_dec(v_connectionLimit_1285_);
lean_inc_ref(v___y_1289_);
v___f_1314_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__22___boxed), 4, 2);
lean_closure_set(v___f_1314_, 0, v___f_1286_);
lean_closure_set(v___f_1314_, 1, v___y_1289_);
v___x_1315_ = lean_box(v___x_1283_);
v___x_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
v___x_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
v___x_1318_ = lean_unsigned_to_nat(0u);
v___x_1319_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1318_, v___x_1283_, v___x_1317_, v___f_1314_);
v___y_1292_ = v___x_1319_;
goto v___jp_1291_;
}
v___jp_1291_:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = lean_unsigned_to_nat(0u);
v___x_1294_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1293_, v___x_1283_, v___y_1292_, v___f_1284_);
return v___x_1294_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26___boxed(lean_object* v___x_1320_, lean_object* v___f_1321_, lean_object* v_connectionLimit_1322_, lean_object* v___f_1323_, lean_object* v___f_1324_, lean_object* v_b_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
uint8_t v___x_14537__boxed_1328_; lean_object* v_res_1329_; 
v___x_14537__boxed_1328_ = lean_unbox(v___x_1320_);
v_res_1329_ = l_Std_Http_Server_serve___redArg___lam__26(v___x_14537__boxed_1328_, v___f_1321_, v_connectionLimit_1322_, v___f_1323_, v___f_1324_, v_b_1325_, v___y_1326_);
lean_dec_ref(v___y_1326_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25(lean_object* v___x_1330_, lean_object* v___f_1331_, lean_object* v___x_1332_, uint8_t v___x_1333_, lean_object* v___f_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v___x_13006__overap_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_13006__overap_1337_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_1330_, v___f_1331_, v___x_1332_);
v___x_1338_ = lean_apply_2(v___x_13006__overap_1337_, v___y_1335_, lean_box(0));
v___x_1339_ = lean_unsigned_to_nat(0u);
v___x_1340_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1339_, v___x_1333_, v___x_1338_, v___f_1334_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25___boxed(lean_object* v___x_1341_, lean_object* v___f_1342_, lean_object* v___x_1343_, lean_object* v___x_1344_, lean_object* v___f_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
uint8_t v___x_14616__boxed_1348_; lean_object* v_res_1349_; 
v___x_14616__boxed_1348_ = lean_unbox(v___x_1344_);
v_res_1349_ = l_Std_Http_Server_serve___redArg___lam__25(v___x_1341_, v___f_1342_, v___x_1343_, v___x_14616__boxed_1348_, v___f_1345_, v___y_1346_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27(lean_object* v_x_1350_, lean_object* v_x_1351_){
_start:
{
if (lean_obj_tag(v_x_1351_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1361_; 
lean_dec_ref(v_x_1350_);
v_a_1353_ = lean_ctor_get(v_x_1351_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_x_1351_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1355_ = v_x_1351_;
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v_x_1351_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1359_; 
v___x_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
return v___x_1359_;
}
}
}
else
{
lean_object* v___x_1362_; 
lean_dec_ref_known(v_x_1351_, 1);
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v_x_1350_);
return v___x_1362_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27___boxed(lean_object* v_x_1363_, lean_object* v_x_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Std_Http_Server_serve___redArg___lam__27(v_x_1363_, v_x_1364_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28(lean_object* v___f_1371_, lean_object* v___x_1372_, lean_object* v___f_1373_, lean_object* v___f_1374_, lean_object* v___x_1375_, lean_object* v_inst_1376_, lean_object* v_handler_1377_, lean_object* v_config_1378_, lean_object* v___f_1379_, lean_object* v___x_1380_, lean_object* v_a_1381_, lean_object* v___f_1382_, lean_object* v___f_1383_, lean_object* v___f_1384_, lean_object* v___f_1385_, lean_object* v___f_1386_, lean_object* v_x_1387_){
_start:
{
if (lean_obj_tag(v_x_1387_) == 0)
{
lean_object* v___x_1389_; 
lean_dec_ref(v___f_1386_);
lean_dec_ref(v___f_1385_);
lean_dec_ref(v___f_1384_);
lean_dec_ref(v___f_1383_);
lean_dec_ref(v___f_1382_);
lean_dec(v_a_1381_);
lean_dec(v___x_1380_);
lean_dec_ref(v___f_1379_);
lean_dec_ref(v_config_1378_);
lean_dec(v_handler_1377_);
lean_dec_ref(v_inst_1376_);
lean_dec_ref(v___x_1375_);
lean_dec_ref(v___f_1374_);
lean_dec_ref(v___f_1373_);
lean_dec_ref(v___x_1372_);
lean_dec_ref(v___f_1371_);
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v_x_1387_);
return v___x_1389_;
}
else
{
lean_object* v_a_1390_; lean_object* v_context_1391_; lean_object* v_activeConnections_1392_; lean_object* v_connectionLimit_1393_; lean_object* v_shutdownPromise_1394_; lean_object* v___f_1395_; lean_object* v___f_1396_; uint8_t v___x_1397_; lean_object* v___x_1398_; lean_object* v___f_1399_; lean_object* v___f_1400_; lean_object* v___x_1401_; lean_object* v___f_1402_; lean_object* v___x_1403_; lean_object* v___f_1404_; lean_object* v___x_1405_; lean_object* v___f_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___f_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v_a_1390_ = lean_ctor_get(v_x_1387_, 0);
v_context_1391_ = lean_ctor_get(v_a_1390_, 0);
v_activeConnections_1392_ = lean_ctor_get(v_a_1390_, 1);
v_connectionLimit_1393_ = lean_ctor_get(v_a_1390_, 2);
v_shutdownPromise_1394_ = lean_ctor_get(v_a_1390_, 3);
lean_inc_ref(v_shutdownPromise_1394_);
lean_inc_ref_n(v_context_1391_, 2);
v___f_1395_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1395_, 0, v_context_1391_);
lean_closure_set(v___f_1395_, 1, v_shutdownPromise_1394_);
v___f_1396_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed), 5, 1);
lean_closure_set(v___f_1396_, 0, v___f_1395_);
v___x_1397_ = 0;
v___x_1398_ = lean_box(0);
v___f_1399_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__28___closed__0));
v___f_1400_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__28___closed__1));
v___x_1401_ = lean_box(v___x_1397_);
lean_inc_ref(v_activeConnections_1392_);
lean_inc_ref(v___x_1372_);
lean_inc_n(v_connectionLimit_1393_, 2);
v___f_1402_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__21___boxed), 23, 20);
lean_closure_set(v___f_1402_, 0, v___x_1401_);
lean_closure_set(v___f_1402_, 1, v___f_1371_);
lean_closure_set(v___f_1402_, 2, v___f_1399_);
lean_closure_set(v___f_1402_, 3, v___x_1398_);
lean_closure_set(v___f_1402_, 4, v_connectionLimit_1393_);
lean_closure_set(v___f_1402_, 5, v___x_1372_);
lean_closure_set(v___f_1402_, 6, v_activeConnections_1392_);
lean_closure_set(v___f_1402_, 7, v___f_1373_);
lean_closure_set(v___f_1402_, 8, v___f_1374_);
lean_closure_set(v___f_1402_, 9, v___f_1396_);
lean_closure_set(v___f_1402_, 10, v___x_1375_);
lean_closure_set(v___f_1402_, 11, v_inst_1376_);
lean_closure_set(v___f_1402_, 12, v_handler_1377_);
lean_closure_set(v___f_1402_, 13, v_config_1378_);
lean_closure_set(v___f_1402_, 14, v___f_1379_);
lean_closure_set(v___f_1402_, 15, v___f_1400_);
lean_closure_set(v___f_1402_, 16, v___x_1380_);
lean_closure_set(v___f_1402_, 17, v_a_1381_);
lean_closure_set(v___f_1402_, 18, v___f_1382_);
lean_closure_set(v___f_1402_, 19, v___f_1383_);
v___x_1403_ = lean_box(v___x_1397_);
v___f_1404_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__26___boxed), 8, 5);
lean_closure_set(v___f_1404_, 0, v___x_1403_);
lean_closure_set(v___f_1404_, 1, v___f_1384_);
lean_closure_set(v___f_1404_, 2, v_connectionLimit_1393_);
lean_closure_set(v___f_1404_, 3, v___f_1402_);
lean_closure_set(v___f_1404_, 4, v___f_1385_);
v___x_1405_ = lean_box(v___x_1397_);
v___f_1406_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__25___boxed), 7, 5);
lean_closure_set(v___f_1406_, 0, v___x_1372_);
lean_closure_set(v___f_1406_, 1, v___f_1404_);
lean_closure_set(v___f_1406_, 2, v___x_1398_);
lean_closure_set(v___f_1406_, 3, v___x_1405_);
lean_closure_set(v___f_1406_, 4, v___f_1386_);
v___x_1407_ = lean_box(v___x_1397_);
lean_inc(v_a_1390_);
v___x_1408_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___boxed), 6, 5);
lean_closure_set(v___x_1408_, 0, lean_box(0));
lean_closure_set(v___x_1408_, 1, v_a_1390_);
lean_closure_set(v___x_1408_, 2, v___x_1407_);
lean_closure_set(v___x_1408_, 3, v___f_1406_);
lean_closure_set(v___x_1408_, 4, v_context_1391_);
v___x_1409_ = lean_unsigned_to_nat(0u);
v___x_1410_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1410_, 0, lean_box(0));
lean_closure_set(v___x_1410_, 1, v___x_1408_);
v___x_1411_ = lean_io_as_task(v___x_1410_, v___x_1409_);
lean_dec_ref(v___x_1411_);
v___f_1412_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__27___boxed), 3, 1);
lean_closure_set(v___f_1412_, 0, v_x_1387_);
v___x_1413_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
v___x_1414_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1409_, v___x_1397_, v___x_1413_, v___f_1412_);
return v___x_1414_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28___boxed(lean_object** _args){
lean_object* v___f_1415_ = _args[0];
lean_object* v___x_1416_ = _args[1];
lean_object* v___f_1417_ = _args[2];
lean_object* v___f_1418_ = _args[3];
lean_object* v___x_1419_ = _args[4];
lean_object* v_inst_1420_ = _args[5];
lean_object* v_handler_1421_ = _args[6];
lean_object* v_config_1422_ = _args[7];
lean_object* v___f_1423_ = _args[8];
lean_object* v___x_1424_ = _args[9];
lean_object* v_a_1425_ = _args[10];
lean_object* v___f_1426_ = _args[11];
lean_object* v___f_1427_ = _args[12];
lean_object* v___f_1428_ = _args[13];
lean_object* v___f_1429_ = _args[14];
lean_object* v___f_1430_ = _args[15];
lean_object* v_x_1431_ = _args[16];
lean_object* v___y_1432_ = _args[17];
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_Std_Http_Server_serve___redArg___lam__28(v___f_1415_, v___x_1416_, v___f_1417_, v___f_1418_, v___x_1419_, v_inst_1420_, v_handler_1421_, v_config_1422_, v___f_1423_, v___x_1424_, v_a_1425_, v___f_1426_, v___f_1427_, v___f_1428_, v___f_1429_, v___f_1430_, v_x_1431_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29(lean_object* v___f_1434_, lean_object* v_config_1435_, lean_object* v_x_1436_){
_start:
{
lean_object* v_val_1439_; 
if (lean_obj_tag(v_x_1436_) == 0)
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1452_; 
lean_dec_ref(v_config_1435_);
lean_dec_ref(v___f_1434_);
v_a_1444_ = lean_ctor_get(v_x_1436_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_x_1436_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1446_ = v_x_1436_;
v_isShared_1447_ = v_isSharedCheck_1452_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v_x_1436_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1452_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
lean_object* v___x_1450_; 
v___x_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
return v___x_1450_;
}
}
}
else
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1463_; 
v_a_1453_ = lean_ctor_get(v_x_1436_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_x_1436_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1455_ = v_x_1436_;
v_isShared_1456_ = v_isSharedCheck_1463_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v_x_1436_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1463_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v_a_1459_; lean_object* v___x_1461_; 
v___x_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1457_, 0, v_a_1453_);
v___x_1458_ = l_Std_Http_Server_new(v_config_1435_, v___x_1457_);
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1459_);
lean_dec_ref(v___x_1458_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 0, v_a_1459_);
v___x_1461_ = v___x_1455_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1459_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
v_val_1439_ = v___x_1461_;
goto v___jp_1438_;
}
}
}
v___jp_1438_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; lean_object* v___x_1443_; 
v___x_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1440_, 0, v_val_1439_);
v___x_1441_ = lean_unsigned_to_nat(0u);
v___x_1442_ = 0;
v___x_1443_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1441_, v___x_1442_, v___x_1440_, v___f_1434_);
return v___x_1443_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29___boxed(lean_object* v___f_1464_, lean_object* v_config_1465_, lean_object* v_x_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Std_Http_Server_serve___redArg___lam__29(v___f_1464_, v_config_1465_, v_x_1466_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30(lean_object* v___f_1469_, lean_object* v_a_1470_, lean_object* v_x_1471_){
_start:
{
lean_object* v_val_1474_; 
if (lean_obj_tag(v_x_1471_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1487_; 
lean_dec_ref(v___f_1469_);
v_a_1479_ = lean_ctor_get(v_x_1471_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v_x_1471_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1481_ = v_x_1471_;
v_isShared_1482_ = v_isSharedCheck_1487_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v_x_1471_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1487_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1485_; 
v___x_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
return v___x_1485_;
}
}
}
else
{
lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1500_; 
v_isSharedCheck_1500_ = !lean_is_exclusive(v_x_1471_);
if (v_isSharedCheck_1500_ == 0)
{
lean_object* v_unused_1501_; 
v_unused_1501_ = lean_ctor_get(v_x_1471_, 0);
lean_dec(v_unused_1501_);
v___x_1489_ = v_x_1471_;
v_isShared_1490_ = v_isSharedCheck_1500_;
goto v_resetjp_1488_;
}
else
{
lean_dec(v_x_1471_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1500_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_uv_tcp_getsockname(v_a_1470_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v___x_1494_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1492_);
lean_dec_ref_known(v___x_1491_, 1);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 0, v_a_1492_);
v___x_1494_ = v___x_1489_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1492_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
v_val_1474_ = v___x_1494_;
goto v___jp_1473_;
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; 
v_a_1496_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1496_);
lean_dec_ref_known(v___x_1491_, 1);
if (v_isShared_1490_ == 0)
{
lean_ctor_set_tag(v___x_1489_, 0);
lean_ctor_set(v___x_1489_, 0, v_a_1496_);
v___x_1498_ = v___x_1489_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1496_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
v_val_1474_ = v___x_1498_;
goto v___jp_1473_;
}
}
}
}
v___jp_1473_:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; lean_object* v___x_1478_; 
v___x_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1475_, 0, v_val_1474_);
v___x_1476_ = lean_unsigned_to_nat(0u);
v___x_1477_ = 0;
v___x_1478_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1476_, v___x_1477_, v___x_1475_, v___f_1469_);
return v___x_1478_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30___boxed(lean_object* v___f_1502_, lean_object* v_a_1503_, lean_object* v_x_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Std_Http_Server_serve___redArg___lam__30(v___f_1502_, v_a_1503_, v_x_1504_);
lean_dec(v_a_1503_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31(lean_object* v___f_1507_, lean_object* v_a_1508_, lean_object* v_x_1509_){
_start:
{
lean_object* v_val_1512_; 
if (lean_obj_tag(v_x_1509_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1525_; 
lean_dec_ref(v___f_1507_);
v_a_1517_ = lean_ctor_get(v_x_1509_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v_x_1509_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1519_ = v_x_1509_;
v_isShared_1520_ = v_isSharedCheck_1525_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v_x_1509_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1525_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1522_; 
if (v_isShared_1520_ == 0)
{
v___x_1522_ = v___x_1519_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_a_1517_);
v___x_1522_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
lean_object* v___x_1523_; 
v___x_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
return v___x_1523_;
}
}
}
else
{
lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1538_; 
v_isSharedCheck_1538_ = !lean_is_exclusive(v_x_1509_);
if (v_isSharedCheck_1538_ == 0)
{
lean_object* v_unused_1539_; 
v_unused_1539_ = lean_ctor_get(v_x_1509_, 0);
lean_dec(v_unused_1539_);
v___x_1527_ = v_x_1509_;
v_isShared_1528_ = v_isSharedCheck_1538_;
goto v_resetjp_1526_;
}
else
{
lean_dec(v_x_1509_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1538_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_uv_tcp_nodelay(v_a_1508_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1532_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1529_, 1);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v_a_1530_);
v___x_1532_ = v___x_1527_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1530_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
v_val_1512_ = v___x_1532_;
goto v___jp_1511_;
}
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; 
v_a_1534_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1534_);
lean_dec_ref_known(v___x_1529_, 1);
if (v_isShared_1528_ == 0)
{
lean_ctor_set_tag(v___x_1527_, 0);
lean_ctor_set(v___x_1527_, 0, v_a_1534_);
v___x_1536_ = v___x_1527_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1534_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
v_val_1512_ = v___x_1536_;
goto v___jp_1511_;
}
}
}
}
v___jp_1511_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; uint8_t v___x_1515_; lean_object* v___x_1516_; 
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v_val_1512_);
v___x_1514_ = lean_unsigned_to_nat(0u);
v___x_1515_ = 0;
v___x_1516_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1514_, v___x_1515_, v___x_1513_, v___f_1507_);
return v___x_1516_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31___boxed(lean_object* v___f_1540_, lean_object* v_a_1541_, lean_object* v_x_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Std_Http_Server_serve___redArg___lam__31(v___f_1540_, v_a_1541_, v_x_1542_);
lean_dec(v_a_1541_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32(lean_object* v___f_1545_, lean_object* v_a_1546_, uint32_t v_backlog_1547_, lean_object* v_x_1548_){
_start:
{
lean_object* v_val_1551_; 
if (lean_obj_tag(v_x_1548_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1564_; 
lean_dec_ref(v___f_1545_);
v_a_1556_ = lean_ctor_get(v_x_1548_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v_x_1548_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1558_ = v_x_1548_;
v_isShared_1559_ = v_isSharedCheck_1564_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v_x_1548_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1564_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
lean_object* v___x_1562_; 
v___x_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
return v___x_1562_;
}
}
}
else
{
lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1577_; 
v_isSharedCheck_1577_ = !lean_is_exclusive(v_x_1548_);
if (v_isSharedCheck_1577_ == 0)
{
lean_object* v_unused_1578_; 
v_unused_1578_ = lean_ctor_get(v_x_1548_, 0);
lean_dec(v_unused_1578_);
v___x_1566_ = v_x_1548_;
v_isShared_1567_ = v_isSharedCheck_1577_;
goto v_resetjp_1565_;
}
else
{
lean_dec(v_x_1548_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1577_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1568_; 
v___x_1568_ = lean_uv_tcp_listen(v_a_1546_, v_backlog_1547_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1571_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
lean_dec_ref_known(v___x_1568_, 1);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v_a_1569_);
v___x_1571_ = v___x_1566_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1569_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
v_val_1551_ = v___x_1571_;
goto v___jp_1550_;
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; 
v_a_1573_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1573_);
lean_dec_ref_known(v___x_1568_, 1);
if (v_isShared_1567_ == 0)
{
lean_ctor_set_tag(v___x_1566_, 0);
lean_ctor_set(v___x_1566_, 0, v_a_1573_);
v___x_1575_ = v___x_1566_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1573_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
v_val_1551_ = v___x_1575_;
goto v___jp_1550_;
}
}
}
}
v___jp_1550_:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; lean_object* v___x_1555_; 
v___x_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1552_, 0, v_val_1551_);
v___x_1553_ = lean_unsigned_to_nat(0u);
v___x_1554_ = 0;
v___x_1555_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1553_, v___x_1554_, v___x_1552_, v___f_1545_);
return v___x_1555_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32___boxed(lean_object* v___f_1579_, lean_object* v_a_1580_, lean_object* v_backlog_1581_, lean_object* v_x_1582_, lean_object* v___y_1583_){
_start:
{
uint32_t v_backlog_boxed_1584_; lean_object* v_res_1585_; 
v_backlog_boxed_1584_ = lean_unbox_uint32(v_backlog_1581_);
lean_dec(v_backlog_1581_);
v_res_1585_ = l_Std_Http_Server_serve___redArg___lam__32(v___f_1579_, v_a_1580_, v_backlog_boxed_1584_, v_x_1582_);
lean_dec(v_a_1580_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__33(lean_object* v___f_1586_, lean_object* v___x_1587_, lean_object* v___f_1588_, lean_object* v___f_1589_, lean_object* v___x_1590_, lean_object* v_inst_1591_, lean_object* v_handler_1592_, lean_object* v_config_1593_, lean_object* v___f_1594_, lean_object* v___x_1595_, lean_object* v___f_1596_, lean_object* v___f_1597_, lean_object* v___f_1598_, lean_object* v___f_1599_, lean_object* v___f_1600_, uint32_t v_backlog_1601_, lean_object* v_addr_1602_, lean_object* v_x_1603_){
_start:
{
if (lean_obj_tag(v_x_1603_) == 0)
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1613_; 
lean_dec_ref(v___f_1600_);
lean_dec_ref(v___f_1599_);
lean_dec_ref(v___f_1598_);
lean_dec_ref(v___f_1597_);
lean_dec_ref(v___f_1596_);
lean_dec(v___x_1595_);
lean_dec_ref(v___f_1594_);
lean_dec_ref(v_config_1593_);
lean_dec(v_handler_1592_);
lean_dec_ref(v_inst_1591_);
lean_dec_ref(v___x_1590_);
lean_dec_ref(v___f_1589_);
lean_dec_ref(v___f_1588_);
lean_dec_ref(v___x_1587_);
lean_dec_ref(v___f_1586_);
v_a_1605_ = lean_ctor_get(v_x_1603_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v_x_1603_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1607_ = v_x_1603_;
v_isShared_1608_ = v_isSharedCheck_1613_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v_x_1603_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1613_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
lean_object* v___x_1611_; 
v___x_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
return v___x_1611_;
}
}
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1639_; 
v_a_1614_ = lean_ctor_get(v_x_1603_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v_x_1603_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1616_ = v_x_1603_;
v_isShared_1617_ = v_isSharedCheck_1639_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v_x_1603_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1639_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___f_1618_; lean_object* v___f_1619_; lean_object* v___f_1620_; lean_object* v___f_1621_; lean_object* v___x_1622_; lean_object* v___f_1623_; lean_object* v_val_1625_; lean_object* v___x_1630_; 
lean_inc_n(v_a_1614_, 4);
lean_inc_ref(v_config_1593_);
v___f_1618_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__28___boxed), 18, 16);
lean_closure_set(v___f_1618_, 0, v___f_1586_);
lean_closure_set(v___f_1618_, 1, v___x_1587_);
lean_closure_set(v___f_1618_, 2, v___f_1588_);
lean_closure_set(v___f_1618_, 3, v___f_1589_);
lean_closure_set(v___f_1618_, 4, v___x_1590_);
lean_closure_set(v___f_1618_, 5, v_inst_1591_);
lean_closure_set(v___f_1618_, 6, v_handler_1592_);
lean_closure_set(v___f_1618_, 7, v_config_1593_);
lean_closure_set(v___f_1618_, 8, v___f_1594_);
lean_closure_set(v___f_1618_, 9, v___x_1595_);
lean_closure_set(v___f_1618_, 10, v_a_1614_);
lean_closure_set(v___f_1618_, 11, v___f_1596_);
lean_closure_set(v___f_1618_, 12, v___f_1597_);
lean_closure_set(v___f_1618_, 13, v___f_1598_);
lean_closure_set(v___f_1618_, 14, v___f_1599_);
lean_closure_set(v___f_1618_, 15, v___f_1600_);
v___f_1619_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__29___boxed), 4, 2);
lean_closure_set(v___f_1619_, 0, v___f_1618_);
lean_closure_set(v___f_1619_, 1, v_config_1593_);
v___f_1620_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__30___boxed), 4, 2);
lean_closure_set(v___f_1620_, 0, v___f_1619_);
lean_closure_set(v___f_1620_, 1, v_a_1614_);
v___f_1621_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__31___boxed), 4, 2);
lean_closure_set(v___f_1621_, 0, v___f_1620_);
lean_closure_set(v___f_1621_, 1, v_a_1614_);
v___x_1622_ = lean_box_uint32(v_backlog_1601_);
v___f_1623_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__32___boxed), 5, 3);
lean_closure_set(v___f_1623_, 0, v___f_1621_);
lean_closure_set(v___f_1623_, 1, v_a_1614_);
lean_closure_set(v___f_1623_, 2, v___x_1622_);
v___x_1630_ = lean_uv_tcp_bind(v_a_1614_, v_addr_1602_);
lean_dec(v_a_1614_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1633_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_a_1631_);
lean_dec_ref_known(v___x_1630_, 1);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 0, v_a_1631_);
v___x_1633_ = v___x_1616_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1631_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
v_val_1625_ = v___x_1633_;
goto v___jp_1624_;
}
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; 
v_a_1635_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_a_1635_);
lean_dec_ref_known(v___x_1630_, 1);
if (v_isShared_1617_ == 0)
{
lean_ctor_set_tag(v___x_1616_, 0);
lean_ctor_set(v___x_1616_, 0, v_a_1635_);
v___x_1637_ = v___x_1616_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1635_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
v_val_1625_ = v___x_1637_;
goto v___jp_1624_;
}
}
v___jp_1624_:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; uint8_t v___x_1628_; lean_object* v___x_1629_; 
v___x_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1626_, 0, v_val_1625_);
v___x_1627_ = lean_unsigned_to_nat(0u);
v___x_1628_ = 0;
v___x_1629_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1627_, v___x_1628_, v___x_1626_, v___f_1623_);
return v___x_1629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__33___boxed(lean_object** _args){
lean_object* v___f_1640_ = _args[0];
lean_object* v___x_1641_ = _args[1];
lean_object* v___f_1642_ = _args[2];
lean_object* v___f_1643_ = _args[3];
lean_object* v___x_1644_ = _args[4];
lean_object* v_inst_1645_ = _args[5];
lean_object* v_handler_1646_ = _args[6];
lean_object* v_config_1647_ = _args[7];
lean_object* v___f_1648_ = _args[8];
lean_object* v___x_1649_ = _args[9];
lean_object* v___f_1650_ = _args[10];
lean_object* v___f_1651_ = _args[11];
lean_object* v___f_1652_ = _args[12];
lean_object* v___f_1653_ = _args[13];
lean_object* v___f_1654_ = _args[14];
lean_object* v_backlog_1655_ = _args[15];
lean_object* v_addr_1656_ = _args[16];
lean_object* v_x_1657_ = _args[17];
lean_object* v___y_1658_ = _args[18];
_start:
{
uint32_t v_backlog_boxed_1659_; lean_object* v_res_1660_; 
v_backlog_boxed_1659_ = lean_unbox_uint32(v_backlog_1655_);
lean_dec(v_backlog_1655_);
v_res_1660_ = l_Std_Http_Server_serve___redArg___lam__33(v___f_1640_, v___x_1641_, v___f_1642_, v___f_1643_, v___x_1644_, v_inst_1645_, v_handler_1646_, v_config_1647_, v___f_1648_, v___x_1649_, v___f_1650_, v___f_1651_, v___f_1652_, v___f_1653_, v___f_1654_, v_backlog_boxed_1659_, v_addr_1656_, v_x_1657_);
lean_dec_ref(v_addr_1656_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg(lean_object* v_inst_1667_, lean_object* v_addr_1668_, lean_object* v_handler_1669_, lean_object* v_config_1670_, uint32_t v_backlog_1671_){
_start:
{
lean_object* v___f_1673_; lean_object* v___f_1674_; lean_object* v___f_1675_; lean_object* v___f_1676_; lean_object* v___f_1677_; lean_object* v___f_1678_; lean_object* v___f_1679_; lean_object* v___f_1680_; lean_object* v___f_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___f_1686_; lean_object* v_val_1688_; lean_object* v___x_1693_; 
v___f_1673_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__0));
v___f_1674_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__1));
v___f_1675_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__2));
v___f_1676_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6));
v___f_1677_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0));
v___f_1678_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__3));
v___f_1679_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__4));
v___f_1680_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__5));
v___f_1681_ = ((lean_object*)(l_Std_Http_Server_waitShutdown___closed__0));
v___x_1682_ = l_Std_Async_ContextAsync_instMonad;
v___x_1683_ = l_Std_Http_instTransportClient;
v___x_1684_ = l_Std_Http_Server_instImpl_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8_;
v___x_1685_ = lean_box_uint32(v_backlog_1671_);
v___f_1686_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__33___boxed), 19, 17);
lean_closure_set(v___f_1686_, 0, v___f_1680_);
lean_closure_set(v___f_1686_, 1, v___x_1682_);
lean_closure_set(v___f_1686_, 2, v___f_1677_);
lean_closure_set(v___f_1686_, 3, v___f_1676_);
lean_closure_set(v___f_1686_, 4, v___x_1683_);
lean_closure_set(v___f_1686_, 5, v_inst_1667_);
lean_closure_set(v___f_1686_, 6, v_handler_1669_);
lean_closure_set(v___f_1686_, 7, v_config_1670_);
lean_closure_set(v___f_1686_, 8, v___f_1675_);
lean_closure_set(v___f_1686_, 9, v___x_1684_);
lean_closure_set(v___f_1686_, 10, v___f_1679_);
lean_closure_set(v___f_1686_, 11, v___f_1678_);
lean_closure_set(v___f_1686_, 12, v___f_1674_);
lean_closure_set(v___f_1686_, 13, v___f_1681_);
lean_closure_set(v___f_1686_, 14, v___f_1673_);
lean_closure_set(v___f_1686_, 15, v___x_1685_);
lean_closure_set(v___f_1686_, 16, v_addr_1668_);
v___x_1693_ = lean_uv_tcp_new();
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1693_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1693_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
lean_ctor_set_tag(v___x_1696_, 1);
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
v_val_1688_ = v___x_1699_;
goto v___jp_1687_;
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
v_a_1702_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1693_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1693_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
lean_ctor_set_tag(v___x_1704_, 0);
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
v_val_1688_ = v___x_1707_;
goto v___jp_1687_;
}
}
}
v___jp_1687_:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; uint8_t v___x_1691_; lean_object* v___x_1692_; 
v___x_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1689_, 0, v_val_1688_);
v___x_1690_ = lean_unsigned_to_nat(0u);
v___x_1691_ = 0;
v___x_1692_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1690_, v___x_1691_, v___x_1689_, v___f_1686_);
return v___x_1692_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___boxed(lean_object* v_inst_1710_, lean_object* v_addr_1711_, lean_object* v_handler_1712_, lean_object* v_config_1713_, lean_object* v_backlog_1714_, lean_object* v_a_1715_){
_start:
{
uint32_t v_backlog_boxed_1716_; lean_object* v_res_1717_; 
v_backlog_boxed_1716_ = lean_unbox_uint32(v_backlog_1714_);
lean_dec(v_backlog_1714_);
v_res_1717_ = l_Std_Http_Server_serve___redArg(v_inst_1710_, v_addr_1711_, v_handler_1712_, v_config_1713_, v_backlog_boxed_1716_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve(lean_object* v_00_u03c3_1718_, lean_object* v_inst_1719_, lean_object* v_addr_1720_, lean_object* v_handler_1721_, lean_object* v_config_1722_, uint32_t v_backlog_1723_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Std_Http_Server_serve___redArg(v_inst_1719_, v_addr_1720_, v_handler_1721_, v_config_1722_, v_backlog_1723_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___boxed(lean_object* v_00_u03c3_1726_, lean_object* v_inst_1727_, lean_object* v_addr_1728_, lean_object* v_handler_1729_, lean_object* v_config_1730_, lean_object* v_backlog_1731_, lean_object* v_a_1732_){
_start:
{
uint32_t v_backlog_boxed_1733_; lean_object* v_res_1734_; 
v_backlog_boxed_1733_ = lean_unbox_uint32(v_backlog_1731_);
lean_dec(v_backlog_1731_);
v_res_1734_ = l_Std_Http_Server_serve(v_00_u03c3_1726_, v_inst_1727_, v_addr_1728_, v_handler_1729_, v_config_1730_, v_backlog_boxed_1733_);
return v_res_1734_;
}
}
lean_object* runtime_initialize_Std_Async(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_TCP(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_CancellationToken(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_Semaphore(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Server_Config(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Server_Handler(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Server_Connection(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Server(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Async(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_TCP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_CancellationToken(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_Semaphore(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Server_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Server_Handler(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Server_Connection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Server(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Async(uint8_t builtin);
lean_object* initialize_Std_Async_TCP(uint8_t builtin);
lean_object* initialize_Std_Sync_CancellationToken(uint8_t builtin);
lean_object* initialize_Std_Sync_Semaphore(uint8_t builtin);
lean_object* initialize_Std_Http_Server_Config(uint8_t builtin);
lean_object* initialize_Std_Http_Server_Handler(uint8_t builtin);
lean_object* initialize_Std_Http_Server_Connection(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Server(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Async(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Async_TCP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sync_CancellationToken(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sync_Semaphore(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Server_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Server_Handler(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Server_Connection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Server(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Server(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Server(builtin);
}
#ifdef __cplusplus
}
#endif
