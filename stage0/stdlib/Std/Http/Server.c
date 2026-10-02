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
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_uv_tcp_nodelay(lean_object*);
lean_object* l_Std_Channel_send___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Std_CancellationToken_isCancelled(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Std_Async_ContextAsync_instMonad;
lean_object* l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_ContextAsync_instMonadFinally___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Mutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Server_serveConnection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_CancellationContext_cancel(lean_object*, lean_object*);
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
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* l_Std_Semaphore_acquire(lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_new();
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_CancellationContext_new();
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* l_Std_CloseableChannel_new___redArg(lean_object*);
lean_object* l_Std_Semaphore_new(lean_object*);
lean_object* lean_uv_tcp_getsockname(lean_object*);
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
static const lean_closure_object l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1_value;
static const lean_closure_object l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2 = (const lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2_value;
static const lean_closure_object l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3 = (const lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3_value;
static const lean_closure_object l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4 = (const lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4_value;
static const lean_closure_object l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4_value),((lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3_value)} };
static const lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5 = (const lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5_value;
static const lean_closure_object l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_instMonadFinally___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6 = (const lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Server_serve___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Server_serve___redArg___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Http_Server_serve___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Server_serve___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Std_Http_Server_serve___redArg___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Server_serve___redArg___lam__20___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Server_serve___redArg___lam__20___closed__0;
static lean_once_cell_t l_Std_Http_Server_serve___redArg___lam__20___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Server_serve___redArg___lam__20___closed__1;
static const lean_closure_object l_Std_Http_Server_serve___redArg___lam__20___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Extensions_compareName___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___lam__20___closed__2 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__20___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__19(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__19___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Server_serve___redArg___lam__30___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__9___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Server_serve___redArg___lam__30___closed__0 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__30___closed__0_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___lam__30___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__5___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Server_serve___redArg___lam__30___closed__1 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__30___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__33(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__34(lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__35(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__35___boxed(lean_object**);
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__0 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__0_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__1 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__1_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__2 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__2_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__6___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__3 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__3_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__4 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__4_value;
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
lean_object* v_shutdownPromise_60_; lean_object* v___f_61_; lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v_shutdownPromise_60_ = lean_ctor_get(v_s_58_, 3);
lean_inc_ref(v_shutdownPromise_60_);
lean_dec_ref(v_s_58_);
v___f_61_ = ((lean_object*)(l_Std_Http_Server_waitShutdown___closed__1));
v___x_62_ = lean_box(0);
v___x_63_ = lean_unsigned_to_nat(0u);
v___x_64_ = 0;
v___x_65_ = l_Std_Channel_recv___redArg(v___x_62_, v_shutdownPromise_60_);
v___x_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
v___x_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
v___x_68_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_63_, v___x_64_, v___x_67_, v___f_61_);
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
lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_89_; 
v___x_84_ = lean_box(0);
v___x_85_ = lean_unsigned_to_nat(0u);
v___x_86_ = 0;
v___x_87_ = l_Std_Channel_recv___redArg(v___x_84_, v_shutdownPromise_76_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 0, v___x_87_);
v___x_89_ = v___x_82_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_87_);
v___x_89_ = v_reuseFailAlloc_92_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
v___x_91_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_85_, v___x_86_, v___x_90_, v___f_77_);
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
lean_object* v_context_102_; lean_object* v_shutdownPromise_103_; lean_object* v___f_104_; lean_object* v___f_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v_context_102_ = lean_ctor_get(v_s_100_, 0);
lean_inc_ref(v_context_102_);
v_shutdownPromise_103_ = lean_ctor_get(v_s_100_, 3);
lean_inc_ref(v_shutdownPromise_103_);
lean_dec_ref(v_s_100_);
v___f_104_ = ((lean_object*)(l_Std_Http_Server_waitShutdown___closed__1));
v___f_105_ = lean_alloc_closure((void*)(l_Std_Http_Server_shutdownAndWait___lam__2___boxed), 4, 2);
lean_closure_set(v___f_105_, 0, v_shutdownPromise_103_);
lean_closure_set(v___f_105_, 1, v___f_104_);
v___x_106_ = lean_box(1);
v___x_107_ = lean_unsigned_to_nat(0u);
v___x_108_ = 0;
v___x_109_ = l_Std_CancellationContext_cancel(v_context_102_, v___x_106_);
v___x_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
v___x_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
v___x_112_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_107_, v___x_108_, v___x_111_, v___f_105_);
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
lean_object* v_token_181_; lean_object* v___f_182_; lean_object* v___x_183_; uint8_t v___x_184_; uint8_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_188_; 
v_token_181_ = lean_ctor_get(v_context_164_, 1);
lean_inc_ref(v_token_181_);
lean_dec_ref(v_context_164_);
v___f_182_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_182_, 0, v_shutdownPromise_165_);
lean_closure_set(v___f_182_, 1, v_a_177_);
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = 0;
v___x_185_ = l_Std_CancellationToken_isCancelled(v_token_181_);
v___x_186_ = lean_box(v___x_185_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_186_);
v___x_188_ = v___x_179_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_186_);
v___x_188_ = v_reuseFailAlloc_191_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
v___x_190_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_183_, v___x_184_, v___x_189_, v___f_182_);
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
lean_object* v___x_203_; uint8_t v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_203_ = lean_unsigned_to_nat(0u);
v___x_204_ = 0;
v___x_205_ = lean_st_ref_get(v___y_200_);
v___x_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
v___x_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
v___x_208_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_203_, v___x_204_, v___x_207_, v___f_198_);
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
lean_object* v___x_236_; lean_object* v___x_2167__overap_237_; lean_object* v___x_238_; 
lean_inc_ref(v___x_227_);
v___x_236_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_236_, 0, lean_box(0));
lean_closure_set(v___x_236_, 1, lean_box(0));
lean_closure_set(v___x_236_, 2, v___x_227_);
lean_closure_set(v___x_236_, 3, lean_box(0));
lean_closure_set(v___x_236_, 4, lean_box(0));
lean_closure_set(v___x_236_, 5, v___f_228_);
lean_closure_set(v___x_236_, 6, v___f_229_);
v___x_2167__overap_237_ = l_Std_Mutex_atomically___redArg(v___x_227_, v___f_230_, v___f_231_, v_activeConnections_232_, v___x_236_);
lean_inc_ref(v___y_234_);
v___x_238_ = lean_apply_2(v___x_2167__overap_237_, v___y_234_, lean_box(0));
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
lean_object* v___x_274_; uint8_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_274_ = lean_unsigned_to_nat(0u);
v___x_275_ = 0;
v___x_276_ = l_Std_Semaphore_release(v_val_270_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_276_);
v___x_278_ = v___x_272_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_276_);
v___x_278_ = v_reuseFailAlloc_281_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
v___x_280_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_274_, v___x_275_, v___x_279_, v___f_265_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9(lean_object* v___f_294_, lean_object* v_action_295_, lean_object* v_a_296_, lean_object* v___f_297_, lean_object* v_x_298_){
_start:
{
if (lean_obj_tag(v_x_298_) == 0)
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_308_; 
lean_dec_ref(v___f_297_);
lean_dec_ref(v_action_295_);
lean_dec(v___f_294_);
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
lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___y_315_; 
lean_dec_ref_known(v_x_298_, 1);
v___x_309_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_309_, 0, lean_box(0));
lean_closure_set(v___x_309_, 1, lean_box(0));
lean_closure_set(v___x_309_, 2, lean_box(0));
lean_closure_set(v___x_309_, 3, v___f_294_);
v___x_310_ = lean_unsigned_to_nat(0u);
v___x_311_ = 0;
lean_inc_ref(v_a_296_);
v___x_312_ = lean_apply_1(v_action_295_, v_a_296_);
v___x_313_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_312_, v___f_297_, v___x_310_, v___x_311_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v_a_317_; 
lean_dec_ref(v___x_309_);
v_a_317_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_a_317_);
lean_dec_ref_known(v___x_313_, 1);
if (lean_obj_tag(v_a_317_) == 0)
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
v_a_318_ = lean_ctor_get(v_a_317_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v_a_317_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v_a_317_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v_a_317_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
v___y_315_ = v___x_323_;
goto v___jp_314_;
}
}
}
else
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_334_; 
v_a_326_ = lean_ctor_get(v_a_317_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v_a_317_);
if (v_isSharedCheck_334_ == 0)
{
v___x_328_ = v_a_317_;
v_isShared_329_ = v_isSharedCheck_334_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v_a_317_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_334_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v_fst_330_; lean_object* v___x_332_; 
v_fst_330_ = lean_ctor_get(v_a_326_, 0);
lean_inc(v_fst_330_);
lean_dec(v_a_326_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v_fst_330_);
v___x_332_ = v___x_328_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_fst_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
v___y_315_ = v___x_332_;
goto v___jp_314_;
}
}
}
}
else
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_343_; 
v_a_335_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_343_ == 0)
{
v___x_337_ = v___x_313_;
v_isShared_338_ = v_isSharedCheck_343_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_313_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_343_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_339_; lean_object* v___x_341_; 
v___x_339_ = lean_task_map(v___x_309_, v_a_335_, v___x_310_, v___x_311_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_339_);
v___x_341_ = v___x_337_;
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
v___jp_314_:
{
lean_object* v___x_316_; 
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___y_315_);
return v___x_316_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed(lean_object* v___f_344_, lean_object* v_action_345_, lean_object* v_a_346_, lean_object* v___f_347_, lean_object* v_x_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9(v___f_344_, v_action_345_, v_a_346_, v___f_347_, v_x_348_);
lean_dec_ref(v_a_346_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg(lean_object* v_s_360_, uint8_t v_releaseConnectionPermit_361_, lean_object* v_action_362_, lean_object* v_a_363_){
_start:
{
lean_object* v___x_365_; lean_object* v_context_366_; lean_object* v_activeConnections_367_; lean_object* v_connectionLimit_368_; lean_object* v_shutdownPromise_369_; lean_object* v___f_370_; lean_object* v___f_371_; lean_object* v___f_372_; lean_object* v___f_373_; lean_object* v___f_374_; lean_object* v___f_375_; lean_object* v___f_376_; lean_object* v___f_377_; lean_object* v___f_378_; lean_object* v___x_379_; lean_object* v___f_380_; lean_object* v___f_381_; lean_object* v___x_382_; uint8_t v___x_383_; lean_object* v___x_1918__overap_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
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
v___f_371_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1));
v___f_372_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_372_, 0, v_context_366_);
lean_closure_set(v___f_372_, 1, v_shutdownPromise_369_);
v___f_373_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed), 5, 1);
lean_closure_set(v___f_373_, 0, v___f_372_);
v___f_374_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2));
v___f_375_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5));
v___f_376_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6));
v___f_377_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed), 9, 6);
lean_closure_set(v___f_377_, 0, v___x_365_);
lean_closure_set(v___f_377_, 1, v___f_374_);
lean_closure_set(v___f_377_, 2, v___f_373_);
lean_closure_set(v___f_377_, 3, v___f_375_);
lean_closure_set(v___f_377_, 4, v___f_376_);
lean_closure_set(v___f_377_, 5, v_activeConnections_367_);
lean_inc_ref_n(v_a_363_, 4);
lean_inc_ref(v___f_377_);
v___f_378_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_378_, 0, v___f_377_);
lean_closure_set(v___f_378_, 1, v_a_363_);
v___x_379_ = lean_box(v_releaseConnectionPermit_361_);
v___f_380_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed), 7, 5);
lean_closure_set(v___f_380_, 0, v___x_379_);
lean_closure_set(v___f_380_, 1, v___f_377_);
lean_closure_set(v___f_380_, 2, v_a_363_);
lean_closure_set(v___f_380_, 3, v_connectionLimit_368_);
lean_closure_set(v___f_380_, 4, v___f_378_);
v___f_381_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed), 6, 4);
lean_closure_set(v___f_381_, 0, v___f_371_);
lean_closure_set(v___f_381_, 1, v_action_362_);
lean_closure_set(v___f_381_, 2, v_a_363_);
lean_closure_set(v___f_381_, 3, v___f_380_);
v___x_382_ = lean_unsigned_to_nat(0u);
v___x_383_ = 0;
v___x_1918__overap_384_ = l_Std_Mutex_atomically___redArg(v___x_365_, v___f_375_, v___f_376_, v_activeConnections_367_, v___f_370_);
v___x_385_ = lean_apply_2(v___x_1918__overap_384_, v_a_363_, lean_box(0));
v___x_386_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_382_, v___x_383_, v___x_385_, v___f_381_);
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
lean_object* v___x_400_; lean_object* v_context_401_; lean_object* v_activeConnections_402_; lean_object* v_connectionLimit_403_; lean_object* v_shutdownPromise_404_; lean_object* v___f_405_; lean_object* v___f_406_; lean_object* v___f_407_; lean_object* v___f_408_; lean_object* v___f_409_; lean_object* v___f_410_; lean_object* v___f_411_; lean_object* v___f_412_; lean_object* v___f_413_; lean_object* v___x_414_; lean_object* v___f_415_; lean_object* v___f_416_; lean_object* v___x_417_; uint8_t v___x_418_; lean_object* v___x_2071__overap_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
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
v___f_406_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1));
v___f_407_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_407_, 0, v_context_401_);
lean_closure_set(v___f_407_, 1, v_shutdownPromise_404_);
v___f_408_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed), 5, 1);
lean_closure_set(v___f_408_, 0, v___f_407_);
v___f_409_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2));
v___f_410_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5));
v___f_411_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6));
v___f_412_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed), 9, 6);
lean_closure_set(v___f_412_, 0, v___x_400_);
lean_closure_set(v___f_412_, 1, v___f_409_);
lean_closure_set(v___f_412_, 2, v___f_408_);
lean_closure_set(v___f_412_, 3, v___f_410_);
lean_closure_set(v___f_412_, 4, v___f_411_);
lean_closure_set(v___f_412_, 5, v_activeConnections_402_);
lean_inc_ref_n(v_a_398_, 4);
lean_inc_ref(v___f_412_);
v___f_413_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_413_, 0, v___f_412_);
lean_closure_set(v___f_413_, 1, v_a_398_);
v___x_414_ = lean_box(v_releaseConnectionPermit_396_);
v___f_415_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed), 7, 5);
lean_closure_set(v___f_415_, 0, v___x_414_);
lean_closure_set(v___f_415_, 1, v___f_412_);
lean_closure_set(v___f_415_, 2, v_a_398_);
lean_closure_set(v___f_415_, 3, v_connectionLimit_403_);
lean_closure_set(v___f_415_, 4, v___f_413_);
v___f_416_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed), 6, 4);
lean_closure_set(v___f_416_, 0, v___f_406_);
lean_closure_set(v___f_416_, 1, v_action_397_);
lean_closure_set(v___f_416_, 2, v_a_398_);
lean_closure_set(v___f_416_, 3, v___f_415_);
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = 0;
v___x_2071__overap_419_ = l_Std_Mutex_atomically___redArg(v___x_400_, v___f_410_, v___f_411_, v_activeConnections_402_, v___f_405_);
v___x_420_ = lean_apply_2(v___x_2071__overap_419_, v_a_398_, lean_box(0));
v___x_421_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_417_, v___x_418_, v___x_420_, v___f_416_);
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
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1(lean_object* v_x_430_){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_432_, 0, v_x_430_);
v___x_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1___boxed(lean_object* v_x_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Std_Http_Server_serve___redArg___lam__1(v_x_435_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__0(lean_object* v_x_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__0___closed__1));
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__0___boxed(lean_object* v_x_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Std_Http_Server_serve___redArg___lam__0(v_x_445_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2(lean_object* v_x_448_){
_start:
{
lean_object* v_fst_449_; 
v_fst_449_ = lean_ctor_get(v_x_448_, 0);
lean_inc(v_fst_449_);
return v_fst_449_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2___boxed(lean_object* v_x_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Std_Http_Server_serve___redArg___lam__2(v_x_450_);
lean_dec_ref(v_x_450_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6(lean_object* v_x_452_){
_start:
{
if (lean_obj_tag(v_x_452_) == 0)
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_462_; 
v_a_454_ = lean_ctor_get(v_x_452_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v_x_452_);
if (v_isSharedCheck_462_ == 0)
{
v___x_456_ = v_x_452_;
v_isShared_457_ = v_isSharedCheck_462_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v_x_452_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_462_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_454_);
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
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_473_; 
v_a_463_ = lean_ctor_get(v_x_452_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v_x_452_);
if (v_isSharedCheck_473_ == 0)
{
v___x_465_ = v_x_452_;
v_isShared_466_ = v_isSharedCheck_473_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v_x_452_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_473_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v_token_467_; lean_object* v___x_468_; lean_object* v___x_470_; 
v_token_467_ = lean_ctor_get(v_a_463_, 1);
lean_inc_ref(v_token_467_);
lean_dec(v_a_463_);
v___x_468_ = l_Std_CancellationToken_selector(v_token_467_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 0, v___x_468_);
v___x_470_ = v___x_465_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_468_);
v___x_470_ = v_reuseFailAlloc_472_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
lean_object* v___x_471_; 
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
return v___x_471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6___boxed(lean_object* v_x_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Std_Http_Server_serve___redArg___lam__6(v_x_474_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3(lean_object* v_x_477_){
_start:
{
if (lean_obj_tag(v_x_477_) == 0)
{
lean_object* v___x_479_; 
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v_x_477_);
return v___x_479_;
}
else
{
lean_object* v___x_480_; 
lean_dec_ref_known(v_x_477_, 1);
v___x_480_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_480_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3___boxed(lean_object* v_x_481_, lean_object* v___y_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Std_Http_Server_serve___redArg___lam__3(v_x_481_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4(lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
if (lean_obj_tag(v_x_485_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_495_; 
lean_dec_ref(v_x_484_);
v_a_487_ = lean_ctor_get(v_x_485_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v_x_485_);
if (v_isSharedCheck_495_ == 0)
{
v___x_489_ = v_x_485_;
v_isShared_490_ = v_isSharedCheck_495_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v_x_485_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_495_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_494_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; 
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
}
}
else
{
lean_object* v___x_496_; 
lean_dec_ref_known(v_x_485_, 1);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v_x_484_);
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4___boxed(lean_object* v_x_497_, lean_object* v_x_498_, lean_object* v___y_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Std_Http_Server_serve___redArg___lam__4(v_x_497_, v_x_498_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9(lean_object* v___x_501_, lean_object* v_____r_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_501_);
v___x_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
v___x_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9___boxed(lean_object* v___x_508_, lean_object* v_____r_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Std_Http_Server_serve___redArg___lam__9(v___x_508_, v_____r_509_, v___y_510_);
lean_dec_ref(v___y_510_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5(lean_object* v___x_513_, lean_object* v_x_514_){
_start:
{
if (lean_obj_tag(v_x_514_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_524_; 
v_a_516_ = lean_ctor_get(v_x_514_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v_x_514_);
if (v_isSharedCheck_524_ == 0)
{
v___x_518_ = v_x_514_;
v_isShared_519_ = v_isSharedCheck_524_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v_x_514_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_524_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_523_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_522_; 
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
return v___x_522_;
}
}
}
else
{
lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_533_; 
v_isSharedCheck_533_ = !lean_is_exclusive(v_x_514_);
if (v_isSharedCheck_533_ == 0)
{
lean_object* v_unused_534_; 
v_unused_534_ = lean_ctor_get(v_x_514_, 0);
lean_dec(v_unused_534_);
v___x_526_ = v_x_514_;
v_isShared_527_ = v_isSharedCheck_533_;
goto v_resetjp_525_;
}
else
{
lean_dec(v_x_514_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_533_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_513_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_528_);
v___x_530_ = v___x_526_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_528_);
v___x_530_ = v_reuseFailAlloc_532_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_531_; 
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
return v___x_531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5___boxed(lean_object* v___x_535_, lean_object* v_x_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Std_Http_Server_serve___redArg___lam__5(v___x_535_, v_x_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7(lean_object* v___f_539_, lean_object* v___y_540_, lean_object* v_x_541_){
_start:
{
if (lean_obj_tag(v_x_541_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_551_; 
lean_dec_ref(v___f_539_);
v_a_543_ = lean_ctor_get(v_x_541_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v_x_541_);
if (v_isSharedCheck_551_ == 0)
{
v___x_545_ = v_x_541_;
v_isShared_546_ = v_isSharedCheck_551_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v_x_541_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_551_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_543_);
v___x_548_ = v_reuseFailAlloc_550_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_549_; 
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
}
}
else
{
lean_object* v_a_552_; lean_object* v___x_553_; 
v_a_552_ = lean_ctor_get(v_x_541_, 0);
lean_inc(v_a_552_);
lean_dec_ref_known(v_x_541_, 1);
lean_inc_ref(v___y_540_);
v___x_553_ = lean_apply_3(v___f_539_, v_a_552_, v___y_540_, lean_box(0));
return v___x_553_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7___boxed(lean_object* v___f_554_, lean_object* v___y_555_, lean_object* v_x_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Std_Http_Server_serve___redArg___lam__7(v___f_554_, v___y_555_, v_x_556_);
lean_dec_ref(v___y_555_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10(lean_object* v___f_559_, lean_object* v_a_560_, lean_object* v_x_561_){
_start:
{
if (lean_obj_tag(v_x_561_) == 0)
{
lean_object* v___x_563_; 
lean_dec_ref(v_a_560_);
lean_dec_ref(v___f_559_);
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v_x_561_);
return v___x_563_;
}
else
{
lean_object* v_a_564_; lean_object* v___x_565_; 
v_a_564_ = lean_ctor_get(v_x_561_, 0);
lean_inc(v_a_564_);
lean_dec_ref_known(v_x_561_, 1);
v___x_565_ = lean_apply_3(v___f_559_, v_a_564_, v_a_560_, lean_box(0));
return v___x_565_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10___boxed(lean_object* v___f_566_, lean_object* v_a_567_, lean_object* v_x_568_, lean_object* v___y_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Std_Http_Server_serve___redArg___lam__10(v___f_566_, v_a_567_, v_x_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8(uint8_t v_permitAcquired_571_, lean_object* v___f_572_, lean_object* v___x_573_, lean_object* v_a_574_, lean_object* v_connectionLimit_575_, lean_object* v___x_576_, uint8_t v___x_577_, lean_object* v___f_578_, lean_object* v_opt_579_){
_start:
{
if (v_permitAcquired_571_ == 0)
{
lean_object* v___x_581_; 
lean_dec_ref(v___f_578_);
lean_dec(v___x_576_);
lean_dec(v_connectionLimit_575_);
v___x_581_ = lean_apply_3(v___f_572_, v___x_573_, v_a_574_, lean_box(0));
return v___x_581_;
}
else
{
if (lean_obj_tag(v_connectionLimit_575_) == 1)
{
lean_object* v_val_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_592_; 
lean_dec_ref(v_a_574_);
lean_dec_ref(v___f_572_);
v_val_582_ = lean_ctor_get(v_connectionLimit_575_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v_connectionLimit_575_);
if (v_isSharedCheck_592_ == 0)
{
v___x_584_ = v_connectionLimit_575_;
v_isShared_585_ = v_isSharedCheck_592_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_val_582_);
lean_dec(v_connectionLimit_575_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_592_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_586_ = l_Std_Semaphore_release(v_val_582_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_586_);
v___x_588_ = v___x_584_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_591_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
v___x_590_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_576_, v___x_577_, v___x_589_, v___f_578_);
return v___x_590_;
}
}
}
else
{
lean_object* v___x_593_; 
lean_dec_ref(v___f_578_);
lean_dec(v___x_576_);
lean_dec(v_connectionLimit_575_);
v___x_593_ = lean_apply_3(v___f_572_, v___x_573_, v_a_574_, lean_box(0));
return v___x_593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8___boxed(lean_object* v_permitAcquired_594_, lean_object* v___f_595_, lean_object* v___x_596_, lean_object* v_a_597_, lean_object* v_connectionLimit_598_, lean_object* v___x_599_, lean_object* v___x_600_, lean_object* v___f_601_, lean_object* v_opt_602_, lean_object* v___y_603_){
_start:
{
uint8_t v_permitAcquired_boxed_604_; uint8_t v___x_13139__boxed_605_; lean_object* v_res_606_; 
v_permitAcquired_boxed_604_ = lean_unbox(v_permitAcquired_594_);
v___x_13139__boxed_605_ = lean_unbox(v___x_600_);
v_res_606_ = l_Std_Http_Server_serve___redArg___lam__8(v_permitAcquired_boxed_604_, v___f_595_, v___x_596_, v_a_597_, v_connectionLimit_598_, v___x_599_, v___x_13139__boxed_605_, v___f_601_, v_opt_602_);
lean_dec(v_opt_602_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11(lean_object* v___f_607_, lean_object* v___x_608_, lean_object* v_inst_609_, lean_object* v_val_610_, lean_object* v_handler_611_, lean_object* v_config_612_, lean_object* v_extensions_613_, lean_object* v_a_614_, lean_object* v___f_615_, lean_object* v___x_616_, uint8_t v___x_617_, lean_object* v_x_618_){
_start:
{
if (lean_obj_tag(v_x_618_) == 0)
{
lean_object* v___x_620_; 
lean_dec(v___x_616_);
lean_dec_ref(v___f_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_extensions_613_);
lean_dec_ref(v_config_612_);
lean_dec(v_handler_611_);
lean_dec(v_val_610_);
lean_dec_ref(v_inst_609_);
lean_dec_ref(v___x_608_);
lean_dec_ref(v___f_607_);
v___x_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_620_, 0, v_x_618_);
return v___x_620_;
}
else
{
lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_659_; 
v_isSharedCheck_659_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_659_ == 0)
{
lean_object* v_unused_660_; 
v_unused_660_ = lean_ctor_get(v_x_618_, 0);
lean_dec(v_unused_660_);
v___x_622_ = v_x_618_;
v_isShared_623_ = v_isSharedCheck_659_;
goto v_resetjp_621_;
}
else
{
lean_dec(v_x_618_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_659_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___y_628_; 
v___x_624_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_624_, 0, lean_box(0));
lean_closure_set(v___x_624_, 1, lean_box(0));
lean_closure_set(v___x_624_, 2, lean_box(0));
lean_closure_set(v___x_624_, 3, v___f_607_);
v___x_625_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___boxed), 10, 9);
lean_closure_set(v___x_625_, 0, lean_box(0));
lean_closure_set(v___x_625_, 1, lean_box(0));
lean_closure_set(v___x_625_, 2, v___x_608_);
lean_closure_set(v___x_625_, 3, v_inst_609_);
lean_closure_set(v___x_625_, 4, v_val_610_);
lean_closure_set(v___x_625_, 5, v_handler_611_);
lean_closure_set(v___x_625_, 6, v_config_612_);
lean_closure_set(v___x_625_, 7, v_extensions_613_);
lean_closure_set(v___x_625_, 8, v_a_614_);
lean_inc(v___x_616_);
v___x_626_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_625_, v___f_615_, v___x_616_, v___x_617_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_632_; 
lean_dec_ref(v___x_624_);
lean_dec(v___x_616_);
v_a_632_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_a_632_);
lean_dec_ref_known(v___x_626_, 1);
if (lean_obj_tag(v_a_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
v_a_633_ = lean_ctor_get(v_a_632_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v_a_632_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v_a_632_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v_a_632_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
v___y_628_ = v___x_638_;
goto v___jp_627_;
}
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_649_; 
v_a_641_ = lean_ctor_get(v_a_632_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v_a_632_);
if (v_isSharedCheck_649_ == 0)
{
v___x_643_ = v_a_632_;
v_isShared_644_ = v_isSharedCheck_649_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v_a_632_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_649_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v_fst_645_; lean_object* v___x_647_; 
v_fst_645_ = lean_ctor_get(v_a_641_, 0);
lean_inc(v_fst_645_);
lean_dec(v_a_641_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v_fst_645_);
v___x_647_ = v___x_643_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_fst_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
v___y_628_ = v___x_647_;
goto v___jp_627_;
}
}
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_658_; 
lean_del_object(v___x_622_);
v_a_650_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_658_ == 0)
{
v___x_652_ = v___x_626_;
v_isShared_653_ = v_isSharedCheck_658_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_626_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_658_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_654_ = lean_task_map(v___x_624_, v_a_650_, v___x_616_, v___x_617_);
if (v_isShared_653_ == 0)
{
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
}
v___jp_627_:
{
lean_object* v___x_630_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set_tag(v___x_622_, 0);
lean_ctor_set(v___x_622_, 0, v___y_628_);
v___x_630_ = v___x_622_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___y_628_);
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
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11___boxed(lean_object* v___f_661_, lean_object* v___x_662_, lean_object* v_inst_663_, lean_object* v_val_664_, lean_object* v_handler_665_, lean_object* v_config_666_, lean_object* v_extensions_667_, lean_object* v_a_668_, lean_object* v___f_669_, lean_object* v___x_670_, lean_object* v___x_671_, lean_object* v_x_672_, lean_object* v___y_673_){
_start:
{
uint8_t v___x_13189__boxed_674_; lean_object* v_res_675_; 
v___x_13189__boxed_674_ = lean_unbox(v___x_671_);
v_res_675_ = l_Std_Http_Server_serve___redArg___lam__11(v___f_661_, v___x_662_, v_inst_663_, v_val_664_, v_handler_665_, v_config_666_, v_extensions_667_, v_a_668_, v___f_669_, v___x_670_, v___x_13189__boxed_674_, v_x_672_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12(lean_object* v___f_676_, lean_object* v___f_677_, lean_object* v_activeConnections_678_, lean_object* v_a_679_, uint8_t v_permitAcquired_680_, lean_object* v___x_681_, lean_object* v_connectionLimit_682_, lean_object* v___x_683_, uint8_t v___x_684_, lean_object* v___f_685_, lean_object* v___x_686_, lean_object* v_inst_687_, lean_object* v_val_688_, lean_object* v_handler_689_, lean_object* v_config_690_, lean_object* v_extensions_691_, lean_object* v___f_692_){
_start:
{
lean_object* v___x_694_; lean_object* v___f_695_; lean_object* v___f_696_; lean_object* v___f_697_; lean_object* v___f_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___f_701_; lean_object* v___x_702_; lean_object* v___f_703_; lean_object* v___x_12356__overap_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_694_ = l_Std_Async_ContextAsync_instMonad;
v___f_695_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5));
v___f_696_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6));
lean_inc_ref(v_activeConnections_678_);
v___f_697_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed), 9, 6);
lean_closure_set(v___f_697_, 0, v___x_694_);
lean_closure_set(v___f_697_, 1, v___f_676_);
lean_closure_set(v___f_697_, 2, v___f_677_);
lean_closure_set(v___f_697_, 3, v___f_695_);
lean_closure_set(v___f_697_, 4, v___f_696_);
lean_closure_set(v___f_697_, 5, v_activeConnections_678_);
lean_inc_ref_n(v_a_679_, 3);
lean_inc_ref(v___f_697_);
v___f_698_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__10___boxed), 4, 2);
lean_closure_set(v___f_698_, 0, v___f_697_);
lean_closure_set(v___f_698_, 1, v_a_679_);
v___x_699_ = lean_box(v_permitAcquired_680_);
v___x_700_ = lean_box(v___x_684_);
lean_inc_n(v___x_683_, 2);
v___f_701_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__8___boxed), 10, 8);
lean_closure_set(v___f_701_, 0, v___x_699_);
lean_closure_set(v___f_701_, 1, v___f_697_);
lean_closure_set(v___f_701_, 2, v___x_681_);
lean_closure_set(v___f_701_, 3, v_a_679_);
lean_closure_set(v___f_701_, 4, v_connectionLimit_682_);
lean_closure_set(v___f_701_, 5, v___x_683_);
lean_closure_set(v___f_701_, 6, v___x_700_);
lean_closure_set(v___f_701_, 7, v___f_698_);
v___x_702_ = lean_box(v___x_684_);
v___f_703_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__11___boxed), 13, 11);
lean_closure_set(v___f_703_, 0, v___f_685_);
lean_closure_set(v___f_703_, 1, v___x_686_);
lean_closure_set(v___f_703_, 2, v_inst_687_);
lean_closure_set(v___f_703_, 3, v_val_688_);
lean_closure_set(v___f_703_, 4, v_handler_689_);
lean_closure_set(v___f_703_, 5, v_config_690_);
lean_closure_set(v___f_703_, 6, v_extensions_691_);
lean_closure_set(v___f_703_, 7, v_a_679_);
lean_closure_set(v___f_703_, 8, v___f_701_);
lean_closure_set(v___f_703_, 9, v___x_683_);
lean_closure_set(v___f_703_, 10, v___x_702_);
v___x_12356__overap_704_ = l_Std_Mutex_atomically___redArg(v___x_694_, v___f_695_, v___f_696_, v_activeConnections_678_, v___f_692_);
v___x_705_ = lean_apply_2(v___x_12356__overap_704_, v_a_679_, lean_box(0));
v___x_706_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_683_, v___x_684_, v___x_705_, v___f_703_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12___boxed(lean_object** _args){
lean_object* v___f_707_ = _args[0];
lean_object* v___f_708_ = _args[1];
lean_object* v_activeConnections_709_ = _args[2];
lean_object* v_a_710_ = _args[3];
lean_object* v_permitAcquired_711_ = _args[4];
lean_object* v___x_712_ = _args[5];
lean_object* v_connectionLimit_713_ = _args[6];
lean_object* v___x_714_ = _args[7];
lean_object* v___x_715_ = _args[8];
lean_object* v___f_716_ = _args[9];
lean_object* v___x_717_ = _args[10];
lean_object* v_inst_718_ = _args[11];
lean_object* v_val_719_ = _args[12];
lean_object* v_handler_720_ = _args[13];
lean_object* v_config_721_ = _args[14];
lean_object* v_extensions_722_ = _args[15];
lean_object* v___f_723_ = _args[16];
lean_object* v___y_724_ = _args[17];
_start:
{
uint8_t v_permitAcquired_boxed_725_; uint8_t v___x_13305__boxed_726_; lean_object* v_res_727_; 
v_permitAcquired_boxed_725_ = lean_unbox(v_permitAcquired_711_);
v___x_13305__boxed_726_ = lean_unbox(v___x_715_);
v_res_727_ = l_Std_Http_Server_serve___redArg___lam__12(v___f_707_, v___f_708_, v_activeConnections_709_, v_a_710_, v_permitAcquired_boxed_725_, v___x_712_, v_connectionLimit_713_, v___x_714_, v___x_13305__boxed_726_, v___f_716_, v___x_717_, v_inst_718_, v_val_719_, v_handler_720_, v_config_721_, v_extensions_722_, v___f_723_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13(lean_object* v_a_728_, lean_object* v___x_729_, lean_object* v_a_x3f_730_){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_732_ = l_Std_CancellationContext_cancel(v_a_728_, v___x_729_);
v___x_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13___boxed(lean_object* v_a_735_, lean_object* v___x_736_, lean_object* v_a_x3f_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Std_Http_Server_serve___redArg___lam__13(v_a_735_, v___x_736_, v_a_x3f_737_);
lean_dec(v_a_x3f_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14(lean_object* v___f_740_, lean_object* v___f_741_, lean_object* v___f_742_, lean_object* v___x_743_, uint8_t v___x_744_){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___y_749_; 
v___x_746_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_746_, 0, lean_box(0));
lean_closure_set(v___x_746_, 1, lean_box(0));
lean_closure_set(v___x_746_, 2, lean_box(0));
lean_closure_set(v___x_746_, 3, v___f_740_);
lean_inc(v___x_743_);
v___x_747_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_741_, v___f_742_, v___x_743_, v___x_744_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_751_; 
lean_dec_ref(v___x_746_);
lean_dec(v___x_743_);
v_a_751_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_751_);
lean_dec_ref_known(v___x_747_, 1);
if (lean_obj_tag(v_a_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
v_a_752_ = lean_ctor_get(v_a_751_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v_a_751_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v_a_751_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v_a_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
v___y_749_ = v___x_757_;
goto v___jp_748_;
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_768_; 
v_a_760_ = lean_ctor_get(v_a_751_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v_a_751_);
if (v_isSharedCheck_768_ == 0)
{
v___x_762_ = v_a_751_;
v_isShared_763_ = v_isSharedCheck_768_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v_a_751_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_768_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v_fst_764_; lean_object* v___x_766_; 
v_fst_764_ = lean_ctor_get(v_a_760_, 0);
lean_inc(v_fst_764_);
lean_dec(v_a_760_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v_fst_764_);
v___x_766_ = v___x_762_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_fst_764_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
v___y_749_ = v___x_766_;
goto v___jp_748_;
}
}
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_777_; 
v_a_769_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_777_ == 0)
{
v___x_771_ = v___x_747_;
v_isShared_772_ = v_isSharedCheck_777_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_747_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_777_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_773_ = lean_task_map(v___x_746_, v_a_769_, v___x_743_, v___x_744_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_773_);
v___x_775_ = v___x_771_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
v___jp_748_:
{
lean_object* v___x_750_; 
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v___y_749_);
return v___x_750_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14___boxed(lean_object* v___f_778_, lean_object* v___f_779_, lean_object* v___f_780_, lean_object* v___x_781_, lean_object* v___x_782_, lean_object* v___y_783_){
_start:
{
uint8_t v___x_13381__boxed_784_; lean_object* v_res_785_; 
v___x_13381__boxed_784_ = lean_unbox(v___x_782_);
v_res_785_ = l_Std_Http_Server_serve___redArg___lam__14(v___f_778_, v___f_779_, v___f_780_, v___x_781_, v___x_13381__boxed_784_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15(lean_object* v___f_786_, lean_object* v___f_787_, lean_object* v_activeConnections_788_, uint8_t v_permitAcquired_789_, lean_object* v___x_790_, lean_object* v_connectionLimit_791_, lean_object* v___x_792_, uint8_t v___x_793_, lean_object* v___f_794_, lean_object* v___x_795_, lean_object* v_inst_796_, lean_object* v_val_797_, lean_object* v_handler_798_, lean_object* v_config_799_, lean_object* v_extensions_800_, lean_object* v___f_801_, lean_object* v___f_802_, lean_object* v_x_803_){
_start:
{
if (lean_obj_tag(v_x_803_) == 0)
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_813_; 
lean_dec_ref(v___f_802_);
lean_dec_ref(v___f_801_);
lean_dec(v_extensions_800_);
lean_dec_ref(v_config_799_);
lean_dec(v_handler_798_);
lean_dec(v_val_797_);
lean_dec_ref(v_inst_796_);
lean_dec_ref(v___x_795_);
lean_dec_ref(v___f_794_);
lean_dec(v___x_792_);
lean_dec(v_connectionLimit_791_);
lean_dec_ref(v_activeConnections_788_);
lean_dec_ref(v___f_787_);
lean_dec_ref(v___f_786_);
v_a_805_ = lean_ctor_get(v_x_803_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v_x_803_);
if (v_isSharedCheck_813_ == 0)
{
v___x_807_ = v_x_803_;
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v_x_803_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_812_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_811_; 
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
return v___x_811_;
}
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_831_; 
v_a_814_ = lean_ctor_get(v_x_803_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v_x_803_);
if (v_isSharedCheck_831_ == 0)
{
v___x_816_ = v_x_803_;
v_isShared_817_ = v_isSharedCheck_831_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v_x_803_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_831_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___f_820_; lean_object* v___x_821_; lean_object* v___f_822_; lean_object* v___x_823_; lean_object* v___f_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_818_ = lean_box(v_permitAcquired_789_);
v___x_819_ = lean_box(v___x_793_);
lean_inc_n(v___x_792_, 2);
lean_inc(v_a_814_);
v___f_820_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__12___boxed), 18, 17);
lean_closure_set(v___f_820_, 0, v___f_786_);
lean_closure_set(v___f_820_, 1, v___f_787_);
lean_closure_set(v___f_820_, 2, v_activeConnections_788_);
lean_closure_set(v___f_820_, 3, v_a_814_);
lean_closure_set(v___f_820_, 4, v___x_818_);
lean_closure_set(v___f_820_, 5, v___x_790_);
lean_closure_set(v___f_820_, 6, v_connectionLimit_791_);
lean_closure_set(v___f_820_, 7, v___x_792_);
lean_closure_set(v___f_820_, 8, v___x_819_);
lean_closure_set(v___f_820_, 9, v___f_794_);
lean_closure_set(v___f_820_, 10, v___x_795_);
lean_closure_set(v___f_820_, 11, v_inst_796_);
lean_closure_set(v___f_820_, 12, v_val_797_);
lean_closure_set(v___f_820_, 13, v_handler_798_);
lean_closure_set(v___f_820_, 14, v_config_799_);
lean_closure_set(v___f_820_, 15, v_extensions_800_);
lean_closure_set(v___f_820_, 16, v___f_801_);
v___x_821_ = lean_box(2);
v___f_822_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__13___boxed), 4, 2);
lean_closure_set(v___f_822_, 0, v_a_814_);
lean_closure_set(v___f_822_, 1, v___x_821_);
v___x_823_ = lean_box(v___x_793_);
v___f_824_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__14___boxed), 6, 5);
lean_closure_set(v___f_824_, 0, v___f_802_);
lean_closure_set(v___f_824_, 1, v___f_820_);
lean_closure_set(v___f_824_, 2, v___f_822_);
lean_closure_set(v___f_824_, 3, v___x_792_);
lean_closure_set(v___f_824_, 4, v___x_823_);
v___x_825_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_825_, 0, lean_box(0));
lean_closure_set(v___x_825_, 1, v___f_824_);
v___x_826_ = lean_io_as_task(v___x_825_, v___x_792_);
lean_dec_ref(v___x_826_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v___x_790_);
v___x_828_ = v___x_816_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_790_);
v___x_828_ = v_reuseFailAlloc_830_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_829_; 
v___x_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
return v___x_829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15___boxed(lean_object** _args){
lean_object* v___f_832_ = _args[0];
lean_object* v___f_833_ = _args[1];
lean_object* v_activeConnections_834_ = _args[2];
lean_object* v_permitAcquired_835_ = _args[3];
lean_object* v___x_836_ = _args[4];
lean_object* v_connectionLimit_837_ = _args[5];
lean_object* v___x_838_ = _args[6];
lean_object* v___x_839_ = _args[7];
lean_object* v___f_840_ = _args[8];
lean_object* v___x_841_ = _args[9];
lean_object* v_inst_842_ = _args[10];
lean_object* v_val_843_ = _args[11];
lean_object* v_handler_844_ = _args[12];
lean_object* v_config_845_ = _args[13];
lean_object* v_extensions_846_ = _args[14];
lean_object* v___f_847_ = _args[15];
lean_object* v___f_848_ = _args[16];
lean_object* v_x_849_ = _args[17];
lean_object* v___y_850_ = _args[18];
_start:
{
uint8_t v_permitAcquired_boxed_851_; uint8_t v___x_13461__boxed_852_; lean_object* v_res_853_; 
v_permitAcquired_boxed_851_ = lean_unbox(v_permitAcquired_835_);
v___x_13461__boxed_852_ = lean_unbox(v___x_839_);
v_res_853_ = l_Std_Http_Server_serve___redArg___lam__15(v___f_832_, v___f_833_, v_activeConnections_834_, v_permitAcquired_boxed_851_, v___x_836_, v_connectionLimit_837_, v___x_838_, v___x_13461__boxed_852_, v___f_840_, v___x_841_, v_inst_842_, v_val_843_, v_handler_844_, v_config_845_, v_extensions_846_, v___f_847_, v___f_848_, v_x_849_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16(lean_object* v___x_854_, uint8_t v___x_855_, lean_object* v___f_856_, lean_object* v_x_857_){
_start:
{
if (lean_obj_tag(v_x_857_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_867_; 
lean_dec_ref(v___f_856_);
lean_dec(v___x_854_);
v_a_859_ = lean_ctor_get(v_x_857_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v_x_857_);
if (v_isSharedCheck_867_ == 0)
{
v___x_861_ = v_x_857_;
v_isShared_862_ = v_isSharedCheck_867_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v_x_857_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_867_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_859_);
v___x_864_ = v_reuseFailAlloc_866_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_865_; 
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
return v___x_865_;
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_878_; 
v_a_868_ = lean_ctor_get(v_x_857_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v_x_857_);
if (v_isSharedCheck_878_ == 0)
{
v___x_870_ = v_x_857_;
v_isShared_871_ = v_isSharedCheck_878_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v_x_857_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_878_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_872_ = l_Std_CancellationContext_fork(v_a_868_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v___x_872_);
v___x_874_ = v___x_870_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_872_);
v___x_874_ = v_reuseFailAlloc_877_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
v___x_876_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_854_, v___x_855_, v___x_875_, v___f_856_);
return v___x_876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16___boxed(lean_object* v___x_879_, lean_object* v___x_880_, lean_object* v___f_881_, lean_object* v_x_882_, lean_object* v___y_883_){
_start:
{
uint8_t v___x_13551__boxed_884_; lean_object* v_res_885_; 
v___x_13551__boxed_884_ = lean_unbox(v___x_880_);
v_res_885_ = l_Std_Http_Server_serve___redArg___lam__16(v___x_879_, v___x_13551__boxed_884_, v___f_881_, v_x_882_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17(lean_object* v___f_886_, lean_object* v___f_887_, lean_object* v_activeConnections_888_, uint8_t v_permitAcquired_889_, lean_object* v___x_890_, lean_object* v_connectionLimit_891_, uint8_t v___x_892_, lean_object* v___f_893_, lean_object* v___x_894_, lean_object* v_inst_895_, lean_object* v_val_896_, lean_object* v_handler_897_, lean_object* v_config_898_, lean_object* v___f_899_, lean_object* v___f_900_, lean_object* v___f_901_, lean_object* v_extensions_902_, lean_object* v___y_903_){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___f_908_; lean_object* v___x_909_; lean_object* v___f_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_905_ = lean_unsigned_to_nat(0u);
v___x_906_ = lean_box(v_permitAcquired_889_);
v___x_907_ = lean_box(v___x_892_);
v___f_908_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__15___boxed), 19, 17);
lean_closure_set(v___f_908_, 0, v___f_886_);
lean_closure_set(v___f_908_, 1, v___f_887_);
lean_closure_set(v___f_908_, 2, v_activeConnections_888_);
lean_closure_set(v___f_908_, 3, v___x_906_);
lean_closure_set(v___f_908_, 4, v___x_890_);
lean_closure_set(v___f_908_, 5, v_connectionLimit_891_);
lean_closure_set(v___f_908_, 6, v___x_905_);
lean_closure_set(v___f_908_, 7, v___x_907_);
lean_closure_set(v___f_908_, 8, v___f_893_);
lean_closure_set(v___f_908_, 9, v___x_894_);
lean_closure_set(v___f_908_, 10, v_inst_895_);
lean_closure_set(v___f_908_, 11, v_val_896_);
lean_closure_set(v___f_908_, 12, v_handler_897_);
lean_closure_set(v___f_908_, 13, v_config_898_);
lean_closure_set(v___f_908_, 14, v_extensions_902_);
lean_closure_set(v___f_908_, 15, v___f_899_);
lean_closure_set(v___f_908_, 16, v___f_900_);
v___x_909_ = lean_box(v___x_892_);
v___f_910_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__16___boxed), 5, 3);
lean_closure_set(v___f_910_, 0, v___x_905_);
lean_closure_set(v___f_910_, 1, v___x_909_);
lean_closure_set(v___f_910_, 2, v___f_908_);
lean_inc_ref(v___y_903_);
v___x_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_911_, 0, v___y_903_);
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
v___x_913_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_905_, v___x_892_, v___x_912_, v___f_910_);
v___x_914_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_905_, v___x_892_, v___x_913_, v___f_901_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17___boxed(lean_object** _args){
lean_object* v___f_915_ = _args[0];
lean_object* v___f_916_ = _args[1];
lean_object* v_activeConnections_917_ = _args[2];
lean_object* v_permitAcquired_918_ = _args[3];
lean_object* v___x_919_ = _args[4];
lean_object* v_connectionLimit_920_ = _args[5];
lean_object* v___x_921_ = _args[6];
lean_object* v___f_922_ = _args[7];
lean_object* v___x_923_ = _args[8];
lean_object* v_inst_924_ = _args[9];
lean_object* v_val_925_ = _args[10];
lean_object* v_handler_926_ = _args[11];
lean_object* v_config_927_ = _args[12];
lean_object* v___f_928_ = _args[13];
lean_object* v___f_929_ = _args[14];
lean_object* v___f_930_ = _args[15];
lean_object* v_extensions_931_ = _args[16];
lean_object* v___y_932_ = _args[17];
lean_object* v___y_933_ = _args[18];
_start:
{
uint8_t v_permitAcquired_boxed_934_; uint8_t v___x_13608__boxed_935_; lean_object* v_res_936_; 
v_permitAcquired_boxed_934_ = lean_unbox(v_permitAcquired_918_);
v___x_13608__boxed_935_ = lean_unbox(v___x_921_);
v_res_936_ = l_Std_Http_Server_serve___redArg___lam__17(v___f_915_, v___f_916_, v_activeConnections_917_, v_permitAcquired_boxed_934_, v___x_919_, v_connectionLimit_920_, v___x_13608__boxed_935_, v___f_922_, v___x_923_, v_inst_924_, v_val_925_, v_handler_926_, v_config_927_, v___f_928_, v___f_929_, v___f_930_, v_extensions_931_, v___y_932_);
lean_dec_ref(v___y_932_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18(lean_object* v___f_937_, lean_object* v___y_938_, lean_object* v_x_939_){
_start:
{
if (lean_obj_tag(v_x_939_) == 0)
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_949_; 
lean_dec_ref(v___f_937_);
v_a_941_ = lean_ctor_get(v_x_939_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v_x_939_);
if (v_isSharedCheck_949_ == 0)
{
v___x_943_ = v_x_939_;
v_isShared_944_ = v_isSharedCheck_949_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v_x_939_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_949_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_948_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_947_; 
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
return v___x_947_;
}
}
}
else
{
lean_object* v_a_950_; lean_object* v___x_951_; 
v_a_950_ = lean_ctor_get(v_x_939_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v_x_939_, 1);
lean_inc_ref(v___y_938_);
v___x_951_ = lean_apply_3(v___f_937_, v_a_950_, v___y_938_, lean_box(0));
return v___x_951_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18___boxed(lean_object* v___f_952_, lean_object* v___y_953_, lean_object* v_x_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Std_Http_Server_serve___redArg___lam__18(v___f_952_, v___y_953_, v_x_954_);
lean_dec_ref(v___y_953_);
return v_res_956_;
}
}
static lean_object* _init_l_Std_Http_Server_serve___redArg___lam__20___closed__0(void){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = l_Std_Http_Extensions_empty;
v___x_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
return v___x_958_;
}
}
static lean_object* _init_l_Std_Http_Server_serve___redArg___lam__20___closed__1(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = lean_obj_once(&l_Std_Http_Server_serve___redArg___lam__20___closed__0, &l_Std_Http_Server_serve___redArg___lam__20___closed__0_once, _init_l_Std_Http_Server_serve___redArg___lam__20___closed__0);
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20(uint8_t v___x_962_, lean_object* v___f_963_, lean_object* v___x_964_, lean_object* v___f_965_, lean_object* v_x_966_){
_start:
{
if (lean_obj_tag(v_x_966_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_976_; 
lean_dec_ref(v___f_965_);
lean_dec(v___x_964_);
lean_dec_ref(v___f_963_);
v_a_968_ = lean_ctor_get(v_x_966_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v_x_966_);
if (v_isSharedCheck_976_ == 0)
{
v___x_970_ = v_x_966_;
v_isShared_971_ = v_isSharedCheck_976_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v_x_966_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_976_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_975_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_974_; 
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
return v___x_974_;
}
}
}
else
{
lean_object* v_a_977_; 
v_a_977_ = lean_ctor_get(v_x_966_, 0);
lean_inc(v_a_977_);
lean_dec_ref_known(v_x_966_, 1);
if (lean_obj_tag(v_a_977_) == 0)
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
lean_dec_ref_known(v_a_977_, 1);
lean_dec_ref(v___f_965_);
lean_dec(v___x_964_);
v___x_978_ = lean_unsigned_to_nat(0u);
v___x_979_ = lean_obj_once(&l_Std_Http_Server_serve___redArg___lam__20___closed__1, &l_Std_Http_Server_serve___redArg___lam__20___closed__1_once, _init_l_Std_Http_Server_serve___redArg___lam__20___closed__1);
v___x_980_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_978_, v___x_962_, v___x_979_, v___f_963_);
return v___x_980_;
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_996_; 
lean_dec_ref(v___f_963_);
v_a_981_ = lean_ctor_get(v_a_977_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v_a_977_);
if (v_isSharedCheck_996_ == 0)
{
v___x_983_ = v_a_977_;
v_isShared_984_ = v_isSharedCheck_996_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v_a_977_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_996_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v_dyn_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_985_ = l_Std_Http_Extensions_empty;
v_dyn_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_986_, 0, v___x_964_);
lean_ctor_set(v_dyn_986_, 1, v_a_981_);
v___x_987_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__20___closed__2));
v___x_988_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_986_);
v___x_989_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_987_, v___x_988_, v_dyn_986_, v___x_985_);
v___x_990_ = lean_unsigned_to_nat(0u);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_989_);
v___x_992_ = v___x_983_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_989_);
v___x_992_ = v_reuseFailAlloc_995_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
v___x_994_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_990_, v___x_962_, v___x_993_, v___f_965_);
return v___x_994_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20___boxed(lean_object* v___x_997_, lean_object* v___f_998_, lean_object* v___x_999_, lean_object* v___f_1000_, lean_object* v_x_1001_, lean_object* v___y_1002_){
_start:
{
uint8_t v___x_13708__boxed_1003_; lean_object* v_res_1004_; 
v___x_13708__boxed_1003_ = lean_unbox(v___x_997_);
v_res_1004_ = l_Std_Http_Server_serve___redArg___lam__20(v___x_13708__boxed_1003_, v___f_998_, v___x_999_, v___f_1000_, v_x_1001_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__19(uint8_t v_permitAcquired_1005_, lean_object* v___f_1006_, lean_object* v___x_1007_, lean_object* v___y_1008_, lean_object* v_connectionLimit_1009_, uint8_t v___x_1010_, lean_object* v___f_1011_, lean_object* v___f_1012_, lean_object* v___f_1013_, lean_object* v_activeConnections_1014_, lean_object* v___f_1015_, lean_object* v___x_1016_, lean_object* v_inst_1017_, lean_object* v_handler_1018_, lean_object* v_config_1019_, lean_object* v___f_1020_, lean_object* v___f_1021_, lean_object* v___f_1022_, lean_object* v___x_1023_, lean_object* v_x_1024_){
_start:
{
if (lean_obj_tag(v_x_1024_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1034_; 
lean_dec(v___x_1023_);
lean_dec_ref(v___f_1022_);
lean_dec_ref(v___f_1021_);
lean_dec_ref(v___f_1020_);
lean_dec_ref(v_config_1019_);
lean_dec(v_handler_1018_);
lean_dec_ref(v_inst_1017_);
lean_dec_ref(v___x_1016_);
lean_dec_ref(v___f_1015_);
lean_dec_ref(v_activeConnections_1014_);
lean_dec_ref(v___f_1013_);
lean_dec_ref(v___f_1012_);
lean_dec_ref(v___f_1011_);
lean_dec(v_connectionLimit_1009_);
lean_dec_ref(v___f_1006_);
v_a_1026_ = lean_ctor_get(v_x_1024_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_x_1024_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1028_ = v_x_1024_;
v_isShared_1029_ = v_isSharedCheck_1034_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v_x_1024_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1034_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1032_; 
v___x_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
return v___x_1032_;
}
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1093_; 
v_a_1035_ = lean_ctor_get(v_x_1024_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_x_1024_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1037_ = v_x_1024_;
v_isShared_1038_ = v_isSharedCheck_1093_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v_x_1024_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1093_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
if (lean_obj_tag(v_a_1035_) == 0)
{
lean_dec(v___x_1023_);
lean_dec_ref(v___f_1022_);
lean_dec_ref(v___f_1021_);
lean_dec_ref(v___f_1020_);
lean_dec_ref(v_config_1019_);
lean_dec(v_handler_1018_);
lean_dec_ref(v_inst_1017_);
lean_dec_ref(v___x_1016_);
lean_dec_ref(v___f_1015_);
lean_dec_ref(v_activeConnections_1014_);
lean_dec_ref(v___f_1013_);
lean_dec_ref(v___f_1012_);
if (v_permitAcquired_1005_ == 0)
{
lean_object* v___x_1039_; 
lean_del_object(v___x_1037_);
lean_dec_ref(v___f_1011_);
lean_dec(v_connectionLimit_1009_);
lean_inc_ref(v___y_1008_);
v___x_1039_ = lean_apply_3(v___f_1006_, v___x_1007_, v___y_1008_, lean_box(0));
return v___x_1039_;
}
else
{
if (lean_obj_tag(v_connectionLimit_1009_) == 1)
{
lean_object* v_val_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1053_; 
lean_dec_ref(v___f_1006_);
v_val_1040_ = lean_ctor_get(v_connectionLimit_1009_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_connectionLimit_1009_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1042_ = v_connectionLimit_1009_;
v_isShared_1043_ = v_isSharedCheck_1053_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_val_1040_);
lean_dec(v_connectionLimit_1009_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1053_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1044_ = lean_unsigned_to_nat(0u);
v___x_1045_ = l_Std_Semaphore_release(v_val_1040_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v___x_1045_);
v___x_1047_ = v___x_1037_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1049_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set_tag(v___x_1042_, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1047_);
v___x_1049_ = v___x_1042_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1047_);
v___x_1049_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1050_; 
v___x_1050_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1044_, v___x_1010_, v___x_1049_, v___f_1011_);
return v___x_1050_;
}
}
}
}
else
{
lean_object* v___x_1054_; 
lean_del_object(v___x_1037_);
lean_dec_ref(v___f_1011_);
lean_dec(v_connectionLimit_1009_);
lean_inc_ref(v___y_1008_);
v___x_1054_ = lean_apply_3(v___f_1006_, v___x_1007_, v___y_1008_, lean_box(0));
return v___x_1054_;
}
}
}
else
{
lean_object* v_val_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1092_; 
lean_dec_ref(v___f_1011_);
lean_dec_ref(v___f_1006_);
v_val_1055_ = lean_ctor_get(v_a_1035_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_a_1035_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1057_ = v_a_1035_;
v_isShared_1058_ = v_isSharedCheck_1092_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_val_1055_);
lean_dec(v_a_1035_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1092_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___f_1061_; lean_object* v___f_1062_; lean_object* v___x_1063_; lean_object* v___f_1064_; lean_object* v___x_1065_; lean_object* v_val_1067_; lean_object* v___x_1075_; 
v___x_1059_ = lean_box(v_permitAcquired_1005_);
v___x_1060_ = lean_box(v___x_1010_);
lean_inc(v_val_1055_);
v___f_1061_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__17___boxed), 19, 16);
lean_closure_set(v___f_1061_, 0, v___f_1012_);
lean_closure_set(v___f_1061_, 1, v___f_1013_);
lean_closure_set(v___f_1061_, 2, v_activeConnections_1014_);
lean_closure_set(v___f_1061_, 3, v___x_1059_);
lean_closure_set(v___f_1061_, 4, v___x_1007_);
lean_closure_set(v___f_1061_, 5, v_connectionLimit_1009_);
lean_closure_set(v___f_1061_, 6, v___x_1060_);
lean_closure_set(v___f_1061_, 7, v___f_1015_);
lean_closure_set(v___f_1061_, 8, v___x_1016_);
lean_closure_set(v___f_1061_, 9, v_inst_1017_);
lean_closure_set(v___f_1061_, 10, v_val_1055_);
lean_closure_set(v___f_1061_, 11, v_handler_1018_);
lean_closure_set(v___f_1061_, 12, v_config_1019_);
lean_closure_set(v___f_1061_, 13, v___f_1020_);
lean_closure_set(v___f_1061_, 14, v___f_1021_);
lean_closure_set(v___f_1061_, 15, v___f_1022_);
lean_inc_ref(v___y_1008_);
v___f_1062_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__18___boxed), 4, 2);
lean_closure_set(v___f_1062_, 0, v___f_1061_);
lean_closure_set(v___f_1062_, 1, v___y_1008_);
v___x_1063_ = lean_box(v___x_1010_);
lean_inc_ref(v___f_1062_);
v___f_1064_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__20___boxed), 6, 4);
lean_closure_set(v___f_1064_, 0, v___x_1063_);
lean_closure_set(v___f_1064_, 1, v___f_1062_);
lean_closure_set(v___f_1064_, 2, v___x_1023_);
lean_closure_set(v___f_1064_, 3, v___f_1062_);
v___x_1065_ = lean_unsigned_to_nat(0u);
v___x_1075_ = lean_uv_tcp_getpeername(v_val_1055_);
lean_dec(v_val_1055_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1075_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1075_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
lean_ctor_set_tag(v___x_1078_, 1);
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
v_val_1067_ = v___x_1081_;
goto v___jp_1066_;
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
v_a_1084_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1075_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1075_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
lean_ctor_set_tag(v___x_1086_, 0);
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
v_val_1067_ = v___x_1089_;
goto v___jp_1066_;
}
}
}
v___jp_1066_:
{
lean_object* v___x_1069_; 
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v_val_1067_);
v___x_1069_ = v___x_1037_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_val_1067_);
v___x_1069_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
lean_object* v___x_1071_; 
if (v_isShared_1058_ == 0)
{
lean_ctor_set_tag(v___x_1057_, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1069_);
v___x_1071_ = v___x_1057_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; 
v___x_1072_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1065_, v___x_1010_, v___x_1071_, v___f_1064_);
return v___x_1072_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_permitAcquired_1094_ = _args[0];
lean_object* v___f_1095_ = _args[1];
lean_object* v___x_1096_ = _args[2];
lean_object* v___y_1097_ = _args[3];
lean_object* v_connectionLimit_1098_ = _args[4];
lean_object* v___x_1099_ = _args[5];
lean_object* v___f_1100_ = _args[6];
lean_object* v___f_1101_ = _args[7];
lean_object* v___f_1102_ = _args[8];
lean_object* v_activeConnections_1103_ = _args[9];
lean_object* v___f_1104_ = _args[10];
lean_object* v___x_1105_ = _args[11];
lean_object* v_inst_1106_ = _args[12];
lean_object* v_handler_1107_ = _args[13];
lean_object* v_config_1108_ = _args[14];
lean_object* v___f_1109_ = _args[15];
lean_object* v___f_1110_ = _args[16];
lean_object* v___f_1111_ = _args[17];
lean_object* v___x_1112_ = _args[18];
lean_object* v_x_1113_ = _args[19];
lean_object* v___y_1114_ = _args[20];
_start:
{
uint8_t v_permitAcquired_boxed_1115_; uint8_t v___x_13791__boxed_1116_; lean_object* v_res_1117_; 
v_permitAcquired_boxed_1115_ = lean_unbox(v_permitAcquired_1094_);
v___x_13791__boxed_1116_ = lean_unbox(v___x_1099_);
v_res_1117_ = l_Std_Http_Server_serve___redArg___lam__19(v_permitAcquired_boxed_1115_, v___f_1095_, v___x_1096_, v___y_1097_, v_connectionLimit_1098_, v___x_13791__boxed_1116_, v___f_1100_, v___f_1101_, v___f_1102_, v_activeConnections_1103_, v___f_1104_, v___x_1105_, v_inst_1106_, v_handler_1107_, v_config_1108_, v___f_1109_, v___f_1110_, v___f_1111_, v___x_1112_, v_x_1113_);
lean_dec_ref(v___y_1097_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21(lean_object* v_a_1118_, lean_object* v___f_1119_, lean_object* v___f_1120_, uint8_t v___x_1121_, lean_object* v___f_1122_, lean_object* v_x_1123_){
_start:
{
if (lean_obj_tag(v_x_1123_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1133_; 
lean_dec_ref(v___f_1122_);
lean_dec_ref(v___f_1120_);
lean_dec_ref(v___f_1119_);
lean_dec(v_a_1118_);
v_a_1125_ = lean_ctor_get(v_x_1123_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_x_1123_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1127_ = v_x_1123_;
v_isShared_1128_ = v_isSharedCheck_1133_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v_x_1123_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1133_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1131_; 
v___x_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
return v___x_1131_;
}
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v_a_1134_ = lean_ctor_get(v_x_1123_, 0);
lean_inc(v_a_1134_);
lean_dec_ref_known(v_x_1123_, 1);
v___x_1135_ = l_Std_Async_TCP_Socket_Server_acceptSelector(v_a_1118_);
v___x_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
lean_ctor_set(v___x_1136_, 1, v___f_1119_);
v___x_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1137_, 0, v_a_1134_);
lean_ctor_set(v___x_1137_, 1, v___f_1120_);
v___x_1138_ = lean_unsigned_to_nat(2u);
v___x_1139_ = lean_mk_empty_array_with_capacity(v___x_1138_);
v___x_1140_ = lean_array_push(v___x_1139_, v___x_1136_);
v___x_1141_ = lean_array_push(v___x_1140_, v___x_1137_);
v___x_1142_ = lean_unsigned_to_nat(0u);
v___x_1143_ = l_Std_Async_Selectable_one___redArg(v___x_1141_);
v___x_1144_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1142_, v___x_1121_, v___x_1143_, v___f_1122_);
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21___boxed(lean_object* v_a_1145_, lean_object* v___f_1146_, lean_object* v___f_1147_, lean_object* v___x_1148_, lean_object* v___f_1149_, lean_object* v_x_1150_, lean_object* v___y_1151_){
_start:
{
uint8_t v___x_13975__boxed_1152_; lean_object* v_res_1153_; 
v___x_13975__boxed_1152_ = lean_unbox(v___x_1148_);
v_res_1153_ = l_Std_Http_Server_serve___redArg___lam__21(v_a_1145_, v___f_1146_, v___f_1147_, v___x_13975__boxed_1152_, v___f_1149_, v_x_1150_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22(lean_object* v___f_1154_, lean_object* v___x_1155_, lean_object* v_connectionLimit_1156_, uint8_t v___x_1157_, lean_object* v___f_1158_, lean_object* v___f_1159_, lean_object* v_activeConnections_1160_, lean_object* v___f_1161_, lean_object* v___x_1162_, lean_object* v_inst_1163_, lean_object* v_handler_1164_, lean_object* v_config_1165_, lean_object* v___f_1166_, lean_object* v___f_1167_, lean_object* v___f_1168_, lean_object* v___x_1169_, lean_object* v_a_1170_, lean_object* v___f_1171_, lean_object* v___f_1172_, lean_object* v___f_1173_, uint8_t v_permitAcquired_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v___f_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___f_1180_; lean_object* v___x_1181_; lean_object* v___f_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
lean_inc_ref_n(v___y_1175_, 3);
lean_inc_ref(v___f_1154_);
v___f_1177_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_1177_, 0, v___f_1154_);
lean_closure_set(v___f_1177_, 1, v___y_1175_);
v___x_1178_ = lean_box(v_permitAcquired_1174_);
v___x_1179_ = lean_box(v___x_1157_);
v___f_1180_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__19___boxed), 21, 19);
lean_closure_set(v___f_1180_, 0, v___x_1178_);
lean_closure_set(v___f_1180_, 1, v___f_1154_);
lean_closure_set(v___f_1180_, 2, v___x_1155_);
lean_closure_set(v___f_1180_, 3, v___y_1175_);
lean_closure_set(v___f_1180_, 4, v_connectionLimit_1156_);
lean_closure_set(v___f_1180_, 5, v___x_1179_);
lean_closure_set(v___f_1180_, 6, v___f_1177_);
lean_closure_set(v___f_1180_, 7, v___f_1158_);
lean_closure_set(v___f_1180_, 8, v___f_1159_);
lean_closure_set(v___f_1180_, 9, v_activeConnections_1160_);
lean_closure_set(v___f_1180_, 10, v___f_1161_);
lean_closure_set(v___f_1180_, 11, v___x_1162_);
lean_closure_set(v___f_1180_, 12, v_inst_1163_);
lean_closure_set(v___f_1180_, 13, v_handler_1164_);
lean_closure_set(v___f_1180_, 14, v_config_1165_);
lean_closure_set(v___f_1180_, 15, v___f_1166_);
lean_closure_set(v___f_1180_, 16, v___f_1167_);
lean_closure_set(v___f_1180_, 17, v___f_1168_);
lean_closure_set(v___f_1180_, 18, v___x_1169_);
v___x_1181_ = lean_box(v___x_1157_);
v___f_1182_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__21___boxed), 7, 5);
lean_closure_set(v___f_1182_, 0, v_a_1170_);
lean_closure_set(v___f_1182_, 1, v___f_1171_);
lean_closure_set(v___f_1182_, 2, v___f_1172_);
lean_closure_set(v___f_1182_, 3, v___x_1181_);
lean_closure_set(v___f_1182_, 4, v___f_1180_);
v___x_1183_ = lean_unsigned_to_nat(0u);
v___x_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1184_, 0, v___y_1175_);
v___x_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
v___x_1186_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1183_, v___x_1157_, v___x_1185_, v___f_1173_);
v___x_1187_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1183_, v___x_1157_, v___x_1186_, v___f_1182_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22___boxed(lean_object** _args){
lean_object* v___f_1188_ = _args[0];
lean_object* v___x_1189_ = _args[1];
lean_object* v_connectionLimit_1190_ = _args[2];
lean_object* v___x_1191_ = _args[3];
lean_object* v___f_1192_ = _args[4];
lean_object* v___f_1193_ = _args[5];
lean_object* v_activeConnections_1194_ = _args[6];
lean_object* v___f_1195_ = _args[7];
lean_object* v___x_1196_ = _args[8];
lean_object* v_inst_1197_ = _args[9];
lean_object* v_handler_1198_ = _args[10];
lean_object* v_config_1199_ = _args[11];
lean_object* v___f_1200_ = _args[12];
lean_object* v___f_1201_ = _args[13];
lean_object* v___f_1202_ = _args[14];
lean_object* v___x_1203_ = _args[15];
lean_object* v_a_1204_ = _args[16];
lean_object* v___f_1205_ = _args[17];
lean_object* v___f_1206_ = _args[18];
lean_object* v___f_1207_ = _args[19];
lean_object* v_permitAcquired_1208_ = _args[20];
lean_object* v___y_1209_ = _args[21];
lean_object* v___y_1210_ = _args[22];
_start:
{
uint8_t v___x_14035__boxed_1211_; uint8_t v_permitAcquired_boxed_1212_; lean_object* v_res_1213_; 
v___x_14035__boxed_1211_ = lean_unbox(v___x_1191_);
v_permitAcquired_boxed_1212_ = lean_unbox(v_permitAcquired_1208_);
v_res_1213_ = l_Std_Http_Server_serve___redArg___lam__22(v___f_1188_, v___x_1189_, v_connectionLimit_1190_, v___x_14035__boxed_1211_, v___f_1192_, v___f_1193_, v_activeConnections_1194_, v___f_1195_, v___x_1196_, v_inst_1197_, v_handler_1198_, v_config_1199_, v___f_1200_, v___f_1201_, v___f_1202_, v___x_1203_, v_a_1204_, v___f_1205_, v___f_1206_, v___f_1207_, v_permitAcquired_boxed_1212_, v___y_1209_);
lean_dec_ref(v___y_1209_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23(lean_object* v___f_1214_, lean_object* v___y_1215_, lean_object* v_x_1216_){
_start:
{
if (lean_obj_tag(v_x_1216_) == 0)
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1226_; 
lean_dec_ref(v___y_1215_);
lean_dec_ref(v___f_1214_);
v_a_1218_ = lean_ctor_get(v_x_1216_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_x_1216_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1220_ = v_x_1216_;
v_isShared_1221_ = v_isSharedCheck_1226_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v_x_1216_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1226_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1224_; 
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1228_; 
v_a_1227_ = lean_ctor_get(v_x_1216_, 0);
lean_inc(v_a_1227_);
lean_dec_ref_known(v_x_1216_, 1);
v___x_1228_ = lean_apply_3(v___f_1214_, v_a_1227_, v___y_1215_, lean_box(0));
return v___x_1228_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23___boxed(lean_object* v___f_1229_, lean_object* v___y_1230_, lean_object* v_x_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Std_Http_Server_serve___redArg___lam__23(v___f_1229_, v___y_1230_, v_x_1231_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25(uint8_t v___x_1234_, uint8_t v___x_1235_, lean_object* v___f_1236_, lean_object* v_x_1237_){
_start:
{
if (lean_obj_tag(v_x_1237_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1247_; 
lean_dec_ref(v___f_1236_);
v_a_1239_ = lean_ctor_get(v_x_1237_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_x_1237_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1241_ = v_x_1237_;
v_isShared_1242_ = v_isSharedCheck_1247_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v_x_1237_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1247_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1245_; 
v___x_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
return v___x_1245_;
}
}
}
else
{
lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1258_; 
v_isSharedCheck_1258_ = !lean_is_exclusive(v_x_1237_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; 
v_unused_1259_ = lean_ctor_get(v_x_1237_, 0);
lean_dec(v_unused_1259_);
v___x_1249_ = v_x_1237_;
v_isShared_1250_ = v_isSharedCheck_1258_;
goto v_resetjp_1248_;
}
else
{
lean_dec(v_x_1237_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1258_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1251_ = lean_unsigned_to_nat(0u);
v___x_1252_ = lean_box(v___x_1234_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1252_);
v___x_1254_ = v___x_1249_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
v___x_1256_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1251_, v___x_1235_, v___x_1255_, v___f_1236_);
return v___x_1256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25___boxed(lean_object* v___x_1260_, lean_object* v___x_1261_, lean_object* v___f_1262_, lean_object* v_x_1263_, lean_object* v___y_1264_){
_start:
{
uint8_t v___x_14143__boxed_1265_; uint8_t v___x_14144__boxed_1266_; lean_object* v_res_1267_; 
v___x_14143__boxed_1265_ = lean_unbox(v___x_1260_);
v___x_14144__boxed_1266_ = lean_unbox(v___x_1261_);
v_res_1267_ = l_Std_Http_Server_serve___redArg___lam__25(v___x_14143__boxed_1265_, v___x_14144__boxed_1266_, v___f_1262_, v_x_1263_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24(lean_object* v___f_1268_, uint8_t v___x_1269_, lean_object* v___f_1270_, lean_object* v_x_1271_){
_start:
{
if (lean_obj_tag(v_x_1271_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1281_; 
lean_dec_ref(v___f_1270_);
lean_dec_ref(v___f_1268_);
v_a_1273_ = lean_ctor_get(v_x_1271_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_x_1271_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1275_ = v_x_1271_;
v_isShared_1276_ = v_isSharedCheck_1281_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v_x_1271_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1281_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1279_; 
v___x_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
return v___x_1279_;
}
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v_a_1282_ = lean_ctor_get(v_x_1271_, 0);
lean_inc(v_a_1282_);
lean_dec_ref_known(v_x_1271_, 1);
v___x_1283_ = lean_unsigned_to_nat(0u);
v___x_1284_ = l_IO_Promise_result_x21___redArg(v_a_1282_);
lean_dec(v_a_1282_);
v___x_1285_ = lean_task_map(v___f_1268_, v___x_1284_, v___x_1283_, v___x_1269_);
v___x_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
v___x_1287_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1283_, v___x_1269_, v___x_1286_, v___f_1270_);
return v___x_1287_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24___boxed(lean_object* v___f_1288_, lean_object* v___x_1289_, lean_object* v___f_1290_, lean_object* v_x_1291_, lean_object* v___y_1292_){
_start:
{
uint8_t v___x_14202__boxed_1293_; lean_object* v_res_1294_; 
v___x_14202__boxed_1293_ = lean_unbox(v___x_1289_);
v_res_1294_ = l_Std_Http_Server_serve___redArg___lam__24(v___f_1288_, v___x_14202__boxed_1293_, v___f_1290_, v_x_1291_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26(lean_object* v_connectionLimit_1295_, uint8_t v___x_1296_, lean_object* v___f_1297_, lean_object* v___f_1298_, lean_object* v___f_1299_, lean_object* v_u_1300_, lean_object* v_b_1301_){
_start:
{
if (lean_obj_tag(v_connectionLimit_1295_) == 1)
{
lean_object* v_val_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1320_; 
lean_dec_ref(v___f_1299_);
v_val_1303_ = lean_ctor_get(v_connectionLimit_1295_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_connectionLimit_1295_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1305_ = v_connectionLimit_1295_;
v_isShared_1306_ = v_isSharedCheck_1320_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_val_1303_);
lean_dec(v_connectionLimit_1295_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1320_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
uint8_t v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___f_1310_; lean_object* v___x_1311_; lean_object* v___f_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1307_ = 1;
v___x_1308_ = lean_box(v___x_1307_);
v___x_1309_ = lean_box(v___x_1296_);
v___f_1310_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__25___boxed), 5, 3);
lean_closure_set(v___f_1310_, 0, v___x_1308_);
lean_closure_set(v___f_1310_, 1, v___x_1309_);
lean_closure_set(v___f_1310_, 2, v___f_1297_);
v___x_1311_ = lean_box(v___x_1296_);
v___f_1312_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__24___boxed), 5, 3);
lean_closure_set(v___f_1312_, 0, v___f_1298_);
lean_closure_set(v___f_1312_, 1, v___x_1311_);
lean_closure_set(v___f_1312_, 2, v___f_1310_);
v___x_1313_ = lean_unsigned_to_nat(0u);
v___x_1314_ = l_Std_Semaphore_acquire(v_val_1303_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 0, v___x_1314_);
v___x_1316_ = v___x_1305_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
v___x_1318_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1313_, v___x_1296_, v___x_1317_, v___f_1312_);
return v___x_1318_;
}
}
}
else
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
lean_dec_ref(v___f_1298_);
lean_dec_ref(v___f_1297_);
lean_dec(v_connectionLimit_1295_);
v___x_1321_ = lean_unsigned_to_nat(0u);
v___x_1322_ = lean_box(v___x_1296_);
v___x_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
v___x_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
v___x_1325_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1321_, v___x_1296_, v___x_1324_, v___f_1299_);
return v___x_1325_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26___boxed(lean_object* v_connectionLimit_1326_, lean_object* v___x_1327_, lean_object* v___f_1328_, lean_object* v___f_1329_, lean_object* v___f_1330_, lean_object* v_u_1331_, lean_object* v_b_1332_, lean_object* v___y_1333_){
_start:
{
uint8_t v___x_14246__boxed_1334_; lean_object* v_res_1335_; 
v___x_14246__boxed_1334_ = lean_unbox(v___x_1327_);
v_res_1335_ = l_Std_Http_Server_serve___redArg___lam__26(v_connectionLimit_1326_, v___x_14246__boxed_1334_, v___f_1328_, v___f_1329_, v___f_1330_, v_u_1331_, v_b_1332_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27(lean_object* v_a_1336_, lean_object* v_x_1337_){
_start:
{
if (lean_obj_tag(v_x_1337_) == 0)
{
lean_object* v___x_1339_; 
v___x_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1339_, 0, v_x_1337_);
return v___x_1339_;
}
else
{
lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1347_; 
v_isSharedCheck_1347_ = !lean_is_exclusive(v_x_1337_);
if (v_isSharedCheck_1347_ == 0)
{
lean_object* v_unused_1348_; 
v_unused_1348_ = lean_ctor_get(v_x_1337_, 0);
lean_dec(v_unused_1348_);
v___x_1341_ = v_x_1337_;
v_isShared_1342_ = v_isSharedCheck_1347_;
goto v_resetjp_1340_;
}
else
{
lean_dec(v_x_1337_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1347_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1343_ = l_IO_Promise_result_x21___redArg(v_a_1336_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 0, v___x_1343_);
v___x_1345_ = v___x_1341_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1343_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27___boxed(lean_object* v_a_1349_, lean_object* v_x_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Std_Http_Server_serve___redArg___lam__27(v_a_1349_, v_x_1350_);
lean_dec(v_a_1349_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28(lean_object* v___f_1353_, lean_object* v___x_1354_, lean_object* v___x_1355_, uint8_t v___x_1356_, lean_object* v_x_1357_){
_start:
{
if (lean_obj_tag(v_x_1357_) == 0)
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1367_; 
lean_dec(v___x_1354_);
lean_dec_ref(v___f_1353_);
v_a_1359_ = lean_ctor_get(v_x_1357_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_x_1357_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1361_ = v_x_1357_;
v_isShared_1362_ = v_isSharedCheck_1367_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v_x_1357_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1367_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
lean_object* v___x_1365_; 
v___x_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
return v___x_1365_;
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1379_; 
v_a_1368_ = lean_ctor_get(v_x_1357_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_x_1357_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1370_ = v_x_1357_;
v_isShared_1371_ = v_isSharedCheck_1379_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v_x_1357_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1379_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___f_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
lean_inc(v_a_1368_);
v___f_1372_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__27___boxed), 3, 1);
lean_closure_set(v___f_1372_, 0, v_a_1368_);
lean_inc(v___x_1354_);
v___x_1373_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_1353_, v___x_1354_, v_a_1368_, v___x_1355_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1373_);
v___x_1375_ = v___x_1370_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
v___x_1377_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1354_, v___x_1356_, v___x_1376_, v___f_1372_);
return v___x_1377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28___boxed(lean_object* v___f_1380_, lean_object* v___x_1381_, lean_object* v___x_1382_, lean_object* v___x_1383_, lean_object* v_x_1384_, lean_object* v___y_1385_){
_start:
{
uint8_t v___x_14341__boxed_1386_; lean_object* v_res_1387_; 
v___x_14341__boxed_1386_ = lean_unbox(v___x_1383_);
v_res_1387_ = l_Std_Http_Server_serve___redArg___lam__28(v___f_1380_, v___x_1381_, v___x_1382_, v___x_14341__boxed_1386_, v_x_1384_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29(lean_object* v___f_1388_, lean_object* v_connectionLimit_1389_, uint8_t v___x_1390_, lean_object* v___f_1391_, lean_object* v___x_1392_, lean_object* v___f_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v___f_1396_; lean_object* v___x_1397_; lean_object* v___f_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___f_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___f_1396_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__23___boxed), 4, 2);
lean_closure_set(v___f_1396_, 0, v___f_1388_);
lean_closure_set(v___f_1396_, 1, v___y_1394_);
v___x_1397_ = lean_box(v___x_1390_);
lean_inc_ref(v___f_1396_);
v___f_1398_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__26___boxed), 8, 5);
lean_closure_set(v___f_1398_, 0, v_connectionLimit_1389_);
lean_closure_set(v___f_1398_, 1, v___x_1397_);
lean_closure_set(v___f_1398_, 2, v___f_1396_);
lean_closure_set(v___f_1398_, 3, v___f_1391_);
lean_closure_set(v___f_1398_, 4, v___f_1396_);
v___x_1399_ = lean_unsigned_to_nat(0u);
v___x_1400_ = lean_box(v___x_1390_);
v___f_1401_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__28___boxed), 6, 4);
lean_closure_set(v___f_1401_, 0, v___f_1398_);
lean_closure_set(v___f_1401_, 1, v___x_1399_);
lean_closure_set(v___f_1401_, 2, v___x_1392_);
lean_closure_set(v___f_1401_, 3, v___x_1400_);
v___x_1402_ = lean_io_promise_new();
v___x_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1402_);
v___x_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
v___x_1405_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1399_, v___x_1390_, v___x_1404_, v___f_1401_);
v___x_1406_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1399_, v___x_1390_, v___x_1405_, v___f_1393_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29___boxed(lean_object* v___f_1407_, lean_object* v_connectionLimit_1408_, lean_object* v___x_1409_, lean_object* v___f_1410_, lean_object* v___x_1411_, lean_object* v___f_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
uint8_t v___x_14399__boxed_1415_; lean_object* v_res_1416_; 
v___x_14399__boxed_1415_ = lean_unbox(v___x_1409_);
v_res_1416_ = l_Std_Http_Server_serve___redArg___lam__29(v___f_1407_, v_connectionLimit_1408_, v___x_14399__boxed_1415_, v___f_1410_, v___x_1411_, v___f_1412_, v___y_1413_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30(lean_object* v___f_1421_, lean_object* v___f_1422_, lean_object* v___x_1423_, lean_object* v_inst_1424_, lean_object* v_handler_1425_, lean_object* v_config_1426_, lean_object* v___f_1427_, lean_object* v___f_1428_, lean_object* v___x_1429_, lean_object* v_a_1430_, lean_object* v___f_1431_, lean_object* v___f_1432_, lean_object* v___f_1433_, lean_object* v___f_1434_, lean_object* v___f_1435_, lean_object* v_x_1436_){
_start:
{
if (lean_obj_tag(v_x_1436_) == 0)
{
lean_object* v___x_1438_; 
lean_dec_ref(v___f_1435_);
lean_dec_ref(v___f_1434_);
lean_dec_ref(v___f_1433_);
lean_dec_ref(v___f_1432_);
lean_dec_ref(v___f_1431_);
lean_dec(v_a_1430_);
lean_dec(v___x_1429_);
lean_dec_ref(v___f_1428_);
lean_dec_ref(v___f_1427_);
lean_dec_ref(v_config_1426_);
lean_dec(v_handler_1425_);
lean_dec_ref(v_inst_1424_);
lean_dec_ref(v___x_1423_);
lean_dec_ref(v___f_1422_);
lean_dec_ref(v___f_1421_);
v___x_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1438_, 0, v_x_1436_);
return v___x_1438_;
}
else
{
lean_object* v_a_1439_; lean_object* v_context_1440_; lean_object* v_activeConnections_1441_; lean_object* v_connectionLimit_1442_; lean_object* v_shutdownPromise_1443_; lean_object* v___f_1444_; lean_object* v___f_1445_; lean_object* v___f_1446_; uint8_t v___x_1447_; lean_object* v___x_1448_; lean_object* v___f_1449_; lean_object* v___f_1450_; lean_object* v___x_1451_; lean_object* v___f_1452_; lean_object* v___x_1453_; lean_object* v___f_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v_a_1439_ = lean_ctor_get(v_x_1436_, 0);
lean_inc(v_a_1439_);
v_context_1440_ = lean_ctor_get(v_a_1439_, 0);
lean_inc_ref_n(v_context_1440_, 2);
v_activeConnections_1441_ = lean_ctor_get(v_a_1439_, 1);
v_connectionLimit_1442_ = lean_ctor_get(v_a_1439_, 2);
v_shutdownPromise_1443_ = lean_ctor_get(v_a_1439_, 3);
v___f_1444_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1444_, 0, v_x_1436_);
lean_inc_ref(v_shutdownPromise_1443_);
v___f_1445_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1445_, 0, v_context_1440_);
lean_closure_set(v___f_1445_, 1, v_shutdownPromise_1443_);
v___f_1446_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed), 5, 1);
lean_closure_set(v___f_1446_, 0, v___f_1445_);
v___x_1447_ = 0;
v___x_1448_ = lean_box(0);
v___f_1449_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__30___closed__0));
v___f_1450_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__30___closed__1));
v___x_1451_ = lean_box(v___x_1447_);
lean_inc_ref(v_activeConnections_1441_);
lean_inc_n(v_connectionLimit_1442_, 2);
v___f_1452_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__22___boxed), 23, 20);
lean_closure_set(v___f_1452_, 0, v___f_1449_);
lean_closure_set(v___f_1452_, 1, v___x_1448_);
lean_closure_set(v___f_1452_, 2, v_connectionLimit_1442_);
lean_closure_set(v___f_1452_, 3, v___x_1451_);
lean_closure_set(v___f_1452_, 4, v___f_1421_);
lean_closure_set(v___f_1452_, 5, v___f_1446_);
lean_closure_set(v___f_1452_, 6, v_activeConnections_1441_);
lean_closure_set(v___f_1452_, 7, v___f_1422_);
lean_closure_set(v___f_1452_, 8, v___x_1423_);
lean_closure_set(v___f_1452_, 9, v_inst_1424_);
lean_closure_set(v___f_1452_, 10, v_handler_1425_);
lean_closure_set(v___f_1452_, 11, v_config_1426_);
lean_closure_set(v___f_1452_, 12, v___f_1427_);
lean_closure_set(v___f_1452_, 13, v___f_1428_);
lean_closure_set(v___f_1452_, 14, v___f_1450_);
lean_closure_set(v___f_1452_, 15, v___x_1429_);
lean_closure_set(v___f_1452_, 16, v_a_1430_);
lean_closure_set(v___f_1452_, 17, v___f_1431_);
lean_closure_set(v___f_1452_, 18, v___f_1432_);
lean_closure_set(v___f_1452_, 19, v___f_1433_);
v___x_1453_ = lean_box(v___x_1447_);
v___f_1454_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__29___boxed), 8, 6);
lean_closure_set(v___f_1454_, 0, v___f_1452_);
lean_closure_set(v___f_1454_, 1, v_connectionLimit_1442_);
lean_closure_set(v___f_1454_, 2, v___x_1453_);
lean_closure_set(v___f_1454_, 3, v___f_1434_);
lean_closure_set(v___f_1454_, 4, v___x_1448_);
lean_closure_set(v___f_1454_, 5, v___f_1435_);
v___x_1455_ = lean_box(v___x_1447_);
v___x_1456_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___boxed), 6, 5);
lean_closure_set(v___x_1456_, 0, lean_box(0));
lean_closure_set(v___x_1456_, 1, v_a_1439_);
lean_closure_set(v___x_1456_, 2, v___x_1455_);
lean_closure_set(v___x_1456_, 3, v___f_1454_);
lean_closure_set(v___x_1456_, 4, v_context_1440_);
v___x_1457_ = lean_unsigned_to_nat(0u);
v___x_1458_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1458_, 0, lean_box(0));
lean_closure_set(v___x_1458_, 1, v___x_1456_);
v___x_1459_ = lean_io_as_task(v___x_1458_, v___x_1457_);
lean_dec_ref(v___x_1459_);
v___x_1460_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
v___x_1461_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1457_, v___x_1447_, v___x_1460_, v___f_1444_);
return v___x_1461_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30___boxed(lean_object** _args){
lean_object* v___f_1462_ = _args[0];
lean_object* v___f_1463_ = _args[1];
lean_object* v___x_1464_ = _args[2];
lean_object* v_inst_1465_ = _args[3];
lean_object* v_handler_1466_ = _args[4];
lean_object* v_config_1467_ = _args[5];
lean_object* v___f_1468_ = _args[6];
lean_object* v___f_1469_ = _args[7];
lean_object* v___x_1470_ = _args[8];
lean_object* v_a_1471_ = _args[9];
lean_object* v___f_1472_ = _args[10];
lean_object* v___f_1473_ = _args[11];
lean_object* v___f_1474_ = _args[12];
lean_object* v___f_1475_ = _args[13];
lean_object* v___f_1476_ = _args[14];
lean_object* v_x_1477_ = _args[15];
lean_object* v___y_1478_ = _args[16];
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Std_Http_Server_serve___redArg___lam__30(v___f_1462_, v___f_1463_, v___x_1464_, v_inst_1465_, v_handler_1466_, v_config_1467_, v___f_1468_, v___f_1469_, v___x_1470_, v_a_1471_, v___f_1472_, v___f_1473_, v___f_1474_, v___f_1475_, v___f_1476_, v_x_1477_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31(lean_object* v___f_1480_, lean_object* v_config_1481_, lean_object* v_x_1482_){
_start:
{
if (lean_obj_tag(v_x_1482_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1492_; 
lean_dec_ref(v_config_1481_);
lean_dec_ref(v___f_1480_);
v_a_1484_ = lean_ctor_get(v_x_1482_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_x_1482_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1486_ = v_x_1482_;
v_isShared_1487_ = v_isSharedCheck_1492_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v_x_1482_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1492_;
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
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
return v___x_1490_;
}
}
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1509_; 
v_a_1493_ = lean_ctor_get(v_x_1482_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_x_1482_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1495_ = v_x_1482_;
v_isShared_1496_ = v_isSharedCheck_1509_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v_x_1482_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1509_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; lean_object* v_val_1501_; lean_object* v___x_1504_; lean_object* v_a_1505_; lean_object* v___x_1507_; 
v___x_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1497_, 0, v_a_1493_);
v___x_1498_ = lean_unsigned_to_nat(0u);
v___x_1499_ = 0;
v___x_1504_ = l_Std_Http_Server_new(v_config_1481_, v___x_1497_);
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_a_1505_);
lean_dec_ref(v___x_1504_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 0, v_a_1505_);
v___x_1507_ = v___x_1495_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1505_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v___jp_1500_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1502_, 0, v_val_1501_);
v___x_1503_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1498_, v___x_1499_, v___x_1502_, v___f_1480_);
return v___x_1503_;
}
v_reusejp_1506_:
{
v_val_1501_ = v___x_1507_;
goto v___jp_1500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31___boxed(lean_object* v___f_1510_, lean_object* v_config_1511_, lean_object* v_x_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Std_Http_Server_serve___redArg___lam__31(v___f_1510_, v_config_1511_, v_x_1512_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32(lean_object* v___f_1515_, lean_object* v_a_1516_, lean_object* v_x_1517_){
_start:
{
if (lean_obj_tag(v_x_1517_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1527_; 
lean_dec_ref(v___f_1515_);
v_a_1519_ = lean_ctor_get(v_x_1517_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v_x_1517_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1521_ = v_x_1517_;
v_isShared_1522_ = v_isSharedCheck_1527_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v_x_1517_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1527_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
return v___x_1525_;
}
}
}
else
{
lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1546_; 
v_isSharedCheck_1546_ = !lean_is_exclusive(v_x_1517_);
if (v_isSharedCheck_1546_ == 0)
{
lean_object* v_unused_1547_; 
v_unused_1547_ = lean_ctor_get(v_x_1517_, 0);
lean_dec(v_unused_1547_);
v___x_1529_ = v_x_1517_;
v_isShared_1530_ = v_isSharedCheck_1546_;
goto v_resetjp_1528_;
}
else
{
lean_dec(v_x_1517_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1546_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1531_; uint8_t v___x_1532_; lean_object* v_val_1534_; lean_object* v___x_1537_; 
v___x_1531_ = lean_unsigned_to_nat(0u);
v___x_1532_ = 0;
v___x_1537_ = lean_uv_tcp_getsockname(v_a_1516_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1540_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v___x_1537_, 1);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 0, v_a_1538_);
v___x_1540_ = v___x_1529_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1538_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
v_val_1534_ = v___x_1540_;
goto v___jp_1533_;
}
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; 
v_a_1542_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1542_);
lean_dec_ref_known(v___x_1537_, 1);
if (v_isShared_1530_ == 0)
{
lean_ctor_set_tag(v___x_1529_, 0);
lean_ctor_set(v___x_1529_, 0, v_a_1542_);
v___x_1544_ = v___x_1529_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1542_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
v_val_1534_ = v___x_1544_;
goto v___jp_1533_;
}
}
v___jp_1533_:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1535_, 0, v_val_1534_);
v___x_1536_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1531_, v___x_1532_, v___x_1535_, v___f_1515_);
return v___x_1536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32___boxed(lean_object* v___f_1548_, lean_object* v_a_1549_, lean_object* v_x_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Std_Http_Server_serve___redArg___lam__32(v___f_1548_, v_a_1549_, v_x_1550_);
lean_dec(v_a_1549_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__33(lean_object* v___f_1553_, lean_object* v_a_1554_, lean_object* v_x_1555_){
_start:
{
if (lean_obj_tag(v_x_1555_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1565_; 
lean_dec_ref(v___f_1553_);
v_a_1557_ = lean_ctor_get(v_x_1555_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v_x_1555_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1559_ = v_x_1555_;
v_isShared_1560_ = v_isSharedCheck_1565_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v_x_1555_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1565_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
lean_object* v___x_1563_; 
v___x_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
return v___x_1563_;
}
}
}
else
{
lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1584_; 
v_isSharedCheck_1584_ = !lean_is_exclusive(v_x_1555_);
if (v_isSharedCheck_1584_ == 0)
{
lean_object* v_unused_1585_; 
v_unused_1585_ = lean_ctor_get(v_x_1555_, 0);
lean_dec(v_unused_1585_);
v___x_1567_ = v_x_1555_;
v_isShared_1568_ = v_isSharedCheck_1584_;
goto v_resetjp_1566_;
}
else
{
lean_dec(v_x_1555_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1584_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1569_; uint8_t v___x_1570_; lean_object* v_val_1572_; lean_object* v___x_1575_; 
v___x_1569_ = lean_unsigned_to_nat(0u);
v___x_1570_ = 0;
v___x_1575_ = lean_uv_tcp_nodelay(v_a_1554_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v___x_1578_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v___x_1575_, 1);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 0, v_a_1576_);
v___x_1578_ = v___x_1567_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
v_val_1572_ = v___x_1578_;
goto v___jp_1571_;
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; 
v_a_1580_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1575_, 1);
if (v_isShared_1568_ == 0)
{
lean_ctor_set_tag(v___x_1567_, 0);
lean_ctor_set(v___x_1567_, 0, v_a_1580_);
v___x_1582_ = v___x_1567_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1580_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
v_val_1572_ = v___x_1582_;
goto v___jp_1571_;
}
}
v___jp_1571_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1573_, 0, v_val_1572_);
v___x_1574_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1569_, v___x_1570_, v___x_1573_, v___f_1553_);
return v___x_1574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__33___boxed(lean_object* v___f_1586_, lean_object* v_a_1587_, lean_object* v_x_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Std_Http_Server_serve___redArg___lam__33(v___f_1586_, v_a_1587_, v_x_1588_);
lean_dec(v_a_1587_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__34(lean_object* v___f_1591_, lean_object* v_a_1592_, uint32_t v_backlog_1593_, lean_object* v_x_1594_){
_start:
{
if (lean_obj_tag(v_x_1594_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1604_; 
lean_dec_ref(v___f_1591_);
v_a_1596_ = lean_ctor_get(v_x_1594_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v_x_1594_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1598_ = v_x_1594_;
v_isShared_1599_ = v_isSharedCheck_1604_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v_x_1594_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1604_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
lean_object* v___x_1602_; 
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
return v___x_1602_;
}
}
}
else
{
lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1623_; 
v_isSharedCheck_1623_ = !lean_is_exclusive(v_x_1594_);
if (v_isSharedCheck_1623_ == 0)
{
lean_object* v_unused_1624_; 
v_unused_1624_ = lean_ctor_get(v_x_1594_, 0);
lean_dec(v_unused_1624_);
v___x_1606_ = v_x_1594_;
v_isShared_1607_ = v_isSharedCheck_1623_;
goto v_resetjp_1605_;
}
else
{
lean_dec(v_x_1594_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1623_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1608_; uint8_t v___x_1609_; lean_object* v_val_1611_; lean_object* v___x_1614_; 
v___x_1608_ = lean_unsigned_to_nat(0u);
v___x_1609_ = 0;
v___x_1614_ = lean_uv_tcp_listen(v_a_1592_, v_backlog_1593_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v___x_1617_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_a_1615_);
lean_dec_ref_known(v___x_1614_, 1);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v_a_1615_);
v___x_1617_ = v___x_1606_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1615_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
v_val_1611_ = v___x_1617_;
goto v___jp_1610_;
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; 
v_a_1619_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_a_1619_);
lean_dec_ref_known(v___x_1614_, 1);
if (v_isShared_1607_ == 0)
{
lean_ctor_set_tag(v___x_1606_, 0);
lean_ctor_set(v___x_1606_, 0, v_a_1619_);
v___x_1621_ = v___x_1606_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
v_val_1611_ = v___x_1621_;
goto v___jp_1610_;
}
}
v___jp_1610_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1612_, 0, v_val_1611_);
v___x_1613_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1608_, v___x_1609_, v___x_1612_, v___f_1591_);
return v___x_1613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__34___boxed(lean_object* v___f_1625_, lean_object* v_a_1626_, lean_object* v_backlog_1627_, lean_object* v_x_1628_, lean_object* v___y_1629_){
_start:
{
uint32_t v_backlog_boxed_1630_; lean_object* v_res_1631_; 
v_backlog_boxed_1630_ = lean_unbox_uint32(v_backlog_1627_);
lean_dec(v_backlog_1627_);
v_res_1631_ = l_Std_Http_Server_serve___redArg___lam__34(v___f_1625_, v_a_1626_, v_backlog_boxed_1630_, v_x_1628_);
lean_dec(v_a_1626_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__35(lean_object* v___f_1632_, lean_object* v___f_1633_, lean_object* v___x_1634_, lean_object* v_inst_1635_, lean_object* v_handler_1636_, lean_object* v_config_1637_, lean_object* v___f_1638_, lean_object* v___f_1639_, lean_object* v___x_1640_, lean_object* v___f_1641_, lean_object* v___f_1642_, lean_object* v___f_1643_, lean_object* v___f_1644_, lean_object* v___f_1645_, uint32_t v_backlog_1646_, lean_object* v_addr_1647_, lean_object* v_x_1648_){
_start:
{
if (lean_obj_tag(v_x_1648_) == 0)
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1658_; 
lean_dec_ref(v___f_1645_);
lean_dec_ref(v___f_1644_);
lean_dec_ref(v___f_1643_);
lean_dec_ref(v___f_1642_);
lean_dec_ref(v___f_1641_);
lean_dec(v___x_1640_);
lean_dec_ref(v___f_1639_);
lean_dec_ref(v___f_1638_);
lean_dec_ref(v_config_1637_);
lean_dec(v_handler_1636_);
lean_dec_ref(v_inst_1635_);
lean_dec_ref(v___x_1634_);
lean_dec_ref(v___f_1633_);
lean_dec_ref(v___f_1632_);
v_a_1650_ = lean_ctor_get(v_x_1648_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_x_1648_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1652_ = v_x_1648_;
v_isShared_1653_ = v_isSharedCheck_1658_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v_x_1648_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1658_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_object* v___x_1656_; 
v___x_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
return v___x_1656_;
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1684_; 
v_a_1659_ = lean_ctor_get(v_x_1648_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_x_1648_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1661_ = v_x_1648_;
v_isShared_1662_ = v_isSharedCheck_1684_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v_x_1648_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1684_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___f_1663_; lean_object* v___f_1664_; lean_object* v___f_1665_; lean_object* v___f_1666_; lean_object* v___x_1667_; lean_object* v___f_1668_; lean_object* v___x_1669_; uint8_t v___x_1670_; lean_object* v_val_1672_; lean_object* v___x_1675_; 
lean_inc_n(v_a_1659_, 4);
lean_inc_ref(v_config_1637_);
v___f_1663_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__30___boxed), 17, 15);
lean_closure_set(v___f_1663_, 0, v___f_1632_);
lean_closure_set(v___f_1663_, 1, v___f_1633_);
lean_closure_set(v___f_1663_, 2, v___x_1634_);
lean_closure_set(v___f_1663_, 3, v_inst_1635_);
lean_closure_set(v___f_1663_, 4, v_handler_1636_);
lean_closure_set(v___f_1663_, 5, v_config_1637_);
lean_closure_set(v___f_1663_, 6, v___f_1638_);
lean_closure_set(v___f_1663_, 7, v___f_1639_);
lean_closure_set(v___f_1663_, 8, v___x_1640_);
lean_closure_set(v___f_1663_, 9, v_a_1659_);
lean_closure_set(v___f_1663_, 10, v___f_1641_);
lean_closure_set(v___f_1663_, 11, v___f_1642_);
lean_closure_set(v___f_1663_, 12, v___f_1643_);
lean_closure_set(v___f_1663_, 13, v___f_1644_);
lean_closure_set(v___f_1663_, 14, v___f_1645_);
v___f_1664_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__31___boxed), 4, 2);
lean_closure_set(v___f_1664_, 0, v___f_1663_);
lean_closure_set(v___f_1664_, 1, v_config_1637_);
v___f_1665_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__32___boxed), 4, 2);
lean_closure_set(v___f_1665_, 0, v___f_1664_);
lean_closure_set(v___f_1665_, 1, v_a_1659_);
v___f_1666_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__33___boxed), 4, 2);
lean_closure_set(v___f_1666_, 0, v___f_1665_);
lean_closure_set(v___f_1666_, 1, v_a_1659_);
v___x_1667_ = lean_box_uint32(v_backlog_1646_);
v___f_1668_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__34___boxed), 5, 3);
lean_closure_set(v___f_1668_, 0, v___f_1666_);
lean_closure_set(v___f_1668_, 1, v_a_1659_);
lean_closure_set(v___f_1668_, 2, v___x_1667_);
v___x_1669_ = lean_unsigned_to_nat(0u);
v___x_1670_ = 0;
v___x_1675_ = lean_uv_tcp_bind(v_a_1659_, v_addr_1647_);
lean_dec(v_a_1659_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v___x_1678_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1676_);
lean_dec_ref_known(v___x_1675_, 1);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 0, v_a_1676_);
v___x_1678_ = v___x_1661_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1676_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
v_val_1672_ = v___x_1678_;
goto v___jp_1671_;
}
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; 
v_a_1680_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1680_);
lean_dec_ref_known(v___x_1675_, 1);
if (v_isShared_1662_ == 0)
{
lean_ctor_set_tag(v___x_1661_, 0);
lean_ctor_set(v___x_1661_, 0, v_a_1680_);
v___x_1682_ = v___x_1661_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1680_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
v_val_1672_ = v___x_1682_;
goto v___jp_1671_;
}
}
v___jp_1671_:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1673_, 0, v_val_1672_);
v___x_1674_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1669_, v___x_1670_, v___x_1673_, v___f_1668_);
return v___x_1674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__35___boxed(lean_object** _args){
lean_object* v___f_1685_ = _args[0];
lean_object* v___f_1686_ = _args[1];
lean_object* v___x_1687_ = _args[2];
lean_object* v_inst_1688_ = _args[3];
lean_object* v_handler_1689_ = _args[4];
lean_object* v_config_1690_ = _args[5];
lean_object* v___f_1691_ = _args[6];
lean_object* v___f_1692_ = _args[7];
lean_object* v___x_1693_ = _args[8];
lean_object* v___f_1694_ = _args[9];
lean_object* v___f_1695_ = _args[10];
lean_object* v___f_1696_ = _args[11];
lean_object* v___f_1697_ = _args[12];
lean_object* v___f_1698_ = _args[13];
lean_object* v_backlog_1699_ = _args[14];
lean_object* v_addr_1700_ = _args[15];
lean_object* v_x_1701_ = _args[16];
lean_object* v___y_1702_ = _args[17];
_start:
{
uint32_t v_backlog_boxed_1703_; lean_object* v_res_1704_; 
v_backlog_boxed_1703_ = lean_unbox_uint32(v_backlog_1699_);
lean_dec(v_backlog_1699_);
v_res_1704_ = l_Std_Http_Server_serve___redArg___lam__35(v___f_1685_, v___f_1686_, v___x_1687_, v_inst_1688_, v_handler_1689_, v_config_1690_, v___f_1691_, v___f_1692_, v___x_1693_, v___f_1694_, v___f_1695_, v___f_1696_, v___f_1697_, v___f_1698_, v_backlog_boxed_1703_, v_addr_1700_, v_x_1701_);
lean_dec_ref(v_addr_1700_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg(lean_object* v_inst_1710_, lean_object* v_addr_1711_, lean_object* v_handler_1712_, lean_object* v_config_1713_, uint32_t v_backlog_1714_){
_start:
{
lean_object* v___f_1716_; lean_object* v___f_1717_; lean_object* v___f_1718_; lean_object* v___f_1719_; lean_object* v___f_1720_; lean_object* v___f_1721_; lean_object* v___f_1722_; lean_object* v___f_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___f_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; lean_object* v_val_1731_; lean_object* v___x_1734_; 
v___f_1716_ = ((lean_object*)(l_Std_Http_Server_waitShutdown___closed__0));
v___f_1717_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__0));
v___f_1718_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__1));
v___f_1719_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__2));
v___f_1720_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2));
v___f_1721_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0));
v___f_1722_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__3));
v___f_1723_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__4));
v___x_1724_ = l_Std_Http_instTransportClient;
v___x_1725_ = l_Std_Http_Server_instImpl_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8_;
v___x_1726_ = lean_box_uint32(v_backlog_1714_);
v___f_1727_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__35___boxed), 18, 16);
lean_closure_set(v___f_1727_, 0, v___f_1720_);
lean_closure_set(v___f_1727_, 1, v___f_1719_);
lean_closure_set(v___f_1727_, 2, v___x_1724_);
lean_closure_set(v___f_1727_, 3, v_inst_1710_);
lean_closure_set(v___f_1727_, 4, v_handler_1712_);
lean_closure_set(v___f_1727_, 5, v_config_1713_);
lean_closure_set(v___f_1727_, 6, v___f_1721_);
lean_closure_set(v___f_1727_, 7, v___f_1719_);
lean_closure_set(v___f_1727_, 8, v___x_1725_);
lean_closure_set(v___f_1727_, 9, v___f_1717_);
lean_closure_set(v___f_1727_, 10, v___f_1718_);
lean_closure_set(v___f_1727_, 11, v___f_1722_);
lean_closure_set(v___f_1727_, 12, v___f_1716_);
lean_closure_set(v___f_1727_, 13, v___f_1723_);
lean_closure_set(v___f_1727_, 14, v___x_1726_);
lean_closure_set(v___f_1727_, 15, v_addr_1711_);
v___x_1728_ = lean_unsigned_to_nat(0u);
v___x_1729_ = 0;
v___x_1734_ = lean_uv_tcp_new();
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1734_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1734_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
lean_ctor_set_tag(v___x_1737_, 1);
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1735_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
v_val_1731_ = v___x_1740_;
goto v___jp_1730_;
}
}
}
else
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
v_a_1743_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1745_ = v___x_1734_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1734_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
lean_ctor_set_tag(v___x_1745_, 0);
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
v_val_1731_ = v___x_1748_;
goto v___jp_1730_;
}
}
}
v___jp_1730_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1732_, 0, v_val_1731_);
v___x_1733_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1728_, v___x_1729_, v___x_1732_, v___f_1727_);
return v___x_1733_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___boxed(lean_object* v_inst_1751_, lean_object* v_addr_1752_, lean_object* v_handler_1753_, lean_object* v_config_1754_, lean_object* v_backlog_1755_, lean_object* v_a_1756_){
_start:
{
uint32_t v_backlog_boxed_1757_; lean_object* v_res_1758_; 
v_backlog_boxed_1757_ = lean_unbox_uint32(v_backlog_1755_);
lean_dec(v_backlog_1755_);
v_res_1758_ = l_Std_Http_Server_serve___redArg(v_inst_1751_, v_addr_1752_, v_handler_1753_, v_config_1754_, v_backlog_boxed_1757_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve(lean_object* v_00_u03c3_1759_, lean_object* v_inst_1760_, lean_object* v_addr_1761_, lean_object* v_handler_1762_, lean_object* v_config_1763_, uint32_t v_backlog_1764_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Std_Http_Server_serve___redArg(v_inst_1760_, v_addr_1761_, v_handler_1762_, v_config_1763_, v_backlog_1764_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___boxed(lean_object* v_00_u03c3_1767_, lean_object* v_inst_1768_, lean_object* v_addr_1769_, lean_object* v_handler_1770_, lean_object* v_config_1771_, lean_object* v_backlog_1772_, lean_object* v_a_1773_){
_start:
{
uint32_t v_backlog_boxed_1774_; lean_object* v_res_1775_; 
v_backlog_boxed_1774_ = lean_unbox_uint32(v_backlog_1772_);
lean_dec(v_backlog_1772_);
v_res_1775_ = l_Std_Http_Server_serve(v_00_u03c3_1767_, v_inst_1768_, v_addr_1769_, v_handler_1770_, v_config_1771_, v_backlog_boxed_1774_);
return v_res_1775_;
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
