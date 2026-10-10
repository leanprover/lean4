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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Channel_send___redArg(lean_object*, lean_object*);
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
lean_object* l_Std_Http_Server_new(lean_object* v_config_1_, lean_object* v_localAddr_2_){
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
LEAN_EXPORT void l_Std_Http_Server_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_1_ = stack[0].m_obj;
lean_object* v_localAddr_2_ = stack[1].m_obj;
lean_object* v_res_18_;
v_res_18_ = l_Std_Http_Server_new(v_config_1_, v_localAddr_2_);
stack->m_obj
 = v_res_18_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_new___boxed(lean_object* v_config_19_, lean_object* v_localAddr_20_, lean_object* v_a_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Std_Http_Server_new(v_config_19_, v_localAddr_20_);
return v_res_22_;
}
}
lean_object* l_Std_Http_Server_shutdown(lean_object* v_s_23_){
_start:
{
lean_object* v_context_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v_context_25_ = lean_ctor_get(v_s_23_, 0);
lean_inc_ref(v_context_25_);
lean_dec_ref(v_s_23_);
v___x_26_ = lean_box(1);
v___x_27_ = l_Std_CancellationContext_cancel(v_context_25_, v___x_26_);
v___x_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
v___x_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT void l_Std_Http_Server_shutdown_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_23_ = stack[0].m_obj;
lean_object* v_res_30_;
v_res_30_ = l_Std_Http_Server_shutdown(v_s_23_);
stack->m_obj
 = v_res_30_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdown___boxed(lean_object* v_s_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Std_Http_Server_shutdown(v_s_31_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___lam__0(lean_object* v_a_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_35_, 0, v_a_34_);
return v___x_35_;
}
}
lean_object* l_Std_Http_Server_waitShutdown___lam__1(lean_object* v___f_36_, lean_object* v_x_37_){
_start:
{
if (lean_obj_tag(v_x_37_) == 0)
{
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_47_; 
lean_dec_ref(v___f_36_);
v_a_39_ = lean_ctor_get(v_x_37_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v_x_37_);
if (v_isSharedCheck_47_ == 0)
{
v___x_41_ = v_x_37_;
v_isShared_42_ = v_isSharedCheck_47_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v_x_37_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_47_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_44_; 
if (v_isShared_42_ == 0)
{
v___x_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_a_39_);
v___x_44_ = v_reuseFailAlloc_46_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
lean_object* v___x_45_; 
v___x_45_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
return v___x_45_;
}
}
}
else
{
lean_object* v_a_48_; lean_object* v___x_49_; uint8_t v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v_a_48_ = lean_ctor_get(v_x_37_, 0);
lean_inc(v_a_48_);
lean_dec_ref_known(v_x_37_, 1);
v___x_49_ = lean_unsigned_to_nat(0u);
v___x_50_ = 0;
v___x_51_ = lean_task_map(v___f_36_, v_a_48_, v___x_49_, v___x_50_);
v___x_52_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
return v___x_52_;
}
}
}
LEAN_EXPORT void l_Std_Http_Server_waitShutdown___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_36_ = stack[0].m_obj;
lean_object* v_x_37_ = stack[1].m_obj;
lean_object* v_res_53_;
v_res_53_ = l_Std_Http_Server_waitShutdown___lam__1(v___f_36_, v_x_37_);
stack->m_obj
 = v_res_53_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___lam__1___boxed(lean_object* v___f_54_, lean_object* v_x_55_, lean_object* v___y_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Std_Http_Server_waitShutdown___lam__1(v___f_54_, v_x_55_);
return v_res_57_;
}
}
lean_object* l_Std_Http_Server_waitShutdown(lean_object* v_s_61_){
_start:
{
lean_object* v_shutdownPromise_63_; lean_object* v___f_64_; lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v_shutdownPromise_63_ = lean_ctor_get(v_s_61_, 3);
lean_inc_ref(v_shutdownPromise_63_);
lean_dec_ref(v_s_61_);
v___f_64_ = ((lean_object*)(l_Std_Http_Server_waitShutdown___closed__1));
v___x_65_ = lean_box(0);
v___x_66_ = lean_unsigned_to_nat(0u);
v___x_67_ = 0;
v___x_68_ = l_Std_Channel_recv___redArg(v___x_65_, v_shutdownPromise_63_);
v___x_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
v___x_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
v___x_71_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_66_, v___x_67_, v___x_70_, v___f_64_);
return v___x_71_;
}
}
LEAN_EXPORT void l_Std_Http_Server_waitShutdown_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_61_ = stack[0].m_obj;
lean_object* v_res_72_;
v_res_72_ = l_Std_Http_Server_waitShutdown(v_s_61_);
stack->m_obj
 = v_res_72_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___boxed(lean_object* v_s_73_, lean_object* v_a_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Std_Http_Server_waitShutdown(v_s_73_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdownSelector(lean_object* v_s_76_){
_start:
{
lean_object* v_shutdownPromise_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v_shutdownPromise_77_ = lean_ctor_get(v_s_76_, 3);
lean_inc_ref(v_shutdownPromise_77_);
lean_dec_ref(v_s_76_);
v___x_78_ = lean_box(0);
v___x_79_ = l_Std_Channel_recvSelector___redArg(v___x_78_, v_shutdownPromise_77_);
return v___x_79_;
}
}
lean_object* l_Std_Http_Server_shutdownAndWait___lam__2(lean_object* v_shutdownPromise_80_, lean_object* v___f_81_, lean_object* v_x_82_){
_start:
{
if (lean_obj_tag(v_x_82_) == 0)
{
lean_object* v___x_84_; 
lean_dec_ref(v___f_81_);
lean_dec_ref(v_shutdownPromise_80_);
v___x_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_84_, 0, v_x_82_);
return v___x_84_;
}
else
{
lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_97_; 
v_isSharedCheck_97_ = !lean_is_exclusive(v_x_82_);
if (v_isSharedCheck_97_ == 0)
{
lean_object* v_unused_98_; 
v_unused_98_ = lean_ctor_get(v_x_82_, 0);
lean_dec(v_unused_98_);
v___x_86_ = v_x_82_;
v_isShared_87_ = v_isSharedCheck_97_;
goto v_resetjp_85_;
}
else
{
lean_dec(v_x_82_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_97_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_88_ = lean_box(0);
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = 0;
v___x_91_ = l_Std_Channel_recv___redArg(v___x_88_, v_shutdownPromise_80_);
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 0, v___x_91_);
v___x_93_ = v___x_86_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_91_);
v___x_93_ = v_reuseFailAlloc_96_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
v___x_95_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_89_, v___x_90_, v___x_94_, v___f_81_);
return v___x_95_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Server_shutdownAndWait___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_shutdownPromise_80_ = stack[0].m_obj;
lean_object* v___f_81_ = stack[1].m_obj;
lean_object* v_x_82_ = stack[2].m_obj;
lean_object* v_res_99_;
v_res_99_ = l_Std_Http_Server_shutdownAndWait___lam__2(v_shutdownPromise_80_, v___f_81_, v_x_82_);
stack->m_obj
 = v_res_99_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait___lam__2___boxed(lean_object* v_shutdownPromise_100_, lean_object* v___f_101_, lean_object* v_x_102_, lean_object* v___y_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Std_Http_Server_shutdownAndWait___lam__2(v_shutdownPromise_100_, v___f_101_, v_x_102_);
return v_res_104_;
}
}
lean_object* l_Std_Http_Server_shutdownAndWait(lean_object* v_s_105_){
_start:
{
lean_object* v_context_107_; lean_object* v_shutdownPromise_108_; lean_object* v___f_109_; lean_object* v___f_110_; lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_context_107_ = lean_ctor_get(v_s_105_, 0);
lean_inc_ref(v_context_107_);
v_shutdownPromise_108_ = lean_ctor_get(v_s_105_, 3);
lean_inc_ref(v_shutdownPromise_108_);
lean_dec_ref(v_s_105_);
v___f_109_ = ((lean_object*)(l_Std_Http_Server_waitShutdown___closed__1));
v___f_110_ = lean_alloc_closure((void*)(l_Std_Http_Server_shutdownAndWait___lam__2___boxed), 4, 2);
lean_closure_set(v___f_110_, 0, v_shutdownPromise_108_);
lean_closure_set(v___f_110_, 1, v___f_109_);
v___x_111_ = lean_box(1);
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = 0;
v___x_114_ = l_Std_CancellationContext_cancel(v_context_107_, v___x_111_);
v___x_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
v___x_117_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_112_, v___x_113_, v___x_116_, v___f_110_);
return v___x_117_;
}
}
LEAN_EXPORT void l_Std_Http_Server_shutdownAndWait_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_105_ = stack[0].m_obj;
lean_object* v_res_118_;
v_res_118_ = l_Std_Http_Server_shutdownAndWait(v_s_105_);
stack->m_obj
 = v_res_118_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait___boxed(lean_object* v_s_119_, lean_object* v_a_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Std_Http_Server_shutdownAndWait(v_s_119_);
return v_res_121_;
}
}
lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0(lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_129_ = lean_st_ref_take(v___y_126_);
v___x_130_ = lean_unsigned_to_nat(1u);
v___x_131_ = lean_nat_add(v___x_129_, v___x_130_);
lean_dec(v___x_129_);
v___x_132_ = lean_st_ref_put(v___y_126_, v___x_131_);
v___x_133_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_133_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_126_ = stack[0].m_obj;
lean_object* v___y_127_ = stack[1].m_obj;
lean_object* v_res_134_;
v_res_134_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0(v___y_126_, v___y_127_);
stack->m_obj
 = v_res_134_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___boxed(lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0(v___y_135_, v___y_136_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1(lean_object* v_x_139_){
_start:
{
lean_object* v_fst_140_; 
v_fst_140_ = lean_ctor_get(v_x_139_, 0);
lean_inc(v_fst_140_);
return v_fst_140_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1___boxed(lean_object* v_x_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1(v_x_141_);
lean_dec_ref(v_x_141_);
return v_res_142_;
}
}
lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2(lean_object* v_a_143_, lean_object* v_shutdownPromise_144_, lean_object* v_x_145_){
_start:
{
if (lean_obj_tag(v_x_145_) == 0)
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_157_; 
lean_dec_ref(v_shutdownPromise_144_);
v_a_149_ = lean_ctor_get(v_x_145_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v_x_145_);
if (v_isSharedCheck_157_ == 0)
{
v___x_151_ = v_x_145_;
v_isShared_152_ = v_isSharedCheck_157_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v_x_145_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_157_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_a_149_);
v___x_154_ = v_reuseFailAlloc_156_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_object* v___x_155_; 
v___x_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
return v___x_155_;
}
}
}
else
{
lean_object* v_a_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v_a_158_ = lean_ctor_get(v_x_145_, 0);
lean_inc(v_a_158_);
lean_dec_ref_known(v_x_145_, 1);
v___x_159_ = lean_unsigned_to_nat(0u);
v___x_160_ = lean_nat_dec_eq(v_a_143_, v___x_159_);
if (v___x_160_ == 0)
{
lean_dec(v_a_158_);
lean_dec_ref(v_shutdownPromise_144_);
goto v___jp_147_;
}
else
{
uint8_t v___x_161_; 
v___x_161_ = lean_unbox(v_a_158_);
lean_dec(v_a_158_);
if (v___x_161_ == 0)
{
lean_dec_ref(v_shutdownPromise_144_);
goto v___jp_147_;
}
else
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = lean_box(0);
v___x_163_ = l_Std_Channel_send___redArg(v_shutdownPromise_144_, v___x_162_);
lean_dec_ref(v___x_163_);
v___x_164_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_164_;
}
}
}
v___jp_147_:
{
lean_object* v___x_148_; 
v___x_148_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_148_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_143_ = stack[0].m_obj;
lean_object* v_shutdownPromise_144_ = stack[1].m_obj;
lean_object* v_x_145_ = stack[2].m_obj;
lean_object* v_res_165_;
v_res_165_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2(v_a_143_, v_shutdownPromise_144_, v_x_145_);
stack->m_obj
 = v_res_165_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2___boxed(lean_object* v_a_166_, lean_object* v_shutdownPromise_167_, lean_object* v_x_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2(v_a_166_, v_shutdownPromise_167_, v_x_168_);
lean_dec(v_a_166_);
return v_res_170_;
}
}
lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3(lean_object* v_context_171_, lean_object* v_shutdownPromise_172_, lean_object* v_x_173_){
_start:
{
if (lean_obj_tag(v_x_173_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_183_; 
lean_dec_ref(v_shutdownPromise_172_);
lean_dec_ref(v_context_171_);
v_a_175_ = lean_ctor_get(v_x_173_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v_x_173_);
if (v_isSharedCheck_183_ == 0)
{
v___x_177_ = v_x_173_;
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v_x_173_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
if (v_isShared_178_ == 0)
{
v___x_180_ = v___x_177_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_a_175_);
v___x_180_ = v_reuseFailAlloc_182_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_181_; 
v___x_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
return v___x_181_;
}
}
}
else
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_199_; 
v_a_184_ = lean_ctor_get(v_x_173_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v_x_173_);
if (v_isSharedCheck_199_ == 0)
{
v___x_186_ = v_x_173_;
v_isShared_187_ = v_isSharedCheck_199_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v_x_173_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_199_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v_token_188_; lean_object* v___f_189_; lean_object* v___x_190_; uint8_t v___x_191_; uint8_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_195_; 
v_token_188_ = lean_ctor_get(v_context_171_, 1);
lean_inc_ref(v_token_188_);
lean_dec_ref(v_context_171_);
v___f_189_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_189_, 0, v_a_184_);
lean_closure_set(v___f_189_, 1, v_shutdownPromise_172_);
v___x_190_ = lean_unsigned_to_nat(0u);
v___x_191_ = 0;
v___x_192_ = l_Std_CancellationToken_isCancelled(v_token_188_);
v___x_193_ = lean_box(v___x_192_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_193_);
v___x_195_ = v___x_186_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_193_);
v___x_195_ = v_reuseFailAlloc_198_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
v___x_197_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_190_, v___x_191_, v___x_196_, v___f_189_);
return v___x_197_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_context_171_ = stack[0].m_obj;
lean_object* v_shutdownPromise_172_ = stack[1].m_obj;
lean_object* v_x_173_ = stack[2].m_obj;
lean_object* v_res_200_;
v_res_200_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3(v_context_171_, v_shutdownPromise_172_, v_x_173_);
stack->m_obj
 = v_res_200_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed(lean_object* v_context_201_, lean_object* v_shutdownPromise_202_, lean_object* v_x_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3(v_context_201_, v_shutdownPromise_202_, v_x_203_);
return v_res_205_;
}
}
lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4(lean_object* v___f_206_, lean_object* v_____r_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v___x_211_; uint8_t v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = 0;
v___x_213_ = lean_st_ref_get(v___y_208_);
v___x_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
v___x_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
v___x_216_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_211_, v___x_212_, v___x_215_, v___f_206_);
return v___x_216_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_206_ = stack[0].m_obj;
lean_object* v_____r_207_ = stack[1].m_obj;
lean_object* v___y_208_ = stack[2].m_obj;
lean_object* v___y_209_ = stack[3].m_obj;
lean_object* v_res_217_;
v_res_217_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4(v___f_206_, v_____r_207_, v___y_208_, v___y_209_);
stack->m_obj
 = v_res_217_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed(lean_object* v___f_218_, lean_object* v_____r_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4(v___f_218_, v_____r_219_, v___y_220_, v___y_221_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
return v_res_223_;
}
}
lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5(lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_227_ = lean_st_ref_take(v___y_224_);
v___x_228_ = lean_unsigned_to_nat(1u);
v___x_229_ = lean_nat_sub(v___x_227_, v___x_228_);
lean_dec(v___x_227_);
v___x_230_ = lean_st_ref_put(v___y_224_, v___x_229_);
v___x_231_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_231_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_224_ = stack[0].m_obj;
lean_object* v___y_225_ = stack[1].m_obj;
lean_object* v_res_232_;
v_res_232_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5(v___y_224_, v___y_225_);
stack->m_obj
 = v_res_232_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5___boxed(lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5(v___y_233_, v___y_234_);
lean_dec_ref(v___y_234_);
lean_dec(v___y_233_);
return v_res_236_;
}
}
lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6(lean_object* v___x_237_, lean_object* v___f_238_, lean_object* v___f_239_, lean_object* v___f_240_, lean_object* v___f_241_, lean_object* v_activeConnections_242_, lean_object* v_____r_243_, lean_object* v___y_244_){
_start:
{
lean_object* v___x_246_; lean_object* v___x_2168__overap_247_; lean_object* v___x_248_; 
lean_inc_ref(v___x_237_);
v___x_246_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_246_, 0, lean_box(0));
lean_closure_set(v___x_246_, 1, lean_box(0));
lean_closure_set(v___x_246_, 2, v___x_237_);
lean_closure_set(v___x_246_, 3, lean_box(0));
lean_closure_set(v___x_246_, 4, lean_box(0));
lean_closure_set(v___x_246_, 5, v___f_238_);
lean_closure_set(v___x_246_, 6, v___f_239_);
v___x_2168__overap_247_ = l_Std_Mutex_atomically___redArg(v___x_237_, v___f_240_, v___f_241_, v_activeConnections_242_, v___x_246_);
lean_inc_ref(v___y_244_);
v___x_248_ = lean_apply_2(v___x_2168__overap_247_, v___y_244_, lean_box(0));
return v___x_248_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_237_ = stack[0].m_obj;
lean_object* v___f_238_ = stack[1].m_obj;
lean_object* v___f_239_ = stack[2].m_obj;
lean_object* v___f_240_ = stack[3].m_obj;
lean_object* v___f_241_ = stack[4].m_obj;
lean_object* v_activeConnections_242_ = stack[5].m_obj;
lean_object* v_____r_243_ = stack[6].m_obj;
lean_object* v___y_244_ = stack[7].m_obj;
lean_object* v_res_249_;
v_res_249_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6(v___x_237_, v___f_238_, v___f_239_, v___f_240_, v___f_241_, v_activeConnections_242_, v_____r_243_, v___y_244_);
stack->m_obj
 = v_res_249_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed(lean_object* v___x_250_, lean_object* v___f_251_, lean_object* v___f_252_, lean_object* v___f_253_, lean_object* v___f_254_, lean_object* v_activeConnections_255_, lean_object* v_____r_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6(v___x_250_, v___f_251_, v___f_252_, v___f_253_, v___f_254_, v_activeConnections_255_, v_____r_256_, v___y_257_);
lean_dec_ref(v___y_257_);
return v_res_259_;
}
}
lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7(lean_object* v___f_260_, lean_object* v_a_261_, lean_object* v_x_262_){
_start:
{
if (lean_obj_tag(v_x_262_) == 0)
{
lean_object* v___x_264_; 
lean_dec_ref(v___f_260_);
v___x_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_264_, 0, v_x_262_);
return v___x_264_;
}
else
{
lean_object* v_a_265_; lean_object* v___x_266_; 
v_a_265_ = lean_ctor_get(v_x_262_, 0);
lean_inc(v_a_265_);
lean_dec_ref_known(v_x_262_, 1);
lean_inc_ref(v_a_261_);
v___x_266_ = lean_apply_3(v___f_260_, v_a_265_, v_a_261_, lean_box(0));
return v___x_266_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_260_ = stack[0].m_obj;
lean_object* v_a_261_ = stack[1].m_obj;
lean_object* v_x_262_ = stack[2].m_obj;
lean_object* v_res_267_;
v_res_267_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7(v___f_260_, v_a_261_, v_x_262_);
stack->m_obj
 = v_res_267_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed(lean_object* v___f_268_, lean_object* v_a_269_, lean_object* v_x_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7(v___f_268_, v_a_269_, v_x_270_);
lean_dec_ref(v_a_269_);
return v_res_272_;
}
}
lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8(uint8_t v_releaseConnectionPermit_273_, lean_object* v___f_274_, lean_object* v_a_275_, lean_object* v_connectionLimit_276_, lean_object* v___f_277_, lean_object* v_opt_278_){
_start:
{
if (v_releaseConnectionPermit_273_ == 0)
{
lean_object* v___x_280_; lean_object* v___x_281_; 
lean_dec_ref(v___f_277_);
lean_dec(v_connectionLimit_276_);
v___x_280_ = lean_box(0);
lean_inc_ref(v_a_275_);
v___x_281_ = lean_apply_3(v___f_274_, v___x_280_, v_a_275_, lean_box(0));
return v___x_281_;
}
else
{
if (lean_obj_tag(v_connectionLimit_276_) == 1)
{
lean_object* v_val_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_294_; 
lean_dec_ref(v___f_274_);
v_val_282_ = lean_ctor_get(v_connectionLimit_276_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v_connectionLimit_276_);
if (v_isSharedCheck_294_ == 0)
{
v___x_284_ = v_connectionLimit_276_;
v_isShared_285_ = v_isSharedCheck_294_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_val_282_);
lean_dec(v_connectionLimit_276_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_294_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_286_; uint8_t v___x_287_; lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_286_ = lean_unsigned_to_nat(0u);
v___x_287_ = 0;
v___x_288_ = l_Std_Semaphore_release(v_val_282_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v___x_288_);
v___x_290_ = v___x_284_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_288_);
v___x_290_ = v_reuseFailAlloc_293_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
v___x_292_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_286_, v___x_287_, v___x_291_, v___f_277_);
return v___x_292_;
}
}
}
else
{
lean_object* v___x_295_; lean_object* v___x_296_; 
lean_dec_ref(v___f_277_);
lean_dec(v_connectionLimit_276_);
v___x_295_ = lean_box(0);
lean_inc_ref(v_a_275_);
v___x_296_ = lean_apply_3(v___f_274_, v___x_295_, v_a_275_, lean_box(0));
return v___x_296_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
uint8_t v_releaseConnectionPermit_273_ = stack[0].m_num;
lean_object* v___f_274_ = stack[1].m_obj;
lean_object* v_a_275_ = stack[2].m_obj;
lean_object* v_connectionLimit_276_ = stack[3].m_obj;
lean_object* v___f_277_ = stack[4].m_obj;
lean_object* v_opt_278_ = stack[5].m_obj;
lean_object* v_res_297_;
v_res_297_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8(v_releaseConnectionPermit_273_, v___f_274_, v_a_275_, v_connectionLimit_276_, v___f_277_, v_opt_278_);
stack->m_obj
 = v_res_297_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed(lean_object* v_releaseConnectionPermit_298_, lean_object* v___f_299_, lean_object* v_a_300_, lean_object* v_connectionLimit_301_, lean_object* v___f_302_, lean_object* v_opt_303_, lean_object* v___y_304_){
_start:
{
uint8_t v_releaseConnectionPermit_boxed_305_; lean_object* v_res_306_; 
v_releaseConnectionPermit_boxed_305_ = lean_unbox(v_releaseConnectionPermit_298_);
v_res_306_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8(v_releaseConnectionPermit_boxed_305_, v___f_299_, v_a_300_, v_connectionLimit_301_, v___f_302_, v_opt_303_);
lean_dec(v_opt_303_);
lean_dec_ref(v_a_300_);
return v_res_306_;
}
}
lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9(lean_object* v___f_307_, lean_object* v_action_308_, lean_object* v_a_309_, lean_object* v___f_310_, lean_object* v_x_311_){
_start:
{
if (lean_obj_tag(v_x_311_) == 0)
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_321_; 
lean_dec_ref(v___f_310_);
lean_dec_ref(v_action_308_);
lean_dec(v___f_307_);
v_a_313_ = lean_ctor_get(v_x_311_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v_x_311_);
if (v_isSharedCheck_321_ == 0)
{
v___x_315_ = v_x_311_;
v_isShared_316_ = v_isSharedCheck_321_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v_x_311_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_321_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_313_);
v___x_318_ = v_reuseFailAlloc_320_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v___x_319_; 
v___x_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
return v___x_319_;
}
}
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___y_328_; 
lean_dec_ref_known(v_x_311_, 1);
v___x_322_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_322_, 0, lean_box(0));
lean_closure_set(v___x_322_, 1, lean_box(0));
lean_closure_set(v___x_322_, 2, lean_box(0));
lean_closure_set(v___x_322_, 3, v___f_307_);
v___x_323_ = lean_unsigned_to_nat(0u);
v___x_324_ = 0;
lean_inc_ref(v_a_309_);
v___x_325_ = lean_apply_1(v_action_308_, v_a_309_);
v___x_326_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_325_, v___f_310_, v___x_323_, v___x_324_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_330_; 
lean_dec_ref(v___x_322_);
v_a_330_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_a_330_);
lean_dec_ref_known(v___x_326_, 1);
if (lean_obj_tag(v_a_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
v_a_331_ = lean_ctor_get(v_a_330_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v_a_330_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v_a_330_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v_a_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_331_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
v___y_328_ = v___x_336_;
goto v___jp_327_;
}
}
}
else
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_347_; 
v_a_339_ = lean_ctor_get(v_a_330_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v_a_330_);
if (v_isSharedCheck_347_ == 0)
{
v___x_341_ = v_a_330_;
v_isShared_342_ = v_isSharedCheck_347_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v_a_330_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_347_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v_fst_343_; lean_object* v___x_345_; 
v_fst_343_ = lean_ctor_get(v_a_339_, 0);
lean_inc(v_fst_343_);
lean_dec(v_a_339_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v_fst_343_);
v___x_345_ = v___x_341_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_fst_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
v___y_328_ = v___x_345_;
goto v___jp_327_;
}
}
}
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_356_; 
v_a_348_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_356_ == 0)
{
v___x_350_ = v___x_326_;
v_isShared_351_ = v_isSharedCheck_356_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_326_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_356_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_352_ = lean_task_map(v___x_322_, v_a_348_, v___x_323_, v___x_324_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v___x_352_);
v___x_354_ = v___x_350_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
v___jp_327_:
{
lean_object* v___x_329_; 
v___x_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_329_, 0, v___y_328_);
return v___x_329_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_307_ = stack[0].m_obj;
lean_object* v_action_308_ = stack[1].m_obj;
lean_object* v_a_309_ = stack[2].m_obj;
lean_object* v___f_310_ = stack[3].m_obj;
lean_object* v_x_311_ = stack[4].m_obj;
lean_object* v_res_357_;
v_res_357_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9(v___f_307_, v_action_308_, v_a_309_, v___f_310_, v_x_311_);
stack->m_obj
 = v_res_357_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed(lean_object* v___f_358_, lean_object* v_action_359_, lean_object* v_a_360_, lean_object* v___f_361_, lean_object* v_x_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9(v___f_358_, v_action_359_, v_a_360_, v___f_361_, v_x_362_);
lean_dec_ref(v_a_360_);
return v_res_364_;
}
}
lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg(lean_object* v_s_374_, uint8_t v_releaseConnectionPermit_375_, lean_object* v_action_376_, lean_object* v_a_377_){
_start:
{
lean_object* v___x_379_; lean_object* v_context_380_; lean_object* v_activeConnections_381_; lean_object* v_connectionLimit_382_; lean_object* v_shutdownPromise_383_; lean_object* v___f_384_; lean_object* v___f_385_; lean_object* v___f_386_; lean_object* v___f_387_; lean_object* v___f_388_; lean_object* v___f_389_; lean_object* v___f_390_; lean_object* v___f_391_; lean_object* v___f_392_; lean_object* v___x_393_; lean_object* v___f_394_; lean_object* v___f_395_; lean_object* v___x_396_; uint8_t v___x_397_; lean_object* v___x_1921__overap_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_379_ = l_Std_Async_ContextAsync_instMonad;
v_context_380_ = lean_ctor_get(v_s_374_, 0);
lean_inc_ref(v_context_380_);
v_activeConnections_381_ = lean_ctor_get(v_s_374_, 1);
lean_inc_ref_n(v_activeConnections_381_, 2);
v_connectionLimit_382_ = lean_ctor_get(v_s_374_, 2);
lean_inc(v_connectionLimit_382_);
v_shutdownPromise_383_ = lean_ctor_get(v_s_374_, 3);
lean_inc_ref(v_shutdownPromise_383_);
lean_dec_ref(v_s_374_);
v___f_384_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0));
v___f_385_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1));
v___f_386_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_386_, 0, v_context_380_);
lean_closure_set(v___f_386_, 1, v_shutdownPromise_383_);
v___f_387_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed), 5, 1);
lean_closure_set(v___f_387_, 0, v___f_386_);
v___f_388_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2));
v___f_389_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5));
v___f_390_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6));
v___f_391_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed), 9, 6);
lean_closure_set(v___f_391_, 0, v___x_379_);
lean_closure_set(v___f_391_, 1, v___f_388_);
lean_closure_set(v___f_391_, 2, v___f_387_);
lean_closure_set(v___f_391_, 3, v___f_389_);
lean_closure_set(v___f_391_, 4, v___f_390_);
lean_closure_set(v___f_391_, 5, v_activeConnections_381_);
lean_inc_ref_n(v_a_377_, 4);
lean_inc_ref(v___f_391_);
v___f_392_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_392_, 0, v___f_391_);
lean_closure_set(v___f_392_, 1, v_a_377_);
v___x_393_ = lean_box(v_releaseConnectionPermit_375_);
v___f_394_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed), 7, 5);
lean_closure_set(v___f_394_, 0, v___x_393_);
lean_closure_set(v___f_394_, 1, v___f_391_);
lean_closure_set(v___f_394_, 2, v_a_377_);
lean_closure_set(v___f_394_, 3, v_connectionLimit_382_);
lean_closure_set(v___f_394_, 4, v___f_392_);
v___f_395_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed), 6, 4);
lean_closure_set(v___f_395_, 0, v___f_385_);
lean_closure_set(v___f_395_, 1, v_action_376_);
lean_closure_set(v___f_395_, 2, v_a_377_);
lean_closure_set(v___f_395_, 3, v___f_394_);
v___x_396_ = lean_unsigned_to_nat(0u);
v___x_397_ = 0;
v___x_1921__overap_398_ = l_Std_Mutex_atomically___redArg(v___x_379_, v___f_389_, v___f_390_, v_activeConnections_381_, v___f_384_);
v___x_399_ = lean_apply_2(v___x_1921__overap_398_, v_a_377_, lean_box(0));
v___x_400_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_396_, v___x_397_, v___x_399_, v___f_395_);
return v___x_400_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_374_ = stack[0].m_obj;
uint8_t v_releaseConnectionPermit_375_ = stack[1].m_num;
lean_object* v_action_376_ = stack[2].m_obj;
lean_object* v_a_377_ = stack[3].m_obj;
lean_object* v_res_401_;
v_res_401_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg(v_s_374_, v_releaseConnectionPermit_375_, v_action_376_, v_a_377_);
stack->m_obj
 = v_res_401_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___boxed(lean_object* v_s_402_, lean_object* v_releaseConnectionPermit_403_, lean_object* v_action_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
uint8_t v_releaseConnectionPermit_boxed_407_; lean_object* v_res_408_; 
v_releaseConnectionPermit_boxed_407_ = lean_unbox(v_releaseConnectionPermit_403_);
v_res_408_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg(v_s_402_, v_releaseConnectionPermit_boxed_407_, v_action_404_, v_a_405_);
lean_dec_ref(v_a_405_);
return v_res_408_;
}
}
lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation(lean_object* v_00_u03b1_409_, lean_object* v_s_410_, uint8_t v_releaseConnectionPermit_411_, lean_object* v_action_412_, lean_object* v_a_413_){
_start:
{
lean_object* v___x_415_; lean_object* v_context_416_; lean_object* v_activeConnections_417_; lean_object* v_connectionLimit_418_; lean_object* v_shutdownPromise_419_; lean_object* v___f_420_; lean_object* v___f_421_; lean_object* v___f_422_; lean_object* v___f_423_; lean_object* v___f_424_; lean_object* v___f_425_; lean_object* v___f_426_; lean_object* v___f_427_; lean_object* v___f_428_; lean_object* v___x_429_; lean_object* v___f_430_; lean_object* v___f_431_; lean_object* v___x_432_; uint8_t v___x_433_; lean_object* v___x_2073__overap_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_415_ = l_Std_Async_ContextAsync_instMonad;
v_context_416_ = lean_ctor_get(v_s_410_, 0);
lean_inc_ref(v_context_416_);
v_activeConnections_417_ = lean_ctor_get(v_s_410_, 1);
lean_inc_ref_n(v_activeConnections_417_, 2);
v_connectionLimit_418_ = lean_ctor_get(v_s_410_, 2);
lean_inc(v_connectionLimit_418_);
v_shutdownPromise_419_ = lean_ctor_get(v_s_410_, 3);
lean_inc_ref(v_shutdownPromise_419_);
lean_dec_ref(v_s_410_);
v___f_420_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0));
v___f_421_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1));
v___f_422_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_422_, 0, v_context_416_);
lean_closure_set(v___f_422_, 1, v_shutdownPromise_419_);
v___f_423_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed), 5, 1);
lean_closure_set(v___f_423_, 0, v___f_422_);
v___f_424_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2));
v___f_425_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5));
v___f_426_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6));
v___f_427_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed), 9, 6);
lean_closure_set(v___f_427_, 0, v___x_415_);
lean_closure_set(v___f_427_, 1, v___f_424_);
lean_closure_set(v___f_427_, 2, v___f_423_);
lean_closure_set(v___f_427_, 3, v___f_425_);
lean_closure_set(v___f_427_, 4, v___f_426_);
lean_closure_set(v___f_427_, 5, v_activeConnections_417_);
lean_inc_ref_n(v_a_413_, 4);
lean_inc_ref(v___f_427_);
v___f_428_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_428_, 0, v___f_427_);
lean_closure_set(v___f_428_, 1, v_a_413_);
v___x_429_ = lean_box(v_releaseConnectionPermit_411_);
v___f_430_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed), 7, 5);
lean_closure_set(v___f_430_, 0, v___x_429_);
lean_closure_set(v___f_430_, 1, v___f_427_);
lean_closure_set(v___f_430_, 2, v_a_413_);
lean_closure_set(v___f_430_, 3, v_connectionLimit_418_);
lean_closure_set(v___f_430_, 4, v___f_428_);
v___f_431_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed), 6, 4);
lean_closure_set(v___f_431_, 0, v___f_421_);
lean_closure_set(v___f_431_, 1, v_action_412_);
lean_closure_set(v___f_431_, 2, v_a_413_);
lean_closure_set(v___f_431_, 3, v___f_430_);
v___x_432_ = lean_unsigned_to_nat(0u);
v___x_433_ = 0;
v___x_2073__overap_434_ = l_Std_Mutex_atomically___redArg(v___x_415_, v___f_425_, v___f_426_, v_activeConnections_417_, v___f_420_);
v___x_435_ = lean_apply_2(v___x_2073__overap_434_, v_a_413_, lean_box(0));
v___x_436_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_432_, v___x_433_, v___x_435_, v___f_431_);
return v___x_436_;
}
}
LEAN_EXPORT void l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_410_ = stack[1].m_obj;
uint8_t v_releaseConnectionPermit_411_ = stack[2].m_num;
lean_object* v_action_412_ = stack[3].m_obj;
lean_object* v_a_413_ = stack[4].m_obj;
lean_object* v_res_437_;
v_res_437_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation(lean_box(0), v_s_410_, v_releaseConnectionPermit_411_, v_action_412_, v_a_413_);
stack->m_obj
 = v_res_437_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___boxed(lean_object* v_00_u03b1_438_, lean_object* v_s_439_, lean_object* v_releaseConnectionPermit_440_, lean_object* v_action_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
uint8_t v_releaseConnectionPermit_boxed_444_; lean_object* v_res_445_; 
v_releaseConnectionPermit_boxed_444_ = lean_unbox(v_releaseConnectionPermit_440_);
v_res_445_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation(v_00_u03b1_438_, v_s_439_, v_releaseConnectionPermit_boxed_444_, v_action_441_, v_a_442_);
lean_dec_ref(v_a_442_);
return v_res_445_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__1(lean_object* v_x_446_){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_448_, 0, v_x_446_);
v___x_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
v___x_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_446_ = stack[0].m_obj;
lean_object* v_res_451_;
v_res_451_ = l_Std_Http_Server_serve___redArg___lam__1(v_x_446_);
stack->m_obj
 = v_res_451_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1___boxed(lean_object* v_x_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Std_Http_Server_serve___redArg___lam__1(v_x_452_);
return v_res_454_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__0(lean_object* v_x_459_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__0___closed__1));
return v___x_461_;
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_459_ = stack[0].m_obj;
lean_object* v_res_462_;
v_res_462_ = l_Std_Http_Server_serve___redArg___lam__0(v_x_459_);
stack->m_obj
 = v_res_462_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__0___boxed(lean_object* v_x_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Std_Http_Server_serve___redArg___lam__0(v_x_463_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2(lean_object* v_x_466_){
_start:
{
lean_object* v_fst_467_; 
v_fst_467_ = lean_ctor_get(v_x_466_, 0);
lean_inc(v_fst_467_);
return v_fst_467_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2___boxed(lean_object* v_x_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Std_Http_Server_serve___redArg___lam__2(v_x_468_);
lean_dec_ref(v_x_468_);
return v_res_469_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__6(lean_object* v_x_470_){
_start:
{
if (lean_obj_tag(v_x_470_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_480_; 
v_a_472_ = lean_ctor_get(v_x_470_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v_x_470_);
if (v_isSharedCheck_480_ == 0)
{
v___x_474_ = v_x_470_;
v_isShared_475_ = v_isSharedCheck_480_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v_x_470_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_480_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_479_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_478_; 
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
return v___x_478_;
}
}
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_491_; 
v_a_481_ = lean_ctor_get(v_x_470_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v_x_470_);
if (v_isSharedCheck_491_ == 0)
{
v___x_483_ = v_x_470_;
v_isShared_484_ = v_isSharedCheck_491_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v_x_470_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_491_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v_token_485_; lean_object* v___x_486_; lean_object* v___x_488_; 
v_token_485_ = lean_ctor_get(v_a_481_, 1);
lean_inc_ref(v_token_485_);
lean_dec(v_a_481_);
v___x_486_ = l_Std_CancellationToken_selector(v_token_485_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_486_);
v___x_488_ = v___x_483_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_486_);
v___x_488_ = v_reuseFailAlloc_490_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_489_; 
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
return v___x_489_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_470_ = stack[0].m_obj;
lean_object* v_res_492_;
v_res_492_ = l_Std_Http_Server_serve___redArg___lam__6(v_x_470_);
stack->m_obj
 = v_res_492_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6___boxed(lean_object* v_x_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Std_Http_Server_serve___redArg___lam__6(v_x_493_);
return v_res_495_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__3(lean_object* v_x_496_){
_start:
{
if (lean_obj_tag(v_x_496_) == 0)
{
lean_object* v___x_498_; 
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v_x_496_);
return v___x_498_;
}
else
{
lean_object* v___x_499_; 
lean_dec_ref_known(v_x_496_, 1);
v___x_499_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_499_;
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_496_ = stack[0].m_obj;
lean_object* v_res_500_;
v_res_500_ = l_Std_Http_Server_serve___redArg___lam__3(v_x_496_);
stack->m_obj
 = v_res_500_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3___boxed(lean_object* v_x_501_, lean_object* v___y_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Std_Http_Server_serve___redArg___lam__3(v_x_501_);
return v_res_503_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__4(lean_object* v_x_504_, lean_object* v_x_505_){
_start:
{
if (lean_obj_tag(v_x_505_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_515_; 
lean_dec_ref(v_x_504_);
v_a_507_ = lean_ctor_get(v_x_505_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v_x_505_);
if (v_isSharedCheck_515_ == 0)
{
v___x_509_ = v_x_505_;
v_isShared_510_ = v_isSharedCheck_515_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v_x_505_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_515_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_507_);
v___x_512_ = v_reuseFailAlloc_514_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_513_; 
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
return v___x_513_;
}
}
}
else
{
lean_object* v___x_516_; 
lean_dec_ref_known(v_x_505_, 1);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v_x_504_);
return v___x_516_;
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_504_ = stack[0].m_obj;
lean_object* v_x_505_ = stack[1].m_obj;
lean_object* v_res_517_;
v_res_517_ = l_Std_Http_Server_serve___redArg___lam__4(v_x_504_, v_x_505_);
stack->m_obj
 = v_res_517_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4___boxed(lean_object* v_x_518_, lean_object* v_x_519_, lean_object* v___y_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Std_Http_Server_serve___redArg___lam__4(v_x_518_, v_x_519_);
return v_res_521_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__9(lean_object* v___x_522_, lean_object* v_____r_523_, lean_object* v___y_524_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_522_);
v___x_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
return v___x_528_;
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_522_ = stack[0].m_obj;
lean_object* v_____r_523_ = stack[1].m_obj;
lean_object* v___y_524_ = stack[2].m_obj;
lean_object* v_res_529_;
v_res_529_ = l_Std_Http_Server_serve___redArg___lam__9(v___x_522_, v_____r_523_, v___y_524_);
stack->m_obj
 = v_res_529_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9___boxed(lean_object* v___x_530_, lean_object* v_____r_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_Http_Server_serve___redArg___lam__9(v___x_530_, v_____r_531_, v___y_532_);
lean_dec_ref(v___y_532_);
return v_res_534_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__5(lean_object* v___x_535_, lean_object* v_x_536_){
_start:
{
if (lean_obj_tag(v_x_536_) == 0)
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_546_; 
v_a_538_ = lean_ctor_get(v_x_536_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v_x_536_);
if (v_isSharedCheck_546_ == 0)
{
v___x_540_ = v_x_536_;
v_isShared_541_ = v_isSharedCheck_546_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v_x_536_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_546_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_545_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; 
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
}
}
else
{
lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_555_; 
v_isSharedCheck_555_ = !lean_is_exclusive(v_x_536_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; 
v_unused_556_ = lean_ctor_get(v_x_536_, 0);
lean_dec(v_unused_556_);
v___x_548_ = v_x_536_;
v_isShared_549_ = v_isSharedCheck_555_;
goto v_resetjp_547_;
}
else
{
lean_dec(v_x_536_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_555_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_535_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v___x_550_);
v___x_552_ = v___x_548_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_550_);
v___x_552_ = v_reuseFailAlloc_554_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_553_; 
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
return v___x_553_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_535_ = stack[0].m_obj;
lean_object* v_x_536_ = stack[1].m_obj;
lean_object* v_res_557_;
v_res_557_ = l_Std_Http_Server_serve___redArg___lam__5(v___x_535_, v_x_536_);
stack->m_obj
 = v_res_557_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5___boxed(lean_object* v___x_558_, lean_object* v_x_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_Http_Server_serve___redArg___lam__5(v___x_558_, v_x_559_);
return v_res_561_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__7(lean_object* v___f_562_, lean_object* v___y_563_, lean_object* v_x_564_){
_start:
{
if (lean_obj_tag(v_x_564_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_574_; 
lean_dec_ref(v___f_562_);
v_a_566_ = lean_ctor_get(v_x_564_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v_x_564_);
if (v_isSharedCheck_574_ == 0)
{
v___x_568_ = v_x_564_;
v_isShared_569_ = v_isSharedCheck_574_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v_x_564_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_574_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_566_);
v___x_571_ = v_reuseFailAlloc_573_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
lean_object* v___x_572_; 
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
}
else
{
lean_object* v_a_575_; lean_object* v___x_576_; 
v_a_575_ = lean_ctor_get(v_x_564_, 0);
lean_inc(v_a_575_);
lean_dec_ref_known(v_x_564_, 1);
lean_inc_ref(v___y_563_);
v___x_576_ = lean_apply_3(v___f_562_, v_a_575_, v___y_563_, lean_box(0));
return v___x_576_;
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_562_ = stack[0].m_obj;
lean_object* v___y_563_ = stack[1].m_obj;
lean_object* v_x_564_ = stack[2].m_obj;
lean_object* v_res_577_;
v_res_577_ = l_Std_Http_Server_serve___redArg___lam__7(v___f_562_, v___y_563_, v_x_564_);
stack->m_obj
 = v_res_577_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7___boxed(lean_object* v___f_578_, lean_object* v___y_579_, lean_object* v_x_580_, lean_object* v___y_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Std_Http_Server_serve___redArg___lam__7(v___f_578_, v___y_579_, v_x_580_);
lean_dec_ref(v___y_579_);
return v_res_582_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__10(lean_object* v___f_583_, lean_object* v_a_584_, lean_object* v_x_585_){
_start:
{
if (lean_obj_tag(v_x_585_) == 0)
{
lean_object* v___x_587_; 
lean_dec_ref(v_a_584_);
lean_dec_ref(v___f_583_);
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v_x_585_);
return v___x_587_;
}
else
{
lean_object* v_a_588_; lean_object* v___x_589_; 
v_a_588_ = lean_ctor_get(v_x_585_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v_x_585_, 1);
v___x_589_ = lean_apply_3(v___f_583_, v_a_588_, v_a_584_, lean_box(0));
return v___x_589_;
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_583_ = stack[0].m_obj;
lean_object* v_a_584_ = stack[1].m_obj;
lean_object* v_x_585_ = stack[2].m_obj;
lean_object* v_res_590_;
v_res_590_ = l_Std_Http_Server_serve___redArg___lam__10(v___f_583_, v_a_584_, v_x_585_);
stack->m_obj
 = v_res_590_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10___boxed(lean_object* v___f_591_, lean_object* v_a_592_, lean_object* v_x_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Std_Http_Server_serve___redArg___lam__10(v___f_591_, v_a_592_, v_x_593_);
return v_res_595_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__8(uint8_t v_permitAcquired_596_, lean_object* v___f_597_, lean_object* v___x_598_, lean_object* v_a_599_, lean_object* v_connectionLimit_600_, lean_object* v___x_601_, uint8_t v___x_602_, lean_object* v___f_603_, lean_object* v_opt_604_){
_start:
{
if (v_permitAcquired_596_ == 0)
{
lean_object* v___x_606_; 
lean_dec_ref(v___f_603_);
lean_dec(v___x_601_);
lean_dec(v_connectionLimit_600_);
v___x_606_ = lean_apply_3(v___f_597_, v___x_598_, v_a_599_, lean_box(0));
return v___x_606_;
}
else
{
if (lean_obj_tag(v_connectionLimit_600_) == 1)
{
lean_object* v_val_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_617_; 
lean_dec_ref(v_a_599_);
lean_dec_ref(v___f_597_);
v_val_607_ = lean_ctor_get(v_connectionLimit_600_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v_connectionLimit_600_);
if (v_isSharedCheck_617_ == 0)
{
v___x_609_ = v_connectionLimit_600_;
v_isShared_610_ = v_isSharedCheck_617_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_val_607_);
lean_dec(v_connectionLimit_600_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_617_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_611_ = l_Std_Semaphore_release(v_val_607_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v___x_611_);
v___x_613_ = v___x_609_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_611_);
v___x_613_ = v_reuseFailAlloc_616_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
v___x_615_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_601_, v___x_602_, v___x_614_, v___f_603_);
return v___x_615_;
}
}
}
else
{
lean_object* v___x_618_; 
lean_dec_ref(v___f_603_);
lean_dec(v___x_601_);
lean_dec(v_connectionLimit_600_);
v___x_618_ = lean_apply_3(v___f_597_, v___x_598_, v_a_599_, lean_box(0));
return v___x_618_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
uint8_t v_permitAcquired_596_ = stack[0].m_num;
lean_object* v___f_597_ = stack[1].m_obj;
lean_object* v___x_598_ = stack[2].m_obj;
lean_object* v_a_599_ = stack[3].m_obj;
lean_object* v_connectionLimit_600_ = stack[4].m_obj;
lean_object* v___x_601_ = stack[5].m_obj;
uint8_t v___x_602_ = stack[6].m_num;
lean_object* v___f_603_ = stack[7].m_obj;
lean_object* v_opt_604_ = stack[8].m_obj;
lean_object* v_res_619_;
v_res_619_ = l_Std_Http_Server_serve___redArg___lam__8(v_permitAcquired_596_, v___f_597_, v___x_598_, v_a_599_, v_connectionLimit_600_, v___x_601_, v___x_602_, v___f_603_, v_opt_604_);
stack->m_obj
 = v_res_619_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8___boxed(lean_object* v_permitAcquired_620_, lean_object* v___f_621_, lean_object* v___x_622_, lean_object* v_a_623_, lean_object* v_connectionLimit_624_, lean_object* v___x_625_, lean_object* v___x_626_, lean_object* v___f_627_, lean_object* v_opt_628_, lean_object* v___y_629_){
_start:
{
uint8_t v_permitAcquired_boxed_630_; uint8_t v___x_13195__boxed_631_; lean_object* v_res_632_; 
v_permitAcquired_boxed_630_ = lean_unbox(v_permitAcquired_620_);
v___x_13195__boxed_631_ = lean_unbox(v___x_626_);
v_res_632_ = l_Std_Http_Server_serve___redArg___lam__8(v_permitAcquired_boxed_630_, v___f_621_, v___x_622_, v_a_623_, v_connectionLimit_624_, v___x_625_, v___x_13195__boxed_631_, v___f_627_, v_opt_628_);
lean_dec(v_opt_628_);
return v_res_632_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__11(lean_object* v___f_633_, lean_object* v___x_634_, lean_object* v_inst_635_, lean_object* v_val_636_, lean_object* v_handler_637_, lean_object* v_config_638_, lean_object* v_extensions_639_, lean_object* v_a_640_, lean_object* v___f_641_, lean_object* v___x_642_, uint8_t v___x_643_, lean_object* v_x_644_){
_start:
{
if (lean_obj_tag(v_x_644_) == 0)
{
lean_object* v___x_646_; 
lean_dec(v___x_642_);
lean_dec_ref(v___f_641_);
lean_dec_ref(v_a_640_);
lean_dec(v_extensions_639_);
lean_dec_ref(v_config_638_);
lean_dec(v_handler_637_);
lean_dec(v_val_636_);
lean_dec_ref(v_inst_635_);
lean_dec_ref(v___x_634_);
lean_dec_ref(v___f_633_);
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v_x_644_);
return v___x_646_;
}
else
{
lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_685_; 
v_isSharedCheck_685_ = !lean_is_exclusive(v_x_644_);
if (v_isSharedCheck_685_ == 0)
{
lean_object* v_unused_686_; 
v_unused_686_ = lean_ctor_get(v_x_644_, 0);
lean_dec(v_unused_686_);
v___x_648_ = v_x_644_;
v_isShared_649_ = v_isSharedCheck_685_;
goto v_resetjp_647_;
}
else
{
lean_dec(v_x_644_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_685_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___y_654_; 
v___x_650_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_650_, 0, lean_box(0));
lean_closure_set(v___x_650_, 1, lean_box(0));
lean_closure_set(v___x_650_, 2, lean_box(0));
lean_closure_set(v___x_650_, 3, v___f_633_);
v___x_651_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___boxed), 10, 9);
lean_closure_set(v___x_651_, 0, lean_box(0));
lean_closure_set(v___x_651_, 1, lean_box(0));
lean_closure_set(v___x_651_, 2, v___x_634_);
lean_closure_set(v___x_651_, 3, v_inst_635_);
lean_closure_set(v___x_651_, 4, v_val_636_);
lean_closure_set(v___x_651_, 5, v_handler_637_);
lean_closure_set(v___x_651_, 6, v_config_638_);
lean_closure_set(v___x_651_, 7, v_extensions_639_);
lean_closure_set(v___x_651_, 8, v_a_640_);
lean_inc(v___x_642_);
v___x_652_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_651_, v___f_641_, v___x_642_, v___x_643_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_658_; 
lean_dec_ref(v___x_650_);
lean_dec(v___x_642_);
v_a_658_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v___x_652_, 1);
if (lean_obj_tag(v_a_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
v_a_659_ = lean_ctor_get(v_a_658_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v_a_658_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v_a_658_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v_a_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_659_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
v___y_654_ = v___x_664_;
goto v___jp_653_;
}
}
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_675_; 
v_a_667_ = lean_ctor_get(v_a_658_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v_a_658_);
if (v_isSharedCheck_675_ == 0)
{
v___x_669_ = v_a_658_;
v_isShared_670_ = v_isSharedCheck_675_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v_a_658_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_675_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v_fst_671_; lean_object* v___x_673_; 
v_fst_671_ = lean_ctor_get(v_a_667_, 0);
lean_inc(v_fst_671_);
lean_dec(v_a_667_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v_fst_671_);
v___x_673_ = v___x_669_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_fst_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
v___y_654_ = v___x_673_;
goto v___jp_653_;
}
}
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_684_; 
lean_del_object(v___x_648_);
v_a_676_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_684_ == 0)
{
v___x_678_ = v___x_652_;
v_isShared_679_ = v_isSharedCheck_684_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_652_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_684_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_680_; lean_object* v___x_682_; 
v___x_680_ = lean_task_map(v___x_650_, v_a_676_, v___x_642_, v___x_643_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v___x_680_);
v___x_682_ = v___x_678_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_680_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
v___jp_653_:
{
lean_object* v___x_656_; 
if (v_isShared_649_ == 0)
{
lean_ctor_set_tag(v___x_648_, 0);
lean_ctor_set(v___x_648_, 0, v___y_654_);
v___x_656_ = v___x_648_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___y_654_);
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
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_633_ = stack[0].m_obj;
lean_object* v___x_634_ = stack[1].m_obj;
lean_object* v_inst_635_ = stack[2].m_obj;
lean_object* v_val_636_ = stack[3].m_obj;
lean_object* v_handler_637_ = stack[4].m_obj;
lean_object* v_config_638_ = stack[5].m_obj;
lean_object* v_extensions_639_ = stack[6].m_obj;
lean_object* v_a_640_ = stack[7].m_obj;
lean_object* v___f_641_ = stack[8].m_obj;
lean_object* v___x_642_ = stack[9].m_obj;
uint8_t v___x_643_ = stack[10].m_num;
lean_object* v_x_644_ = stack[11].m_obj;
lean_object* v_res_687_;
v_res_687_ = l_Std_Http_Server_serve___redArg___lam__11(v___f_633_, v___x_634_, v_inst_635_, v_val_636_, v_handler_637_, v_config_638_, v_extensions_639_, v_a_640_, v___f_641_, v___x_642_, v___x_643_, v_x_644_);
stack->m_obj
 = v_res_687_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11___boxed(lean_object* v___f_688_, lean_object* v___x_689_, lean_object* v_inst_690_, lean_object* v_val_691_, lean_object* v_handler_692_, lean_object* v_config_693_, lean_object* v_extensions_694_, lean_object* v_a_695_, lean_object* v___f_696_, lean_object* v___x_697_, lean_object* v___x_698_, lean_object* v_x_699_, lean_object* v___y_700_){
_start:
{
uint8_t v___x_13272__boxed_701_; lean_object* v_res_702_; 
v___x_13272__boxed_701_ = lean_unbox(v___x_698_);
v_res_702_ = l_Std_Http_Server_serve___redArg___lam__11(v___f_688_, v___x_689_, v_inst_690_, v_val_691_, v_handler_692_, v_config_693_, v_extensions_694_, v_a_695_, v___f_696_, v___x_697_, v___x_13272__boxed_701_, v_x_699_);
return v_res_702_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__12(lean_object* v___f_703_, lean_object* v___f_704_, lean_object* v_activeConnections_705_, lean_object* v_a_706_, uint8_t v_permitAcquired_707_, lean_object* v___x_708_, lean_object* v_connectionLimit_709_, lean_object* v___x_710_, uint8_t v___x_711_, lean_object* v___f_712_, lean_object* v___x_713_, lean_object* v_inst_714_, lean_object* v_val_715_, lean_object* v_handler_716_, lean_object* v_config_717_, lean_object* v_extensions_718_, lean_object* v___f_719_){
_start:
{
lean_object* v___x_721_; lean_object* v___f_722_; lean_object* v___f_723_; lean_object* v___f_724_; lean_object* v___f_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___f_728_; lean_object* v___x_729_; lean_object* v___f_730_; lean_object* v___x_12285__overap_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_721_ = l_Std_Async_ContextAsync_instMonad;
v___f_722_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5));
v___f_723_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6));
lean_inc_ref(v_activeConnections_705_);
v___f_724_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed), 9, 6);
lean_closure_set(v___f_724_, 0, v___x_721_);
lean_closure_set(v___f_724_, 1, v___f_703_);
lean_closure_set(v___f_724_, 2, v___f_704_);
lean_closure_set(v___f_724_, 3, v___f_722_);
lean_closure_set(v___f_724_, 4, v___f_723_);
lean_closure_set(v___f_724_, 5, v_activeConnections_705_);
lean_inc_ref_n(v_a_706_, 3);
lean_inc_ref(v___f_724_);
v___f_725_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__10___boxed), 4, 2);
lean_closure_set(v___f_725_, 0, v___f_724_);
lean_closure_set(v___f_725_, 1, v_a_706_);
v___x_726_ = lean_box(v_permitAcquired_707_);
v___x_727_ = lean_box(v___x_711_);
lean_inc_n(v___x_710_, 2);
v___f_728_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__8___boxed), 10, 8);
lean_closure_set(v___f_728_, 0, v___x_726_);
lean_closure_set(v___f_728_, 1, v___f_724_);
lean_closure_set(v___f_728_, 2, v___x_708_);
lean_closure_set(v___f_728_, 3, v_a_706_);
lean_closure_set(v___f_728_, 4, v_connectionLimit_709_);
lean_closure_set(v___f_728_, 5, v___x_710_);
lean_closure_set(v___f_728_, 6, v___x_727_);
lean_closure_set(v___f_728_, 7, v___f_725_);
v___x_729_ = lean_box(v___x_711_);
v___f_730_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__11___boxed), 13, 11);
lean_closure_set(v___f_730_, 0, v___f_712_);
lean_closure_set(v___f_730_, 1, v___x_713_);
lean_closure_set(v___f_730_, 2, v_inst_714_);
lean_closure_set(v___f_730_, 3, v_val_715_);
lean_closure_set(v___f_730_, 4, v_handler_716_);
lean_closure_set(v___f_730_, 5, v_config_717_);
lean_closure_set(v___f_730_, 6, v_extensions_718_);
lean_closure_set(v___f_730_, 7, v_a_706_);
lean_closure_set(v___f_730_, 8, v___f_728_);
lean_closure_set(v___f_730_, 9, v___x_710_);
lean_closure_set(v___f_730_, 10, v___x_729_);
v___x_12285__overap_731_ = l_Std_Mutex_atomically___redArg(v___x_721_, v___f_722_, v___f_723_, v_activeConnections_705_, v___f_719_);
v___x_732_ = lean_apply_2(v___x_12285__overap_731_, v_a_706_, lean_box(0));
v___x_733_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_710_, v___x_711_, v___x_732_, v___f_730_);
return v___x_733_;
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__12_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_703_ = stack[0].m_obj;
lean_object* v___f_704_ = stack[1].m_obj;
lean_object* v_activeConnections_705_ = stack[2].m_obj;
lean_object* v_a_706_ = stack[3].m_obj;
uint8_t v_permitAcquired_707_ = stack[4].m_num;
lean_object* v___x_708_ = stack[5].m_obj;
lean_object* v_connectionLimit_709_ = stack[6].m_obj;
lean_object* v___x_710_ = stack[7].m_obj;
uint8_t v___x_711_ = stack[8].m_num;
lean_object* v___f_712_ = stack[9].m_obj;
lean_object* v___x_713_ = stack[10].m_obj;
lean_object* v_inst_714_ = stack[11].m_obj;
lean_object* v_val_715_ = stack[12].m_obj;
lean_object* v_handler_716_ = stack[13].m_obj;
lean_object* v_config_717_ = stack[14].m_obj;
lean_object* v_extensions_718_ = stack[15].m_obj;
lean_object* v___f_719_ = stack[16].m_obj;
lean_object* v_res_734_;
v_res_734_ = l_Std_Http_Server_serve___redArg___lam__12(v___f_703_, v___f_704_, v_activeConnections_705_, v_a_706_, v_permitAcquired_707_, v___x_708_, v_connectionLimit_709_, v___x_710_, v___x_711_, v___f_712_, v___x_713_, v_inst_714_, v_val_715_, v_handler_716_, v_config_717_, v_extensions_718_, v___f_719_);
stack->m_obj
 = v_res_734_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12___boxed(lean_object** _args){
lean_object* v___f_735_ = _args[0];
lean_object* v___f_736_ = _args[1];
lean_object* v_activeConnections_737_ = _args[2];
lean_object* v_a_738_ = _args[3];
lean_object* v_permitAcquired_739_ = _args[4];
lean_object* v___x_740_ = _args[5];
lean_object* v_connectionLimit_741_ = _args[6];
lean_object* v___x_742_ = _args[7];
lean_object* v___x_743_ = _args[8];
lean_object* v___f_744_ = _args[9];
lean_object* v___x_745_ = _args[10];
lean_object* v_inst_746_ = _args[11];
lean_object* v_val_747_ = _args[12];
lean_object* v_handler_748_ = _args[13];
lean_object* v_config_749_ = _args[14];
lean_object* v_extensions_750_ = _args[15];
lean_object* v___f_751_ = _args[16];
lean_object* v___y_752_ = _args[17];
_start:
{
uint8_t v_permitAcquired_boxed_753_; uint8_t v___x_13448__boxed_754_; lean_object* v_res_755_; 
v_permitAcquired_boxed_753_ = lean_unbox(v_permitAcquired_739_);
v___x_13448__boxed_754_ = lean_unbox(v___x_743_);
v_res_755_ = l_Std_Http_Server_serve___redArg___lam__12(v___f_735_, v___f_736_, v_activeConnections_737_, v_a_738_, v_permitAcquired_boxed_753_, v___x_740_, v_connectionLimit_741_, v___x_742_, v___x_13448__boxed_754_, v___f_744_, v___x_745_, v_inst_746_, v_val_747_, v_handler_748_, v_config_749_, v_extensions_750_, v___f_751_);
return v_res_755_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__13(lean_object* v_a_756_, lean_object* v___x_757_, lean_object* v_a_x3f_758_){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_760_ = l_Std_CancellationContext_cancel(v_a_756_, v___x_757_);
v___x_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
v___x_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
return v___x_762_;
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_756_ = stack[0].m_obj;
lean_object* v___x_757_ = stack[1].m_obj;
lean_object* v_a_x3f_758_ = stack[2].m_obj;
lean_object* v_res_763_;
v_res_763_ = l_Std_Http_Server_serve___redArg___lam__13(v_a_756_, v___x_757_, v_a_x3f_758_);
stack->m_obj
 = v_res_763_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13___boxed(lean_object* v_a_764_, lean_object* v___x_765_, lean_object* v_a_x3f_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Std_Http_Server_serve___redArg___lam__13(v_a_764_, v___x_765_, v_a_x3f_766_);
lean_dec(v_a_x3f_766_);
return v_res_768_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__14(lean_object* v___f_769_, lean_object* v___f_770_, lean_object* v___f_771_, lean_object* v___x_772_, uint8_t v___x_773_){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___y_778_; 
v___x_775_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_775_, 0, lean_box(0));
lean_closure_set(v___x_775_, 1, lean_box(0));
lean_closure_set(v___x_775_, 2, lean_box(0));
lean_closure_set(v___x_775_, 3, v___f_769_);
lean_inc(v___x_772_);
v___x_776_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_770_, v___f_771_, v___x_772_, v___x_773_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_780_; 
lean_dec_ref(v___x_775_);
lean_dec(v___x_772_);
v_a_780_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_a_780_);
lean_dec_ref_known(v___x_776_, 1);
if (lean_obj_tag(v_a_780_) == 0)
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
v_a_781_ = lean_ctor_get(v_a_780_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v_a_780_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v_a_780_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v_a_780_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
v___y_778_ = v___x_786_;
goto v___jp_777_;
}
}
}
else
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_797_; 
v_a_789_ = lean_ctor_get(v_a_780_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v_a_780_);
if (v_isSharedCheck_797_ == 0)
{
v___x_791_ = v_a_780_;
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v_a_780_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v_fst_793_; lean_object* v___x_795_; 
v_fst_793_ = lean_ctor_get(v_a_789_, 0);
lean_inc(v_fst_793_);
lean_dec(v_a_789_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v_fst_793_);
v___x_795_ = v___x_791_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_fst_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
v___y_778_ = v___x_795_;
goto v___jp_777_;
}
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_806_; 
v_a_798_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_806_ == 0)
{
v___x_800_ = v___x_776_;
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_776_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_802_ = lean_task_map(v___x_775_, v_a_798_, v___x_772_, v___x_773_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v___x_802_);
v___x_804_ = v___x_800_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
v___jp_777_:
{
lean_object* v___x_779_; 
v___x_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_779_, 0, v___y_778_);
return v___x_779_;
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__14_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_769_ = stack[0].m_obj;
lean_object* v___f_770_ = stack[1].m_obj;
lean_object* v___f_771_ = stack[2].m_obj;
lean_object* v___x_772_ = stack[3].m_obj;
uint8_t v___x_773_ = stack[4].m_num;
lean_object* v_res_807_;
v_res_807_ = l_Std_Http_Server_serve___redArg___lam__14(v___f_769_, v___f_770_, v___f_771_, v___x_772_, v___x_773_);
stack->m_obj
 = v_res_807_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14___boxed(lean_object* v___f_808_, lean_object* v___f_809_, lean_object* v___f_810_, lean_object* v___x_811_, lean_object* v___x_812_, lean_object* v___y_813_){
_start:
{
uint8_t v___x_13569__boxed_814_; lean_object* v_res_815_; 
v___x_13569__boxed_814_ = lean_unbox(v___x_812_);
v_res_815_ = l_Std_Http_Server_serve___redArg___lam__14(v___f_808_, v___f_809_, v___f_810_, v___x_811_, v___x_13569__boxed_814_);
return v_res_815_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__15(lean_object* v___f_816_, lean_object* v___f_817_, lean_object* v_activeConnections_818_, uint8_t v_permitAcquired_819_, lean_object* v___x_820_, lean_object* v_connectionLimit_821_, lean_object* v___x_822_, uint8_t v___x_823_, lean_object* v___f_824_, lean_object* v___x_825_, lean_object* v_inst_826_, lean_object* v_val_827_, lean_object* v_handler_828_, lean_object* v_config_829_, lean_object* v_extensions_830_, lean_object* v___f_831_, lean_object* v___f_832_, lean_object* v_x_833_){
_start:
{
if (lean_obj_tag(v_x_833_) == 0)
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_843_; 
lean_dec_ref(v___f_832_);
lean_dec_ref(v___f_831_);
lean_dec(v_extensions_830_);
lean_dec_ref(v_config_829_);
lean_dec(v_handler_828_);
lean_dec(v_val_827_);
lean_dec_ref(v_inst_826_);
lean_dec_ref(v___x_825_);
lean_dec_ref(v___f_824_);
lean_dec(v___x_822_);
lean_dec(v_connectionLimit_821_);
lean_dec_ref(v_activeConnections_818_);
lean_dec_ref(v___f_817_);
lean_dec_ref(v___f_816_);
v_a_835_ = lean_ctor_get(v_x_833_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v_x_833_);
if (v_isSharedCheck_843_ == 0)
{
v___x_837_ = v_x_833_;
v_isShared_838_ = v_isSharedCheck_843_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v_x_833_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_843_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_842_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v___x_841_; 
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_861_; 
v_a_844_ = lean_ctor_get(v_x_833_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v_x_833_);
if (v_isSharedCheck_861_ == 0)
{
v___x_846_ = v_x_833_;
v_isShared_847_ = v_isSharedCheck_861_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v_x_833_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_861_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___f_850_; lean_object* v___x_851_; lean_object* v___f_852_; lean_object* v___x_853_; lean_object* v___f_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_848_ = lean_box(v_permitAcquired_819_);
v___x_849_ = lean_box(v___x_823_);
lean_inc_n(v___x_822_, 2);
lean_inc(v_a_844_);
v___f_850_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__12___boxed), 18, 17);
lean_closure_set(v___f_850_, 0, v___f_816_);
lean_closure_set(v___f_850_, 1, v___f_817_);
lean_closure_set(v___f_850_, 2, v_activeConnections_818_);
lean_closure_set(v___f_850_, 3, v_a_844_);
lean_closure_set(v___f_850_, 4, v___x_848_);
lean_closure_set(v___f_850_, 5, v___x_820_);
lean_closure_set(v___f_850_, 6, v_connectionLimit_821_);
lean_closure_set(v___f_850_, 7, v___x_822_);
lean_closure_set(v___f_850_, 8, v___x_849_);
lean_closure_set(v___f_850_, 9, v___f_824_);
lean_closure_set(v___f_850_, 10, v___x_825_);
lean_closure_set(v___f_850_, 11, v_inst_826_);
lean_closure_set(v___f_850_, 12, v_val_827_);
lean_closure_set(v___f_850_, 13, v_handler_828_);
lean_closure_set(v___f_850_, 14, v_config_829_);
lean_closure_set(v___f_850_, 15, v_extensions_830_);
lean_closure_set(v___f_850_, 16, v___f_831_);
v___x_851_ = lean_box(2);
v___f_852_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__13___boxed), 4, 2);
lean_closure_set(v___f_852_, 0, v_a_844_);
lean_closure_set(v___f_852_, 1, v___x_851_);
v___x_853_ = lean_box(v___x_823_);
v___f_854_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__14___boxed), 6, 5);
lean_closure_set(v___f_854_, 0, v___f_832_);
lean_closure_set(v___f_854_, 1, v___f_850_);
lean_closure_set(v___f_854_, 2, v___f_852_);
lean_closure_set(v___f_854_, 3, v___x_822_);
lean_closure_set(v___f_854_, 4, v___x_853_);
v___x_855_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_855_, 0, lean_box(0));
lean_closure_set(v___x_855_, 1, v___f_854_);
v___x_856_ = lean_io_as_task(v___x_855_, v___x_822_);
lean_dec_ref(v___x_856_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_820_);
v___x_858_ = v___x_846_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_820_);
v___x_858_ = v_reuseFailAlloc_860_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_859_; 
v___x_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
return v___x_859_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__15_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_816_ = stack[0].m_obj;
lean_object* v___f_817_ = stack[1].m_obj;
lean_object* v_activeConnections_818_ = stack[2].m_obj;
uint8_t v_permitAcquired_819_ = stack[3].m_num;
lean_object* v___x_820_ = stack[4].m_obj;
lean_object* v_connectionLimit_821_ = stack[5].m_obj;
lean_object* v___x_822_ = stack[6].m_obj;
uint8_t v___x_823_ = stack[7].m_num;
lean_object* v___f_824_ = stack[8].m_obj;
lean_object* v___x_825_ = stack[9].m_obj;
lean_object* v_inst_826_ = stack[10].m_obj;
lean_object* v_val_827_ = stack[11].m_obj;
lean_object* v_handler_828_ = stack[12].m_obj;
lean_object* v_config_829_ = stack[13].m_obj;
lean_object* v_extensions_830_ = stack[14].m_obj;
lean_object* v___f_831_ = stack[15].m_obj;
lean_object* v___f_832_ = stack[16].m_obj;
lean_object* v_x_833_ = stack[17].m_obj;
lean_object* v_res_862_;
v_res_862_ = l_Std_Http_Server_serve___redArg___lam__15(v___f_816_, v___f_817_, v_activeConnections_818_, v_permitAcquired_819_, v___x_820_, v_connectionLimit_821_, v___x_822_, v___x_823_, v___f_824_, v___x_825_, v_inst_826_, v_val_827_, v_handler_828_, v_config_829_, v_extensions_830_, v___f_831_, v___f_832_, v_x_833_);
stack->m_obj
 = v_res_862_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15___boxed(lean_object** _args){
lean_object* v___f_863_ = _args[0];
lean_object* v___f_864_ = _args[1];
lean_object* v_activeConnections_865_ = _args[2];
lean_object* v_permitAcquired_866_ = _args[3];
lean_object* v___x_867_ = _args[4];
lean_object* v_connectionLimit_868_ = _args[5];
lean_object* v___x_869_ = _args[6];
lean_object* v___x_870_ = _args[7];
lean_object* v___f_871_ = _args[8];
lean_object* v___x_872_ = _args[9];
lean_object* v_inst_873_ = _args[10];
lean_object* v_val_874_ = _args[11];
lean_object* v_handler_875_ = _args[12];
lean_object* v_config_876_ = _args[13];
lean_object* v_extensions_877_ = _args[14];
lean_object* v___f_878_ = _args[15];
lean_object* v___f_879_ = _args[16];
lean_object* v_x_880_ = _args[17];
lean_object* v___y_881_ = _args[18];
_start:
{
uint8_t v_permitAcquired_boxed_882_; uint8_t v___x_13692__boxed_883_; lean_object* v_res_884_; 
v_permitAcquired_boxed_882_ = lean_unbox(v_permitAcquired_866_);
v___x_13692__boxed_883_ = lean_unbox(v___x_870_);
v_res_884_ = l_Std_Http_Server_serve___redArg___lam__15(v___f_863_, v___f_864_, v_activeConnections_865_, v_permitAcquired_boxed_882_, v___x_867_, v_connectionLimit_868_, v___x_869_, v___x_13692__boxed_883_, v___f_871_, v___x_872_, v_inst_873_, v_val_874_, v_handler_875_, v_config_876_, v_extensions_877_, v___f_878_, v___f_879_, v_x_880_);
return v_res_884_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__16(lean_object* v___x_885_, uint8_t v___x_886_, lean_object* v___f_887_, lean_object* v_x_888_){
_start:
{
if (lean_obj_tag(v_x_888_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_898_; 
lean_dec_ref(v___f_887_);
lean_dec(v___x_885_);
v_a_890_ = lean_ctor_get(v_x_888_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v_x_888_);
if (v_isSharedCheck_898_ == 0)
{
v___x_892_ = v_x_888_;
v_isShared_893_ = v_isSharedCheck_898_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v_x_888_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_898_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_897_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
lean_object* v___x_896_; 
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
return v___x_896_;
}
}
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_909_; 
v_a_899_ = lean_ctor_get(v_x_888_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v_x_888_);
if (v_isSharedCheck_909_ == 0)
{
v___x_901_ = v_x_888_;
v_isShared_902_ = v_isSharedCheck_909_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v_x_888_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_909_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; lean_object* v___x_905_; 
v___x_903_ = l_Std_CancellationContext_fork(v_a_899_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v___x_903_);
v___x_905_ = v___x_901_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_903_);
v___x_905_ = v_reuseFailAlloc_908_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
v___x_907_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_885_, v___x_886_, v___x_906_, v___f_887_);
return v___x_907_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__16_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_885_ = stack[0].m_obj;
uint8_t v___x_886_ = stack[1].m_num;
lean_object* v___f_887_ = stack[2].m_obj;
lean_object* v_x_888_ = stack[3].m_obj;
lean_object* v_res_910_;
v_res_910_ = l_Std_Http_Server_serve___redArg___lam__16(v___x_885_, v___x_886_, v___f_887_, v_x_888_);
stack->m_obj
 = v_res_910_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16___boxed(lean_object* v___x_911_, lean_object* v___x_912_, lean_object* v___f_913_, lean_object* v_x_914_, lean_object* v___y_915_){
_start:
{
uint8_t v___x_13835__boxed_916_; lean_object* v_res_917_; 
v___x_13835__boxed_916_ = lean_unbox(v___x_912_);
v_res_917_ = l_Std_Http_Server_serve___redArg___lam__16(v___x_911_, v___x_13835__boxed_916_, v___f_913_, v_x_914_);
return v_res_917_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__17(lean_object* v___f_918_, lean_object* v___f_919_, lean_object* v_activeConnections_920_, uint8_t v_permitAcquired_921_, lean_object* v___x_922_, lean_object* v_connectionLimit_923_, uint8_t v___x_924_, lean_object* v___f_925_, lean_object* v___x_926_, lean_object* v_inst_927_, lean_object* v_val_928_, lean_object* v_handler_929_, lean_object* v_config_930_, lean_object* v___f_931_, lean_object* v___f_932_, lean_object* v___f_933_, lean_object* v_extensions_934_, lean_object* v___y_935_){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___f_940_; lean_object* v___x_941_; lean_object* v___f_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_937_ = lean_unsigned_to_nat(0u);
v___x_938_ = lean_box(v_permitAcquired_921_);
v___x_939_ = lean_box(v___x_924_);
v___f_940_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__15___boxed), 19, 17);
lean_closure_set(v___f_940_, 0, v___f_918_);
lean_closure_set(v___f_940_, 1, v___f_919_);
lean_closure_set(v___f_940_, 2, v_activeConnections_920_);
lean_closure_set(v___f_940_, 3, v___x_938_);
lean_closure_set(v___f_940_, 4, v___x_922_);
lean_closure_set(v___f_940_, 5, v_connectionLimit_923_);
lean_closure_set(v___f_940_, 6, v___x_937_);
lean_closure_set(v___f_940_, 7, v___x_939_);
lean_closure_set(v___f_940_, 8, v___f_925_);
lean_closure_set(v___f_940_, 9, v___x_926_);
lean_closure_set(v___f_940_, 10, v_inst_927_);
lean_closure_set(v___f_940_, 11, v_val_928_);
lean_closure_set(v___f_940_, 12, v_handler_929_);
lean_closure_set(v___f_940_, 13, v_config_930_);
lean_closure_set(v___f_940_, 14, v_extensions_934_);
lean_closure_set(v___f_940_, 15, v___f_931_);
lean_closure_set(v___f_940_, 16, v___f_932_);
v___x_941_ = lean_box(v___x_924_);
v___f_942_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__16___boxed), 5, 3);
lean_closure_set(v___f_942_, 0, v___x_937_);
lean_closure_set(v___f_942_, 1, v___x_941_);
lean_closure_set(v___f_942_, 2, v___f_940_);
lean_inc_ref(v___y_935_);
v___x_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_943_, 0, v___y_935_);
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
v___x_945_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_937_, v___x_924_, v___x_944_, v___f_942_);
v___x_946_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_937_, v___x_924_, v___x_945_, v___f_933_);
return v___x_946_;
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__17_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_918_ = stack[0].m_obj;
lean_object* v___f_919_ = stack[1].m_obj;
lean_object* v_activeConnections_920_ = stack[2].m_obj;
uint8_t v_permitAcquired_921_ = stack[3].m_num;
lean_object* v___x_922_ = stack[4].m_obj;
lean_object* v_connectionLimit_923_ = stack[5].m_obj;
uint8_t v___x_924_ = stack[6].m_num;
lean_object* v___f_925_ = stack[7].m_obj;
lean_object* v___x_926_ = stack[8].m_obj;
lean_object* v_inst_927_ = stack[9].m_obj;
lean_object* v_val_928_ = stack[10].m_obj;
lean_object* v_handler_929_ = stack[11].m_obj;
lean_object* v_config_930_ = stack[12].m_obj;
lean_object* v___f_931_ = stack[13].m_obj;
lean_object* v___f_932_ = stack[14].m_obj;
lean_object* v___f_933_ = stack[15].m_obj;
lean_object* v_extensions_934_ = stack[16].m_obj;
lean_object* v___y_935_ = stack[17].m_obj;
lean_object* v_res_947_;
v_res_947_ = l_Std_Http_Server_serve___redArg___lam__17(v___f_918_, v___f_919_, v_activeConnections_920_, v_permitAcquired_921_, v___x_922_, v_connectionLimit_923_, v___x_924_, v___f_925_, v___x_926_, v_inst_927_, v_val_928_, v_handler_929_, v_config_930_, v___f_931_, v___f_932_, v___f_933_, v_extensions_934_, v___y_935_);
stack->m_obj
 = v_res_947_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17___boxed(lean_object** _args){
lean_object* v___f_948_ = _args[0];
lean_object* v___f_949_ = _args[1];
lean_object* v_activeConnections_950_ = _args[2];
lean_object* v_permitAcquired_951_ = _args[3];
lean_object* v___x_952_ = _args[4];
lean_object* v_connectionLimit_953_ = _args[5];
lean_object* v___x_954_ = _args[6];
lean_object* v___f_955_ = _args[7];
lean_object* v___x_956_ = _args[8];
lean_object* v_inst_957_ = _args[9];
lean_object* v_val_958_ = _args[10];
lean_object* v_handler_959_ = _args[11];
lean_object* v_config_960_ = _args[12];
lean_object* v___f_961_ = _args[13];
lean_object* v___f_962_ = _args[14];
lean_object* v___f_963_ = _args[15];
lean_object* v_extensions_964_ = _args[16];
lean_object* v___y_965_ = _args[17];
lean_object* v___y_966_ = _args[18];
_start:
{
uint8_t v_permitAcquired_boxed_967_; uint8_t v___x_13922__boxed_968_; lean_object* v_res_969_; 
v_permitAcquired_boxed_967_ = lean_unbox(v_permitAcquired_951_);
v___x_13922__boxed_968_ = lean_unbox(v___x_954_);
v_res_969_ = l_Std_Http_Server_serve___redArg___lam__17(v___f_948_, v___f_949_, v_activeConnections_950_, v_permitAcquired_boxed_967_, v___x_952_, v_connectionLimit_953_, v___x_13922__boxed_968_, v___f_955_, v___x_956_, v_inst_957_, v_val_958_, v_handler_959_, v_config_960_, v___f_961_, v___f_962_, v___f_963_, v_extensions_964_, v___y_965_);
lean_dec_ref(v___y_965_);
return v_res_969_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__18(lean_object* v___f_970_, lean_object* v___y_971_, lean_object* v_x_972_){
_start:
{
if (lean_obj_tag(v_x_972_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_982_; 
lean_dec_ref(v___f_970_);
v_a_974_ = lean_ctor_get(v_x_972_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v_x_972_);
if (v_isSharedCheck_982_ == 0)
{
v___x_976_ = v_x_972_;
v_isShared_977_ = v_isSharedCheck_982_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v_x_972_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_982_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_981_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
lean_object* v___x_980_; 
v___x_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
return v___x_980_;
}
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_984_; 
v_a_983_ = lean_ctor_get(v_x_972_, 0);
lean_inc(v_a_983_);
lean_dec_ref_known(v_x_972_, 1);
lean_inc_ref(v___y_971_);
v___x_984_ = lean_apply_3(v___f_970_, v_a_983_, v___y_971_, lean_box(0));
return v___x_984_;
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__18_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_970_ = stack[0].m_obj;
lean_object* v___y_971_ = stack[1].m_obj;
lean_object* v_x_972_ = stack[2].m_obj;
lean_object* v_res_985_;
v_res_985_ = l_Std_Http_Server_serve___redArg___lam__18(v___f_970_, v___y_971_, v_x_972_);
stack->m_obj
 = v_res_985_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18___boxed(lean_object* v___f_986_, lean_object* v___y_987_, lean_object* v_x_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Std_Http_Server_serve___redArg___lam__18(v___f_986_, v___y_987_, v_x_988_);
lean_dec_ref(v___y_987_);
return v_res_990_;
}
}
static lean_object* _init_l_Std_Http_Server_serve___redArg___lam__20___closed__0(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = l_Std_Http_Extensions_empty;
v___x_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
return v___x_992_;
}
}
static lean_object* _init_l_Std_Http_Server_serve___redArg___lam__20___closed__1(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = lean_obj_once(&l_Std_Http_Server_serve___redArg___lam__20___closed__0, &l_Std_Http_Server_serve___redArg___lam__20___closed__0_once, _init_l_Std_Http_Server_serve___redArg___lam__20___closed__0);
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
return v___x_994_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__20(uint8_t v___x_996_, lean_object* v___f_997_, lean_object* v___x_998_, lean_object* v___f_999_, lean_object* v_x_1000_){
_start:
{
if (lean_obj_tag(v_x_1000_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1010_; 
lean_dec_ref(v___f_999_);
lean_dec(v___x_998_);
lean_dec_ref(v___f_997_);
v_a_1002_ = lean_ctor_get(v_x_1000_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_x_1000_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1004_ = v_x_1000_;
v_isShared_1005_ = v_isSharedCheck_1010_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v_x_1000_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1010_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1008_; 
v___x_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
return v___x_1008_;
}
}
}
else
{
lean_object* v_a_1011_; 
v_a_1011_ = lean_ctor_get(v_x_1000_, 0);
lean_inc(v_a_1011_);
lean_dec_ref_known(v_x_1000_, 1);
if (lean_obj_tag(v_a_1011_) == 0)
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
lean_dec_ref_known(v_a_1011_, 1);
lean_dec_ref(v___f_999_);
lean_dec(v___x_998_);
v___x_1012_ = lean_unsigned_to_nat(0u);
v___x_1013_ = lean_obj_once(&l_Std_Http_Server_serve___redArg___lam__20___closed__1, &l_Std_Http_Server_serve___redArg___lam__20___closed__1_once, _init_l_Std_Http_Server_serve___redArg___lam__20___closed__1);
v___x_1014_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1012_, v___x_996_, v___x_1013_, v___f_997_);
return v___x_1014_;
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1030_; 
lean_dec_ref(v___f_997_);
v_a_1015_ = lean_ctor_get(v_a_1011_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_a_1011_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1017_ = v_a_1011_;
v_isShared_1018_ = v_isSharedCheck_1030_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v_a_1011_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1030_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1019_; lean_object* v_dyn_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1019_ = l_Std_Http_Extensions_empty;
v_dyn_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_1020_, 0, v___x_998_);
lean_ctor_set(v_dyn_1020_, 1, v_a_1015_);
v___x_1021_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__20___closed__2));
v___x_1022_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_1020_);
v___x_1023_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_1021_, v___x_1022_, v_dyn_1020_, v___x_1019_);
v___x_1024_ = lean_unsigned_to_nat(0u);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 0, v___x_1023_);
v___x_1026_ = v___x_1017_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1023_);
v___x_1026_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
v___x_1028_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1024_, v___x_996_, v___x_1027_, v___f_999_);
return v___x_1028_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__20_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_996_ = stack[0].m_num;
lean_object* v___f_997_ = stack[1].m_obj;
lean_object* v___x_998_ = stack[2].m_obj;
lean_object* v___f_999_ = stack[3].m_obj;
lean_object* v_x_1000_ = stack[4].m_obj;
lean_object* v_res_1031_;
v_res_1031_ = l_Std_Http_Server_serve___redArg___lam__20(v___x_996_, v___f_997_, v___x_998_, v___f_999_, v_x_1000_);
stack->m_obj
 = v_res_1031_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20___boxed(lean_object* v___x_1032_, lean_object* v___f_1033_, lean_object* v___x_1034_, lean_object* v___f_1035_, lean_object* v_x_1036_, lean_object* v___y_1037_){
_start:
{
uint8_t v___x_14077__boxed_1038_; lean_object* v_res_1039_; 
v___x_14077__boxed_1038_ = lean_unbox(v___x_1032_);
v_res_1039_ = l_Std_Http_Server_serve___redArg___lam__20(v___x_14077__boxed_1038_, v___f_1033_, v___x_1034_, v___f_1035_, v_x_1036_);
return v_res_1039_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__19(uint8_t v_permitAcquired_1040_, lean_object* v___f_1041_, lean_object* v___x_1042_, lean_object* v___y_1043_, lean_object* v_connectionLimit_1044_, uint8_t v___x_1045_, lean_object* v___f_1046_, lean_object* v___f_1047_, lean_object* v___f_1048_, lean_object* v_activeConnections_1049_, lean_object* v___f_1050_, lean_object* v___x_1051_, lean_object* v_inst_1052_, lean_object* v_handler_1053_, lean_object* v_config_1054_, lean_object* v___f_1055_, lean_object* v___f_1056_, lean_object* v___f_1057_, lean_object* v___x_1058_, lean_object* v_x_1059_){
_start:
{
if (lean_obj_tag(v_x_1059_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1069_; 
lean_dec(v___x_1058_);
lean_dec_ref(v___f_1057_);
lean_dec_ref(v___f_1056_);
lean_dec_ref(v___f_1055_);
lean_dec_ref(v_config_1054_);
lean_dec(v_handler_1053_);
lean_dec_ref(v_inst_1052_);
lean_dec_ref(v___x_1051_);
lean_dec_ref(v___f_1050_);
lean_dec_ref(v_activeConnections_1049_);
lean_dec_ref(v___f_1048_);
lean_dec_ref(v___f_1047_);
lean_dec_ref(v___f_1046_);
lean_dec(v_connectionLimit_1044_);
lean_dec_ref(v___f_1041_);
v_a_1061_ = lean_ctor_get(v_x_1059_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_x_1059_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1063_ = v_x_1059_;
v_isShared_1064_ = v_isSharedCheck_1069_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v_x_1059_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1069_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
return v___x_1067_;
}
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1128_; 
v_a_1070_ = lean_ctor_get(v_x_1059_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_x_1059_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1072_ = v_x_1059_;
v_isShared_1073_ = v_isSharedCheck_1128_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v_x_1059_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1128_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
if (lean_obj_tag(v_a_1070_) == 0)
{
lean_dec(v___x_1058_);
lean_dec_ref(v___f_1057_);
lean_dec_ref(v___f_1056_);
lean_dec_ref(v___f_1055_);
lean_dec_ref(v_config_1054_);
lean_dec(v_handler_1053_);
lean_dec_ref(v_inst_1052_);
lean_dec_ref(v___x_1051_);
lean_dec_ref(v___f_1050_);
lean_dec_ref(v_activeConnections_1049_);
lean_dec_ref(v___f_1048_);
lean_dec_ref(v___f_1047_);
if (v_permitAcquired_1040_ == 0)
{
lean_object* v___x_1074_; 
lean_del_object(v___x_1072_);
lean_dec_ref(v___f_1046_);
lean_dec(v_connectionLimit_1044_);
lean_inc_ref(v___y_1043_);
v___x_1074_ = lean_apply_3(v___f_1041_, v___x_1042_, v___y_1043_, lean_box(0));
return v___x_1074_;
}
else
{
if (lean_obj_tag(v_connectionLimit_1044_) == 1)
{
lean_object* v_val_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1088_; 
lean_dec_ref(v___f_1041_);
v_val_1075_ = lean_ctor_get(v_connectionLimit_1044_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_connectionLimit_1044_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1077_ = v_connectionLimit_1044_;
v_isShared_1078_ = v_isSharedCheck_1088_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_val_1075_);
lean_dec(v_connectionLimit_1044_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1088_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1079_ = lean_unsigned_to_nat(0u);
v___x_1080_ = l_Std_Semaphore_release(v_val_1075_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1080_);
v___x_1082_ = v___x_1072_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1084_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set_tag(v___x_1077_, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1082_);
v___x_1084_ = v___x_1077_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1085_; 
v___x_1085_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1079_, v___x_1045_, v___x_1084_, v___f_1046_);
return v___x_1085_;
}
}
}
}
else
{
lean_object* v___x_1089_; 
lean_del_object(v___x_1072_);
lean_dec_ref(v___f_1046_);
lean_dec(v_connectionLimit_1044_);
lean_inc_ref(v___y_1043_);
v___x_1089_ = lean_apply_3(v___f_1041_, v___x_1042_, v___y_1043_, lean_box(0));
return v___x_1089_;
}
}
}
else
{
lean_object* v_val_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1127_; 
lean_dec_ref(v___f_1046_);
lean_dec_ref(v___f_1041_);
v_val_1090_ = lean_ctor_get(v_a_1070_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_a_1070_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1092_ = v_a_1070_;
v_isShared_1093_ = v_isSharedCheck_1127_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_val_1090_);
lean_dec(v_a_1070_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1127_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___f_1096_; lean_object* v___f_1097_; lean_object* v___x_1098_; lean_object* v___f_1099_; lean_object* v___x_1100_; lean_object* v_val_1102_; lean_object* v___x_1110_; 
v___x_1094_ = lean_box(v_permitAcquired_1040_);
v___x_1095_ = lean_box(v___x_1045_);
lean_inc(v_val_1090_);
v___f_1096_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__17___boxed), 19, 16);
lean_closure_set(v___f_1096_, 0, v___f_1047_);
lean_closure_set(v___f_1096_, 1, v___f_1048_);
lean_closure_set(v___f_1096_, 2, v_activeConnections_1049_);
lean_closure_set(v___f_1096_, 3, v___x_1094_);
lean_closure_set(v___f_1096_, 4, v___x_1042_);
lean_closure_set(v___f_1096_, 5, v_connectionLimit_1044_);
lean_closure_set(v___f_1096_, 6, v___x_1095_);
lean_closure_set(v___f_1096_, 7, v___f_1050_);
lean_closure_set(v___f_1096_, 8, v___x_1051_);
lean_closure_set(v___f_1096_, 9, v_inst_1052_);
lean_closure_set(v___f_1096_, 10, v_val_1090_);
lean_closure_set(v___f_1096_, 11, v_handler_1053_);
lean_closure_set(v___f_1096_, 12, v_config_1054_);
lean_closure_set(v___f_1096_, 13, v___f_1055_);
lean_closure_set(v___f_1096_, 14, v___f_1056_);
lean_closure_set(v___f_1096_, 15, v___f_1057_);
lean_inc_ref(v___y_1043_);
v___f_1097_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__18___boxed), 4, 2);
lean_closure_set(v___f_1097_, 0, v___f_1096_);
lean_closure_set(v___f_1097_, 1, v___y_1043_);
v___x_1098_ = lean_box(v___x_1045_);
lean_inc_ref(v___f_1097_);
v___f_1099_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__20___boxed), 6, 4);
lean_closure_set(v___f_1099_, 0, v___x_1098_);
lean_closure_set(v___f_1099_, 1, v___f_1097_);
lean_closure_set(v___f_1099_, 2, v___x_1058_);
lean_closure_set(v___f_1099_, 3, v___f_1097_);
v___x_1100_ = lean_unsigned_to_nat(0u);
v___x_1110_ = lean_uv_tcp_getpeername(v_val_1090_);
lean_dec(v_val_1090_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1110_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1110_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set_tag(v___x_1113_, 1);
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
v_val_1102_ = v___x_1116_;
goto v___jp_1101_;
}
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
v_a_1119_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1110_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1110_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set_tag(v___x_1121_, 0);
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
v_val_1102_ = v___x_1124_;
goto v___jp_1101_;
}
}
}
v___jp_1101_:
{
lean_object* v___x_1104_; 
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v_val_1102_);
v___x_1104_ = v___x_1072_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_val_1102_);
v___x_1104_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v___x_1106_; 
if (v_isShared_1093_ == 0)
{
lean_ctor_set_tag(v___x_1092_, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1104_);
v___x_1106_ = v___x_1092_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1107_; 
v___x_1107_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1100_, v___x_1045_, v___x_1106_, v___f_1099_);
return v___x_1107_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__19_0interp(lean_interpreter_value* stack)
{
uint8_t v_permitAcquired_1040_ = stack[0].m_num;
lean_object* v___f_1041_ = stack[1].m_obj;
lean_object* v___x_1042_ = stack[2].m_obj;
lean_object* v___y_1043_ = stack[3].m_obj;
lean_object* v_connectionLimit_1044_ = stack[4].m_obj;
uint8_t v___x_1045_ = stack[5].m_num;
lean_object* v___f_1046_ = stack[6].m_obj;
lean_object* v___f_1047_ = stack[7].m_obj;
lean_object* v___f_1048_ = stack[8].m_obj;
lean_object* v_activeConnections_1049_ = stack[9].m_obj;
lean_object* v___f_1050_ = stack[10].m_obj;
lean_object* v___x_1051_ = stack[11].m_obj;
lean_object* v_inst_1052_ = stack[12].m_obj;
lean_object* v_handler_1053_ = stack[13].m_obj;
lean_object* v_config_1054_ = stack[14].m_obj;
lean_object* v___f_1055_ = stack[15].m_obj;
lean_object* v___f_1056_ = stack[16].m_obj;
lean_object* v___f_1057_ = stack[17].m_obj;
lean_object* v___x_1058_ = stack[18].m_obj;
lean_object* v_x_1059_ = stack[19].m_obj;
lean_object* v_res_1129_;
v_res_1129_ = l_Std_Http_Server_serve___redArg___lam__19(v_permitAcquired_1040_, v___f_1041_, v___x_1042_, v___y_1043_, v_connectionLimit_1044_, v___x_1045_, v___f_1046_, v___f_1047_, v___f_1048_, v_activeConnections_1049_, v___f_1050_, v___x_1051_, v_inst_1052_, v_handler_1053_, v_config_1054_, v___f_1055_, v___f_1056_, v___f_1057_, v___x_1058_, v_x_1059_);
stack->m_obj
 = v_res_1129_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_permitAcquired_1130_ = _args[0];
lean_object* v___f_1131_ = _args[1];
lean_object* v___x_1132_ = _args[2];
lean_object* v___y_1133_ = _args[3];
lean_object* v_connectionLimit_1134_ = _args[4];
lean_object* v___x_1135_ = _args[5];
lean_object* v___f_1136_ = _args[6];
lean_object* v___f_1137_ = _args[7];
lean_object* v___f_1138_ = _args[8];
lean_object* v_activeConnections_1139_ = _args[9];
lean_object* v___f_1140_ = _args[10];
lean_object* v___x_1141_ = _args[11];
lean_object* v_inst_1142_ = _args[12];
lean_object* v_handler_1143_ = _args[13];
lean_object* v_config_1144_ = _args[14];
lean_object* v___f_1145_ = _args[15];
lean_object* v___f_1146_ = _args[16];
lean_object* v___f_1147_ = _args[17];
lean_object* v___x_1148_ = _args[18];
lean_object* v_x_1149_ = _args[19];
lean_object* v___y_1150_ = _args[20];
_start:
{
uint8_t v_permitAcquired_boxed_1151_; uint8_t v___x_14205__boxed_1152_; lean_object* v_res_1153_; 
v_permitAcquired_boxed_1151_ = lean_unbox(v_permitAcquired_1130_);
v___x_14205__boxed_1152_ = lean_unbox(v___x_1135_);
v_res_1153_ = l_Std_Http_Server_serve___redArg___lam__19(v_permitAcquired_boxed_1151_, v___f_1131_, v___x_1132_, v___y_1133_, v_connectionLimit_1134_, v___x_14205__boxed_1152_, v___f_1136_, v___f_1137_, v___f_1138_, v_activeConnections_1139_, v___f_1140_, v___x_1141_, v_inst_1142_, v_handler_1143_, v_config_1144_, v___f_1145_, v___f_1146_, v___f_1147_, v___x_1148_, v_x_1149_);
lean_dec_ref(v___y_1133_);
return v_res_1153_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__21(lean_object* v_a_1154_, lean_object* v___f_1155_, lean_object* v___f_1156_, uint8_t v___x_1157_, lean_object* v___f_1158_, lean_object* v_x_1159_){
_start:
{
if (lean_obj_tag(v_x_1159_) == 0)
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1169_; 
lean_dec_ref(v___f_1158_);
lean_dec_ref(v___f_1156_);
lean_dec_ref(v___f_1155_);
lean_dec(v_a_1154_);
v_a_1161_ = lean_ctor_get(v_x_1159_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_x_1159_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1163_ = v_x_1159_;
v_isShared_1164_ = v_isSharedCheck_1169_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v_x_1159_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1169_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
return v___x_1167_;
}
}
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v_a_1170_ = lean_ctor_get(v_x_1159_, 0);
lean_inc(v_a_1170_);
lean_dec_ref_known(v_x_1159_, 1);
v___x_1171_ = l_Std_Async_TCP_Socket_Server_acceptSelector(v_a_1154_);
v___x_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
lean_ctor_set(v___x_1172_, 1, v___f_1155_);
v___x_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1173_, 0, v_a_1170_);
lean_ctor_set(v___x_1173_, 1, v___f_1156_);
v___x_1174_ = lean_unsigned_to_nat(2u);
v___x_1175_ = lean_mk_empty_array_with_capacity(v___x_1174_);
v___x_1176_ = lean_array_push(v___x_1175_, v___x_1172_);
v___x_1177_ = lean_array_push(v___x_1176_, v___x_1173_);
v___x_1178_ = lean_unsigned_to_nat(0u);
v___x_1179_ = l_Std_Async_Selectable_one___redArg(v___x_1177_);
v___x_1180_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1178_, v___x_1157_, v___x_1179_, v___f_1158_);
return v___x_1180_;
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__21_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1154_ = stack[0].m_obj;
lean_object* v___f_1155_ = stack[1].m_obj;
lean_object* v___f_1156_ = stack[2].m_obj;
uint8_t v___x_1157_ = stack[3].m_num;
lean_object* v___f_1158_ = stack[4].m_obj;
lean_object* v_x_1159_ = stack[5].m_obj;
lean_object* v_res_1181_;
v_res_1181_ = l_Std_Http_Server_serve___redArg___lam__21(v_a_1154_, v___f_1155_, v___f_1156_, v___x_1157_, v___f_1158_, v_x_1159_);
stack->m_obj
 = v_res_1181_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21___boxed(lean_object* v_a_1182_, lean_object* v___f_1183_, lean_object* v___f_1184_, lean_object* v___x_1185_, lean_object* v___f_1186_, lean_object* v_x_1187_, lean_object* v___y_1188_){
_start:
{
uint8_t v___x_14489__boxed_1189_; lean_object* v_res_1190_; 
v___x_14489__boxed_1189_ = lean_unbox(v___x_1185_);
v_res_1190_ = l_Std_Http_Server_serve___redArg___lam__21(v_a_1182_, v___f_1183_, v___f_1184_, v___x_14489__boxed_1189_, v___f_1186_, v_x_1187_);
return v_res_1190_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__22(lean_object* v___f_1191_, lean_object* v___x_1192_, lean_object* v_connectionLimit_1193_, uint8_t v___x_1194_, lean_object* v___f_1195_, lean_object* v___f_1196_, lean_object* v_activeConnections_1197_, lean_object* v___f_1198_, lean_object* v___x_1199_, lean_object* v_inst_1200_, lean_object* v_handler_1201_, lean_object* v_config_1202_, lean_object* v___f_1203_, lean_object* v___f_1204_, lean_object* v___f_1205_, lean_object* v___x_1206_, lean_object* v_a_1207_, lean_object* v___f_1208_, lean_object* v___f_1209_, lean_object* v___f_1210_, uint8_t v_permitAcquired_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v___f_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___f_1217_; lean_object* v___x_1218_; lean_object* v___f_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_inc_ref_n(v___y_1212_, 3);
lean_inc_ref(v___f_1191_);
v___f_1214_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_1214_, 0, v___f_1191_);
lean_closure_set(v___f_1214_, 1, v___y_1212_);
v___x_1215_ = lean_box(v_permitAcquired_1211_);
v___x_1216_ = lean_box(v___x_1194_);
v___f_1217_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__19___boxed), 21, 19);
lean_closure_set(v___f_1217_, 0, v___x_1215_);
lean_closure_set(v___f_1217_, 1, v___f_1191_);
lean_closure_set(v___f_1217_, 2, v___x_1192_);
lean_closure_set(v___f_1217_, 3, v___y_1212_);
lean_closure_set(v___f_1217_, 4, v_connectionLimit_1193_);
lean_closure_set(v___f_1217_, 5, v___x_1216_);
lean_closure_set(v___f_1217_, 6, v___f_1214_);
lean_closure_set(v___f_1217_, 7, v___f_1195_);
lean_closure_set(v___f_1217_, 8, v___f_1196_);
lean_closure_set(v___f_1217_, 9, v_activeConnections_1197_);
lean_closure_set(v___f_1217_, 10, v___f_1198_);
lean_closure_set(v___f_1217_, 11, v___x_1199_);
lean_closure_set(v___f_1217_, 12, v_inst_1200_);
lean_closure_set(v___f_1217_, 13, v_handler_1201_);
lean_closure_set(v___f_1217_, 14, v_config_1202_);
lean_closure_set(v___f_1217_, 15, v___f_1203_);
lean_closure_set(v___f_1217_, 16, v___f_1204_);
lean_closure_set(v___f_1217_, 17, v___f_1205_);
lean_closure_set(v___f_1217_, 18, v___x_1206_);
v___x_1218_ = lean_box(v___x_1194_);
v___f_1219_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__21___boxed), 7, 5);
lean_closure_set(v___f_1219_, 0, v_a_1207_);
lean_closure_set(v___f_1219_, 1, v___f_1208_);
lean_closure_set(v___f_1219_, 2, v___f_1209_);
lean_closure_set(v___f_1219_, 3, v___x_1218_);
lean_closure_set(v___f_1219_, 4, v___f_1217_);
v___x_1220_ = lean_unsigned_to_nat(0u);
v___x_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___y_1212_);
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
v___x_1223_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1220_, v___x_1194_, v___x_1222_, v___f_1210_);
v___x_1224_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1220_, v___x_1194_, v___x_1223_, v___f_1219_);
return v___x_1224_;
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__22_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1191_ = stack[0].m_obj;
lean_object* v___x_1192_ = stack[1].m_obj;
lean_object* v_connectionLimit_1193_ = stack[2].m_obj;
uint8_t v___x_1194_ = stack[3].m_num;
lean_object* v___f_1195_ = stack[4].m_obj;
lean_object* v___f_1196_ = stack[5].m_obj;
lean_object* v_activeConnections_1197_ = stack[6].m_obj;
lean_object* v___f_1198_ = stack[7].m_obj;
lean_object* v___x_1199_ = stack[8].m_obj;
lean_object* v_inst_1200_ = stack[9].m_obj;
lean_object* v_handler_1201_ = stack[10].m_obj;
lean_object* v_config_1202_ = stack[11].m_obj;
lean_object* v___f_1203_ = stack[12].m_obj;
lean_object* v___f_1204_ = stack[13].m_obj;
lean_object* v___f_1205_ = stack[14].m_obj;
lean_object* v___x_1206_ = stack[15].m_obj;
lean_object* v_a_1207_ = stack[16].m_obj;
lean_object* v___f_1208_ = stack[17].m_obj;
lean_object* v___f_1209_ = stack[18].m_obj;
lean_object* v___f_1210_ = stack[19].m_obj;
uint8_t v_permitAcquired_1211_ = stack[20].m_num;
lean_object* v___y_1212_ = stack[21].m_obj;
lean_object* v_res_1225_;
v_res_1225_ = l_Std_Http_Server_serve___redArg___lam__22(v___f_1191_, v___x_1192_, v_connectionLimit_1193_, v___x_1194_, v___f_1195_, v___f_1196_, v_activeConnections_1197_, v___f_1198_, v___x_1199_, v_inst_1200_, v_handler_1201_, v_config_1202_, v___f_1203_, v___f_1204_, v___f_1205_, v___x_1206_, v_a_1207_, v___f_1208_, v___f_1209_, v___f_1210_, v_permitAcquired_1211_, v___y_1212_);
stack->m_obj
 = v_res_1225_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22___boxed(lean_object** _args){
lean_object* v___f_1226_ = _args[0];
lean_object* v___x_1227_ = _args[1];
lean_object* v_connectionLimit_1228_ = _args[2];
lean_object* v___x_1229_ = _args[3];
lean_object* v___f_1230_ = _args[4];
lean_object* v___f_1231_ = _args[5];
lean_object* v_activeConnections_1232_ = _args[6];
lean_object* v___f_1233_ = _args[7];
lean_object* v___x_1234_ = _args[8];
lean_object* v_inst_1235_ = _args[9];
lean_object* v_handler_1236_ = _args[10];
lean_object* v_config_1237_ = _args[11];
lean_object* v___f_1238_ = _args[12];
lean_object* v___f_1239_ = _args[13];
lean_object* v___f_1240_ = _args[14];
lean_object* v___x_1241_ = _args[15];
lean_object* v_a_1242_ = _args[16];
lean_object* v___f_1243_ = _args[17];
lean_object* v___f_1244_ = _args[18];
lean_object* v___f_1245_ = _args[19];
lean_object* v_permitAcquired_1246_ = _args[20];
lean_object* v___y_1247_ = _args[21];
lean_object* v___y_1248_ = _args[22];
_start:
{
uint8_t v___x_14583__boxed_1249_; uint8_t v_permitAcquired_boxed_1250_; lean_object* v_res_1251_; 
v___x_14583__boxed_1249_ = lean_unbox(v___x_1229_);
v_permitAcquired_boxed_1250_ = lean_unbox(v_permitAcquired_1246_);
v_res_1251_ = l_Std_Http_Server_serve___redArg___lam__22(v___f_1226_, v___x_1227_, v_connectionLimit_1228_, v___x_14583__boxed_1249_, v___f_1230_, v___f_1231_, v_activeConnections_1232_, v___f_1233_, v___x_1234_, v_inst_1235_, v_handler_1236_, v_config_1237_, v___f_1238_, v___f_1239_, v___f_1240_, v___x_1241_, v_a_1242_, v___f_1243_, v___f_1244_, v___f_1245_, v_permitAcquired_boxed_1250_, v___y_1247_);
lean_dec_ref(v___y_1247_);
return v_res_1251_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__23(lean_object* v___f_1252_, lean_object* v___y_1253_, lean_object* v_x_1254_){
_start:
{
if (lean_obj_tag(v_x_1254_) == 0)
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1264_; 
lean_dec_ref(v___y_1253_);
lean_dec_ref(v___f_1252_);
v_a_1256_ = lean_ctor_get(v_x_1254_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_x_1254_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1258_ = v_x_1254_;
v_isShared_1259_ = v_isSharedCheck_1264_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v_x_1254_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1264_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1262_; 
v___x_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
return v___x_1262_;
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1266_; 
v_a_1265_ = lean_ctor_get(v_x_1254_, 0);
lean_inc(v_a_1265_);
lean_dec_ref_known(v_x_1254_, 1);
v___x_1266_ = lean_apply_3(v___f_1252_, v_a_1265_, v___y_1253_, lean_box(0));
return v___x_1266_;
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__23_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1252_ = stack[0].m_obj;
lean_object* v___y_1253_ = stack[1].m_obj;
lean_object* v_x_1254_ = stack[2].m_obj;
lean_object* v_res_1267_;
v_res_1267_ = l_Std_Http_Server_serve___redArg___lam__23(v___f_1252_, v___y_1253_, v_x_1254_);
stack->m_obj
 = v_res_1267_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23___boxed(lean_object* v___f_1268_, lean_object* v___y_1269_, lean_object* v_x_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Std_Http_Server_serve___redArg___lam__23(v___f_1268_, v___y_1269_, v_x_1270_);
return v_res_1272_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__25(uint8_t v___x_1273_, uint8_t v___x_1274_, lean_object* v___f_1275_, lean_object* v_x_1276_){
_start:
{
if (lean_obj_tag(v_x_1276_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1286_; 
lean_dec_ref(v___f_1275_);
v_a_1278_ = lean_ctor_get(v_x_1276_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_x_1276_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1280_ = v_x_1276_;
v_isShared_1281_ = v_isSharedCheck_1286_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v_x_1276_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1286_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1284_; 
v___x_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
return v___x_1284_;
}
}
}
else
{
lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1297_; 
v_isSharedCheck_1297_ = !lean_is_exclusive(v_x_1276_);
if (v_isSharedCheck_1297_ == 0)
{
lean_object* v_unused_1298_; 
v_unused_1298_ = lean_ctor_get(v_x_1276_, 0);
lean_dec(v_unused_1298_);
v___x_1288_ = v_x_1276_;
v_isShared_1289_ = v_isSharedCheck_1297_;
goto v_resetjp_1287_;
}
else
{
lean_dec(v_x_1276_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1297_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1290_ = lean_unsigned_to_nat(0u);
v___x_1291_ = lean_box(v___x_1273_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 0, v___x_1291_);
v___x_1293_ = v___x_1288_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
v___x_1295_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1290_, v___x_1274_, v___x_1294_, v___f_1275_);
return v___x_1295_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__25_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1273_ = stack[0].m_num;
uint8_t v___x_1274_ = stack[1].m_num;
lean_object* v___f_1275_ = stack[2].m_obj;
lean_object* v_x_1276_ = stack[3].m_obj;
lean_object* v_res_1299_;
v_res_1299_ = l_Std_Http_Server_serve___redArg___lam__25(v___x_1273_, v___x_1274_, v___f_1275_, v_x_1276_);
stack->m_obj
 = v_res_1299_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25___boxed(lean_object* v___x_1300_, lean_object* v___x_1301_, lean_object* v___f_1302_, lean_object* v_x_1303_, lean_object* v___y_1304_){
_start:
{
uint8_t v___x_14757__boxed_1305_; uint8_t v___x_14758__boxed_1306_; lean_object* v_res_1307_; 
v___x_14757__boxed_1305_ = lean_unbox(v___x_1300_);
v___x_14758__boxed_1306_ = lean_unbox(v___x_1301_);
v_res_1307_ = l_Std_Http_Server_serve___redArg___lam__25(v___x_14757__boxed_1305_, v___x_14758__boxed_1306_, v___f_1302_, v_x_1303_);
return v_res_1307_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__24(lean_object* v___f_1308_, uint8_t v___x_1309_, lean_object* v___f_1310_, lean_object* v_x_1311_){
_start:
{
if (lean_obj_tag(v_x_1311_) == 0)
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1321_; 
lean_dec_ref(v___f_1310_);
lean_dec_ref(v___f_1308_);
v_a_1313_ = lean_ctor_get(v_x_1311_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_x_1311_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1315_ = v_x_1311_;
v_isShared_1316_ = v_isSharedCheck_1321_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v_x_1311_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1321_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
lean_object* v___x_1319_; 
v___x_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
return v___x_1319_;
}
}
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v_a_1322_ = lean_ctor_get(v_x_1311_, 0);
lean_inc(v_a_1322_);
lean_dec_ref_known(v_x_1311_, 1);
v___x_1323_ = lean_unsigned_to_nat(0u);
v___x_1324_ = l_IO_Promise_result_x21___redArg(v_a_1322_);
lean_dec(v_a_1322_);
v___x_1325_ = lean_task_map(v___f_1308_, v___x_1324_, v___x_1323_, v___x_1309_);
v___x_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
v___x_1327_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1323_, v___x_1309_, v___x_1326_, v___f_1310_);
return v___x_1327_;
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__24_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1308_ = stack[0].m_obj;
uint8_t v___x_1309_ = stack[1].m_num;
lean_object* v___f_1310_ = stack[2].m_obj;
lean_object* v_x_1311_ = stack[3].m_obj;
lean_object* v_res_1328_;
v_res_1328_ = l_Std_Http_Server_serve___redArg___lam__24(v___f_1308_, v___x_1309_, v___f_1310_, v_x_1311_);
stack->m_obj
 = v_res_1328_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24___boxed(lean_object* v___f_1329_, lean_object* v___x_1330_, lean_object* v___f_1331_, lean_object* v_x_1332_, lean_object* v___y_1333_){
_start:
{
uint8_t v___x_14847__boxed_1334_; lean_object* v_res_1335_; 
v___x_14847__boxed_1334_ = lean_unbox(v___x_1330_);
v_res_1335_ = l_Std_Http_Server_serve___redArg___lam__24(v___f_1329_, v___x_14847__boxed_1334_, v___f_1331_, v_x_1332_);
return v_res_1335_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__26(lean_object* v_connectionLimit_1336_, uint8_t v___x_1337_, lean_object* v___f_1338_, lean_object* v___f_1339_, lean_object* v___f_1340_, lean_object* v_u_1341_, lean_object* v_b_1342_){
_start:
{
if (lean_obj_tag(v_connectionLimit_1336_) == 1)
{
lean_object* v_val_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1361_; 
lean_dec_ref(v___f_1340_);
v_val_1344_ = lean_ctor_get(v_connectionLimit_1336_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_connectionLimit_1336_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1346_ = v_connectionLimit_1336_;
v_isShared_1347_ = v_isSharedCheck_1361_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_val_1344_);
lean_dec(v_connectionLimit_1336_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1361_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
uint8_t v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___f_1351_; lean_object* v___x_1352_; lean_object* v___f_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1348_ = 1;
v___x_1349_ = lean_box(v___x_1348_);
v___x_1350_ = lean_box(v___x_1337_);
v___f_1351_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__25___boxed), 5, 3);
lean_closure_set(v___f_1351_, 0, v___x_1349_);
lean_closure_set(v___f_1351_, 1, v___x_1350_);
lean_closure_set(v___f_1351_, 2, v___f_1338_);
v___x_1352_ = lean_box(v___x_1337_);
v___f_1353_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__24___boxed), 5, 3);
lean_closure_set(v___f_1353_, 0, v___f_1339_);
lean_closure_set(v___f_1353_, 1, v___x_1352_);
lean_closure_set(v___f_1353_, 2, v___f_1351_);
v___x_1354_ = lean_unsigned_to_nat(0u);
v___x_1355_ = l_Std_Semaphore_acquire(v_val_1344_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 0, v___x_1355_);
v___x_1357_ = v___x_1346_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
v___x_1359_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1354_, v___x_1337_, v___x_1358_, v___f_1353_);
return v___x_1359_;
}
}
}
else
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_dec_ref(v___f_1339_);
lean_dec_ref(v___f_1338_);
lean_dec(v_connectionLimit_1336_);
v___x_1362_ = lean_unsigned_to_nat(0u);
v___x_1363_ = lean_box(v___x_1337_);
v___x_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
v___x_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
v___x_1366_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1362_, v___x_1337_, v___x_1365_, v___f_1340_);
return v___x_1366_;
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__26_0interp(lean_interpreter_value* stack)
{
lean_object* v_connectionLimit_1336_ = stack[0].m_obj;
uint8_t v___x_1337_ = stack[1].m_num;
lean_object* v___f_1338_ = stack[2].m_obj;
lean_object* v___f_1339_ = stack[3].m_obj;
lean_object* v___f_1340_ = stack[4].m_obj;
lean_object* v_u_1341_ = stack[5].m_obj;
lean_object* v_b_1342_ = stack[6].m_obj;
lean_object* v_res_1367_;
v_res_1367_ = l_Std_Http_Server_serve___redArg___lam__26(v_connectionLimit_1336_, v___x_1337_, v___f_1338_, v___f_1339_, v___f_1340_, v_u_1341_, v_b_1342_);
stack->m_obj
 = v_res_1367_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26___boxed(lean_object* v_connectionLimit_1368_, lean_object* v___x_1369_, lean_object* v___f_1370_, lean_object* v___f_1371_, lean_object* v___f_1372_, lean_object* v_u_1373_, lean_object* v_b_1374_, lean_object* v___y_1375_){
_start:
{
uint8_t v___x_14916__boxed_1376_; lean_object* v_res_1377_; 
v___x_14916__boxed_1376_ = lean_unbox(v___x_1369_);
v_res_1377_ = l_Std_Http_Server_serve___redArg___lam__26(v_connectionLimit_1368_, v___x_14916__boxed_1376_, v___f_1370_, v___f_1371_, v___f_1372_, v_u_1373_, v_b_1374_);
return v_res_1377_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__27(lean_object* v_a_1378_, lean_object* v_x_1379_){
_start:
{
if (lean_obj_tag(v_x_1379_) == 0)
{
lean_object* v___x_1381_; 
v___x_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1381_, 0, v_x_1379_);
return v___x_1381_;
}
else
{
lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1389_; 
v_isSharedCheck_1389_ = !lean_is_exclusive(v_x_1379_);
if (v_isSharedCheck_1389_ == 0)
{
lean_object* v_unused_1390_; 
v_unused_1390_ = lean_ctor_get(v_x_1379_, 0);
lean_dec(v_unused_1390_);
v___x_1383_ = v_x_1379_;
v_isShared_1384_ = v_isSharedCheck_1389_;
goto v_resetjp_1382_;
}
else
{
lean_dec(v_x_1379_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1389_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1387_; 
v___x_1385_ = l_IO_Promise_result_x21___redArg(v_a_1378_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v___x_1385_);
v___x_1387_ = v___x_1383_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__27_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1378_ = stack[0].m_obj;
lean_object* v_x_1379_ = stack[1].m_obj;
lean_object* v_res_1391_;
v_res_1391_ = l_Std_Http_Server_serve___redArg___lam__27(v_a_1378_, v_x_1379_);
stack->m_obj
 = v_res_1391_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27___boxed(lean_object* v_a_1392_, lean_object* v_x_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Std_Http_Server_serve___redArg___lam__27(v_a_1392_, v_x_1393_);
lean_dec(v_a_1392_);
return v_res_1395_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__28(lean_object* v___f_1396_, lean_object* v___x_1397_, lean_object* v___x_1398_, uint8_t v___x_1399_, lean_object* v_x_1400_){
_start:
{
if (lean_obj_tag(v_x_1400_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1410_; 
lean_dec(v___x_1397_);
lean_dec_ref(v___f_1396_);
v_a_1402_ = lean_ctor_get(v_x_1400_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_x_1400_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1404_ = v_x_1400_;
v_isShared_1405_ = v_isSharedCheck_1410_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v_x_1400_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1410_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1402_);
v___x_1407_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1408_; 
v___x_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1407_);
return v___x_1408_;
}
}
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1422_; 
v_a_1411_ = lean_ctor_get(v_x_1400_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v_x_1400_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1413_ = v_x_1400_;
v_isShared_1414_ = v_isSharedCheck_1422_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v_x_1400_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1422_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___f_1415_; lean_object* v___x_1416_; lean_object* v___x_1418_; 
lean_inc(v_a_1411_);
v___f_1415_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__27___boxed), 3, 1);
lean_closure_set(v___f_1415_, 0, v_a_1411_);
lean_inc(v___x_1397_);
v___x_1416_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_1396_, v___x_1397_, v_a_1411_, v___x_1398_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 0, v___x_1416_);
v___x_1418_ = v___x_1413_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
v___x_1420_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1397_, v___x_1399_, v___x_1419_, v___f_1415_);
return v___x_1420_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__28_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1396_ = stack[0].m_obj;
lean_object* v___x_1397_ = stack[1].m_obj;
lean_object* v___x_1398_ = stack[2].m_obj;
uint8_t v___x_1399_ = stack[3].m_num;
lean_object* v_x_1400_ = stack[4].m_obj;
lean_object* v_res_1423_;
v_res_1423_ = l_Std_Http_Server_serve___redArg___lam__28(v___f_1396_, v___x_1397_, v___x_1398_, v___x_1399_, v_x_1400_);
stack->m_obj
 = v_res_1423_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28___boxed(lean_object* v___f_1424_, lean_object* v___x_1425_, lean_object* v___x_1426_, lean_object* v___x_1427_, lean_object* v_x_1428_, lean_object* v___y_1429_){
_start:
{
uint8_t v___x_15060__boxed_1430_; lean_object* v_res_1431_; 
v___x_15060__boxed_1430_ = lean_unbox(v___x_1427_);
v_res_1431_ = l_Std_Http_Server_serve___redArg___lam__28(v___f_1424_, v___x_1425_, v___x_1426_, v___x_15060__boxed_1430_, v_x_1428_);
return v_res_1431_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__29(lean_object* v___f_1432_, lean_object* v_connectionLimit_1433_, uint8_t v___x_1434_, lean_object* v___f_1435_, lean_object* v___x_1436_, lean_object* v___f_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v___f_1440_; lean_object* v___x_1441_; lean_object* v___f_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___f_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___f_1440_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__23___boxed), 4, 2);
lean_closure_set(v___f_1440_, 0, v___f_1432_);
lean_closure_set(v___f_1440_, 1, v___y_1438_);
v___x_1441_ = lean_box(v___x_1434_);
lean_inc_ref(v___f_1440_);
v___f_1442_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__26___boxed), 8, 5);
lean_closure_set(v___f_1442_, 0, v_connectionLimit_1433_);
lean_closure_set(v___f_1442_, 1, v___x_1441_);
lean_closure_set(v___f_1442_, 2, v___f_1440_);
lean_closure_set(v___f_1442_, 3, v___f_1435_);
lean_closure_set(v___f_1442_, 4, v___f_1440_);
v___x_1443_ = lean_unsigned_to_nat(0u);
v___x_1444_ = lean_box(v___x_1434_);
v___f_1445_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__28___boxed), 6, 4);
lean_closure_set(v___f_1445_, 0, v___f_1442_);
lean_closure_set(v___f_1445_, 1, v___x_1443_);
lean_closure_set(v___f_1445_, 2, v___x_1436_);
lean_closure_set(v___f_1445_, 3, v___x_1444_);
v___x_1446_ = lean_io_promise_new();
v___x_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1446_);
v___x_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
v___x_1449_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1443_, v___x_1434_, v___x_1448_, v___f_1445_);
v___x_1450_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1443_, v___x_1434_, v___x_1449_, v___f_1437_);
return v___x_1450_;
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__29_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1432_ = stack[0].m_obj;
lean_object* v_connectionLimit_1433_ = stack[1].m_obj;
uint8_t v___x_1434_ = stack[2].m_num;
lean_object* v___f_1435_ = stack[3].m_obj;
lean_object* v___x_1436_ = stack[4].m_obj;
lean_object* v___f_1437_ = stack[5].m_obj;
lean_object* v___y_1438_ = stack[6].m_obj;
lean_object* v_res_1451_;
v_res_1451_ = l_Std_Http_Server_serve___redArg___lam__29(v___f_1432_, v_connectionLimit_1433_, v___x_1434_, v___f_1435_, v___x_1436_, v___f_1437_, v___y_1438_);
stack->m_obj
 = v_res_1451_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29___boxed(lean_object* v___f_1452_, lean_object* v_connectionLimit_1453_, lean_object* v___x_1454_, lean_object* v___f_1455_, lean_object* v___x_1456_, lean_object* v___f_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
uint8_t v___x_15151__boxed_1460_; lean_object* v_res_1461_; 
v___x_15151__boxed_1460_ = lean_unbox(v___x_1454_);
v_res_1461_ = l_Std_Http_Server_serve___redArg___lam__29(v___f_1452_, v_connectionLimit_1453_, v___x_15151__boxed_1460_, v___f_1455_, v___x_1456_, v___f_1457_, v___y_1458_);
return v_res_1461_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__30(lean_object* v___f_1466_, lean_object* v___f_1467_, lean_object* v___x_1468_, lean_object* v_inst_1469_, lean_object* v_handler_1470_, lean_object* v_config_1471_, lean_object* v___f_1472_, lean_object* v___f_1473_, lean_object* v___x_1474_, lean_object* v_a_1475_, lean_object* v___f_1476_, lean_object* v___f_1477_, lean_object* v___f_1478_, lean_object* v___f_1479_, lean_object* v___f_1480_, lean_object* v_x_1481_){
_start:
{
if (lean_obj_tag(v_x_1481_) == 0)
{
lean_object* v___x_1483_; 
lean_dec_ref(v___f_1480_);
lean_dec_ref(v___f_1479_);
lean_dec_ref(v___f_1478_);
lean_dec_ref(v___f_1477_);
lean_dec_ref(v___f_1476_);
lean_dec(v_a_1475_);
lean_dec(v___x_1474_);
lean_dec_ref(v___f_1473_);
lean_dec_ref(v___f_1472_);
lean_dec_ref(v_config_1471_);
lean_dec(v_handler_1470_);
lean_dec_ref(v_inst_1469_);
lean_dec_ref(v___x_1468_);
lean_dec_ref(v___f_1467_);
lean_dec_ref(v___f_1466_);
v___x_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1483_, 0, v_x_1481_);
return v___x_1483_;
}
else
{
lean_object* v_a_1484_; lean_object* v_context_1485_; lean_object* v_activeConnections_1486_; lean_object* v_connectionLimit_1487_; lean_object* v_shutdownPromise_1488_; lean_object* v___f_1489_; lean_object* v___f_1490_; lean_object* v___f_1491_; uint8_t v___x_1492_; lean_object* v___x_1493_; lean_object* v___f_1494_; lean_object* v___f_1495_; lean_object* v___x_1496_; lean_object* v___f_1497_; lean_object* v___x_1498_; lean_object* v___f_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v_a_1484_ = lean_ctor_get(v_x_1481_, 0);
lean_inc(v_a_1484_);
v_context_1485_ = lean_ctor_get(v_a_1484_, 0);
lean_inc_ref_n(v_context_1485_, 2);
v_activeConnections_1486_ = lean_ctor_get(v_a_1484_, 1);
v_connectionLimit_1487_ = lean_ctor_get(v_a_1484_, 2);
v_shutdownPromise_1488_ = lean_ctor_get(v_a_1484_, 3);
v___f_1489_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1489_, 0, v_x_1481_);
lean_inc_ref(v_shutdownPromise_1488_);
v___f_1490_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1490_, 0, v_context_1485_);
lean_closure_set(v___f_1490_, 1, v_shutdownPromise_1488_);
v___f_1491_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed), 5, 1);
lean_closure_set(v___f_1491_, 0, v___f_1490_);
v___x_1492_ = 0;
v___x_1493_ = lean_box(0);
v___f_1494_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__30___closed__0));
v___f_1495_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__30___closed__1));
v___x_1496_ = lean_box(v___x_1492_);
lean_inc_ref(v_activeConnections_1486_);
lean_inc_n(v_connectionLimit_1487_, 2);
v___f_1497_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__22___boxed), 23, 20);
lean_closure_set(v___f_1497_, 0, v___f_1494_);
lean_closure_set(v___f_1497_, 1, v___x_1493_);
lean_closure_set(v___f_1497_, 2, v_connectionLimit_1487_);
lean_closure_set(v___f_1497_, 3, v___x_1496_);
lean_closure_set(v___f_1497_, 4, v___f_1466_);
lean_closure_set(v___f_1497_, 5, v___f_1491_);
lean_closure_set(v___f_1497_, 6, v_activeConnections_1486_);
lean_closure_set(v___f_1497_, 7, v___f_1467_);
lean_closure_set(v___f_1497_, 8, v___x_1468_);
lean_closure_set(v___f_1497_, 9, v_inst_1469_);
lean_closure_set(v___f_1497_, 10, v_handler_1470_);
lean_closure_set(v___f_1497_, 11, v_config_1471_);
lean_closure_set(v___f_1497_, 12, v___f_1472_);
lean_closure_set(v___f_1497_, 13, v___f_1473_);
lean_closure_set(v___f_1497_, 14, v___f_1495_);
lean_closure_set(v___f_1497_, 15, v___x_1474_);
lean_closure_set(v___f_1497_, 16, v_a_1475_);
lean_closure_set(v___f_1497_, 17, v___f_1476_);
lean_closure_set(v___f_1497_, 18, v___f_1477_);
lean_closure_set(v___f_1497_, 19, v___f_1478_);
v___x_1498_ = lean_box(v___x_1492_);
v___f_1499_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__29___boxed), 8, 6);
lean_closure_set(v___f_1499_, 0, v___f_1497_);
lean_closure_set(v___f_1499_, 1, v_connectionLimit_1487_);
lean_closure_set(v___f_1499_, 2, v___x_1498_);
lean_closure_set(v___f_1499_, 3, v___f_1479_);
lean_closure_set(v___f_1499_, 4, v___x_1493_);
lean_closure_set(v___f_1499_, 5, v___f_1480_);
v___x_1500_ = lean_box(v___x_1492_);
v___x_1501_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___boxed), 6, 5);
lean_closure_set(v___x_1501_, 0, lean_box(0));
lean_closure_set(v___x_1501_, 1, v_a_1484_);
lean_closure_set(v___x_1501_, 2, v___x_1500_);
lean_closure_set(v___x_1501_, 3, v___f_1499_);
lean_closure_set(v___x_1501_, 4, v_context_1485_);
v___x_1502_ = lean_unsigned_to_nat(0u);
v___x_1503_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1503_, 0, lean_box(0));
lean_closure_set(v___x_1503_, 1, v___x_1501_);
v___x_1504_ = lean_io_as_task(v___x_1503_, v___x_1502_);
lean_dec_ref(v___x_1504_);
v___x_1505_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
v___x_1506_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1502_, v___x_1492_, v___x_1505_, v___f_1489_);
return v___x_1506_;
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__30_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1466_ = stack[0].m_obj;
lean_object* v___f_1467_ = stack[1].m_obj;
lean_object* v___x_1468_ = stack[2].m_obj;
lean_object* v_inst_1469_ = stack[3].m_obj;
lean_object* v_handler_1470_ = stack[4].m_obj;
lean_object* v_config_1471_ = stack[5].m_obj;
lean_object* v___f_1472_ = stack[6].m_obj;
lean_object* v___f_1473_ = stack[7].m_obj;
lean_object* v___x_1474_ = stack[8].m_obj;
lean_object* v_a_1475_ = stack[9].m_obj;
lean_object* v___f_1476_ = stack[10].m_obj;
lean_object* v___f_1477_ = stack[11].m_obj;
lean_object* v___f_1478_ = stack[12].m_obj;
lean_object* v___f_1479_ = stack[13].m_obj;
lean_object* v___f_1480_ = stack[14].m_obj;
lean_object* v_x_1481_ = stack[15].m_obj;
lean_object* v_res_1507_;
v_res_1507_ = l_Std_Http_Server_serve___redArg___lam__30(v___f_1466_, v___f_1467_, v___x_1468_, v_inst_1469_, v_handler_1470_, v_config_1471_, v___f_1472_, v___f_1473_, v___x_1474_, v_a_1475_, v___f_1476_, v___f_1477_, v___f_1478_, v___f_1479_, v___f_1480_, v_x_1481_);
stack->m_obj
 = v_res_1507_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30___boxed(lean_object** _args){
lean_object* v___f_1508_ = _args[0];
lean_object* v___f_1509_ = _args[1];
lean_object* v___x_1510_ = _args[2];
lean_object* v_inst_1511_ = _args[3];
lean_object* v_handler_1512_ = _args[4];
lean_object* v_config_1513_ = _args[5];
lean_object* v___f_1514_ = _args[6];
lean_object* v___f_1515_ = _args[7];
lean_object* v___x_1516_ = _args[8];
lean_object* v_a_1517_ = _args[9];
lean_object* v___f_1518_ = _args[10];
lean_object* v___f_1519_ = _args[11];
lean_object* v___f_1520_ = _args[12];
lean_object* v___f_1521_ = _args[13];
lean_object* v___f_1522_ = _args[14];
lean_object* v_x_1523_ = _args[15];
lean_object* v___y_1524_ = _args[16];
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Std_Http_Server_serve___redArg___lam__30(v___f_1508_, v___f_1509_, v___x_1510_, v_inst_1511_, v_handler_1512_, v_config_1513_, v___f_1514_, v___f_1515_, v___x_1516_, v_a_1517_, v___f_1518_, v___f_1519_, v___f_1520_, v___f_1521_, v___f_1522_, v_x_1523_);
return v_res_1525_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__31(lean_object* v___f_1526_, lean_object* v_config_1527_, lean_object* v_x_1528_){
_start:
{
if (lean_obj_tag(v_x_1528_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1538_; 
lean_dec_ref(v_config_1527_);
lean_dec_ref(v___f_1526_);
v_a_1530_ = lean_ctor_get(v_x_1528_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v_x_1528_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1532_ = v_x_1528_;
v_isShared_1533_ = v_isSharedCheck_1538_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v_x_1528_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1538_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1536_; 
v___x_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
return v___x_1536_;
}
}
}
else
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1555_; 
v_a_1539_ = lean_ctor_get(v_x_1528_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_x_1528_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1541_ = v_x_1528_;
v_isShared_1542_ = v_isSharedCheck_1555_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v_x_1528_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1555_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; lean_object* v_val_1547_; lean_object* v___x_1550_; lean_object* v_a_1551_; lean_object* v___x_1553_; 
v___x_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1543_, 0, v_a_1539_);
v___x_1544_ = lean_unsigned_to_nat(0u);
v___x_1545_ = 0;
v___x_1550_ = l_Std_Http_Server_new(v_config_1527_, v___x_1543_);
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref(v___x_1550_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v_a_1551_);
v___x_1553_ = v___x_1541_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1551_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v___jp_1546_:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1548_, 0, v_val_1547_);
v___x_1549_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1544_, v___x_1545_, v___x_1548_, v___f_1526_);
return v___x_1549_;
}
v_reusejp_1552_:
{
v_val_1547_ = v___x_1553_;
goto v___jp_1546_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__31_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1526_ = stack[0].m_obj;
lean_object* v_config_1527_ = stack[1].m_obj;
lean_object* v_x_1528_ = stack[2].m_obj;
lean_object* v_res_1556_;
v_res_1556_ = l_Std_Http_Server_serve___redArg___lam__31(v___f_1526_, v_config_1527_, v_x_1528_);
stack->m_obj
 = v_res_1556_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31___boxed(lean_object* v___f_1557_, lean_object* v_config_1558_, lean_object* v_x_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Std_Http_Server_serve___redArg___lam__31(v___f_1557_, v_config_1558_, v_x_1559_);
return v_res_1561_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__32(lean_object* v___f_1562_, lean_object* v_a_1563_, lean_object* v_x_1564_){
_start:
{
if (lean_obj_tag(v_x_1564_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1574_; 
lean_dec_ref(v___f_1562_);
v_a_1566_ = lean_ctor_get(v_x_1564_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v_x_1564_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1568_ = v_x_1564_;
v_isShared_1569_ = v_isSharedCheck_1574_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v_x_1564_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1574_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
lean_object* v___x_1572_; 
v___x_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
return v___x_1572_;
}
}
}
else
{
lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1593_; 
v_isSharedCheck_1593_ = !lean_is_exclusive(v_x_1564_);
if (v_isSharedCheck_1593_ == 0)
{
lean_object* v_unused_1594_; 
v_unused_1594_ = lean_ctor_get(v_x_1564_, 0);
lean_dec(v_unused_1594_);
v___x_1576_ = v_x_1564_;
v_isShared_1577_ = v_isSharedCheck_1593_;
goto v_resetjp_1575_;
}
else
{
lean_dec(v_x_1564_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1593_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1578_; uint8_t v___x_1579_; lean_object* v_val_1581_; lean_object* v___x_1584_; 
v___x_1578_ = lean_unsigned_to_nat(0u);
v___x_1579_ = 0;
v___x_1584_ = lean_uv_tcp_getsockname(v_a_1563_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1587_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v_a_1585_);
v___x_1587_ = v___x_1576_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1585_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
v_val_1581_ = v___x_1587_;
goto v___jp_1580_;
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1591_; 
v_a_1589_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1589_);
lean_dec_ref_known(v___x_1584_, 1);
if (v_isShared_1577_ == 0)
{
lean_ctor_set_tag(v___x_1576_, 0);
lean_ctor_set(v___x_1576_, 0, v_a_1589_);
v___x_1591_ = v___x_1576_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1589_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
v_val_1581_ = v___x_1591_;
goto v___jp_1580_;
}
}
v___jp_1580_:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1582_, 0, v_val_1581_);
v___x_1583_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1578_, v___x_1579_, v___x_1582_, v___f_1562_);
return v___x_1583_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__32_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1562_ = stack[0].m_obj;
lean_object* v_a_1563_ = stack[1].m_obj;
lean_object* v_x_1564_ = stack[2].m_obj;
lean_object* v_res_1595_;
v_res_1595_ = l_Std_Http_Server_serve___redArg___lam__32(v___f_1562_, v_a_1563_, v_x_1564_);
stack->m_obj
 = v_res_1595_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32___boxed(lean_object* v___f_1596_, lean_object* v_a_1597_, lean_object* v_x_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Std_Http_Server_serve___redArg___lam__32(v___f_1596_, v_a_1597_, v_x_1598_);
lean_dec(v_a_1597_);
return v_res_1600_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__33(lean_object* v___f_1601_, lean_object* v_a_1602_, lean_object* v_x_1603_){
_start:
{
if (lean_obj_tag(v_x_1603_) == 0)
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1613_; 
lean_dec_ref(v___f_1601_);
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
lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1632_; 
v_isSharedCheck_1632_ = !lean_is_exclusive(v_x_1603_);
if (v_isSharedCheck_1632_ == 0)
{
lean_object* v_unused_1633_; 
v_unused_1633_ = lean_ctor_get(v_x_1603_, 0);
lean_dec(v_unused_1633_);
v___x_1615_ = v_x_1603_;
v_isShared_1616_ = v_isSharedCheck_1632_;
goto v_resetjp_1614_;
}
else
{
lean_dec(v_x_1603_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1632_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1617_; uint8_t v___x_1618_; lean_object* v_val_1620_; lean_object* v___x_1623_; 
v___x_1617_ = lean_unsigned_to_nat(0u);
v___x_1618_ = 0;
v___x_1623_ = lean_uv_tcp_nodelay(v_a_1602_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1626_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1624_);
lean_dec_ref_known(v___x_1623_, 1);
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 0, v_a_1624_);
v___x_1626_ = v___x_1615_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1624_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
v_val_1620_ = v___x_1626_;
goto v___jp_1619_;
}
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; 
v_a_1628_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1628_);
lean_dec_ref_known(v___x_1623_, 1);
if (v_isShared_1616_ == 0)
{
lean_ctor_set_tag(v___x_1615_, 0);
lean_ctor_set(v___x_1615_, 0, v_a_1628_);
v___x_1630_ = v___x_1615_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1628_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
v_val_1620_ = v___x_1630_;
goto v___jp_1619_;
}
}
v___jp_1619_:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1621_, 0, v_val_1620_);
v___x_1622_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1617_, v___x_1618_, v___x_1621_, v___f_1601_);
return v___x_1622_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__33_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1601_ = stack[0].m_obj;
lean_object* v_a_1602_ = stack[1].m_obj;
lean_object* v_x_1603_ = stack[2].m_obj;
lean_object* v_res_1634_;
v_res_1634_ = l_Std_Http_Server_serve___redArg___lam__33(v___f_1601_, v_a_1602_, v_x_1603_);
stack->m_obj
 = v_res_1634_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__33___boxed(lean_object* v___f_1635_, lean_object* v_a_1636_, lean_object* v_x_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Std_Http_Server_serve___redArg___lam__33(v___f_1635_, v_a_1636_, v_x_1637_);
lean_dec(v_a_1636_);
return v_res_1639_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__34(lean_object* v___f_1640_, lean_object* v_a_1641_, uint32_t v_backlog_1642_, lean_object* v_x_1643_){
_start:
{
if (lean_obj_tag(v_x_1643_) == 0)
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1653_; 
lean_dec_ref(v___f_1640_);
v_a_1645_ = lean_ctor_get(v_x_1643_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v_x_1643_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1647_ = v_x_1643_;
v_isShared_1648_ = v_isSharedCheck_1653_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v_x_1643_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1653_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
lean_object* v___x_1651_; 
v___x_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
return v___x_1651_;
}
}
}
else
{
lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1672_; 
v_isSharedCheck_1672_ = !lean_is_exclusive(v_x_1643_);
if (v_isSharedCheck_1672_ == 0)
{
lean_object* v_unused_1673_; 
v_unused_1673_ = lean_ctor_get(v_x_1643_, 0);
lean_dec(v_unused_1673_);
v___x_1655_ = v_x_1643_;
v_isShared_1656_ = v_isSharedCheck_1672_;
goto v_resetjp_1654_;
}
else
{
lean_dec(v_x_1643_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1672_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1657_; uint8_t v___x_1658_; lean_object* v_val_1660_; lean_object* v___x_1663_; 
v___x_1657_ = lean_unsigned_to_nat(0u);
v___x_1658_ = 0;
v___x_1663_ = lean_uv_tcp_listen(v_a_1641_, v_backlog_1642_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1666_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref_known(v___x_1663_, 1);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v_a_1664_);
v___x_1666_ = v___x_1655_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1664_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
v_val_1660_ = v___x_1666_;
goto v___jp_1659_;
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; 
v_a_1668_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1668_);
lean_dec_ref_known(v___x_1663_, 1);
if (v_isShared_1656_ == 0)
{
lean_ctor_set_tag(v___x_1655_, 0);
lean_ctor_set(v___x_1655_, 0, v_a_1668_);
v___x_1670_ = v___x_1655_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
v_val_1660_ = v___x_1670_;
goto v___jp_1659_;
}
}
v___jp_1659_:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1661_, 0, v_val_1660_);
v___x_1662_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1657_, v___x_1658_, v___x_1661_, v___f_1640_);
return v___x_1662_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__34_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1640_ = stack[0].m_obj;
lean_object* v_a_1641_ = stack[1].m_obj;
uint32_t v_backlog_1642_ = stack[2].m_num;
lean_object* v_x_1643_ = stack[3].m_obj;
lean_object* v_res_1674_;
v_res_1674_ = l_Std_Http_Server_serve___redArg___lam__34(v___f_1640_, v_a_1641_, v_backlog_1642_, v_x_1643_);
stack->m_obj
 = v_res_1674_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__34___boxed(lean_object* v___f_1675_, lean_object* v_a_1676_, lean_object* v_backlog_1677_, lean_object* v_x_1678_, lean_object* v___y_1679_){
_start:
{
uint32_t v_backlog_boxed_1680_; lean_object* v_res_1681_; 
v_backlog_boxed_1680_ = lean_unbox_uint32(v_backlog_1677_);
lean_dec(v_backlog_1677_);
v_res_1681_ = l_Std_Http_Server_serve___redArg___lam__34(v___f_1675_, v_a_1676_, v_backlog_boxed_1680_, v_x_1678_);
lean_dec(v_a_1676_);
return v_res_1681_;
}
}
lean_object* l_Std_Http_Server_serve___redArg___lam__35(lean_object* v___f_1682_, lean_object* v___f_1683_, lean_object* v___x_1684_, lean_object* v_inst_1685_, lean_object* v_handler_1686_, lean_object* v_config_1687_, lean_object* v___f_1688_, lean_object* v___f_1689_, lean_object* v___x_1690_, lean_object* v___f_1691_, lean_object* v___f_1692_, lean_object* v___f_1693_, lean_object* v___f_1694_, lean_object* v___f_1695_, uint32_t v_backlog_1696_, lean_object* v_addr_1697_, lean_object* v_x_1698_){
_start:
{
if (lean_obj_tag(v_x_1698_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1708_; 
lean_dec_ref(v___f_1695_);
lean_dec_ref(v___f_1694_);
lean_dec_ref(v___f_1693_);
lean_dec_ref(v___f_1692_);
lean_dec_ref(v___f_1691_);
lean_dec(v___x_1690_);
lean_dec_ref(v___f_1689_);
lean_dec_ref(v___f_1688_);
lean_dec_ref(v_config_1687_);
lean_dec(v_handler_1686_);
lean_dec_ref(v_inst_1685_);
lean_dec_ref(v___x_1684_);
lean_dec_ref(v___f_1683_);
lean_dec_ref(v___f_1682_);
v_a_1700_ = lean_ctor_get(v_x_1698_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_x_1698_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1702_ = v_x_1698_;
v_isShared_1703_ = v_isSharedCheck_1708_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v_x_1698_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1708_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1700_);
v___x_1705_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
lean_object* v___x_1706_; 
v___x_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1705_);
return v___x_1706_;
}
}
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1734_; 
v_a_1709_ = lean_ctor_get(v_x_1698_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_x_1698_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1711_ = v_x_1698_;
v_isShared_1712_ = v_isSharedCheck_1734_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v_x_1698_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1734_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___f_1713_; lean_object* v___f_1714_; lean_object* v___f_1715_; lean_object* v___f_1716_; lean_object* v___x_1717_; lean_object* v___f_1718_; lean_object* v___x_1719_; uint8_t v___x_1720_; lean_object* v_val_1722_; lean_object* v___x_1725_; 
lean_inc_n(v_a_1709_, 4);
lean_inc_ref(v_config_1687_);
v___f_1713_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__30___boxed), 17, 15);
lean_closure_set(v___f_1713_, 0, v___f_1682_);
lean_closure_set(v___f_1713_, 1, v___f_1683_);
lean_closure_set(v___f_1713_, 2, v___x_1684_);
lean_closure_set(v___f_1713_, 3, v_inst_1685_);
lean_closure_set(v___f_1713_, 4, v_handler_1686_);
lean_closure_set(v___f_1713_, 5, v_config_1687_);
lean_closure_set(v___f_1713_, 6, v___f_1688_);
lean_closure_set(v___f_1713_, 7, v___f_1689_);
lean_closure_set(v___f_1713_, 8, v___x_1690_);
lean_closure_set(v___f_1713_, 9, v_a_1709_);
lean_closure_set(v___f_1713_, 10, v___f_1691_);
lean_closure_set(v___f_1713_, 11, v___f_1692_);
lean_closure_set(v___f_1713_, 12, v___f_1693_);
lean_closure_set(v___f_1713_, 13, v___f_1694_);
lean_closure_set(v___f_1713_, 14, v___f_1695_);
v___f_1714_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__31___boxed), 4, 2);
lean_closure_set(v___f_1714_, 0, v___f_1713_);
lean_closure_set(v___f_1714_, 1, v_config_1687_);
v___f_1715_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__32___boxed), 4, 2);
lean_closure_set(v___f_1715_, 0, v___f_1714_);
lean_closure_set(v___f_1715_, 1, v_a_1709_);
v___f_1716_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__33___boxed), 4, 2);
lean_closure_set(v___f_1716_, 0, v___f_1715_);
lean_closure_set(v___f_1716_, 1, v_a_1709_);
v___x_1717_ = lean_box_uint32(v_backlog_1696_);
v___f_1718_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__34___boxed), 5, 3);
lean_closure_set(v___f_1718_, 0, v___f_1716_);
lean_closure_set(v___f_1718_, 1, v_a_1709_);
lean_closure_set(v___f_1718_, 2, v___x_1717_);
v___x_1719_ = lean_unsigned_to_nat(0u);
v___x_1720_ = 0;
v___x_1725_ = lean_uv_tcp_bind(v_a_1709_, v_addr_1697_);
lean_dec(v_a_1709_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1728_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1725_, 1);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 0, v_a_1726_);
v___x_1728_ = v___x_1711_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1726_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
v_val_1722_ = v___x_1728_;
goto v___jp_1721_;
}
}
else
{
lean_object* v_a_1730_; lean_object* v___x_1732_; 
v_a_1730_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1730_);
lean_dec_ref_known(v___x_1725_, 1);
if (v_isShared_1712_ == 0)
{
lean_ctor_set_tag(v___x_1711_, 0);
lean_ctor_set(v___x_1711_, 0, v_a_1730_);
v___x_1732_ = v___x_1711_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1730_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
v_val_1722_ = v___x_1732_;
goto v___jp_1721_;
}
}
v___jp_1721_:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1723_, 0, v_val_1722_);
v___x_1724_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1719_, v___x_1720_, v___x_1723_, v___f_1718_);
return v___x_1724_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg___lam__35_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1682_ = stack[0].m_obj;
lean_object* v___f_1683_ = stack[1].m_obj;
lean_object* v___x_1684_ = stack[2].m_obj;
lean_object* v_inst_1685_ = stack[3].m_obj;
lean_object* v_handler_1686_ = stack[4].m_obj;
lean_object* v_config_1687_ = stack[5].m_obj;
lean_object* v___f_1688_ = stack[6].m_obj;
lean_object* v___f_1689_ = stack[7].m_obj;
lean_object* v___x_1690_ = stack[8].m_obj;
lean_object* v___f_1691_ = stack[9].m_obj;
lean_object* v___f_1692_ = stack[10].m_obj;
lean_object* v___f_1693_ = stack[11].m_obj;
lean_object* v___f_1694_ = stack[12].m_obj;
lean_object* v___f_1695_ = stack[13].m_obj;
uint32_t v_backlog_1696_ = stack[14].m_num;
lean_object* v_addr_1697_ = stack[15].m_obj;
lean_object* v_x_1698_ = stack[16].m_obj;
lean_object* v_res_1735_;
v_res_1735_ = l_Std_Http_Server_serve___redArg___lam__35(v___f_1682_, v___f_1683_, v___x_1684_, v_inst_1685_, v_handler_1686_, v_config_1687_, v___f_1688_, v___f_1689_, v___x_1690_, v___f_1691_, v___f_1692_, v___f_1693_, v___f_1694_, v___f_1695_, v_backlog_1696_, v_addr_1697_, v_x_1698_);
stack->m_obj
 = v_res_1735_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__35___boxed(lean_object** _args){
lean_object* v___f_1736_ = _args[0];
lean_object* v___f_1737_ = _args[1];
lean_object* v___x_1738_ = _args[2];
lean_object* v_inst_1739_ = _args[3];
lean_object* v_handler_1740_ = _args[4];
lean_object* v_config_1741_ = _args[5];
lean_object* v___f_1742_ = _args[6];
lean_object* v___f_1743_ = _args[7];
lean_object* v___x_1744_ = _args[8];
lean_object* v___f_1745_ = _args[9];
lean_object* v___f_1746_ = _args[10];
lean_object* v___f_1747_ = _args[11];
lean_object* v___f_1748_ = _args[12];
lean_object* v___f_1749_ = _args[13];
lean_object* v_backlog_1750_ = _args[14];
lean_object* v_addr_1751_ = _args[15];
lean_object* v_x_1752_ = _args[16];
lean_object* v___y_1753_ = _args[17];
_start:
{
uint32_t v_backlog_boxed_1754_; lean_object* v_res_1755_; 
v_backlog_boxed_1754_ = lean_unbox_uint32(v_backlog_1750_);
lean_dec(v_backlog_1750_);
v_res_1755_ = l_Std_Http_Server_serve___redArg___lam__35(v___f_1736_, v___f_1737_, v___x_1738_, v_inst_1739_, v_handler_1740_, v_config_1741_, v___f_1742_, v___f_1743_, v___x_1744_, v___f_1745_, v___f_1746_, v___f_1747_, v___f_1748_, v___f_1749_, v_backlog_boxed_1754_, v_addr_1751_, v_x_1752_);
lean_dec_ref(v_addr_1751_);
return v_res_1755_;
}
}
lean_object* l_Std_Http_Server_serve___redArg(lean_object* v_inst_1761_, lean_object* v_addr_1762_, lean_object* v_handler_1763_, lean_object* v_config_1764_, uint32_t v_backlog_1765_){
_start:
{
lean_object* v___f_1767_; lean_object* v___f_1768_; lean_object* v___f_1769_; lean_object* v___f_1770_; lean_object* v___f_1771_; lean_object* v___f_1772_; lean_object* v___f_1773_; lean_object* v___f_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___f_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; lean_object* v_val_1782_; lean_object* v___x_1785_; 
v___f_1767_ = ((lean_object*)(l_Std_Http_Server_waitShutdown___closed__0));
v___f_1768_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__0));
v___f_1769_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__1));
v___f_1770_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__2));
v___f_1771_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2));
v___f_1772_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0));
v___f_1773_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__3));
v___f_1774_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__4));
v___x_1775_ = l_Std_Http_instTransportClient;
v___x_1776_ = l_Std_Http_Server_instImpl_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8_;
v___x_1777_ = lean_box_uint32(v_backlog_1765_);
v___f_1778_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__35___boxed), 18, 16);
lean_closure_set(v___f_1778_, 0, v___f_1771_);
lean_closure_set(v___f_1778_, 1, v___f_1770_);
lean_closure_set(v___f_1778_, 2, v___x_1775_);
lean_closure_set(v___f_1778_, 3, v_inst_1761_);
lean_closure_set(v___f_1778_, 4, v_handler_1763_);
lean_closure_set(v___f_1778_, 5, v_config_1764_);
lean_closure_set(v___f_1778_, 6, v___f_1772_);
lean_closure_set(v___f_1778_, 7, v___f_1770_);
lean_closure_set(v___f_1778_, 8, v___x_1776_);
lean_closure_set(v___f_1778_, 9, v___f_1768_);
lean_closure_set(v___f_1778_, 10, v___f_1769_);
lean_closure_set(v___f_1778_, 11, v___f_1773_);
lean_closure_set(v___f_1778_, 12, v___f_1767_);
lean_closure_set(v___f_1778_, 13, v___f_1774_);
lean_closure_set(v___f_1778_, 14, v___x_1777_);
lean_closure_set(v___f_1778_, 15, v_addr_1762_);
v___x_1779_ = lean_unsigned_to_nat(0u);
v___x_1780_ = 0;
v___x_1785_ = lean_uv_tcp_new();
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1785_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1785_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
lean_ctor_set_tag(v___x_1788_, 1);
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
v_val_1782_ = v___x_1791_;
goto v___jp_1781_;
}
}
}
else
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
v_a_1794_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1785_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1785_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
lean_ctor_set_tag(v___x_1796_, 0);
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
v_val_1782_ = v___x_1799_;
goto v___jp_1781_;
}
}
}
v___jp_1781_:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1783_, 0, v_val_1782_);
v___x_1784_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1779_, v___x_1780_, v___x_1783_, v___f_1778_);
return v___x_1784_;
}
}
}
LEAN_EXPORT void l_Std_Http_Server_serve___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1761_ = stack[0].m_obj;
lean_object* v_addr_1762_ = stack[1].m_obj;
lean_object* v_handler_1763_ = stack[2].m_obj;
lean_object* v_config_1764_ = stack[3].m_obj;
uint32_t v_backlog_1765_ = stack[4].m_num;
lean_object* v_res_1802_;
v_res_1802_ = l_Std_Http_Server_serve___redArg(v_inst_1761_, v_addr_1762_, v_handler_1763_, v_config_1764_, v_backlog_1765_);
stack->m_obj
 = v_res_1802_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___boxed(lean_object* v_inst_1803_, lean_object* v_addr_1804_, lean_object* v_handler_1805_, lean_object* v_config_1806_, lean_object* v_backlog_1807_, lean_object* v_a_1808_){
_start:
{
uint32_t v_backlog_boxed_1809_; lean_object* v_res_1810_; 
v_backlog_boxed_1809_ = lean_unbox_uint32(v_backlog_1807_);
lean_dec(v_backlog_1807_);
v_res_1810_ = l_Std_Http_Server_serve___redArg(v_inst_1803_, v_addr_1804_, v_handler_1805_, v_config_1806_, v_backlog_boxed_1809_);
return v_res_1810_;
}
}
lean_object* l_Std_Http_Server_serve(lean_object* v_00_u03c3_1811_, lean_object* v_inst_1812_, lean_object* v_addr_1813_, lean_object* v_handler_1814_, lean_object* v_config_1815_, uint32_t v_backlog_1816_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Std_Http_Server_serve___redArg(v_inst_1812_, v_addr_1813_, v_handler_1814_, v_config_1815_, v_backlog_1816_);
return v___x_1818_;
}
}
LEAN_EXPORT void l_Std_Http_Server_serve_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1812_ = stack[1].m_obj;
lean_object* v_addr_1813_ = stack[2].m_obj;
lean_object* v_handler_1814_ = stack[3].m_obj;
lean_object* v_config_1815_ = stack[4].m_obj;
uint32_t v_backlog_1816_ = stack[5].m_num;
lean_object* v_res_1819_;
v_res_1819_ = l_Std_Http_Server_serve(lean_box(0), v_inst_1812_, v_addr_1813_, v_handler_1814_, v_config_1815_, v_backlog_1816_);
stack->m_obj
 = v_res_1819_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___boxed(lean_object* v_00_u03c3_1820_, lean_object* v_inst_1821_, lean_object* v_addr_1822_, lean_object* v_handler_1823_, lean_object* v_config_1824_, lean_object* v_backlog_1825_, lean_object* v_a_1826_){
_start:
{
uint32_t v_backlog_boxed_1827_; lean_object* v_res_1828_; 
v_backlog_boxed_1827_ = lean_unbox_uint32(v_backlog_1825_);
lean_dec(v_backlog_1825_);
v_res_1828_ = l_Std_Http_Server_serve(v_00_u03c3_1820_, v_inst_1821_, v_addr_1822_, v_handler_1823_, v_config_1824_, v_backlog_boxed_1827_);
return v_res_1828_;
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
