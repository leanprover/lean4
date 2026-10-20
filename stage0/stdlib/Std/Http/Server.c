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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2(lean_object* v_a_136_, lean_object* v_shutdownPromise_137_, lean_object* v_x_138_){
_start:
{
if (lean_obj_tag(v_x_138_) == 0)
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_150_; 
lean_dec_ref(v_shutdownPromise_137_);
v_a_142_ = lean_ctor_get(v_x_138_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v_x_138_);
if (v_isSharedCheck_150_ == 0)
{
v___x_144_ = v_x_138_;
v_isShared_145_ = v_isSharedCheck_150_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v_x_138_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_150_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_142_);
v___x_147_ = v_reuseFailAlloc_149_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
lean_object* v___x_148_; 
v___x_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
return v___x_148_;
}
}
}
else
{
lean_object* v_a_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v_a_151_ = lean_ctor_get(v_x_138_, 0);
lean_inc(v_a_151_);
lean_dec_ref_known(v_x_138_, 1);
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = lean_nat_dec_eq(v_a_136_, v___x_152_);
if (v___x_153_ == 0)
{
lean_dec(v_a_151_);
lean_dec_ref(v_shutdownPromise_137_);
goto v___jp_140_;
}
else
{
uint8_t v___x_154_; 
v___x_154_ = lean_unbox(v_a_151_);
lean_dec(v_a_151_);
if (v___x_154_ == 0)
{
lean_dec_ref(v_shutdownPromise_137_);
goto v___jp_140_;
}
else
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_box(0);
v___x_156_ = l_Std_Channel_send___redArg(v_shutdownPromise_137_, v___x_155_);
lean_dec_ref(v___x_156_);
v___x_157_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_157_;
}
}
}
v___jp_140_:
{
lean_object* v___x_141_; 
v___x_141_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2___boxed(lean_object* v_a_158_, lean_object* v_shutdownPromise_159_, lean_object* v_x_160_, lean_object* v___y_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2(v_a_158_, v_shutdownPromise_159_, v_x_160_);
lean_dec(v_a_158_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3(lean_object* v_context_163_, lean_object* v_shutdownPromise_164_, lean_object* v_x_165_){
_start:
{
if (lean_obj_tag(v_x_165_) == 0)
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_175_; 
lean_dec_ref(v_shutdownPromise_164_);
lean_dec_ref(v_context_163_);
v_a_167_ = lean_ctor_get(v_x_165_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v_x_165_);
if (v_isSharedCheck_175_ == 0)
{
v___x_169_ = v_x_165_;
v_isShared_170_ = v_isSharedCheck_175_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v_x_165_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_175_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_a_167_);
v___x_172_ = v_reuseFailAlloc_174_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_173_; 
v___x_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
return v___x_173_;
}
}
}
else
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_191_; 
v_a_176_ = lean_ctor_get(v_x_165_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v_x_165_);
if (v_isSharedCheck_191_ == 0)
{
v___x_178_ = v_x_165_;
v_isShared_179_ = v_isSharedCheck_191_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v_x_165_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_191_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v_token_180_; lean_object* v___f_181_; lean_object* v___x_182_; uint8_t v___x_183_; uint8_t v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v_token_180_ = lean_ctor_get(v_context_163_, 1);
lean_inc_ref(v_token_180_);
lean_dec_ref(v_context_163_);
v___f_181_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_181_, 0, v_a_176_);
lean_closure_set(v___f_181_, 1, v_shutdownPromise_164_);
v___x_182_ = lean_unsigned_to_nat(0u);
v___x_183_ = 0;
v___x_184_ = l_Std_CancellationToken_isCancelled(v_token_180_);
v___x_185_ = lean_box(v___x_184_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_185_);
v___x_187_ = v___x_178_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_185_);
v___x_187_ = v_reuseFailAlloc_190_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
v___x_189_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_182_, v___x_183_, v___x_188_, v___f_181_);
return v___x_189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed(lean_object* v_context_192_, lean_object* v_shutdownPromise_193_, lean_object* v_x_194_, lean_object* v___y_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3(v_context_192_, v_shutdownPromise_193_, v_x_194_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4(lean_object* v___f_197_, lean_object* v_____r_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v___x_202_; uint8_t v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_202_ = lean_unsigned_to_nat(0u);
v___x_203_ = 0;
v___x_204_ = lean_st_ref_get(v___y_199_);
v___x_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
v___x_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
v___x_207_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_202_, v___x_203_, v___x_206_, v___f_197_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed(lean_object* v___f_208_, lean_object* v_____r_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4(v___f_208_, v_____r_209_, v___y_210_, v___y_211_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5(lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_217_ = lean_st_ref_take(v___y_214_);
v___x_218_ = lean_unsigned_to_nat(1u);
v___x_219_ = lean_nat_sub(v___x_217_, v___x_218_);
lean_dec(v___x_217_);
v___x_220_ = lean_st_ref_put(v___y_214_, v___x_219_);
v___x_221_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5___boxed(lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5(v___y_222_, v___y_223_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6(lean_object* v___x_226_, lean_object* v___f_227_, lean_object* v___f_228_, lean_object* v___f_229_, lean_object* v___f_230_, lean_object* v_activeConnections_231_, lean_object* v_____r_232_, lean_object* v___y_233_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_2168__overap_236_; lean_object* v___x_237_; 
lean_inc_ref(v___x_226_);
v___x_235_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_235_, 0, lean_box(0));
lean_closure_set(v___x_235_, 1, lean_box(0));
lean_closure_set(v___x_235_, 2, v___x_226_);
lean_closure_set(v___x_235_, 3, lean_box(0));
lean_closure_set(v___x_235_, 4, lean_box(0));
lean_closure_set(v___x_235_, 5, v___f_227_);
lean_closure_set(v___x_235_, 6, v___f_228_);
v___x_2168__overap_236_ = l_Std_Mutex_atomically___redArg(v___x_226_, v___f_229_, v___f_230_, v_activeConnections_231_, v___x_235_);
lean_inc_ref(v___y_233_);
v___x_237_ = lean_apply_2(v___x_2168__overap_236_, v___y_233_, lean_box(0));
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed(lean_object* v___x_238_, lean_object* v___f_239_, lean_object* v___f_240_, lean_object* v___f_241_, lean_object* v___f_242_, lean_object* v_activeConnections_243_, lean_object* v_____r_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6(v___x_238_, v___f_239_, v___f_240_, v___f_241_, v___f_242_, v_activeConnections_243_, v_____r_244_, v___y_245_);
lean_dec_ref(v___y_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7(lean_object* v___f_248_, lean_object* v_a_249_, lean_object* v_x_250_){
_start:
{
if (lean_obj_tag(v_x_250_) == 0)
{
lean_object* v___x_252_; 
lean_dec_ref(v___f_248_);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v_x_250_);
return v___x_252_;
}
else
{
lean_object* v_a_253_; lean_object* v___x_254_; 
v_a_253_ = lean_ctor_get(v_x_250_, 0);
lean_inc(v_a_253_);
lean_dec_ref_known(v_x_250_, 1);
lean_inc_ref(v_a_249_);
v___x_254_ = lean_apply_3(v___f_248_, v_a_253_, v_a_249_, lean_box(0));
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed(lean_object* v___f_255_, lean_object* v_a_256_, lean_object* v_x_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7(v___f_255_, v_a_256_, v_x_257_);
lean_dec_ref(v_a_256_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8(uint8_t v_releaseConnectionPermit_260_, lean_object* v___f_261_, lean_object* v_a_262_, lean_object* v_connectionLimit_263_, lean_object* v___f_264_, lean_object* v_opt_265_){
_start:
{
if (v_releaseConnectionPermit_260_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec_ref(v___f_264_);
lean_dec(v_connectionLimit_263_);
v___x_267_ = lean_box(0);
lean_inc_ref(v_a_262_);
v___x_268_ = lean_apply_3(v___f_261_, v___x_267_, v_a_262_, lean_box(0));
return v___x_268_;
}
else
{
if (lean_obj_tag(v_connectionLimit_263_) == 1)
{
lean_object* v_val_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_281_; 
lean_dec_ref(v___f_261_);
v_val_269_ = lean_ctor_get(v_connectionLimit_263_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v_connectionLimit_263_);
if (v_isSharedCheck_281_ == 0)
{
v___x_271_ = v_connectionLimit_263_;
v_isShared_272_ = v_isSharedCheck_281_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_val_269_);
lean_dec(v_connectionLimit_263_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_281_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; uint8_t v___x_274_; lean_object* v___x_275_; lean_object* v___x_277_; 
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = 0;
v___x_275_ = l_Std_Semaphore_release(v_val_269_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_275_);
v___x_277_ = v___x_271_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_275_);
v___x_277_ = v_reuseFailAlloc_280_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
v___x_279_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_273_, v___x_274_, v___x_278_, v___f_264_);
return v___x_279_;
}
}
}
else
{
lean_object* v___x_282_; lean_object* v___x_283_; 
lean_dec_ref(v___f_264_);
lean_dec(v_connectionLimit_263_);
v___x_282_ = lean_box(0);
lean_inc_ref(v_a_262_);
v___x_283_ = lean_apply_3(v___f_261_, v___x_282_, v_a_262_, lean_box(0));
return v___x_283_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed(lean_object* v_releaseConnectionPermit_284_, lean_object* v___f_285_, lean_object* v_a_286_, lean_object* v_connectionLimit_287_, lean_object* v___f_288_, lean_object* v_opt_289_, lean_object* v___y_290_){
_start:
{
uint8_t v_releaseConnectionPermit_boxed_291_; lean_object* v_res_292_; 
v_releaseConnectionPermit_boxed_291_ = lean_unbox(v_releaseConnectionPermit_284_);
v_res_292_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8(v_releaseConnectionPermit_boxed_291_, v___f_285_, v_a_286_, v_connectionLimit_287_, v___f_288_, v_opt_289_);
lean_dec(v_opt_289_);
lean_dec_ref(v_a_286_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9(lean_object* v___f_293_, lean_object* v_action_294_, lean_object* v_a_295_, lean_object* v___f_296_, lean_object* v_x_297_){
_start:
{
if (lean_obj_tag(v_x_297_) == 0)
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_307_; 
lean_dec_ref(v___f_296_);
lean_dec_ref(v_action_294_);
lean_dec(v___f_293_);
v_a_299_ = lean_ctor_get(v_x_297_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v_x_297_);
if (v_isSharedCheck_307_ == 0)
{
v___x_301_ = v_x_297_;
v_isShared_302_ = v_isSharedCheck_307_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v_x_297_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_307_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_306_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
lean_object* v___x_305_; 
v___x_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
return v___x_305_;
}
}
}
else
{
lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___y_314_; 
lean_dec_ref_known(v_x_297_, 1);
v___x_308_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_308_, 0, lean_box(0));
lean_closure_set(v___x_308_, 1, lean_box(0));
lean_closure_set(v___x_308_, 2, lean_box(0));
lean_closure_set(v___x_308_, 3, v___f_293_);
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = 0;
lean_inc_ref(v_a_295_);
v___x_311_ = lean_apply_1(v_action_294_, v_a_295_);
v___x_312_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_311_, v___f_296_, v___x_309_, v___x_310_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_316_; 
lean_dec_ref(v___x_308_);
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
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_342_; 
v_a_334_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_342_ == 0)
{
v___x_336_ = v___x_312_;
v_isShared_337_ = v_isSharedCheck_342_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_312_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_342_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_338_ = lean_task_map(v___x_308_, v_a_334_, v___x_309_, v___x_310_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_338_);
v___x_340_ = v___x_336_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_338_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed(lean_object* v___f_343_, lean_object* v_action_344_, lean_object* v_a_345_, lean_object* v___f_346_, lean_object* v_x_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9(v___f_343_, v_action_344_, v_a_345_, v___f_346_, v_x_347_);
lean_dec_ref(v_a_345_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg(lean_object* v_s_359_, uint8_t v_releaseConnectionPermit_360_, lean_object* v_action_361_, lean_object* v_a_362_){
_start:
{
lean_object* v___x_364_; lean_object* v_context_365_; lean_object* v_activeConnections_366_; lean_object* v_connectionLimit_367_; lean_object* v_shutdownPromise_368_; lean_object* v___f_369_; lean_object* v___f_370_; lean_object* v___f_371_; lean_object* v___f_372_; lean_object* v___f_373_; lean_object* v___f_374_; lean_object* v___f_375_; lean_object* v___f_376_; lean_object* v___f_377_; lean_object* v___x_378_; lean_object* v___f_379_; lean_object* v___f_380_; lean_object* v___x_381_; uint8_t v___x_382_; lean_object* v___x_1921__overap_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_364_ = l_Std_Async_ContextAsync_instMonad;
v_context_365_ = lean_ctor_get(v_s_359_, 0);
lean_inc_ref(v_context_365_);
v_activeConnections_366_ = lean_ctor_get(v_s_359_, 1);
lean_inc_ref_n(v_activeConnections_366_, 2);
v_connectionLimit_367_ = lean_ctor_get(v_s_359_, 2);
lean_inc(v_connectionLimit_367_);
v_shutdownPromise_368_ = lean_ctor_get(v_s_359_, 3);
lean_inc_ref(v_shutdownPromise_368_);
lean_dec_ref(v_s_359_);
v___f_369_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0));
v___f_370_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1));
v___f_371_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_371_, 0, v_context_365_);
lean_closure_set(v___f_371_, 1, v_shutdownPromise_368_);
v___f_372_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed), 5, 1);
lean_closure_set(v___f_372_, 0, v___f_371_);
v___f_373_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2));
v___f_374_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5));
v___f_375_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6));
v___f_376_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed), 9, 6);
lean_closure_set(v___f_376_, 0, v___x_364_);
lean_closure_set(v___f_376_, 1, v___f_373_);
lean_closure_set(v___f_376_, 2, v___f_372_);
lean_closure_set(v___f_376_, 3, v___f_374_);
lean_closure_set(v___f_376_, 4, v___f_375_);
lean_closure_set(v___f_376_, 5, v_activeConnections_366_);
lean_inc_ref_n(v_a_362_, 4);
lean_inc_ref(v___f_376_);
v___f_377_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_377_, 0, v___f_376_);
lean_closure_set(v___f_377_, 1, v_a_362_);
v___x_378_ = lean_box(v_releaseConnectionPermit_360_);
v___f_379_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed), 7, 5);
lean_closure_set(v___f_379_, 0, v___x_378_);
lean_closure_set(v___f_379_, 1, v___f_376_);
lean_closure_set(v___f_379_, 2, v_a_362_);
lean_closure_set(v___f_379_, 3, v_connectionLimit_367_);
lean_closure_set(v___f_379_, 4, v___f_377_);
v___f_380_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed), 6, 4);
lean_closure_set(v___f_380_, 0, v___f_370_);
lean_closure_set(v___f_380_, 1, v_action_361_);
lean_closure_set(v___f_380_, 2, v_a_362_);
lean_closure_set(v___f_380_, 3, v___f_379_);
v___x_381_ = lean_unsigned_to_nat(0u);
v___x_382_ = 0;
v___x_1921__overap_383_ = l_Std_Mutex_atomically___redArg(v___x_364_, v___f_374_, v___f_375_, v_activeConnections_366_, v___f_369_);
v___x_384_ = lean_apply_2(v___x_1921__overap_383_, v_a_362_, lean_box(0));
v___x_385_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_381_, v___x_382_, v___x_384_, v___f_380_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___boxed(lean_object* v_s_386_, lean_object* v_releaseConnectionPermit_387_, lean_object* v_action_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
uint8_t v_releaseConnectionPermit_boxed_391_; lean_object* v_res_392_; 
v_releaseConnectionPermit_boxed_391_ = lean_unbox(v_releaseConnectionPermit_387_);
v_res_392_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg(v_s_386_, v_releaseConnectionPermit_boxed_391_, v_action_388_, v_a_389_);
lean_dec_ref(v_a_389_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation(lean_object* v_00_u03b1_393_, lean_object* v_s_394_, uint8_t v_releaseConnectionPermit_395_, lean_object* v_action_396_, lean_object* v_a_397_){
_start:
{
lean_object* v___x_399_; lean_object* v_context_400_; lean_object* v_activeConnections_401_; lean_object* v_connectionLimit_402_; lean_object* v_shutdownPromise_403_; lean_object* v___f_404_; lean_object* v___f_405_; lean_object* v___f_406_; lean_object* v___f_407_; lean_object* v___f_408_; lean_object* v___f_409_; lean_object* v___f_410_; lean_object* v___f_411_; lean_object* v___f_412_; lean_object* v___x_413_; lean_object* v___f_414_; lean_object* v___f_415_; lean_object* v___x_416_; uint8_t v___x_417_; lean_object* v___x_2073__overap_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_399_ = l_Std_Async_ContextAsync_instMonad;
v_context_400_ = lean_ctor_get(v_s_394_, 0);
lean_inc_ref(v_context_400_);
v_activeConnections_401_ = lean_ctor_get(v_s_394_, 1);
lean_inc_ref_n(v_activeConnections_401_, 2);
v_connectionLimit_402_ = lean_ctor_get(v_s_394_, 2);
lean_inc(v_connectionLimit_402_);
v_shutdownPromise_403_ = lean_ctor_get(v_s_394_, 3);
lean_inc_ref(v_shutdownPromise_403_);
lean_dec_ref(v_s_394_);
v___f_404_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0));
v___f_405_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1));
v___f_406_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_406_, 0, v_context_400_);
lean_closure_set(v___f_406_, 1, v_shutdownPromise_403_);
v___f_407_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed), 5, 1);
lean_closure_set(v___f_407_, 0, v___f_406_);
v___f_408_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2));
v___f_409_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5));
v___f_410_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6));
v___f_411_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed), 9, 6);
lean_closure_set(v___f_411_, 0, v___x_399_);
lean_closure_set(v___f_411_, 1, v___f_408_);
lean_closure_set(v___f_411_, 2, v___f_407_);
lean_closure_set(v___f_411_, 3, v___f_409_);
lean_closure_set(v___f_411_, 4, v___f_410_);
lean_closure_set(v___f_411_, 5, v_activeConnections_401_);
lean_inc_ref_n(v_a_397_, 4);
lean_inc_ref(v___f_411_);
v___f_412_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_412_, 0, v___f_411_);
lean_closure_set(v___f_412_, 1, v_a_397_);
v___x_413_ = lean_box(v_releaseConnectionPermit_395_);
v___f_414_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed), 7, 5);
lean_closure_set(v___f_414_, 0, v___x_413_);
lean_closure_set(v___f_414_, 1, v___f_411_);
lean_closure_set(v___f_414_, 2, v_a_397_);
lean_closure_set(v___f_414_, 3, v_connectionLimit_402_);
lean_closure_set(v___f_414_, 4, v___f_412_);
v___f_415_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed), 6, 4);
lean_closure_set(v___f_415_, 0, v___f_405_);
lean_closure_set(v___f_415_, 1, v_action_396_);
lean_closure_set(v___f_415_, 2, v_a_397_);
lean_closure_set(v___f_415_, 3, v___f_414_);
v___x_416_ = lean_unsigned_to_nat(0u);
v___x_417_ = 0;
v___x_2073__overap_418_ = l_Std_Mutex_atomically___redArg(v___x_399_, v___f_409_, v___f_410_, v_activeConnections_401_, v___f_404_);
v___x_419_ = lean_apply_2(v___x_2073__overap_418_, v_a_397_, lean_box(0));
v___x_420_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_416_, v___x_417_, v___x_419_, v___f_415_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___boxed(lean_object* v_00_u03b1_421_, lean_object* v_s_422_, lean_object* v_releaseConnectionPermit_423_, lean_object* v_action_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
uint8_t v_releaseConnectionPermit_boxed_427_; lean_object* v_res_428_; 
v_releaseConnectionPermit_boxed_427_ = lean_unbox(v_releaseConnectionPermit_423_);
v_res_428_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation(v_00_u03b1_421_, v_s_422_, v_releaseConnectionPermit_boxed_427_, v_action_424_, v_a_425_);
lean_dec_ref(v_a_425_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1(lean_object* v_x_429_){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_431_, 0, v_x_429_);
v___x_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1___boxed(lean_object* v_x_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Std_Http_Server_serve___redArg___lam__1(v_x_434_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__0(lean_object* v_x_441_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__0___closed__1));
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__0___boxed(lean_object* v_x_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Std_Http_Server_serve___redArg___lam__0(v_x_444_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2(lean_object* v_x_447_){
_start:
{
lean_object* v_fst_448_; 
v_fst_448_ = lean_ctor_get(v_x_447_, 0);
lean_inc(v_fst_448_);
return v_fst_448_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2___boxed(lean_object* v_x_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Std_Http_Server_serve___redArg___lam__2(v_x_449_);
lean_dec_ref(v_x_449_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6(lean_object* v_x_451_){
_start:
{
if (lean_obj_tag(v_x_451_) == 0)
{
lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_461_; 
v_a_453_ = lean_ctor_get(v_x_451_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v_x_451_);
if (v_isSharedCheck_461_ == 0)
{
v___x_455_ = v_x_451_;
v_isShared_456_ = v_isSharedCheck_461_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v_x_451_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_461_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_453_);
v___x_458_ = v_reuseFailAlloc_460_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_459_; 
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
return v___x_459_;
}
}
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_472_; 
v_a_462_ = lean_ctor_get(v_x_451_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v_x_451_);
if (v_isSharedCheck_472_ == 0)
{
v___x_464_ = v_x_451_;
v_isShared_465_ = v_isSharedCheck_472_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v_x_451_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_472_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v_token_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v_token_466_ = lean_ctor_get(v_a_462_, 1);
lean_inc_ref(v_token_466_);
lean_dec(v_a_462_);
v___x_467_ = l_Std_CancellationToken_selector(v_token_466_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_467_);
v___x_469_ = v___x_464_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_471_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; 
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
return v___x_470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6___boxed(lean_object* v_x_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Std_Http_Server_serve___redArg___lam__6(v_x_473_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3(lean_object* v_x_476_){
_start:
{
if (lean_obj_tag(v_x_476_) == 0)
{
lean_object* v___x_478_; 
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v_x_476_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; 
lean_dec_ref_known(v_x_476_, 1);
v___x_479_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_479_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3___boxed(lean_object* v_x_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_Http_Server_serve___redArg___lam__3(v_x_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4(lean_object* v_x_483_, lean_object* v_x_484_){
_start:
{
if (lean_obj_tag(v_x_484_) == 0)
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_494_; 
lean_dec_ref(v_x_483_);
v_a_486_ = lean_ctor_get(v_x_484_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v_x_484_);
if (v_isSharedCheck_494_ == 0)
{
v___x_488_ = v_x_484_;
v_isShared_489_ = v_isSharedCheck_494_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v_x_484_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_494_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_493_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_492_; 
v___x_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
return v___x_492_;
}
}
}
else
{
lean_object* v___x_495_; 
lean_dec_ref_known(v_x_484_, 1);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v_x_483_);
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4___boxed(lean_object* v_x_496_, lean_object* v_x_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Std_Http_Server_serve___redArg___lam__4(v_x_496_, v_x_497_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9(lean_object* v___x_500_, lean_object* v_____r_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_500_);
v___x_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
v___x_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9___boxed(lean_object* v___x_507_, lean_object* v_____r_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Std_Http_Server_serve___redArg___lam__9(v___x_507_, v_____r_508_, v___y_509_);
lean_dec_ref(v___y_509_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5(lean_object* v___x_512_, lean_object* v_x_513_){
_start:
{
if (lean_obj_tag(v_x_513_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_523_; 
v_a_515_ = lean_ctor_get(v_x_513_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v_x_513_);
if (v_isSharedCheck_523_ == 0)
{
v___x_517_ = v_x_513_;
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v_x_513_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_515_);
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
else
{
lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_532_; 
v_isSharedCheck_532_ = !lean_is_exclusive(v_x_513_);
if (v_isSharedCheck_532_ == 0)
{
lean_object* v_unused_533_; 
v_unused_533_ = lean_ctor_get(v_x_513_, 0);
lean_dec(v_unused_533_);
v___x_525_ = v_x_513_;
v_isShared_526_ = v_isSharedCheck_532_;
goto v_resetjp_524_;
}
else
{
lean_dec(v_x_513_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_532_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_512_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_527_);
v___x_529_ = v___x_525_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_531_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
lean_object* v___x_530_; 
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5___boxed(lean_object* v___x_534_, lean_object* v_x_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Std_Http_Server_serve___redArg___lam__5(v___x_534_, v_x_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7(lean_object* v___f_538_, lean_object* v___y_539_, lean_object* v_x_540_){
_start:
{
if (lean_obj_tag(v_x_540_) == 0)
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_550_; 
lean_dec_ref(v___f_538_);
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
lean_object* v_a_551_; lean_object* v___x_552_; 
v_a_551_ = lean_ctor_get(v_x_540_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v_x_540_, 1);
lean_inc_ref(v___y_539_);
v___x_552_ = lean_apply_3(v___f_538_, v_a_551_, v___y_539_, lean_box(0));
return v___x_552_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7___boxed(lean_object* v___f_553_, lean_object* v___y_554_, lean_object* v_x_555_, lean_object* v___y_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Std_Http_Server_serve___redArg___lam__7(v___f_553_, v___y_554_, v_x_555_);
lean_dec_ref(v___y_554_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10(lean_object* v___f_558_, lean_object* v_a_559_, lean_object* v_x_560_){
_start:
{
if (lean_obj_tag(v_x_560_) == 0)
{
lean_object* v___x_562_; 
lean_dec_ref(v_a_559_);
lean_dec_ref(v___f_558_);
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v_x_560_);
return v___x_562_;
}
else
{
lean_object* v_a_563_; lean_object* v___x_564_; 
v_a_563_ = lean_ctor_get(v_x_560_, 0);
lean_inc(v_a_563_);
lean_dec_ref_known(v_x_560_, 1);
v___x_564_ = lean_apply_3(v___f_558_, v_a_563_, v_a_559_, lean_box(0));
return v___x_564_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10___boxed(lean_object* v___f_565_, lean_object* v_a_566_, lean_object* v_x_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Std_Http_Server_serve___redArg___lam__10(v___f_565_, v_a_566_, v_x_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8(uint8_t v_permitAcquired_570_, lean_object* v___f_571_, lean_object* v___x_572_, lean_object* v_a_573_, lean_object* v_connectionLimit_574_, lean_object* v___x_575_, uint8_t v___x_576_, lean_object* v___f_577_, lean_object* v_opt_578_){
_start:
{
if (v_permitAcquired_570_ == 0)
{
lean_object* v___x_580_; 
lean_dec_ref(v___f_577_);
lean_dec(v___x_575_);
lean_dec(v_connectionLimit_574_);
v___x_580_ = lean_apply_3(v___f_571_, v___x_572_, v_a_573_, lean_box(0));
return v___x_580_;
}
else
{
if (lean_obj_tag(v_connectionLimit_574_) == 1)
{
lean_object* v_val_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_591_; 
lean_dec_ref(v_a_573_);
lean_dec_ref(v___f_571_);
v_val_581_ = lean_ctor_get(v_connectionLimit_574_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v_connectionLimit_574_);
if (v_isSharedCheck_591_ == 0)
{
v___x_583_ = v_connectionLimit_574_;
v_isShared_584_ = v_isSharedCheck_591_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_val_581_);
lean_dec(v_connectionLimit_574_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_591_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_585_ = l_Std_Semaphore_release(v_val_581_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_585_);
v___x_587_ = v___x_583_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_585_);
v___x_587_ = v_reuseFailAlloc_590_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
v___x_589_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_575_, v___x_576_, v___x_588_, v___f_577_);
return v___x_589_;
}
}
}
else
{
lean_object* v___x_592_; 
lean_dec_ref(v___f_577_);
lean_dec(v___x_575_);
lean_dec(v_connectionLimit_574_);
v___x_592_ = lean_apply_3(v___f_571_, v___x_572_, v_a_573_, lean_box(0));
return v___x_592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8___boxed(lean_object* v_permitAcquired_593_, lean_object* v___f_594_, lean_object* v___x_595_, lean_object* v_a_596_, lean_object* v_connectionLimit_597_, lean_object* v___x_598_, lean_object* v___x_599_, lean_object* v___f_600_, lean_object* v_opt_601_, lean_object* v___y_602_){
_start:
{
uint8_t v_permitAcquired_boxed_603_; uint8_t v___x_13068__boxed_604_; lean_object* v_res_605_; 
v_permitAcquired_boxed_603_ = lean_unbox(v_permitAcquired_593_);
v___x_13068__boxed_604_ = lean_unbox(v___x_599_);
v_res_605_ = l_Std_Http_Server_serve___redArg___lam__8(v_permitAcquired_boxed_603_, v___f_594_, v___x_595_, v_a_596_, v_connectionLimit_597_, v___x_598_, v___x_13068__boxed_604_, v___f_600_, v_opt_601_);
lean_dec(v_opt_601_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11(lean_object* v___f_606_, lean_object* v___x_607_, lean_object* v_inst_608_, lean_object* v_val_609_, lean_object* v_handler_610_, lean_object* v_config_611_, lean_object* v_extensions_612_, lean_object* v_a_613_, lean_object* v___f_614_, lean_object* v___x_615_, uint8_t v___x_616_, lean_object* v_x_617_){
_start:
{
if (lean_obj_tag(v_x_617_) == 0)
{
lean_object* v___x_619_; 
lean_dec(v___x_615_);
lean_dec_ref(v___f_614_);
lean_dec_ref(v_a_613_);
lean_dec(v_extensions_612_);
lean_dec_ref(v_config_611_);
lean_dec(v_handler_610_);
lean_dec(v_val_609_);
lean_dec_ref(v_inst_608_);
lean_dec_ref(v___x_607_);
lean_dec_ref(v___f_606_);
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v_x_617_);
return v___x_619_;
}
else
{
lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_658_; 
v_isSharedCheck_658_ = !lean_is_exclusive(v_x_617_);
if (v_isSharedCheck_658_ == 0)
{
lean_object* v_unused_659_; 
v_unused_659_ = lean_ctor_get(v_x_617_, 0);
lean_dec(v_unused_659_);
v___x_621_ = v_x_617_;
v_isShared_622_ = v_isSharedCheck_658_;
goto v_resetjp_620_;
}
else
{
lean_dec(v_x_617_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_658_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___y_627_; 
v___x_623_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_623_, 0, lean_box(0));
lean_closure_set(v___x_623_, 1, lean_box(0));
lean_closure_set(v___x_623_, 2, lean_box(0));
lean_closure_set(v___x_623_, 3, v___f_606_);
v___x_624_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___boxed), 10, 9);
lean_closure_set(v___x_624_, 0, lean_box(0));
lean_closure_set(v___x_624_, 1, lean_box(0));
lean_closure_set(v___x_624_, 2, v___x_607_);
lean_closure_set(v___x_624_, 3, v_inst_608_);
lean_closure_set(v___x_624_, 4, v_val_609_);
lean_closure_set(v___x_624_, 5, v_handler_610_);
lean_closure_set(v___x_624_, 6, v_config_611_);
lean_closure_set(v___x_624_, 7, v_extensions_612_);
lean_closure_set(v___x_624_, 8, v_a_613_);
lean_inc(v___x_615_);
v___x_625_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_624_, v___f_614_, v___x_615_, v___x_616_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_631_; 
lean_dec_ref(v___x_623_);
lean_dec(v___x_615_);
v_a_631_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_a_631_);
lean_dec_ref_known(v___x_625_, 1);
if (lean_obj_tag(v_a_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
v_a_632_ = lean_ctor_get(v_a_631_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v_a_631_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v_a_631_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v_a_631_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
v___y_627_ = v___x_637_;
goto v___jp_626_;
}
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_648_; 
v_a_640_ = lean_ctor_get(v_a_631_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v_a_631_);
if (v_isSharedCheck_648_ == 0)
{
v___x_642_ = v_a_631_;
v_isShared_643_ = v_isSharedCheck_648_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v_a_631_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_648_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v_fst_644_; lean_object* v___x_646_; 
v_fst_644_ = lean_ctor_get(v_a_640_, 0);
lean_inc(v_fst_644_);
lean_dec(v_a_640_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v_fst_644_);
v___x_646_ = v___x_642_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_fst_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
v___y_627_ = v___x_646_;
goto v___jp_626_;
}
}
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_657_; 
lean_del_object(v___x_621_);
v_a_649_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_657_ == 0)
{
v___x_651_ = v___x_625_;
v_isShared_652_ = v_isSharedCheck_657_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_625_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_657_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_653_ = lean_task_map(v___x_623_, v_a_649_, v___x_615_, v___x_616_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v___x_653_);
v___x_655_ = v___x_651_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_653_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
v___jp_626_:
{
lean_object* v___x_629_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set_tag(v___x_621_, 0);
lean_ctor_set(v___x_621_, 0, v___y_627_);
v___x_629_ = v___x_621_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___y_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11___boxed(lean_object* v___f_660_, lean_object* v___x_661_, lean_object* v_inst_662_, lean_object* v_val_663_, lean_object* v_handler_664_, lean_object* v_config_665_, lean_object* v_extensions_666_, lean_object* v_a_667_, lean_object* v___f_668_, lean_object* v___x_669_, lean_object* v___x_670_, lean_object* v_x_671_, lean_object* v___y_672_){
_start:
{
uint8_t v___x_13118__boxed_673_; lean_object* v_res_674_; 
v___x_13118__boxed_673_ = lean_unbox(v___x_670_);
v_res_674_ = l_Std_Http_Server_serve___redArg___lam__11(v___f_660_, v___x_661_, v_inst_662_, v_val_663_, v_handler_664_, v_config_665_, v_extensions_666_, v_a_667_, v___f_668_, v___x_669_, v___x_13118__boxed_673_, v_x_671_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12(lean_object* v___f_675_, lean_object* v___f_676_, lean_object* v_activeConnections_677_, lean_object* v_a_678_, uint8_t v_permitAcquired_679_, lean_object* v___x_680_, lean_object* v_connectionLimit_681_, lean_object* v___x_682_, uint8_t v___x_683_, lean_object* v___f_684_, lean_object* v___x_685_, lean_object* v_inst_686_, lean_object* v_val_687_, lean_object* v_handler_688_, lean_object* v_config_689_, lean_object* v_extensions_690_, lean_object* v___f_691_){
_start:
{
lean_object* v___x_693_; lean_object* v___f_694_; lean_object* v___f_695_; lean_object* v___f_696_; lean_object* v___f_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___f_700_; lean_object* v___x_701_; lean_object* v___f_702_; lean_object* v___x_12285__overap_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_693_ = l_Std_Async_ContextAsync_instMonad;
v___f_694_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5));
v___f_695_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6));
lean_inc_ref(v_activeConnections_677_);
v___f_696_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed), 9, 6);
lean_closure_set(v___f_696_, 0, v___x_693_);
lean_closure_set(v___f_696_, 1, v___f_675_);
lean_closure_set(v___f_696_, 2, v___f_676_);
lean_closure_set(v___f_696_, 3, v___f_694_);
lean_closure_set(v___f_696_, 4, v___f_695_);
lean_closure_set(v___f_696_, 5, v_activeConnections_677_);
lean_inc_ref_n(v_a_678_, 3);
lean_inc_ref(v___f_696_);
v___f_697_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__10___boxed), 4, 2);
lean_closure_set(v___f_697_, 0, v___f_696_);
lean_closure_set(v___f_697_, 1, v_a_678_);
v___x_698_ = lean_box(v_permitAcquired_679_);
v___x_699_ = lean_box(v___x_683_);
lean_inc_n(v___x_682_, 2);
v___f_700_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__8___boxed), 10, 8);
lean_closure_set(v___f_700_, 0, v___x_698_);
lean_closure_set(v___f_700_, 1, v___f_696_);
lean_closure_set(v___f_700_, 2, v___x_680_);
lean_closure_set(v___f_700_, 3, v_a_678_);
lean_closure_set(v___f_700_, 4, v_connectionLimit_681_);
lean_closure_set(v___f_700_, 5, v___x_682_);
lean_closure_set(v___f_700_, 6, v___x_699_);
lean_closure_set(v___f_700_, 7, v___f_697_);
v___x_701_ = lean_box(v___x_683_);
v___f_702_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__11___boxed), 13, 11);
lean_closure_set(v___f_702_, 0, v___f_684_);
lean_closure_set(v___f_702_, 1, v___x_685_);
lean_closure_set(v___f_702_, 2, v_inst_686_);
lean_closure_set(v___f_702_, 3, v_val_687_);
lean_closure_set(v___f_702_, 4, v_handler_688_);
lean_closure_set(v___f_702_, 5, v_config_689_);
lean_closure_set(v___f_702_, 6, v_extensions_690_);
lean_closure_set(v___f_702_, 7, v_a_678_);
lean_closure_set(v___f_702_, 8, v___f_700_);
lean_closure_set(v___f_702_, 9, v___x_682_);
lean_closure_set(v___f_702_, 10, v___x_701_);
v___x_12285__overap_703_ = l_Std_Mutex_atomically___redArg(v___x_693_, v___f_694_, v___f_695_, v_activeConnections_677_, v___f_691_);
v___x_704_ = lean_apply_2(v___x_12285__overap_703_, v_a_678_, lean_box(0));
v___x_705_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_682_, v___x_683_, v___x_704_, v___f_702_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12___boxed(lean_object** _args){
lean_object* v___f_706_ = _args[0];
lean_object* v___f_707_ = _args[1];
lean_object* v_activeConnections_708_ = _args[2];
lean_object* v_a_709_ = _args[3];
lean_object* v_permitAcquired_710_ = _args[4];
lean_object* v___x_711_ = _args[5];
lean_object* v_connectionLimit_712_ = _args[6];
lean_object* v___x_713_ = _args[7];
lean_object* v___x_714_ = _args[8];
lean_object* v___f_715_ = _args[9];
lean_object* v___x_716_ = _args[10];
lean_object* v_inst_717_ = _args[11];
lean_object* v_val_718_ = _args[12];
lean_object* v_handler_719_ = _args[13];
lean_object* v_config_720_ = _args[14];
lean_object* v_extensions_721_ = _args[15];
lean_object* v___f_722_ = _args[16];
lean_object* v___y_723_ = _args[17];
_start:
{
uint8_t v_permitAcquired_boxed_724_; uint8_t v___x_13234__boxed_725_; lean_object* v_res_726_; 
v_permitAcquired_boxed_724_ = lean_unbox(v_permitAcquired_710_);
v___x_13234__boxed_725_ = lean_unbox(v___x_714_);
v_res_726_ = l_Std_Http_Server_serve___redArg___lam__12(v___f_706_, v___f_707_, v_activeConnections_708_, v_a_709_, v_permitAcquired_boxed_724_, v___x_711_, v_connectionLimit_712_, v___x_713_, v___x_13234__boxed_725_, v___f_715_, v___x_716_, v_inst_717_, v_val_718_, v_handler_719_, v_config_720_, v_extensions_721_, v___f_722_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13(lean_object* v_a_727_, lean_object* v___x_728_, lean_object* v_a_x3f_729_){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_731_ = l_Std_CancellationContext_cancel(v_a_727_, v___x_728_);
v___x_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13___boxed(lean_object* v_a_734_, lean_object* v___x_735_, lean_object* v_a_x3f_736_, lean_object* v___y_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Std_Http_Server_serve___redArg___lam__13(v_a_734_, v___x_735_, v_a_x3f_736_);
lean_dec(v_a_x3f_736_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14(lean_object* v___f_739_, lean_object* v___f_740_, lean_object* v___f_741_, lean_object* v___x_742_, uint8_t v___x_743_){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___y_748_; 
v___x_745_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_745_, 0, lean_box(0));
lean_closure_set(v___x_745_, 1, lean_box(0));
lean_closure_set(v___x_745_, 2, lean_box(0));
lean_closure_set(v___x_745_, 3, v___f_739_);
lean_inc(v___x_742_);
v___x_746_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_740_, v___f_741_, v___x_742_, v___x_743_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_750_; 
lean_dec_ref(v___x_745_);
lean_dec(v___x_742_);
v_a_750_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_750_);
lean_dec_ref_known(v___x_746_, 1);
if (lean_obj_tag(v_a_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
v_a_751_ = lean_ctor_get(v_a_750_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v_a_750_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v_a_750_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v_a_750_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
v___y_748_ = v___x_756_;
goto v___jp_747_;
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_767_; 
v_a_759_ = lean_ctor_get(v_a_750_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v_a_750_);
if (v_isSharedCheck_767_ == 0)
{
v___x_761_ = v_a_750_;
v_isShared_762_ = v_isSharedCheck_767_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v_a_750_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_767_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v_fst_763_; lean_object* v___x_765_; 
v_fst_763_ = lean_ctor_get(v_a_759_, 0);
lean_inc(v_fst_763_);
lean_dec(v_a_759_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v_fst_763_);
v___x_765_ = v___x_761_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_fst_763_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
v___y_748_ = v___x_765_;
goto v___jp_747_;
}
}
}
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_776_; 
v_a_768_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_776_ == 0)
{
v___x_770_ = v___x_746_;
v_isShared_771_ = v_isSharedCheck_776_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_746_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_776_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; lean_object* v___x_774_; 
v___x_772_ = lean_task_map(v___x_745_, v_a_768_, v___x_742_, v___x_743_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_772_);
v___x_774_ = v___x_770_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_772_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
v___jp_747_:
{
lean_object* v___x_749_; 
v___x_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_749_, 0, v___y_748_);
return v___x_749_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14___boxed(lean_object* v___f_777_, lean_object* v___f_778_, lean_object* v___f_779_, lean_object* v___x_780_, lean_object* v___x_781_, lean_object* v___y_782_){
_start:
{
uint8_t v___x_13310__boxed_783_; lean_object* v_res_784_; 
v___x_13310__boxed_783_ = lean_unbox(v___x_781_);
v_res_784_ = l_Std_Http_Server_serve___redArg___lam__14(v___f_777_, v___f_778_, v___f_779_, v___x_780_, v___x_13310__boxed_783_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15(lean_object* v___f_785_, lean_object* v___f_786_, lean_object* v_activeConnections_787_, uint8_t v_permitAcquired_788_, lean_object* v___x_789_, lean_object* v_connectionLimit_790_, lean_object* v___x_791_, uint8_t v___x_792_, lean_object* v___f_793_, lean_object* v___x_794_, lean_object* v_inst_795_, lean_object* v_val_796_, lean_object* v_handler_797_, lean_object* v_config_798_, lean_object* v_extensions_799_, lean_object* v___f_800_, lean_object* v___f_801_, lean_object* v_x_802_){
_start:
{
if (lean_obj_tag(v_x_802_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_812_; 
lean_dec_ref(v___f_801_);
lean_dec_ref(v___f_800_);
lean_dec(v_extensions_799_);
lean_dec_ref(v_config_798_);
lean_dec(v_handler_797_);
lean_dec(v_val_796_);
lean_dec_ref(v_inst_795_);
lean_dec_ref(v___x_794_);
lean_dec_ref(v___f_793_);
lean_dec(v___x_791_);
lean_dec(v_connectionLimit_790_);
lean_dec_ref(v_activeConnections_787_);
lean_dec_ref(v___f_786_);
lean_dec_ref(v___f_785_);
v_a_804_ = lean_ctor_get(v_x_802_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v_x_802_);
if (v_isSharedCheck_812_ == 0)
{
v___x_806_ = v_x_802_;
v_isShared_807_ = v_isSharedCheck_812_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v_x_802_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_812_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_811_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_810_; 
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
return v___x_810_;
}
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_830_; 
v_a_813_ = lean_ctor_get(v_x_802_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v_x_802_);
if (v_isSharedCheck_830_ == 0)
{
v___x_815_ = v_x_802_;
v_isShared_816_ = v_isSharedCheck_830_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v_x_802_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_830_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___f_819_; lean_object* v___x_820_; lean_object* v___f_821_; lean_object* v___x_822_; lean_object* v___f_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_817_ = lean_box(v_permitAcquired_788_);
v___x_818_ = lean_box(v___x_792_);
lean_inc_n(v___x_791_, 2);
lean_inc(v_a_813_);
v___f_819_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__12___boxed), 18, 17);
lean_closure_set(v___f_819_, 0, v___f_785_);
lean_closure_set(v___f_819_, 1, v___f_786_);
lean_closure_set(v___f_819_, 2, v_activeConnections_787_);
lean_closure_set(v___f_819_, 3, v_a_813_);
lean_closure_set(v___f_819_, 4, v___x_817_);
lean_closure_set(v___f_819_, 5, v___x_789_);
lean_closure_set(v___f_819_, 6, v_connectionLimit_790_);
lean_closure_set(v___f_819_, 7, v___x_791_);
lean_closure_set(v___f_819_, 8, v___x_818_);
lean_closure_set(v___f_819_, 9, v___f_793_);
lean_closure_set(v___f_819_, 10, v___x_794_);
lean_closure_set(v___f_819_, 11, v_inst_795_);
lean_closure_set(v___f_819_, 12, v_val_796_);
lean_closure_set(v___f_819_, 13, v_handler_797_);
lean_closure_set(v___f_819_, 14, v_config_798_);
lean_closure_set(v___f_819_, 15, v_extensions_799_);
lean_closure_set(v___f_819_, 16, v___f_800_);
v___x_820_ = lean_box(2);
v___f_821_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__13___boxed), 4, 2);
lean_closure_set(v___f_821_, 0, v_a_813_);
lean_closure_set(v___f_821_, 1, v___x_820_);
v___x_822_ = lean_box(v___x_792_);
v___f_823_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__14___boxed), 6, 5);
lean_closure_set(v___f_823_, 0, v___f_801_);
lean_closure_set(v___f_823_, 1, v___f_819_);
lean_closure_set(v___f_823_, 2, v___f_821_);
lean_closure_set(v___f_823_, 3, v___x_791_);
lean_closure_set(v___f_823_, 4, v___x_822_);
v___x_824_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_824_, 0, lean_box(0));
lean_closure_set(v___x_824_, 1, v___f_823_);
v___x_825_ = lean_io_as_task(v___x_824_, v___x_791_);
lean_dec_ref(v___x_825_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_789_);
v___x_827_ = v___x_815_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_789_);
v___x_827_ = v_reuseFailAlloc_829_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_828_; 
v___x_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
return v___x_828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15___boxed(lean_object** _args){
lean_object* v___f_831_ = _args[0];
lean_object* v___f_832_ = _args[1];
lean_object* v_activeConnections_833_ = _args[2];
lean_object* v_permitAcquired_834_ = _args[3];
lean_object* v___x_835_ = _args[4];
lean_object* v_connectionLimit_836_ = _args[5];
lean_object* v___x_837_ = _args[6];
lean_object* v___x_838_ = _args[7];
lean_object* v___f_839_ = _args[8];
lean_object* v___x_840_ = _args[9];
lean_object* v_inst_841_ = _args[10];
lean_object* v_val_842_ = _args[11];
lean_object* v_handler_843_ = _args[12];
lean_object* v_config_844_ = _args[13];
lean_object* v_extensions_845_ = _args[14];
lean_object* v___f_846_ = _args[15];
lean_object* v___f_847_ = _args[16];
lean_object* v_x_848_ = _args[17];
lean_object* v___y_849_ = _args[18];
_start:
{
uint8_t v_permitAcquired_boxed_850_; uint8_t v___x_13390__boxed_851_; lean_object* v_res_852_; 
v_permitAcquired_boxed_850_ = lean_unbox(v_permitAcquired_834_);
v___x_13390__boxed_851_ = lean_unbox(v___x_838_);
v_res_852_ = l_Std_Http_Server_serve___redArg___lam__15(v___f_831_, v___f_832_, v_activeConnections_833_, v_permitAcquired_boxed_850_, v___x_835_, v_connectionLimit_836_, v___x_837_, v___x_13390__boxed_851_, v___f_839_, v___x_840_, v_inst_841_, v_val_842_, v_handler_843_, v_config_844_, v_extensions_845_, v___f_846_, v___f_847_, v_x_848_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16(lean_object* v___x_853_, uint8_t v___x_854_, lean_object* v___f_855_, lean_object* v_x_856_){
_start:
{
if (lean_obj_tag(v_x_856_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_866_; 
lean_dec_ref(v___f_855_);
lean_dec(v___x_853_);
v_a_858_ = lean_ctor_get(v_x_856_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v_x_856_);
if (v_isSharedCheck_866_ == 0)
{
v___x_860_ = v_x_856_;
v_isShared_861_ = v_isSharedCheck_866_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v_x_856_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_866_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_865_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_864_; 
v___x_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
return v___x_864_;
}
}
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_877_; 
v_a_867_ = lean_ctor_get(v_x_856_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v_x_856_);
if (v_isSharedCheck_877_ == 0)
{
v___x_869_ = v_x_856_;
v_isShared_870_ = v_isSharedCheck_877_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v_x_856_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_877_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_871_ = l_Std_CancellationContext_fork(v_a_867_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_871_);
v___x_873_ = v___x_869_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_876_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
v___x_875_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_853_, v___x_854_, v___x_874_, v___f_855_);
return v___x_875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16___boxed(lean_object* v___x_878_, lean_object* v___x_879_, lean_object* v___f_880_, lean_object* v_x_881_, lean_object* v___y_882_){
_start:
{
uint8_t v___x_13480__boxed_883_; lean_object* v_res_884_; 
v___x_13480__boxed_883_ = lean_unbox(v___x_879_);
v_res_884_ = l_Std_Http_Server_serve___redArg___lam__16(v___x_878_, v___x_13480__boxed_883_, v___f_880_, v_x_881_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17(lean_object* v___f_885_, lean_object* v___f_886_, lean_object* v_activeConnections_887_, uint8_t v_permitAcquired_888_, lean_object* v___x_889_, lean_object* v_connectionLimit_890_, uint8_t v___x_891_, lean_object* v___f_892_, lean_object* v___x_893_, lean_object* v_inst_894_, lean_object* v_val_895_, lean_object* v_handler_896_, lean_object* v_config_897_, lean_object* v___f_898_, lean_object* v___f_899_, lean_object* v___f_900_, lean_object* v_extensions_901_, lean_object* v___y_902_){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___f_907_; lean_object* v___x_908_; lean_object* v___f_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_904_ = lean_unsigned_to_nat(0u);
v___x_905_ = lean_box(v_permitAcquired_888_);
v___x_906_ = lean_box(v___x_891_);
v___f_907_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__15___boxed), 19, 17);
lean_closure_set(v___f_907_, 0, v___f_885_);
lean_closure_set(v___f_907_, 1, v___f_886_);
lean_closure_set(v___f_907_, 2, v_activeConnections_887_);
lean_closure_set(v___f_907_, 3, v___x_905_);
lean_closure_set(v___f_907_, 4, v___x_889_);
lean_closure_set(v___f_907_, 5, v_connectionLimit_890_);
lean_closure_set(v___f_907_, 6, v___x_904_);
lean_closure_set(v___f_907_, 7, v___x_906_);
lean_closure_set(v___f_907_, 8, v___f_892_);
lean_closure_set(v___f_907_, 9, v___x_893_);
lean_closure_set(v___f_907_, 10, v_inst_894_);
lean_closure_set(v___f_907_, 11, v_val_895_);
lean_closure_set(v___f_907_, 12, v_handler_896_);
lean_closure_set(v___f_907_, 13, v_config_897_);
lean_closure_set(v___f_907_, 14, v_extensions_901_);
lean_closure_set(v___f_907_, 15, v___f_898_);
lean_closure_set(v___f_907_, 16, v___f_899_);
v___x_908_ = lean_box(v___x_891_);
v___f_909_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__16___boxed), 5, 3);
lean_closure_set(v___f_909_, 0, v___x_904_);
lean_closure_set(v___f_909_, 1, v___x_908_);
lean_closure_set(v___f_909_, 2, v___f_907_);
lean_inc_ref(v___y_902_);
v___x_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_910_, 0, v___y_902_);
v___x_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
v___x_912_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_904_, v___x_891_, v___x_911_, v___f_909_);
v___x_913_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_904_, v___x_891_, v___x_912_, v___f_900_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17___boxed(lean_object** _args){
lean_object* v___f_914_ = _args[0];
lean_object* v___f_915_ = _args[1];
lean_object* v_activeConnections_916_ = _args[2];
lean_object* v_permitAcquired_917_ = _args[3];
lean_object* v___x_918_ = _args[4];
lean_object* v_connectionLimit_919_ = _args[5];
lean_object* v___x_920_ = _args[6];
lean_object* v___f_921_ = _args[7];
lean_object* v___x_922_ = _args[8];
lean_object* v_inst_923_ = _args[9];
lean_object* v_val_924_ = _args[10];
lean_object* v_handler_925_ = _args[11];
lean_object* v_config_926_ = _args[12];
lean_object* v___f_927_ = _args[13];
lean_object* v___f_928_ = _args[14];
lean_object* v___f_929_ = _args[15];
lean_object* v_extensions_930_ = _args[16];
lean_object* v___y_931_ = _args[17];
lean_object* v___y_932_ = _args[18];
_start:
{
uint8_t v_permitAcquired_boxed_933_; uint8_t v___x_13537__boxed_934_; lean_object* v_res_935_; 
v_permitAcquired_boxed_933_ = lean_unbox(v_permitAcquired_917_);
v___x_13537__boxed_934_ = lean_unbox(v___x_920_);
v_res_935_ = l_Std_Http_Server_serve___redArg___lam__17(v___f_914_, v___f_915_, v_activeConnections_916_, v_permitAcquired_boxed_933_, v___x_918_, v_connectionLimit_919_, v___x_13537__boxed_934_, v___f_921_, v___x_922_, v_inst_923_, v_val_924_, v_handler_925_, v_config_926_, v___f_927_, v___f_928_, v___f_929_, v_extensions_930_, v___y_931_);
lean_dec_ref(v___y_931_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18(lean_object* v___f_936_, lean_object* v___y_937_, lean_object* v_x_938_){
_start:
{
if (lean_obj_tag(v_x_938_) == 0)
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_948_; 
lean_dec_ref(v___f_936_);
v_a_940_ = lean_ctor_get(v_x_938_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v_x_938_);
if (v_isSharedCheck_948_ == 0)
{
v___x_942_ = v_x_938_;
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v_x_938_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_947_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_946_; 
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
return v___x_946_;
}
}
}
else
{
lean_object* v_a_949_; lean_object* v___x_950_; 
v_a_949_ = lean_ctor_get(v_x_938_, 0);
lean_inc(v_a_949_);
lean_dec_ref_known(v_x_938_, 1);
lean_inc_ref(v___y_937_);
v___x_950_ = lean_apply_3(v___f_936_, v_a_949_, v___y_937_, lean_box(0));
return v___x_950_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18___boxed(lean_object* v___f_951_, lean_object* v___y_952_, lean_object* v_x_953_, lean_object* v___y_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Std_Http_Server_serve___redArg___lam__18(v___f_951_, v___y_952_, v_x_953_);
lean_dec_ref(v___y_952_);
return v_res_955_;
}
}
static lean_object* _init_l_Std_Http_Server_serve___redArg___lam__20___closed__0(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = l_Std_Http_Extensions_empty;
v___x_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
return v___x_957_;
}
}
static lean_object* _init_l_Std_Http_Server_serve___redArg___lam__20___closed__1(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_obj_once(&l_Std_Http_Server_serve___redArg___lam__20___closed__0, &l_Std_Http_Server_serve___redArg___lam__20___closed__0_once, _init_l_Std_Http_Server_serve___redArg___lam__20___closed__0);
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20(uint8_t v___x_961_, lean_object* v___f_962_, lean_object* v___x_963_, lean_object* v___f_964_, lean_object* v_x_965_){
_start:
{
if (lean_obj_tag(v_x_965_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_975_; 
lean_dec_ref(v___f_964_);
lean_dec(v___x_963_);
lean_dec_ref(v___f_962_);
v_a_967_ = lean_ctor_get(v_x_965_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v_x_965_);
if (v_isSharedCheck_975_ == 0)
{
v___x_969_ = v_x_965_;
v_isShared_970_ = v_isSharedCheck_975_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v_x_965_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_975_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_974_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
lean_object* v___x_973_; 
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
return v___x_973_;
}
}
}
else
{
lean_object* v_a_976_; 
v_a_976_ = lean_ctor_get(v_x_965_, 0);
lean_inc(v_a_976_);
lean_dec_ref_known(v_x_965_, 1);
if (lean_obj_tag(v_a_976_) == 0)
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
lean_dec_ref_known(v_a_976_, 1);
lean_dec_ref(v___f_964_);
lean_dec(v___x_963_);
v___x_977_ = lean_unsigned_to_nat(0u);
v___x_978_ = lean_obj_once(&l_Std_Http_Server_serve___redArg___lam__20___closed__1, &l_Std_Http_Server_serve___redArg___lam__20___closed__1_once, _init_l_Std_Http_Server_serve___redArg___lam__20___closed__1);
v___x_979_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_977_, v___x_961_, v___x_978_, v___f_962_);
return v___x_979_;
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_995_; 
lean_dec_ref(v___f_962_);
v_a_980_ = lean_ctor_get(v_a_976_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v_a_976_);
if (v_isSharedCheck_995_ == 0)
{
v___x_982_ = v_a_976_;
v_isShared_983_ = v_isSharedCheck_995_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v_a_976_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_995_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_984_; lean_object* v_dyn_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_984_ = l_Std_Http_Extensions_empty;
v_dyn_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_985_, 0, v___x_963_);
lean_ctor_set(v_dyn_985_, 1, v_a_980_);
v___x_986_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__20___closed__2));
v___x_987_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_985_);
v___x_988_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_986_, v___x_987_, v_dyn_985_, v___x_984_);
v___x_989_ = lean_unsigned_to_nat(0u);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 0, v___x_988_);
v___x_991_ = v___x_982_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_988_);
v___x_991_ = v_reuseFailAlloc_994_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
v___x_993_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_989_, v___x_961_, v___x_992_, v___f_964_);
return v___x_993_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20___boxed(lean_object* v___x_996_, lean_object* v___f_997_, lean_object* v___x_998_, lean_object* v___f_999_, lean_object* v_x_1000_, lean_object* v___y_1001_){
_start:
{
uint8_t v___x_13637__boxed_1002_; lean_object* v_res_1003_; 
v___x_13637__boxed_1002_ = lean_unbox(v___x_996_);
v_res_1003_ = l_Std_Http_Server_serve___redArg___lam__20(v___x_13637__boxed_1002_, v___f_997_, v___x_998_, v___f_999_, v_x_1000_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__19(uint8_t v_permitAcquired_1004_, lean_object* v___f_1005_, lean_object* v___x_1006_, lean_object* v___y_1007_, lean_object* v_connectionLimit_1008_, uint8_t v___x_1009_, lean_object* v___f_1010_, lean_object* v___f_1011_, lean_object* v___f_1012_, lean_object* v_activeConnections_1013_, lean_object* v___f_1014_, lean_object* v___x_1015_, lean_object* v_inst_1016_, lean_object* v_handler_1017_, lean_object* v_config_1018_, lean_object* v___f_1019_, lean_object* v___f_1020_, lean_object* v___f_1021_, lean_object* v___x_1022_, lean_object* v_x_1023_){
_start:
{
if (lean_obj_tag(v_x_1023_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1033_; 
lean_dec(v___x_1022_);
lean_dec_ref(v___f_1021_);
lean_dec_ref(v___f_1020_);
lean_dec_ref(v___f_1019_);
lean_dec_ref(v_config_1018_);
lean_dec(v_handler_1017_);
lean_dec_ref(v_inst_1016_);
lean_dec_ref(v___x_1015_);
lean_dec_ref(v___f_1014_);
lean_dec_ref(v_activeConnections_1013_);
lean_dec_ref(v___f_1012_);
lean_dec_ref(v___f_1011_);
lean_dec_ref(v___f_1010_);
lean_dec(v_connectionLimit_1008_);
lean_dec_ref(v___f_1005_);
v_a_1025_ = lean_ctor_get(v_x_1023_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_x_1023_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1027_ = v_x_1023_;
v_isShared_1028_ = v_isSharedCheck_1033_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v_x_1023_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1033_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1031_; 
v___x_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
return v___x_1031_;
}
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1092_; 
v_a_1034_ = lean_ctor_get(v_x_1023_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_x_1023_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1036_ = v_x_1023_;
v_isShared_1037_ = v_isSharedCheck_1092_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v_x_1023_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1092_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
if (lean_obj_tag(v_a_1034_) == 0)
{
lean_dec(v___x_1022_);
lean_dec_ref(v___f_1021_);
lean_dec_ref(v___f_1020_);
lean_dec_ref(v___f_1019_);
lean_dec_ref(v_config_1018_);
lean_dec(v_handler_1017_);
lean_dec_ref(v_inst_1016_);
lean_dec_ref(v___x_1015_);
lean_dec_ref(v___f_1014_);
lean_dec_ref(v_activeConnections_1013_);
lean_dec_ref(v___f_1012_);
lean_dec_ref(v___f_1011_);
if (v_permitAcquired_1004_ == 0)
{
lean_object* v___x_1038_; 
lean_del_object(v___x_1036_);
lean_dec_ref(v___f_1010_);
lean_dec(v_connectionLimit_1008_);
lean_inc_ref(v___y_1007_);
v___x_1038_ = lean_apply_3(v___f_1005_, v___x_1006_, v___y_1007_, lean_box(0));
return v___x_1038_;
}
else
{
if (lean_obj_tag(v_connectionLimit_1008_) == 1)
{
lean_object* v_val_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1052_; 
lean_dec_ref(v___f_1005_);
v_val_1039_ = lean_ctor_get(v_connectionLimit_1008_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_connectionLimit_1008_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1041_ = v_connectionLimit_1008_;
v_isShared_1042_ = v_isSharedCheck_1052_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_val_1039_);
lean_dec(v_connectionLimit_1008_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1052_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1043_ = lean_unsigned_to_nat(0u);
v___x_1044_ = l_Std_Semaphore_release(v_val_1039_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v___x_1044_);
v___x_1046_ = v___x_1036_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1048_; 
if (v_isShared_1042_ == 0)
{
lean_ctor_set_tag(v___x_1041_, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1046_);
v___x_1048_ = v___x_1041_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1049_; 
v___x_1049_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1043_, v___x_1009_, v___x_1048_, v___f_1010_);
return v___x_1049_;
}
}
}
}
else
{
lean_object* v___x_1053_; 
lean_del_object(v___x_1036_);
lean_dec_ref(v___f_1010_);
lean_dec(v_connectionLimit_1008_);
lean_inc_ref(v___y_1007_);
v___x_1053_ = lean_apply_3(v___f_1005_, v___x_1006_, v___y_1007_, lean_box(0));
return v___x_1053_;
}
}
}
else
{
lean_object* v_val_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1091_; 
lean_dec_ref(v___f_1010_);
lean_dec_ref(v___f_1005_);
v_val_1054_ = lean_ctor_get(v_a_1034_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_a_1034_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1056_ = v_a_1034_;
v_isShared_1057_ = v_isSharedCheck_1091_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_val_1054_);
lean_dec(v_a_1034_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1091_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___f_1060_; lean_object* v___f_1061_; lean_object* v___x_1062_; lean_object* v___f_1063_; lean_object* v___x_1064_; lean_object* v_val_1066_; lean_object* v___x_1074_; 
v___x_1058_ = lean_box(v_permitAcquired_1004_);
v___x_1059_ = lean_box(v___x_1009_);
lean_inc(v_val_1054_);
v___f_1060_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__17___boxed), 19, 16);
lean_closure_set(v___f_1060_, 0, v___f_1011_);
lean_closure_set(v___f_1060_, 1, v___f_1012_);
lean_closure_set(v___f_1060_, 2, v_activeConnections_1013_);
lean_closure_set(v___f_1060_, 3, v___x_1058_);
lean_closure_set(v___f_1060_, 4, v___x_1006_);
lean_closure_set(v___f_1060_, 5, v_connectionLimit_1008_);
lean_closure_set(v___f_1060_, 6, v___x_1059_);
lean_closure_set(v___f_1060_, 7, v___f_1014_);
lean_closure_set(v___f_1060_, 8, v___x_1015_);
lean_closure_set(v___f_1060_, 9, v_inst_1016_);
lean_closure_set(v___f_1060_, 10, v_val_1054_);
lean_closure_set(v___f_1060_, 11, v_handler_1017_);
lean_closure_set(v___f_1060_, 12, v_config_1018_);
lean_closure_set(v___f_1060_, 13, v___f_1019_);
lean_closure_set(v___f_1060_, 14, v___f_1020_);
lean_closure_set(v___f_1060_, 15, v___f_1021_);
lean_inc_ref(v___y_1007_);
v___f_1061_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__18___boxed), 4, 2);
lean_closure_set(v___f_1061_, 0, v___f_1060_);
lean_closure_set(v___f_1061_, 1, v___y_1007_);
v___x_1062_ = lean_box(v___x_1009_);
lean_inc_ref(v___f_1061_);
v___f_1063_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__20___boxed), 6, 4);
lean_closure_set(v___f_1063_, 0, v___x_1062_);
lean_closure_set(v___f_1063_, 1, v___f_1061_);
lean_closure_set(v___f_1063_, 2, v___x_1022_);
lean_closure_set(v___f_1063_, 3, v___f_1061_);
v___x_1064_ = lean_unsigned_to_nat(0u);
v___x_1074_ = lean_uv_tcp_getpeername(v_val_1054_);
lean_dec(v_val_1054_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
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
v_val_1066_ = v___x_1080_;
goto v___jp_1065_;
}
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
v_a_1083_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1074_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1074_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
lean_ctor_set_tag(v___x_1085_, 0);
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
v_val_1066_ = v___x_1088_;
goto v___jp_1065_;
}
}
}
v___jp_1065_:
{
lean_object* v___x_1068_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v_val_1066_);
v___x_1068_ = v___x_1036_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_val_1066_);
v___x_1068_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
lean_object* v___x_1070_; 
if (v_isShared_1057_ == 0)
{
lean_ctor_set_tag(v___x_1056_, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1068_);
v___x_1070_ = v___x_1056_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1068_);
v___x_1070_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1071_; 
v___x_1071_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1064_, v___x_1009_, v___x_1070_, v___f_1063_);
return v___x_1071_;
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
lean_object* v_permitAcquired_1093_ = _args[0];
lean_object* v___f_1094_ = _args[1];
lean_object* v___x_1095_ = _args[2];
lean_object* v___y_1096_ = _args[3];
lean_object* v_connectionLimit_1097_ = _args[4];
lean_object* v___x_1098_ = _args[5];
lean_object* v___f_1099_ = _args[6];
lean_object* v___f_1100_ = _args[7];
lean_object* v___f_1101_ = _args[8];
lean_object* v_activeConnections_1102_ = _args[9];
lean_object* v___f_1103_ = _args[10];
lean_object* v___x_1104_ = _args[11];
lean_object* v_inst_1105_ = _args[12];
lean_object* v_handler_1106_ = _args[13];
lean_object* v_config_1107_ = _args[14];
lean_object* v___f_1108_ = _args[15];
lean_object* v___f_1109_ = _args[16];
lean_object* v___f_1110_ = _args[17];
lean_object* v___x_1111_ = _args[18];
lean_object* v_x_1112_ = _args[19];
lean_object* v___y_1113_ = _args[20];
_start:
{
uint8_t v_permitAcquired_boxed_1114_; uint8_t v___x_13720__boxed_1115_; lean_object* v_res_1116_; 
v_permitAcquired_boxed_1114_ = lean_unbox(v_permitAcquired_1093_);
v___x_13720__boxed_1115_ = lean_unbox(v___x_1098_);
v_res_1116_ = l_Std_Http_Server_serve___redArg___lam__19(v_permitAcquired_boxed_1114_, v___f_1094_, v___x_1095_, v___y_1096_, v_connectionLimit_1097_, v___x_13720__boxed_1115_, v___f_1099_, v___f_1100_, v___f_1101_, v_activeConnections_1102_, v___f_1103_, v___x_1104_, v_inst_1105_, v_handler_1106_, v_config_1107_, v___f_1108_, v___f_1109_, v___f_1110_, v___x_1111_, v_x_1112_);
lean_dec_ref(v___y_1096_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21(lean_object* v_a_1117_, lean_object* v___f_1118_, lean_object* v___f_1119_, uint8_t v___x_1120_, lean_object* v___f_1121_, lean_object* v_x_1122_){
_start:
{
if (lean_obj_tag(v_x_1122_) == 0)
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1132_; 
lean_dec_ref(v___f_1121_);
lean_dec_ref(v___f_1119_);
lean_dec_ref(v___f_1118_);
lean_dec(v_a_1117_);
v_a_1124_ = lean_ctor_get(v_x_1122_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_x_1122_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1126_ = v_x_1122_;
v_isShared_1127_ = v_isSharedCheck_1132_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v_x_1122_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1132_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1124_);
v___x_1129_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
return v___x_1130_;
}
}
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v_a_1133_ = lean_ctor_get(v_x_1122_, 0);
lean_inc(v_a_1133_);
lean_dec_ref_known(v_x_1122_, 1);
v___x_1134_ = l_Std_Async_TCP_Socket_Server_acceptSelector(v_a_1117_);
v___x_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
lean_ctor_set(v___x_1135_, 1, v___f_1118_);
v___x_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1136_, 0, v_a_1133_);
lean_ctor_set(v___x_1136_, 1, v___f_1119_);
v___x_1137_ = lean_unsigned_to_nat(2u);
v___x_1138_ = lean_mk_empty_array_with_capacity(v___x_1137_);
v___x_1139_ = lean_array_push(v___x_1138_, v___x_1135_);
v___x_1140_ = lean_array_push(v___x_1139_, v___x_1136_);
v___x_1141_ = lean_unsigned_to_nat(0u);
v___x_1142_ = l_Std_Async_Selectable_one___redArg(v___x_1140_);
v___x_1143_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1141_, v___x_1120_, v___x_1142_, v___f_1121_);
return v___x_1143_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21___boxed(lean_object* v_a_1144_, lean_object* v___f_1145_, lean_object* v___f_1146_, lean_object* v___x_1147_, lean_object* v___f_1148_, lean_object* v_x_1149_, lean_object* v___y_1150_){
_start:
{
uint8_t v___x_13904__boxed_1151_; lean_object* v_res_1152_; 
v___x_13904__boxed_1151_ = lean_unbox(v___x_1147_);
v_res_1152_ = l_Std_Http_Server_serve___redArg___lam__21(v_a_1144_, v___f_1145_, v___f_1146_, v___x_13904__boxed_1151_, v___f_1148_, v_x_1149_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22(lean_object* v___f_1153_, lean_object* v___x_1154_, lean_object* v_connectionLimit_1155_, uint8_t v___x_1156_, lean_object* v___f_1157_, lean_object* v___f_1158_, lean_object* v_activeConnections_1159_, lean_object* v___f_1160_, lean_object* v___x_1161_, lean_object* v_inst_1162_, lean_object* v_handler_1163_, lean_object* v_config_1164_, lean_object* v___f_1165_, lean_object* v___f_1166_, lean_object* v___f_1167_, lean_object* v___x_1168_, lean_object* v_a_1169_, lean_object* v___f_1170_, lean_object* v___f_1171_, lean_object* v___f_1172_, uint8_t v_permitAcquired_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v___f_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___f_1179_; lean_object* v___x_1180_; lean_object* v___f_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_inc_ref_n(v___y_1174_, 3);
lean_inc_ref(v___f_1153_);
v___f_1176_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_1176_, 0, v___f_1153_);
lean_closure_set(v___f_1176_, 1, v___y_1174_);
v___x_1177_ = lean_box(v_permitAcquired_1173_);
v___x_1178_ = lean_box(v___x_1156_);
v___f_1179_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__19___boxed), 21, 19);
lean_closure_set(v___f_1179_, 0, v___x_1177_);
lean_closure_set(v___f_1179_, 1, v___f_1153_);
lean_closure_set(v___f_1179_, 2, v___x_1154_);
lean_closure_set(v___f_1179_, 3, v___y_1174_);
lean_closure_set(v___f_1179_, 4, v_connectionLimit_1155_);
lean_closure_set(v___f_1179_, 5, v___x_1178_);
lean_closure_set(v___f_1179_, 6, v___f_1176_);
lean_closure_set(v___f_1179_, 7, v___f_1157_);
lean_closure_set(v___f_1179_, 8, v___f_1158_);
lean_closure_set(v___f_1179_, 9, v_activeConnections_1159_);
lean_closure_set(v___f_1179_, 10, v___f_1160_);
lean_closure_set(v___f_1179_, 11, v___x_1161_);
lean_closure_set(v___f_1179_, 12, v_inst_1162_);
lean_closure_set(v___f_1179_, 13, v_handler_1163_);
lean_closure_set(v___f_1179_, 14, v_config_1164_);
lean_closure_set(v___f_1179_, 15, v___f_1165_);
lean_closure_set(v___f_1179_, 16, v___f_1166_);
lean_closure_set(v___f_1179_, 17, v___f_1167_);
lean_closure_set(v___f_1179_, 18, v___x_1168_);
v___x_1180_ = lean_box(v___x_1156_);
v___f_1181_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__21___boxed), 7, 5);
lean_closure_set(v___f_1181_, 0, v_a_1169_);
lean_closure_set(v___f_1181_, 1, v___f_1170_);
lean_closure_set(v___f_1181_, 2, v___f_1171_);
lean_closure_set(v___f_1181_, 3, v___x_1180_);
lean_closure_set(v___f_1181_, 4, v___f_1179_);
v___x_1182_ = lean_unsigned_to_nat(0u);
v___x_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___y_1174_);
v___x_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
v___x_1185_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1182_, v___x_1156_, v___x_1184_, v___f_1172_);
v___x_1186_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1182_, v___x_1156_, v___x_1185_, v___f_1181_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22___boxed(lean_object** _args){
lean_object* v___f_1187_ = _args[0];
lean_object* v___x_1188_ = _args[1];
lean_object* v_connectionLimit_1189_ = _args[2];
lean_object* v___x_1190_ = _args[3];
lean_object* v___f_1191_ = _args[4];
lean_object* v___f_1192_ = _args[5];
lean_object* v_activeConnections_1193_ = _args[6];
lean_object* v___f_1194_ = _args[7];
lean_object* v___x_1195_ = _args[8];
lean_object* v_inst_1196_ = _args[9];
lean_object* v_handler_1197_ = _args[10];
lean_object* v_config_1198_ = _args[11];
lean_object* v___f_1199_ = _args[12];
lean_object* v___f_1200_ = _args[13];
lean_object* v___f_1201_ = _args[14];
lean_object* v___x_1202_ = _args[15];
lean_object* v_a_1203_ = _args[16];
lean_object* v___f_1204_ = _args[17];
lean_object* v___f_1205_ = _args[18];
lean_object* v___f_1206_ = _args[19];
lean_object* v_permitAcquired_1207_ = _args[20];
lean_object* v___y_1208_ = _args[21];
lean_object* v___y_1209_ = _args[22];
_start:
{
uint8_t v___x_13964__boxed_1210_; uint8_t v_permitAcquired_boxed_1211_; lean_object* v_res_1212_; 
v___x_13964__boxed_1210_ = lean_unbox(v___x_1190_);
v_permitAcquired_boxed_1211_ = lean_unbox(v_permitAcquired_1207_);
v_res_1212_ = l_Std_Http_Server_serve___redArg___lam__22(v___f_1187_, v___x_1188_, v_connectionLimit_1189_, v___x_13964__boxed_1210_, v___f_1191_, v___f_1192_, v_activeConnections_1193_, v___f_1194_, v___x_1195_, v_inst_1196_, v_handler_1197_, v_config_1198_, v___f_1199_, v___f_1200_, v___f_1201_, v___x_1202_, v_a_1203_, v___f_1204_, v___f_1205_, v___f_1206_, v_permitAcquired_boxed_1211_, v___y_1208_);
lean_dec_ref(v___y_1208_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23(lean_object* v___f_1213_, lean_object* v___y_1214_, lean_object* v_x_1215_){
_start:
{
if (lean_obj_tag(v_x_1215_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1225_; 
lean_dec_ref(v___y_1214_);
lean_dec_ref(v___f_1213_);
v_a_1217_ = lean_ctor_get(v_x_1215_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_x_1215_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1219_ = v_x_1215_;
v_isShared_1220_ = v_isSharedCheck_1225_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v_x_1215_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1225_;
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
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_object* v___x_1223_; 
v___x_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
return v___x_1223_;
}
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1227_; 
v_a_1226_ = lean_ctor_get(v_x_1215_, 0);
lean_inc(v_a_1226_);
lean_dec_ref_known(v_x_1215_, 1);
v___x_1227_ = lean_apply_3(v___f_1213_, v_a_1226_, v___y_1214_, lean_box(0));
return v___x_1227_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23___boxed(lean_object* v___f_1228_, lean_object* v___y_1229_, lean_object* v_x_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Std_Http_Server_serve___redArg___lam__23(v___f_1228_, v___y_1229_, v_x_1230_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25(uint8_t v___x_1233_, uint8_t v___x_1234_, lean_object* v___f_1235_, lean_object* v_x_1236_){
_start:
{
if (lean_obj_tag(v_x_1236_) == 0)
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1246_; 
lean_dec_ref(v___f_1235_);
v_a_1238_ = lean_ctor_get(v_x_1236_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_x_1236_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1240_ = v_x_1236_;
v_isShared_1241_ = v_isSharedCheck_1246_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v_x_1236_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1246_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1238_);
v___x_1243_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1244_; 
v___x_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
return v___x_1244_;
}
}
}
else
{
lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1257_; 
v_isSharedCheck_1257_ = !lean_is_exclusive(v_x_1236_);
if (v_isSharedCheck_1257_ == 0)
{
lean_object* v_unused_1258_; 
v_unused_1258_ = lean_ctor_get(v_x_1236_, 0);
lean_dec(v_unused_1258_);
v___x_1248_ = v_x_1236_;
v_isShared_1249_ = v_isSharedCheck_1257_;
goto v_resetjp_1247_;
}
else
{
lean_dec(v_x_1236_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1257_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1250_ = lean_unsigned_to_nat(0u);
v___x_1251_ = lean_box(v___x_1233_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 0, v___x_1251_);
v___x_1253_ = v___x_1248_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
v___x_1255_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1250_, v___x_1234_, v___x_1254_, v___f_1235_);
return v___x_1255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25___boxed(lean_object* v___x_1259_, lean_object* v___x_1260_, lean_object* v___f_1261_, lean_object* v_x_1262_, lean_object* v___y_1263_){
_start:
{
uint8_t v___x_14072__boxed_1264_; uint8_t v___x_14073__boxed_1265_; lean_object* v_res_1266_; 
v___x_14072__boxed_1264_ = lean_unbox(v___x_1259_);
v___x_14073__boxed_1265_ = lean_unbox(v___x_1260_);
v_res_1266_ = l_Std_Http_Server_serve___redArg___lam__25(v___x_14072__boxed_1264_, v___x_14073__boxed_1265_, v___f_1261_, v_x_1262_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24(lean_object* v___f_1267_, uint8_t v___x_1268_, lean_object* v___f_1269_, lean_object* v_x_1270_){
_start:
{
if (lean_obj_tag(v_x_1270_) == 0)
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1280_; 
lean_dec_ref(v___f_1269_);
lean_dec_ref(v___f_1267_);
v_a_1272_ = lean_ctor_get(v_x_1270_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_x_1270_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1274_ = v_x_1270_;
v_isShared_1275_ = v_isSharedCheck_1280_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v_x_1270_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1280_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
lean_object* v___x_1278_; 
v___x_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
return v___x_1278_;
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v_a_1281_ = lean_ctor_get(v_x_1270_, 0);
lean_inc(v_a_1281_);
lean_dec_ref_known(v_x_1270_, 1);
v___x_1282_ = lean_unsigned_to_nat(0u);
v___x_1283_ = l_IO_Promise_result_x21___redArg(v_a_1281_);
lean_dec(v_a_1281_);
v___x_1284_ = lean_task_map(v___f_1267_, v___x_1283_, v___x_1282_, v___x_1268_);
v___x_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
v___x_1286_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1282_, v___x_1268_, v___x_1285_, v___f_1269_);
return v___x_1286_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24___boxed(lean_object* v___f_1287_, lean_object* v___x_1288_, lean_object* v___f_1289_, lean_object* v_x_1290_, lean_object* v___y_1291_){
_start:
{
uint8_t v___x_14131__boxed_1292_; lean_object* v_res_1293_; 
v___x_14131__boxed_1292_ = lean_unbox(v___x_1288_);
v_res_1293_ = l_Std_Http_Server_serve___redArg___lam__24(v___f_1287_, v___x_14131__boxed_1292_, v___f_1289_, v_x_1290_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26(lean_object* v_connectionLimit_1294_, uint8_t v___x_1295_, lean_object* v___f_1296_, lean_object* v___f_1297_, lean_object* v___f_1298_, lean_object* v_u_1299_, lean_object* v_b_1300_){
_start:
{
if (lean_obj_tag(v_connectionLimit_1294_) == 1)
{
lean_object* v_val_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1319_; 
lean_dec_ref(v___f_1298_);
v_val_1302_ = lean_ctor_get(v_connectionLimit_1294_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_connectionLimit_1294_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1304_ = v_connectionLimit_1294_;
v_isShared_1305_ = v_isSharedCheck_1319_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_val_1302_);
lean_dec(v_connectionLimit_1294_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1319_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
uint8_t v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___f_1309_; lean_object* v___x_1310_; lean_object* v___f_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1306_ = 1;
v___x_1307_ = lean_box(v___x_1306_);
v___x_1308_ = lean_box(v___x_1295_);
v___f_1309_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__25___boxed), 5, 3);
lean_closure_set(v___f_1309_, 0, v___x_1307_);
lean_closure_set(v___f_1309_, 1, v___x_1308_);
lean_closure_set(v___f_1309_, 2, v___f_1296_);
v___x_1310_ = lean_box(v___x_1295_);
v___f_1311_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__24___boxed), 5, 3);
lean_closure_set(v___f_1311_, 0, v___f_1297_);
lean_closure_set(v___f_1311_, 1, v___x_1310_);
lean_closure_set(v___f_1311_, 2, v___f_1309_);
v___x_1312_ = lean_unsigned_to_nat(0u);
v___x_1313_ = l_Std_Semaphore_acquire(v_val_1302_);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 0, v___x_1313_);
v___x_1315_ = v___x_1304_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
v___x_1317_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1312_, v___x_1295_, v___x_1316_, v___f_1311_);
return v___x_1317_;
}
}
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
lean_dec_ref(v___f_1297_);
lean_dec_ref(v___f_1296_);
lean_dec(v_connectionLimit_1294_);
v___x_1320_ = lean_unsigned_to_nat(0u);
v___x_1321_ = lean_box(v___x_1295_);
v___x_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
v___x_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
v___x_1324_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1320_, v___x_1295_, v___x_1323_, v___f_1298_);
return v___x_1324_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26___boxed(lean_object* v_connectionLimit_1325_, lean_object* v___x_1326_, lean_object* v___f_1327_, lean_object* v___f_1328_, lean_object* v___f_1329_, lean_object* v_u_1330_, lean_object* v_b_1331_, lean_object* v___y_1332_){
_start:
{
uint8_t v___x_14175__boxed_1333_; lean_object* v_res_1334_; 
v___x_14175__boxed_1333_ = lean_unbox(v___x_1326_);
v_res_1334_ = l_Std_Http_Server_serve___redArg___lam__26(v_connectionLimit_1325_, v___x_14175__boxed_1333_, v___f_1327_, v___f_1328_, v___f_1329_, v_u_1330_, v_b_1331_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27(lean_object* v_a_1335_, lean_object* v_x_1336_){
_start:
{
if (lean_obj_tag(v_x_1336_) == 0)
{
lean_object* v___x_1338_; 
v___x_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1338_, 0, v_x_1336_);
return v___x_1338_;
}
else
{
lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1346_; 
v_isSharedCheck_1346_ = !lean_is_exclusive(v_x_1336_);
if (v_isSharedCheck_1346_ == 0)
{
lean_object* v_unused_1347_; 
v_unused_1347_ = lean_ctor_get(v_x_1336_, 0);
lean_dec(v_unused_1347_);
v___x_1340_ = v_x_1336_;
v_isShared_1341_ = v_isSharedCheck_1346_;
goto v_resetjp_1339_;
}
else
{
lean_dec(v_x_1336_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1346_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1342_; lean_object* v___x_1344_; 
v___x_1342_ = l_IO_Promise_result_x21___redArg(v_a_1335_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v___x_1342_);
v___x_1344_ = v___x_1340_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27___boxed(lean_object* v_a_1348_, lean_object* v_x_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Std_Http_Server_serve___redArg___lam__27(v_a_1348_, v_x_1349_);
lean_dec(v_a_1348_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28(lean_object* v___f_1352_, lean_object* v___x_1353_, lean_object* v___x_1354_, uint8_t v___x_1355_, lean_object* v_x_1356_){
_start:
{
if (lean_obj_tag(v_x_1356_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1366_; 
lean_dec(v___x_1353_);
lean_dec_ref(v___f_1352_);
v_a_1358_ = lean_ctor_get(v_x_1356_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_x_1356_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1360_ = v_x_1356_;
v_isShared_1361_ = v_isSharedCheck_1366_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v_x_1356_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1366_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
return v___x_1364_;
}
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1378_; 
v_a_1367_ = lean_ctor_get(v_x_1356_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_x_1356_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1369_ = v_x_1356_;
v_isShared_1370_ = v_isSharedCheck_1378_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v_x_1356_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1378_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___f_1371_; lean_object* v___x_1372_; lean_object* v___x_1374_; 
lean_inc(v_a_1367_);
v___f_1371_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__27___boxed), 3, 1);
lean_closure_set(v___f_1371_, 0, v_a_1367_);
lean_inc(v___x_1353_);
v___x_1372_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_1352_, v___x_1353_, v_a_1367_, v___x_1354_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v___x_1372_);
v___x_1374_ = v___x_1369_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
v___x_1376_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1353_, v___x_1355_, v___x_1375_, v___f_1371_);
return v___x_1376_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28___boxed(lean_object* v___f_1379_, lean_object* v___x_1380_, lean_object* v___x_1381_, lean_object* v___x_1382_, lean_object* v_x_1383_, lean_object* v___y_1384_){
_start:
{
uint8_t v___x_14270__boxed_1385_; lean_object* v_res_1386_; 
v___x_14270__boxed_1385_ = lean_unbox(v___x_1382_);
v_res_1386_ = l_Std_Http_Server_serve___redArg___lam__28(v___f_1379_, v___x_1380_, v___x_1381_, v___x_14270__boxed_1385_, v_x_1383_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29(lean_object* v___f_1387_, lean_object* v_connectionLimit_1388_, uint8_t v___x_1389_, lean_object* v___f_1390_, lean_object* v___x_1391_, lean_object* v___f_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v___f_1395_; lean_object* v___x_1396_; lean_object* v___f_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___f_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___f_1395_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__23___boxed), 4, 2);
lean_closure_set(v___f_1395_, 0, v___f_1387_);
lean_closure_set(v___f_1395_, 1, v___y_1393_);
v___x_1396_ = lean_box(v___x_1389_);
lean_inc_ref(v___f_1395_);
v___f_1397_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__26___boxed), 8, 5);
lean_closure_set(v___f_1397_, 0, v_connectionLimit_1388_);
lean_closure_set(v___f_1397_, 1, v___x_1396_);
lean_closure_set(v___f_1397_, 2, v___f_1395_);
lean_closure_set(v___f_1397_, 3, v___f_1390_);
lean_closure_set(v___f_1397_, 4, v___f_1395_);
v___x_1398_ = lean_unsigned_to_nat(0u);
v___x_1399_ = lean_box(v___x_1389_);
v___f_1400_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__28___boxed), 6, 4);
lean_closure_set(v___f_1400_, 0, v___f_1397_);
lean_closure_set(v___f_1400_, 1, v___x_1398_);
lean_closure_set(v___f_1400_, 2, v___x_1391_);
lean_closure_set(v___f_1400_, 3, v___x_1399_);
v___x_1401_ = lean_io_promise_new();
v___x_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
v___x_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1402_);
v___x_1404_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1398_, v___x_1389_, v___x_1403_, v___f_1400_);
v___x_1405_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1398_, v___x_1389_, v___x_1404_, v___f_1392_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29___boxed(lean_object* v___f_1406_, lean_object* v_connectionLimit_1407_, lean_object* v___x_1408_, lean_object* v___f_1409_, lean_object* v___x_1410_, lean_object* v___f_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
uint8_t v___x_14328__boxed_1414_; lean_object* v_res_1415_; 
v___x_14328__boxed_1414_ = lean_unbox(v___x_1408_);
v_res_1415_ = l_Std_Http_Server_serve___redArg___lam__29(v___f_1406_, v_connectionLimit_1407_, v___x_14328__boxed_1414_, v___f_1409_, v___x_1410_, v___f_1411_, v___y_1412_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30(lean_object* v___f_1420_, lean_object* v___f_1421_, lean_object* v___x_1422_, lean_object* v_inst_1423_, lean_object* v_handler_1424_, lean_object* v_config_1425_, lean_object* v___f_1426_, lean_object* v___f_1427_, lean_object* v___x_1428_, lean_object* v_a_1429_, lean_object* v___f_1430_, lean_object* v___f_1431_, lean_object* v___f_1432_, lean_object* v___f_1433_, lean_object* v___f_1434_, lean_object* v_x_1435_){
_start:
{
if (lean_obj_tag(v_x_1435_) == 0)
{
lean_object* v___x_1437_; 
lean_dec_ref(v___f_1434_);
lean_dec_ref(v___f_1433_);
lean_dec_ref(v___f_1432_);
lean_dec_ref(v___f_1431_);
lean_dec_ref(v___f_1430_);
lean_dec(v_a_1429_);
lean_dec(v___x_1428_);
lean_dec_ref(v___f_1427_);
lean_dec_ref(v___f_1426_);
lean_dec_ref(v_config_1425_);
lean_dec(v_handler_1424_);
lean_dec_ref(v_inst_1423_);
lean_dec_ref(v___x_1422_);
lean_dec_ref(v___f_1421_);
lean_dec_ref(v___f_1420_);
v___x_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1437_, 0, v_x_1435_);
return v___x_1437_;
}
else
{
lean_object* v_a_1438_; lean_object* v_context_1439_; lean_object* v_activeConnections_1440_; lean_object* v_connectionLimit_1441_; lean_object* v_shutdownPromise_1442_; lean_object* v___f_1443_; lean_object* v___f_1444_; lean_object* v___f_1445_; uint8_t v___x_1446_; lean_object* v___x_1447_; lean_object* v___f_1448_; lean_object* v___f_1449_; lean_object* v___x_1450_; lean_object* v___f_1451_; lean_object* v___x_1452_; lean_object* v___f_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v_a_1438_ = lean_ctor_get(v_x_1435_, 0);
lean_inc(v_a_1438_);
v_context_1439_ = lean_ctor_get(v_a_1438_, 0);
lean_inc_ref_n(v_context_1439_, 2);
v_activeConnections_1440_ = lean_ctor_get(v_a_1438_, 1);
v_connectionLimit_1441_ = lean_ctor_get(v_a_1438_, 2);
v_shutdownPromise_1442_ = lean_ctor_get(v_a_1438_, 3);
v___f_1443_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1443_, 0, v_x_1435_);
lean_inc_ref(v_shutdownPromise_1442_);
v___f_1444_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1444_, 0, v_context_1439_);
lean_closure_set(v___f_1444_, 1, v_shutdownPromise_1442_);
v___f_1445_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed), 5, 1);
lean_closure_set(v___f_1445_, 0, v___f_1444_);
v___x_1446_ = 0;
v___x_1447_ = lean_box(0);
v___f_1448_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__30___closed__0));
v___f_1449_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__30___closed__1));
v___x_1450_ = lean_box(v___x_1446_);
lean_inc_ref(v_activeConnections_1440_);
lean_inc_n(v_connectionLimit_1441_, 2);
v___f_1451_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__22___boxed), 23, 20);
lean_closure_set(v___f_1451_, 0, v___f_1448_);
lean_closure_set(v___f_1451_, 1, v___x_1447_);
lean_closure_set(v___f_1451_, 2, v_connectionLimit_1441_);
lean_closure_set(v___f_1451_, 3, v___x_1450_);
lean_closure_set(v___f_1451_, 4, v___f_1420_);
lean_closure_set(v___f_1451_, 5, v___f_1445_);
lean_closure_set(v___f_1451_, 6, v_activeConnections_1440_);
lean_closure_set(v___f_1451_, 7, v___f_1421_);
lean_closure_set(v___f_1451_, 8, v___x_1422_);
lean_closure_set(v___f_1451_, 9, v_inst_1423_);
lean_closure_set(v___f_1451_, 10, v_handler_1424_);
lean_closure_set(v___f_1451_, 11, v_config_1425_);
lean_closure_set(v___f_1451_, 12, v___f_1426_);
lean_closure_set(v___f_1451_, 13, v___f_1427_);
lean_closure_set(v___f_1451_, 14, v___f_1449_);
lean_closure_set(v___f_1451_, 15, v___x_1428_);
lean_closure_set(v___f_1451_, 16, v_a_1429_);
lean_closure_set(v___f_1451_, 17, v___f_1430_);
lean_closure_set(v___f_1451_, 18, v___f_1431_);
lean_closure_set(v___f_1451_, 19, v___f_1432_);
v___x_1452_ = lean_box(v___x_1446_);
v___f_1453_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__29___boxed), 8, 6);
lean_closure_set(v___f_1453_, 0, v___f_1451_);
lean_closure_set(v___f_1453_, 1, v_connectionLimit_1441_);
lean_closure_set(v___f_1453_, 2, v___x_1452_);
lean_closure_set(v___f_1453_, 3, v___f_1433_);
lean_closure_set(v___f_1453_, 4, v___x_1447_);
lean_closure_set(v___f_1453_, 5, v___f_1434_);
v___x_1454_ = lean_box(v___x_1446_);
v___x_1455_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___boxed), 6, 5);
lean_closure_set(v___x_1455_, 0, lean_box(0));
lean_closure_set(v___x_1455_, 1, v_a_1438_);
lean_closure_set(v___x_1455_, 2, v___x_1454_);
lean_closure_set(v___x_1455_, 3, v___f_1453_);
lean_closure_set(v___x_1455_, 4, v_context_1439_);
v___x_1456_ = lean_unsigned_to_nat(0u);
v___x_1457_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1457_, 0, lean_box(0));
lean_closure_set(v___x_1457_, 1, v___x_1455_);
v___x_1458_ = lean_io_as_task(v___x_1457_, v___x_1456_);
lean_dec_ref(v___x_1458_);
v___x_1459_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
v___x_1460_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1456_, v___x_1446_, v___x_1459_, v___f_1443_);
return v___x_1460_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30___boxed(lean_object** _args){
lean_object* v___f_1461_ = _args[0];
lean_object* v___f_1462_ = _args[1];
lean_object* v___x_1463_ = _args[2];
lean_object* v_inst_1464_ = _args[3];
lean_object* v_handler_1465_ = _args[4];
lean_object* v_config_1466_ = _args[5];
lean_object* v___f_1467_ = _args[6];
lean_object* v___f_1468_ = _args[7];
lean_object* v___x_1469_ = _args[8];
lean_object* v_a_1470_ = _args[9];
lean_object* v___f_1471_ = _args[10];
lean_object* v___f_1472_ = _args[11];
lean_object* v___f_1473_ = _args[12];
lean_object* v___f_1474_ = _args[13];
lean_object* v___f_1475_ = _args[14];
lean_object* v_x_1476_ = _args[15];
lean_object* v___y_1477_ = _args[16];
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Std_Http_Server_serve___redArg___lam__30(v___f_1461_, v___f_1462_, v___x_1463_, v_inst_1464_, v_handler_1465_, v_config_1466_, v___f_1467_, v___f_1468_, v___x_1469_, v_a_1470_, v___f_1471_, v___f_1472_, v___f_1473_, v___f_1474_, v___f_1475_, v_x_1476_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31(lean_object* v___f_1479_, lean_object* v_config_1480_, lean_object* v_x_1481_){
_start:
{
if (lean_obj_tag(v_x_1481_) == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1491_; 
lean_dec_ref(v_config_1480_);
lean_dec_ref(v___f_1479_);
v_a_1483_ = lean_ctor_get(v_x_1481_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_x_1481_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1485_ = v_x_1481_;
v_isShared_1486_ = v_isSharedCheck_1491_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v_x_1481_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1491_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
return v___x_1489_;
}
}
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1508_; 
v_a_1492_ = lean_ctor_get(v_x_1481_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_x_1481_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1494_ = v_x_1481_;
v_isShared_1495_ = v_isSharedCheck_1508_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v_x_1481_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1508_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; uint8_t v___x_1498_; lean_object* v_val_1500_; lean_object* v___x_1503_; lean_object* v_a_1504_; lean_object* v___x_1506_; 
v___x_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1496_, 0, v_a_1492_);
v___x_1497_ = lean_unsigned_to_nat(0u);
v___x_1498_ = 0;
v___x_1503_ = l_Std_Http_Server_new(v_config_1480_, v___x_1496_);
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1504_);
lean_dec_ref(v___x_1503_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 0, v_a_1504_);
v___x_1506_ = v___x_1494_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v___jp_1499_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1501_, 0, v_val_1500_);
v___x_1502_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1497_, v___x_1498_, v___x_1501_, v___f_1479_);
return v___x_1502_;
}
v_reusejp_1505_:
{
v_val_1500_ = v___x_1506_;
goto v___jp_1499_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31___boxed(lean_object* v___f_1509_, lean_object* v_config_1510_, lean_object* v_x_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Std_Http_Server_serve___redArg___lam__31(v___f_1509_, v_config_1510_, v_x_1511_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32(lean_object* v___f_1514_, lean_object* v_a_1515_, lean_object* v_x_1516_){
_start:
{
if (lean_obj_tag(v_x_1516_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1526_; 
lean_dec_ref(v___f_1514_);
v_a_1518_ = lean_ctor_get(v_x_1516_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v_x_1516_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1520_ = v_x_1516_;
v_isShared_1521_ = v_isSharedCheck_1526_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v_x_1516_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1526_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1518_);
v___x_1523_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
lean_object* v___x_1524_; 
v___x_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
return v___x_1524_;
}
}
}
else
{
lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1545_; 
v_isSharedCheck_1545_ = !lean_is_exclusive(v_x_1516_);
if (v_isSharedCheck_1545_ == 0)
{
lean_object* v_unused_1546_; 
v_unused_1546_ = lean_ctor_get(v_x_1516_, 0);
lean_dec(v_unused_1546_);
v___x_1528_ = v_x_1516_;
v_isShared_1529_ = v_isSharedCheck_1545_;
goto v_resetjp_1527_;
}
else
{
lean_dec(v_x_1516_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1545_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1530_; uint8_t v___x_1531_; lean_object* v_val_1533_; lean_object* v___x_1536_; 
v___x_1530_ = lean_unsigned_to_nat(0u);
v___x_1531_ = 0;
v___x_1536_ = lean_uv_tcp_getsockname(v_a_1515_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1539_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref_known(v___x_1536_, 1);
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 0, v_a_1537_);
v___x_1539_ = v___x_1528_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1537_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
v_val_1533_ = v___x_1539_;
goto v___jp_1532_;
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; 
v_a_1541_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1541_);
lean_dec_ref_known(v___x_1536_, 1);
if (v_isShared_1529_ == 0)
{
lean_ctor_set_tag(v___x_1528_, 0);
lean_ctor_set(v___x_1528_, 0, v_a_1541_);
v___x_1543_ = v___x_1528_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1541_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
v_val_1533_ = v___x_1543_;
goto v___jp_1532_;
}
}
v___jp_1532_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1534_, 0, v_val_1533_);
v___x_1535_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1530_, v___x_1531_, v___x_1534_, v___f_1514_);
return v___x_1535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32___boxed(lean_object* v___f_1547_, lean_object* v_a_1548_, lean_object* v_x_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Std_Http_Server_serve___redArg___lam__32(v___f_1547_, v_a_1548_, v_x_1549_);
lean_dec(v_a_1548_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__33(lean_object* v___f_1552_, lean_object* v_a_1553_, lean_object* v_x_1554_){
_start:
{
if (lean_obj_tag(v_x_1554_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1564_; 
lean_dec_ref(v___f_1552_);
v_a_1556_ = lean_ctor_get(v_x_1554_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v_x_1554_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1558_ = v_x_1554_;
v_isShared_1559_ = v_isSharedCheck_1564_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v_x_1554_);
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
lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1583_; 
v_isSharedCheck_1583_ = !lean_is_exclusive(v_x_1554_);
if (v_isSharedCheck_1583_ == 0)
{
lean_object* v_unused_1584_; 
v_unused_1584_ = lean_ctor_get(v_x_1554_, 0);
lean_dec(v_unused_1584_);
v___x_1566_ = v_x_1554_;
v_isShared_1567_ = v_isSharedCheck_1583_;
goto v_resetjp_1565_;
}
else
{
lean_dec(v_x_1554_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1583_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1568_; uint8_t v___x_1569_; lean_object* v_val_1571_; lean_object* v___x_1574_; 
v___x_1568_ = lean_unsigned_to_nat(0u);
v___x_1569_ = 0;
v___x_1574_ = lean_uv_tcp_nodelay(v_a_1553_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v___x_1577_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1575_);
lean_dec_ref_known(v___x_1574_, 1);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v_a_1575_);
v___x_1577_ = v___x_1566_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
v_val_1571_ = v___x_1577_;
goto v___jp_1570_;
}
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; 
v_a_1579_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1579_);
lean_dec_ref_known(v___x_1574_, 1);
if (v_isShared_1567_ == 0)
{
lean_ctor_set_tag(v___x_1566_, 0);
lean_ctor_set(v___x_1566_, 0, v_a_1579_);
v___x_1581_ = v___x_1566_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1579_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
v_val_1571_ = v___x_1581_;
goto v___jp_1570_;
}
}
v___jp_1570_:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1572_, 0, v_val_1571_);
v___x_1573_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1568_, v___x_1569_, v___x_1572_, v___f_1552_);
return v___x_1573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__33___boxed(lean_object* v___f_1585_, lean_object* v_a_1586_, lean_object* v_x_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Std_Http_Server_serve___redArg___lam__33(v___f_1585_, v_a_1586_, v_x_1587_);
lean_dec(v_a_1586_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__34(lean_object* v___f_1590_, lean_object* v_a_1591_, uint32_t v_backlog_1592_, lean_object* v_x_1593_){
_start:
{
if (lean_obj_tag(v_x_1593_) == 0)
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1603_; 
lean_dec_ref(v___f_1590_);
v_a_1595_ = lean_ctor_get(v_x_1593_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v_x_1593_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1597_ = v_x_1593_;
v_isShared_1598_ = v_isSharedCheck_1603_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v_x_1593_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1603_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v___x_1601_; 
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
return v___x_1601_;
}
}
}
else
{
lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1622_; 
v_isSharedCheck_1622_ = !lean_is_exclusive(v_x_1593_);
if (v_isSharedCheck_1622_ == 0)
{
lean_object* v_unused_1623_; 
v_unused_1623_ = lean_ctor_get(v_x_1593_, 0);
lean_dec(v_unused_1623_);
v___x_1605_ = v_x_1593_;
v_isShared_1606_ = v_isSharedCheck_1622_;
goto v_resetjp_1604_;
}
else
{
lean_dec(v_x_1593_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1622_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1607_; uint8_t v___x_1608_; lean_object* v_val_1610_; lean_object* v___x_1613_; 
v___x_1607_ = lean_unsigned_to_nat(0u);
v___x_1608_ = 0;
v___x_1613_ = lean_uv_tcp_listen(v_a_1591_, v_backlog_1592_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___x_1616_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref_known(v___x_1613_, 1);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 0, v_a_1614_);
v___x_1616_ = v___x_1605_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1614_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
v_val_1610_ = v___x_1616_;
goto v___jp_1609_;
}
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1620_; 
v_a_1618_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1618_);
lean_dec_ref_known(v___x_1613_, 1);
if (v_isShared_1606_ == 0)
{
lean_ctor_set_tag(v___x_1605_, 0);
lean_ctor_set(v___x_1605_, 0, v_a_1618_);
v___x_1620_ = v___x_1605_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1618_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
v_val_1610_ = v___x_1620_;
goto v___jp_1609_;
}
}
v___jp_1609_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1611_, 0, v_val_1610_);
v___x_1612_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1607_, v___x_1608_, v___x_1611_, v___f_1590_);
return v___x_1612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__34___boxed(lean_object* v___f_1624_, lean_object* v_a_1625_, lean_object* v_backlog_1626_, lean_object* v_x_1627_, lean_object* v___y_1628_){
_start:
{
uint32_t v_backlog_boxed_1629_; lean_object* v_res_1630_; 
v_backlog_boxed_1629_ = lean_unbox_uint32(v_backlog_1626_);
lean_dec(v_backlog_1626_);
v_res_1630_ = l_Std_Http_Server_serve___redArg___lam__34(v___f_1624_, v_a_1625_, v_backlog_boxed_1629_, v_x_1627_);
lean_dec(v_a_1625_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__35(lean_object* v___f_1631_, lean_object* v___f_1632_, lean_object* v___x_1633_, lean_object* v_inst_1634_, lean_object* v_handler_1635_, lean_object* v_config_1636_, lean_object* v___f_1637_, lean_object* v___f_1638_, lean_object* v___x_1639_, lean_object* v___f_1640_, lean_object* v___f_1641_, lean_object* v___f_1642_, lean_object* v___f_1643_, lean_object* v___f_1644_, uint32_t v_backlog_1645_, lean_object* v_addr_1646_, lean_object* v_x_1647_){
_start:
{
if (lean_obj_tag(v_x_1647_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1657_; 
lean_dec_ref(v___f_1644_);
lean_dec_ref(v___f_1643_);
lean_dec_ref(v___f_1642_);
lean_dec_ref(v___f_1641_);
lean_dec_ref(v___f_1640_);
lean_dec(v___x_1639_);
lean_dec_ref(v___f_1638_);
lean_dec_ref(v___f_1637_);
lean_dec_ref(v_config_1636_);
lean_dec(v_handler_1635_);
lean_dec_ref(v_inst_1634_);
lean_dec_ref(v___x_1633_);
lean_dec_ref(v___f_1632_);
lean_dec_ref(v___f_1631_);
v_a_1649_ = lean_ctor_get(v_x_1647_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_x_1647_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1651_ = v_x_1647_;
v_isShared_1652_ = v_isSharedCheck_1657_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v_x_1647_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1657_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
lean_object* v___x_1655_; 
v___x_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
return v___x_1655_;
}
}
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1683_; 
v_a_1658_ = lean_ctor_get(v_x_1647_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v_x_1647_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1660_ = v_x_1647_;
v_isShared_1661_ = v_isSharedCheck_1683_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v_x_1647_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1683_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___f_1662_; lean_object* v___f_1663_; lean_object* v___f_1664_; lean_object* v___f_1665_; lean_object* v___x_1666_; lean_object* v___f_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; lean_object* v_val_1671_; lean_object* v___x_1674_; 
lean_inc_n(v_a_1658_, 4);
lean_inc_ref(v_config_1636_);
v___f_1662_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__30___boxed), 17, 15);
lean_closure_set(v___f_1662_, 0, v___f_1631_);
lean_closure_set(v___f_1662_, 1, v___f_1632_);
lean_closure_set(v___f_1662_, 2, v___x_1633_);
lean_closure_set(v___f_1662_, 3, v_inst_1634_);
lean_closure_set(v___f_1662_, 4, v_handler_1635_);
lean_closure_set(v___f_1662_, 5, v_config_1636_);
lean_closure_set(v___f_1662_, 6, v___f_1637_);
lean_closure_set(v___f_1662_, 7, v___f_1638_);
lean_closure_set(v___f_1662_, 8, v___x_1639_);
lean_closure_set(v___f_1662_, 9, v_a_1658_);
lean_closure_set(v___f_1662_, 10, v___f_1640_);
lean_closure_set(v___f_1662_, 11, v___f_1641_);
lean_closure_set(v___f_1662_, 12, v___f_1642_);
lean_closure_set(v___f_1662_, 13, v___f_1643_);
lean_closure_set(v___f_1662_, 14, v___f_1644_);
v___f_1663_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__31___boxed), 4, 2);
lean_closure_set(v___f_1663_, 0, v___f_1662_);
lean_closure_set(v___f_1663_, 1, v_config_1636_);
v___f_1664_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__32___boxed), 4, 2);
lean_closure_set(v___f_1664_, 0, v___f_1663_);
lean_closure_set(v___f_1664_, 1, v_a_1658_);
v___f_1665_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__33___boxed), 4, 2);
lean_closure_set(v___f_1665_, 0, v___f_1664_);
lean_closure_set(v___f_1665_, 1, v_a_1658_);
v___x_1666_ = lean_box_uint32(v_backlog_1645_);
v___f_1667_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__34___boxed), 5, 3);
lean_closure_set(v___f_1667_, 0, v___f_1665_);
lean_closure_set(v___f_1667_, 1, v_a_1658_);
lean_closure_set(v___f_1667_, 2, v___x_1666_);
v___x_1668_ = lean_unsigned_to_nat(0u);
v___x_1669_ = 0;
v___x_1674_ = lean_uv_tcp_bind(v_a_1658_, v_addr_1646_);
lean_dec(v_a_1658_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; lean_object* v___x_1677_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_a_1675_);
lean_dec_ref_known(v___x_1674_, 1);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v_a_1675_);
v___x_1677_ = v___x_1660_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
v_val_1671_ = v___x_1677_;
goto v___jp_1670_;
}
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; 
v_a_1679_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_a_1679_);
lean_dec_ref_known(v___x_1674_, 1);
if (v_isShared_1661_ == 0)
{
lean_ctor_set_tag(v___x_1660_, 0);
lean_ctor_set(v___x_1660_, 0, v_a_1679_);
v___x_1681_ = v___x_1660_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1679_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
v_val_1671_ = v___x_1681_;
goto v___jp_1670_;
}
}
v___jp_1670_:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1672_, 0, v_val_1671_);
v___x_1673_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1668_, v___x_1669_, v___x_1672_, v___f_1667_);
return v___x_1673_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__35___boxed(lean_object** _args){
lean_object* v___f_1684_ = _args[0];
lean_object* v___f_1685_ = _args[1];
lean_object* v___x_1686_ = _args[2];
lean_object* v_inst_1687_ = _args[3];
lean_object* v_handler_1688_ = _args[4];
lean_object* v_config_1689_ = _args[5];
lean_object* v___f_1690_ = _args[6];
lean_object* v___f_1691_ = _args[7];
lean_object* v___x_1692_ = _args[8];
lean_object* v___f_1693_ = _args[9];
lean_object* v___f_1694_ = _args[10];
lean_object* v___f_1695_ = _args[11];
lean_object* v___f_1696_ = _args[12];
lean_object* v___f_1697_ = _args[13];
lean_object* v_backlog_1698_ = _args[14];
lean_object* v_addr_1699_ = _args[15];
lean_object* v_x_1700_ = _args[16];
lean_object* v___y_1701_ = _args[17];
_start:
{
uint32_t v_backlog_boxed_1702_; lean_object* v_res_1703_; 
v_backlog_boxed_1702_ = lean_unbox_uint32(v_backlog_1698_);
lean_dec(v_backlog_1698_);
v_res_1703_ = l_Std_Http_Server_serve___redArg___lam__35(v___f_1684_, v___f_1685_, v___x_1686_, v_inst_1687_, v_handler_1688_, v_config_1689_, v___f_1690_, v___f_1691_, v___x_1692_, v___f_1693_, v___f_1694_, v___f_1695_, v___f_1696_, v___f_1697_, v_backlog_boxed_1702_, v_addr_1699_, v_x_1700_);
lean_dec_ref(v_addr_1699_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg(lean_object* v_inst_1709_, lean_object* v_addr_1710_, lean_object* v_handler_1711_, lean_object* v_config_1712_, uint32_t v_backlog_1713_){
_start:
{
lean_object* v___f_1715_; lean_object* v___f_1716_; lean_object* v___f_1717_; lean_object* v___f_1718_; lean_object* v___f_1719_; lean_object* v___f_1720_; lean_object* v___f_1721_; lean_object* v___f_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___f_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; lean_object* v_val_1730_; lean_object* v___x_1733_; 
v___f_1715_ = ((lean_object*)(l_Std_Http_Server_waitShutdown___closed__0));
v___f_1716_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__0));
v___f_1717_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__1));
v___f_1718_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__2));
v___f_1719_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2));
v___f_1720_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0));
v___f_1721_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__3));
v___f_1722_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__4));
v___x_1723_ = l_Std_Http_instTransportClient;
v___x_1724_ = l_Std_Http_Server_instImpl_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8_;
v___x_1725_ = lean_box_uint32(v_backlog_1713_);
v___f_1726_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__35___boxed), 18, 16);
lean_closure_set(v___f_1726_, 0, v___f_1719_);
lean_closure_set(v___f_1726_, 1, v___f_1718_);
lean_closure_set(v___f_1726_, 2, v___x_1723_);
lean_closure_set(v___f_1726_, 3, v_inst_1709_);
lean_closure_set(v___f_1726_, 4, v_handler_1711_);
lean_closure_set(v___f_1726_, 5, v_config_1712_);
lean_closure_set(v___f_1726_, 6, v___f_1720_);
lean_closure_set(v___f_1726_, 7, v___f_1718_);
lean_closure_set(v___f_1726_, 8, v___x_1724_);
lean_closure_set(v___f_1726_, 9, v___f_1716_);
lean_closure_set(v___f_1726_, 10, v___f_1717_);
lean_closure_set(v___f_1726_, 11, v___f_1721_);
lean_closure_set(v___f_1726_, 12, v___f_1715_);
lean_closure_set(v___f_1726_, 13, v___f_1722_);
lean_closure_set(v___f_1726_, 14, v___x_1725_);
lean_closure_set(v___f_1726_, 15, v_addr_1710_);
v___x_1727_ = lean_unsigned_to_nat(0u);
v___x_1728_ = 0;
v___x_1733_ = lean_uv_tcp_new();
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1741_; 
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1736_ = v___x_1733_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1733_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
if (v_isShared_1737_ == 0)
{
lean_ctor_set_tag(v___x_1736_, 1);
v___x_1739_ = v___x_1736_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_a_1734_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
v_val_1730_ = v___x_1739_;
goto v___jp_1729_;
}
}
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
v_a_1742_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1733_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1733_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
lean_ctor_set_tag(v___x_1744_, 0);
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
v_val_1730_ = v___x_1747_;
goto v___jp_1729_;
}
}
}
v___jp_1729_:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v_val_1730_);
v___x_1732_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1727_, v___x_1728_, v___x_1731_, v___f_1726_);
return v___x_1732_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___boxed(lean_object* v_inst_1750_, lean_object* v_addr_1751_, lean_object* v_handler_1752_, lean_object* v_config_1753_, lean_object* v_backlog_1754_, lean_object* v_a_1755_){
_start:
{
uint32_t v_backlog_boxed_1756_; lean_object* v_res_1757_; 
v_backlog_boxed_1756_ = lean_unbox_uint32(v_backlog_1754_);
lean_dec(v_backlog_1754_);
v_res_1757_ = l_Std_Http_Server_serve___redArg(v_inst_1750_, v_addr_1751_, v_handler_1752_, v_config_1753_, v_backlog_boxed_1756_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve(lean_object* v_00_u03c3_1758_, lean_object* v_inst_1759_, lean_object* v_addr_1760_, lean_object* v_handler_1761_, lean_object* v_config_1762_, uint32_t v_backlog_1763_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Std_Http_Server_serve___redArg(v_inst_1759_, v_addr_1760_, v_handler_1761_, v_config_1762_, v_backlog_1763_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___boxed(lean_object* v_00_u03c3_1766_, lean_object* v_inst_1767_, lean_object* v_addr_1768_, lean_object* v_handler_1769_, lean_object* v_config_1770_, lean_object* v_backlog_1771_, lean_object* v_a_1772_){
_start:
{
uint32_t v_backlog_boxed_1773_; lean_object* v_res_1774_; 
v_backlog_boxed_1773_ = lean_unbox_uint32(v_backlog_1771_);
lean_dec(v_backlog_1771_);
v_res_1774_ = l_Std_Http_Server_serve(v_00_u03c3_1766_, v_inst_1767_, v_addr_1768_, v_handler_1769_, v_config_1770_, v_backlog_boxed_1773_);
return v_res_1774_;
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
