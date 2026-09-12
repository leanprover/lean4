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
lean_object* l_Std_Channel_send___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Std_CancellationToken_isCancelled(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Std_CancellationContext_cancel(lean_object*, lean_object*);
lean_object* l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_ContextAsync_instMonadFinally___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Mutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* l_Std_Semaphore_acquire(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Server_serve___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Server_serve___redArg___lam__1___closed__0 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Std_Http_Server_serve___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Server_serve___redArg___lam__1___closed__0_value)}};
static const lean_object* l_Std_Http_Server_serve___redArg___lam__1___closed__1 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Server_serve___redArg___lam__28___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__10___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Server_serve___redArg___lam__28___closed__0 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__28___closed__0_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___lam__28___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__7___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
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
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__1 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__1_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__2 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__2_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__4___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__3 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__3_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__5___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__4 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__4_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2(lean_object* v_x_437_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_439_, 0, v_x_437_);
v___x_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2___boxed(lean_object* v_x_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Std_Http_Server_serve___redArg___lam__2(v_x_442_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1(lean_object* v_x_449_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__1___closed__1));
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1___boxed(lean_object* v_x_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Std_Http_Server_serve___redArg___lam__1(v_x_452_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4(lean_object* v_x_455_){
_start:
{
lean_object* v_fst_456_; 
v_fst_456_ = lean_ctor_get(v_x_455_, 0);
lean_inc(v_fst_456_);
return v_fst_456_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4___boxed(lean_object* v_x_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Std_Http_Server_serve___redArg___lam__4(v_x_457_);
lean_dec_ref(v_x_457_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5(lean_object* v_x_459_){
_start:
{
if (lean_obj_tag(v_x_459_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_469_; 
v_a_461_ = lean_ctor_get(v_x_459_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v_x_459_);
if (v_isSharedCheck_469_ == 0)
{
v___x_463_ = v_x_459_;
v_isShared_464_ = v_isSharedCheck_469_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v_x_459_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_469_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_468_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_467_; 
v___x_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
return v___x_467_;
}
}
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_480_; 
v_a_470_ = lean_ctor_get(v_x_459_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v_x_459_);
if (v_isSharedCheck_480_ == 0)
{
v___x_472_ = v_x_459_;
v_isShared_473_ = v_isSharedCheck_480_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v_x_459_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_480_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v_token_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v_token_474_ = lean_ctor_get(v_a_470_, 1);
lean_inc_ref(v_token_474_);
lean_dec(v_a_470_);
v___x_475_ = l_Std_CancellationToken_selector(v_token_474_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_475_);
v___x_477_ = v___x_472_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_475_);
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
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5___boxed(lean_object* v_x_481_, lean_object* v___y_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Std_Http_Server_serve___redArg___lam__5(v_x_481_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3(lean_object* v_x_484_){
_start:
{
if (lean_obj_tag(v_x_484_) == 0)
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_494_; 
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
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_523_; 
v_a_495_ = lean_ctor_get(v_x_484_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v_x_484_);
if (v_isSharedCheck_523_ == 0)
{
v___x_497_ = v_x_484_;
v_isShared_498_ = v_isSharedCheck_523_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v_x_484_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_523_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
if (lean_obj_tag(v_a_495_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_510_; 
v_a_499_ = lean_ctor_get(v_a_495_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v_a_495_);
if (v_isSharedCheck_510_ == 0)
{
v___x_501_ = v_a_495_;
v_isShared_502_ = v_isSharedCheck_510_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v_a_495_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_510_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
lean_ctor_set_tag(v___x_501_, 1);
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_509_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_506_; 
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_504_);
v___x_506_ = v___x_497_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_508_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_507_; 
v___x_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
return v___x_507_;
}
}
}
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_522_; 
v_a_511_ = lean_ctor_get(v_a_495_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v_a_495_);
if (v_isSharedCheck_522_ == 0)
{
v___x_513_ = v_a_495_;
v_isShared_514_ = v_isSharedCheck_522_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v_a_495_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_522_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
lean_ctor_set_tag(v___x_513_, 0);
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_521_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_518_; 
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_516_);
v___x_518_ = v___x_497_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_516_);
v___x_518_ = v_reuseFailAlloc_520_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_519_; 
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3___boxed(lean_object* v_x_524_, lean_object* v___y_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Std_Http_Server_serve___redArg___lam__3(v_x_524_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6(lean_object* v_x_527_, lean_object* v_x_528_){
_start:
{
if (lean_obj_tag(v_x_528_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_538_; 
lean_dec_ref(v_x_527_);
v_a_530_ = lean_ctor_get(v_x_528_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v_x_528_);
if (v_isSharedCheck_538_ == 0)
{
v___x_532_ = v_x_528_;
v_isShared_533_ = v_isSharedCheck_538_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v_x_528_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_538_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_530_);
v___x_535_ = v_reuseFailAlloc_537_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_536_; 
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
return v___x_536_;
}
}
}
else
{
lean_object* v___x_539_; 
lean_dec_ref_known(v_x_528_, 1);
v___x_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_539_, 0, v_x_527_);
return v___x_539_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6___boxed(lean_object* v_x_540_, lean_object* v_x_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Std_Http_Server_serve___redArg___lam__6(v_x_540_, v_x_541_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10(lean_object* v___x_544_, lean_object* v_x_545_){
_start:
{
if (lean_obj_tag(v_x_545_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_555_; 
v_a_547_ = lean_ctor_get(v_x_545_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v_x_545_);
if (v_isSharedCheck_555_ == 0)
{
v___x_549_ = v_x_545_;
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v_x_545_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_547_);
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
else
{
lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_564_; 
v_isSharedCheck_564_ = !lean_is_exclusive(v_x_545_);
if (v_isSharedCheck_564_ == 0)
{
lean_object* v_unused_565_; 
v_unused_565_ = lean_ctor_get(v_x_545_, 0);
lean_dec(v_unused_565_);
v___x_557_ = v_x_545_;
v_isShared_558_ = v_isSharedCheck_564_;
goto v_resetjp_556_;
}
else
{
lean_dec(v_x_545_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_564_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_544_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_559_);
v___x_561_ = v___x_557_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_559_);
v___x_561_ = v_reuseFailAlloc_563_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v___x_562_; 
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
return v___x_562_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10___boxed(lean_object* v___x_566_, lean_object* v_x_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Std_Http_Server_serve___redArg___lam__10(v___x_566_, v_x_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7(lean_object* v___x_570_, lean_object* v_____r_571_, lean_object* v___y_572_){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_570_);
v___x_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7___boxed(lean_object* v___x_577_, lean_object* v_____r_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Std_Http_Server_serve___redArg___lam__7(v___x_577_, v_____r_578_, v___y_579_);
lean_dec_ref(v___y_579_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8(lean_object* v___f_582_, lean_object* v___y_583_, lean_object* v_x_584_){
_start:
{
if (lean_obj_tag(v_x_584_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_594_; 
lean_dec_ref(v___f_582_);
v_a_586_ = lean_ctor_get(v_x_584_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v_x_584_);
if (v_isSharedCheck_594_ == 0)
{
v___x_588_ = v_x_584_;
v_isShared_589_ = v_isSharedCheck_594_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v_x_584_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_594_;
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
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_593_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_592_; 
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
return v___x_592_;
}
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_596_; 
v_a_595_ = lean_ctor_get(v_x_584_, 0);
lean_inc(v_a_595_);
lean_dec_ref_known(v_x_584_, 1);
lean_inc_ref(v___y_583_);
v___x_596_ = lean_apply_3(v___f_582_, v_a_595_, v___y_583_, lean_box(0));
return v___x_596_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8___boxed(lean_object* v___f_597_, lean_object* v___y_598_, lean_object* v_x_599_, lean_object* v___y_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Std_Http_Server_serve___redArg___lam__8(v___f_597_, v___y_598_, v_x_599_);
lean_dec_ref(v___y_598_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9(lean_object* v_a_602_, lean_object* v_x_603_){
_start:
{
if (lean_obj_tag(v_x_603_) == 0)
{
lean_object* v___x_605_; 
lean_dec_ref(v_a_602_);
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v_x_603_);
return v___x_605_;
}
else
{
lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_615_; 
v_isSharedCheck_615_ = !lean_is_exclusive(v_x_603_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v_x_603_, 0);
lean_dec(v_unused_616_);
v___x_607_ = v_x_603_;
v_isShared_608_ = v_isSharedCheck_615_;
goto v_resetjp_606_;
}
else
{
lean_dec(v_x_603_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_615_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_609_ = lean_box(2);
v___x_610_ = l_Std_CancellationContext_cancel(v_a_602_, v___x_609_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_610_);
v___x_612_ = v___x_607_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_614_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_613_; 
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
return v___x_613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9___boxed(lean_object* v_a_617_, lean_object* v_x_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Std_Http_Server_serve___redArg___lam__9(v_a_617_, v_x_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12(lean_object* v___f_621_, lean_object* v_a_622_, lean_object* v_x_623_){
_start:
{
if (lean_obj_tag(v_x_623_) == 0)
{
lean_object* v___x_625_; 
lean_dec_ref(v_a_622_);
lean_dec_ref(v___f_621_);
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v_x_623_);
return v___x_625_;
}
else
{
lean_object* v_a_626_; lean_object* v___x_627_; 
v_a_626_ = lean_ctor_get(v_x_623_, 0);
lean_inc(v_a_626_);
lean_dec_ref_known(v_x_623_, 1);
v___x_627_ = lean_apply_3(v___f_621_, v_a_626_, v_a_622_, lean_box(0));
return v___x_627_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12___boxed(lean_object* v___f_628_, lean_object* v_a_629_, lean_object* v_x_630_, lean_object* v___y_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Std_Http_Server_serve___redArg___lam__12(v___f_628_, v_a_629_, v_x_630_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11(uint8_t v_permitAcquired_633_, lean_object* v___f_634_, lean_object* v___x_635_, lean_object* v_a_636_, lean_object* v_connectionLimit_637_, lean_object* v___x_638_, uint8_t v___x_639_, lean_object* v___f_640_, lean_object* v_opt_641_){
_start:
{
if (v_permitAcquired_633_ == 0)
{
lean_object* v___x_643_; 
lean_dec_ref(v___f_640_);
lean_dec(v___x_638_);
lean_dec(v_connectionLimit_637_);
v___x_643_ = lean_apply_3(v___f_634_, v___x_635_, v_a_636_, lean_box(0));
return v___x_643_;
}
else
{
if (lean_obj_tag(v_connectionLimit_637_) == 1)
{
lean_object* v_val_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_654_; 
lean_dec_ref(v_a_636_);
lean_dec_ref(v___f_634_);
v_val_644_ = lean_ctor_get(v_connectionLimit_637_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v_connectionLimit_637_);
if (v_isSharedCheck_654_ == 0)
{
v___x_646_ = v_connectionLimit_637_;
v_isShared_647_ = v_isSharedCheck_654_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_val_644_);
lean_dec(v_connectionLimit_637_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_654_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_648_; lean_object* v___x_650_; 
v___x_648_ = l_Std_Semaphore_release(v_val_644_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v___x_648_);
v___x_650_ = v___x_646_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_648_);
v___x_650_ = v_reuseFailAlloc_653_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
v___x_652_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_638_, v___x_639_, v___x_651_, v___f_640_);
return v___x_652_;
}
}
}
else
{
lean_object* v___x_655_; 
lean_dec_ref(v___f_640_);
lean_dec(v___x_638_);
lean_dec(v_connectionLimit_637_);
v___x_655_ = lean_apply_3(v___f_634_, v___x_635_, v_a_636_, lean_box(0));
return v___x_655_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11___boxed(lean_object* v_permitAcquired_656_, lean_object* v___f_657_, lean_object* v___x_658_, lean_object* v_a_659_, lean_object* v_connectionLimit_660_, lean_object* v___x_661_, lean_object* v___x_662_, lean_object* v___f_663_, lean_object* v_opt_664_, lean_object* v___y_665_){
_start:
{
uint8_t v_permitAcquired_boxed_666_; uint8_t v___x_13545__boxed_667_; lean_object* v_res_668_; 
v_permitAcquired_boxed_666_ = lean_unbox(v_permitAcquired_656_);
v___x_13545__boxed_667_ = lean_unbox(v___x_662_);
v_res_668_ = l_Std_Http_Server_serve___redArg___lam__11(v_permitAcquired_boxed_666_, v___f_657_, v___x_658_, v_a_659_, v_connectionLimit_660_, v___x_661_, v___x_13545__boxed_667_, v___f_663_, v_opt_664_);
lean_dec(v_opt_664_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13(lean_object* v___f_669_, lean_object* v___x_670_, lean_object* v_inst_671_, lean_object* v_val_672_, lean_object* v_handler_673_, lean_object* v_config_674_, lean_object* v_extensions_675_, lean_object* v_a_676_, lean_object* v___f_677_, lean_object* v___x_678_, uint8_t v___x_679_, lean_object* v_x_680_){
_start:
{
if (lean_obj_tag(v_x_680_) == 0)
{
lean_object* v___x_682_; 
lean_dec(v___x_678_);
lean_dec_ref(v___f_677_);
lean_dec_ref(v_a_676_);
lean_dec(v_extensions_675_);
lean_dec_ref(v_config_674_);
lean_dec(v_handler_673_);
lean_dec(v_val_672_);
lean_dec_ref(v_inst_671_);
lean_dec_ref(v___x_670_);
lean_dec_ref(v___f_669_);
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v_x_680_);
return v___x_682_;
}
else
{
lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_721_; 
v_isSharedCheck_721_ = !lean_is_exclusive(v_x_680_);
if (v_isSharedCheck_721_ == 0)
{
lean_object* v_unused_722_; 
v_unused_722_ = lean_ctor_get(v_x_680_, 0);
lean_dec(v_unused_722_);
v___x_684_ = v_x_680_;
v_isShared_685_ = v_isSharedCheck_721_;
goto v_resetjp_683_;
}
else
{
lean_dec(v_x_680_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_721_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___y_690_; 
v___x_686_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_686_, 0, lean_box(0));
lean_closure_set(v___x_686_, 1, lean_box(0));
lean_closure_set(v___x_686_, 2, lean_box(0));
lean_closure_set(v___x_686_, 3, v___f_669_);
v___x_687_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___boxed), 10, 9);
lean_closure_set(v___x_687_, 0, lean_box(0));
lean_closure_set(v___x_687_, 1, lean_box(0));
lean_closure_set(v___x_687_, 2, v___x_670_);
lean_closure_set(v___x_687_, 3, v_inst_671_);
lean_closure_set(v___x_687_, 4, v_val_672_);
lean_closure_set(v___x_687_, 5, v_handler_673_);
lean_closure_set(v___x_687_, 6, v_config_674_);
lean_closure_set(v___x_687_, 7, v_extensions_675_);
lean_closure_set(v___x_687_, 8, v_a_676_);
lean_inc(v___x_678_);
v___x_688_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_687_, v___f_677_, v___x_678_, v___x_679_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_694_; 
lean_dec_ref(v___x_686_);
lean_dec(v___x_678_);
v_a_694_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_a_694_);
lean_dec_ref_known(v___x_688_, 1);
if (lean_obj_tag(v_a_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
v_a_695_ = lean_ctor_get(v_a_694_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v_a_694_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v_a_694_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v_a_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
v___y_690_ = v___x_700_;
goto v___jp_689_;
}
}
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_711_; 
v_a_703_ = lean_ctor_get(v_a_694_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v_a_694_);
if (v_isSharedCheck_711_ == 0)
{
v___x_705_ = v_a_694_;
v_isShared_706_ = v_isSharedCheck_711_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v_a_694_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_711_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v_fst_707_; lean_object* v___x_709_; 
v_fst_707_ = lean_ctor_get(v_a_703_, 0);
lean_inc(v_fst_707_);
lean_dec(v_a_703_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v_fst_707_);
v___x_709_ = v___x_705_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_fst_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
v___y_690_ = v___x_709_;
goto v___jp_689_;
}
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_720_; 
lean_del_object(v___x_684_);
v_a_712_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_720_ == 0)
{
v___x_714_ = v___x_688_;
v_isShared_715_ = v_isSharedCheck_720_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_688_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_720_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_716_ = lean_task_map(v___x_686_, v_a_712_, v___x_678_, v___x_679_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_716_);
v___x_718_ = v___x_714_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
v___jp_689_:
{
lean_object* v___x_692_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set_tag(v___x_684_, 0);
lean_ctor_set(v___x_684_, 0, v___y_690_);
v___x_692_ = v___x_684_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___y_690_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13___boxed(lean_object* v___f_723_, lean_object* v___x_724_, lean_object* v_inst_725_, lean_object* v_val_726_, lean_object* v_handler_727_, lean_object* v_config_728_, lean_object* v_extensions_729_, lean_object* v_a_730_, lean_object* v___f_731_, lean_object* v___x_732_, lean_object* v___x_733_, lean_object* v_x_734_, lean_object* v___y_735_){
_start:
{
uint8_t v___x_13595__boxed_736_; lean_object* v_res_737_; 
v___x_13595__boxed_736_ = lean_unbox(v___x_733_);
v_res_737_ = l_Std_Http_Server_serve___redArg___lam__13(v___f_723_, v___x_724_, v_inst_725_, v_val_726_, v_handler_727_, v_config_728_, v_extensions_729_, v_a_730_, v___f_731_, v___x_732_, v___x_13595__boxed_736_, v_x_734_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14(lean_object* v___x_738_, lean_object* v___f_739_, lean_object* v___f_740_, lean_object* v_activeConnections_741_, lean_object* v_a_742_, uint8_t v_permitAcquired_743_, lean_object* v___x_744_, lean_object* v_connectionLimit_745_, lean_object* v___x_746_, uint8_t v___x_747_, lean_object* v___f_748_, lean_object* v___x_749_, lean_object* v_inst_750_, lean_object* v_val_751_, lean_object* v_handler_752_, lean_object* v_config_753_, lean_object* v_extensions_754_, lean_object* v___f_755_, lean_object* v___f_756_){
_start:
{
lean_object* v___f_758_; lean_object* v___f_759_; lean_object* v___f_760_; lean_object* v___f_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___f_764_; lean_object* v___x_765_; lean_object* v___f_766_; lean_object* v___x_12703__overap_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___f_758_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5));
v___f_759_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6));
lean_inc_ref(v_activeConnections_741_);
lean_inc_ref(v___x_738_);
v___f_760_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed), 9, 6);
lean_closure_set(v___f_760_, 0, v___x_738_);
lean_closure_set(v___f_760_, 1, v___f_739_);
lean_closure_set(v___f_760_, 2, v___f_740_);
lean_closure_set(v___f_760_, 3, v___f_758_);
lean_closure_set(v___f_760_, 4, v___f_759_);
lean_closure_set(v___f_760_, 5, v_activeConnections_741_);
lean_inc_ref_n(v_a_742_, 3);
lean_inc_ref(v___f_760_);
v___f_761_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__12___boxed), 4, 2);
lean_closure_set(v___f_761_, 0, v___f_760_);
lean_closure_set(v___f_761_, 1, v_a_742_);
v___x_762_ = lean_box(v_permitAcquired_743_);
v___x_763_ = lean_box(v___x_747_);
lean_inc_n(v___x_746_, 3);
v___f_764_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__11___boxed), 10, 8);
lean_closure_set(v___f_764_, 0, v___x_762_);
lean_closure_set(v___f_764_, 1, v___f_760_);
lean_closure_set(v___f_764_, 2, v___x_744_);
lean_closure_set(v___f_764_, 3, v_a_742_);
lean_closure_set(v___f_764_, 4, v_connectionLimit_745_);
lean_closure_set(v___f_764_, 5, v___x_746_);
lean_closure_set(v___f_764_, 6, v___x_763_);
lean_closure_set(v___f_764_, 7, v___f_761_);
v___x_765_ = lean_box(v___x_747_);
v___f_766_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__13___boxed), 13, 11);
lean_closure_set(v___f_766_, 0, v___f_748_);
lean_closure_set(v___f_766_, 1, v___x_749_);
lean_closure_set(v___f_766_, 2, v_inst_750_);
lean_closure_set(v___f_766_, 3, v_val_751_);
lean_closure_set(v___f_766_, 4, v_handler_752_);
lean_closure_set(v___f_766_, 5, v_config_753_);
lean_closure_set(v___f_766_, 6, v_extensions_754_);
lean_closure_set(v___f_766_, 7, v_a_742_);
lean_closure_set(v___f_766_, 8, v___f_764_);
lean_closure_set(v___f_766_, 9, v___x_746_);
lean_closure_set(v___f_766_, 10, v___x_765_);
v___x_12703__overap_767_ = l_Std_Mutex_atomically___redArg(v___x_738_, v___f_758_, v___f_759_, v_activeConnections_741_, v___f_755_);
v___x_768_ = lean_apply_2(v___x_12703__overap_767_, v_a_742_, lean_box(0));
v___x_769_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_746_, v___x_747_, v___x_768_, v___f_766_);
v___x_770_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_746_, v___x_747_, v___x_769_, v___f_756_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14___boxed(lean_object** _args){
lean_object* v___x_771_ = _args[0];
lean_object* v___f_772_ = _args[1];
lean_object* v___f_773_ = _args[2];
lean_object* v_activeConnections_774_ = _args[3];
lean_object* v_a_775_ = _args[4];
lean_object* v_permitAcquired_776_ = _args[5];
lean_object* v___x_777_ = _args[6];
lean_object* v_connectionLimit_778_ = _args[7];
lean_object* v___x_779_ = _args[8];
lean_object* v___x_780_ = _args[9];
lean_object* v___f_781_ = _args[10];
lean_object* v___x_782_ = _args[11];
lean_object* v_inst_783_ = _args[12];
lean_object* v_val_784_ = _args[13];
lean_object* v_handler_785_ = _args[14];
lean_object* v_config_786_ = _args[15];
lean_object* v_extensions_787_ = _args[16];
lean_object* v___f_788_ = _args[17];
lean_object* v___f_789_ = _args[18];
lean_object* v___y_790_ = _args[19];
_start:
{
uint8_t v_permitAcquired_boxed_791_; uint8_t v___x_13712__boxed_792_; lean_object* v_res_793_; 
v_permitAcquired_boxed_791_ = lean_unbox(v_permitAcquired_776_);
v___x_13712__boxed_792_ = lean_unbox(v___x_780_);
v_res_793_ = l_Std_Http_Server_serve___redArg___lam__14(v___x_771_, v___f_772_, v___f_773_, v_activeConnections_774_, v_a_775_, v_permitAcquired_boxed_791_, v___x_777_, v_connectionLimit_778_, v___x_779_, v___x_13712__boxed_792_, v___f_781_, v___x_782_, v_inst_783_, v_val_784_, v_handler_785_, v_config_786_, v_extensions_787_, v___f_788_, v___f_789_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15(lean_object* v___x_794_, lean_object* v___f_795_, lean_object* v___f_796_, lean_object* v_activeConnections_797_, uint8_t v_permitAcquired_798_, lean_object* v___x_799_, lean_object* v_connectionLimit_800_, lean_object* v___x_801_, uint8_t v___x_802_, lean_object* v___f_803_, lean_object* v___x_804_, lean_object* v_inst_805_, lean_object* v_val_806_, lean_object* v_handler_807_, lean_object* v_config_808_, lean_object* v_extensions_809_, lean_object* v___f_810_, lean_object* v_x_811_){
_start:
{
if (lean_obj_tag(v_x_811_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_821_; 
lean_dec_ref(v___f_810_);
lean_dec(v_extensions_809_);
lean_dec_ref(v_config_808_);
lean_dec(v_handler_807_);
lean_dec(v_val_806_);
lean_dec_ref(v_inst_805_);
lean_dec_ref(v___x_804_);
lean_dec_ref(v___f_803_);
lean_dec(v___x_801_);
lean_dec(v_connectionLimit_800_);
lean_dec_ref(v_activeConnections_797_);
lean_dec_ref(v___f_796_);
lean_dec_ref(v___f_795_);
lean_dec_ref(v___x_794_);
v_a_813_ = lean_ctor_get(v_x_811_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v_x_811_);
if (v_isSharedCheck_821_ == 0)
{
v___x_815_ = v_x_811_;
v_isShared_816_ = v_isSharedCheck_821_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v_x_811_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_821_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_820_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_819_; 
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
return v___x_819_;
}
}
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_836_; 
v_a_822_ = lean_ctor_get(v_x_811_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v_x_811_);
if (v_isSharedCheck_836_ == 0)
{
v___x_824_ = v_x_811_;
v_isShared_825_ = v_isSharedCheck_836_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v_x_811_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_836_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___f_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___f_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_833_; 
lean_inc(v_a_822_);
v___f_826_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_826_, 0, v_a_822_);
v___x_827_ = lean_box(v_permitAcquired_798_);
v___x_828_ = lean_box(v___x_802_);
lean_inc(v___x_801_);
v___f_829_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__14___boxed), 20, 19);
lean_closure_set(v___f_829_, 0, v___x_794_);
lean_closure_set(v___f_829_, 1, v___f_795_);
lean_closure_set(v___f_829_, 2, v___f_796_);
lean_closure_set(v___f_829_, 3, v_activeConnections_797_);
lean_closure_set(v___f_829_, 4, v_a_822_);
lean_closure_set(v___f_829_, 5, v___x_827_);
lean_closure_set(v___f_829_, 6, v___x_799_);
lean_closure_set(v___f_829_, 7, v_connectionLimit_800_);
lean_closure_set(v___f_829_, 8, v___x_801_);
lean_closure_set(v___f_829_, 9, v___x_828_);
lean_closure_set(v___f_829_, 10, v___f_803_);
lean_closure_set(v___f_829_, 11, v___x_804_);
lean_closure_set(v___f_829_, 12, v_inst_805_);
lean_closure_set(v___f_829_, 13, v_val_806_);
lean_closure_set(v___f_829_, 14, v_handler_807_);
lean_closure_set(v___f_829_, 15, v_config_808_);
lean_closure_set(v___f_829_, 16, v_extensions_809_);
lean_closure_set(v___f_829_, 17, v___f_810_);
lean_closure_set(v___f_829_, 18, v___f_826_);
v___x_830_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_830_, 0, lean_box(0));
lean_closure_set(v___x_830_, 1, v___f_829_);
v___x_831_ = lean_io_as_task(v___x_830_, v___x_801_);
lean_dec_ref(v___x_831_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_799_);
v___x_833_ = v___x_824_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_799_);
v___x_833_ = v_reuseFailAlloc_835_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_834_; 
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
return v___x_834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15___boxed(lean_object** _args){
lean_object* v___x_837_ = _args[0];
lean_object* v___f_838_ = _args[1];
lean_object* v___f_839_ = _args[2];
lean_object* v_activeConnections_840_ = _args[3];
lean_object* v_permitAcquired_841_ = _args[4];
lean_object* v___x_842_ = _args[5];
lean_object* v_connectionLimit_843_ = _args[6];
lean_object* v___x_844_ = _args[7];
lean_object* v___x_845_ = _args[8];
lean_object* v___f_846_ = _args[9];
lean_object* v___x_847_ = _args[10];
lean_object* v_inst_848_ = _args[11];
lean_object* v_val_849_ = _args[12];
lean_object* v_handler_850_ = _args[13];
lean_object* v_config_851_ = _args[14];
lean_object* v_extensions_852_ = _args[15];
lean_object* v___f_853_ = _args[16];
lean_object* v_x_854_ = _args[17];
lean_object* v___y_855_ = _args[18];
_start:
{
uint8_t v_permitAcquired_boxed_856_; uint8_t v___x_13779__boxed_857_; lean_object* v_res_858_; 
v_permitAcquired_boxed_856_ = lean_unbox(v_permitAcquired_841_);
v___x_13779__boxed_857_ = lean_unbox(v___x_845_);
v_res_858_ = l_Std_Http_Server_serve___redArg___lam__15(v___x_837_, v___f_838_, v___f_839_, v_activeConnections_840_, v_permitAcquired_boxed_856_, v___x_842_, v_connectionLimit_843_, v___x_844_, v___x_13779__boxed_857_, v___f_846_, v___x_847_, v_inst_848_, v_val_849_, v_handler_850_, v_config_851_, v_extensions_852_, v___f_853_, v_x_854_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16(lean_object* v___x_859_, uint8_t v___x_860_, lean_object* v___f_861_, lean_object* v_x_862_){
_start:
{
if (lean_obj_tag(v_x_862_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_872_; 
lean_dec_ref(v___f_861_);
lean_dec(v___x_859_);
v_a_864_ = lean_ctor_get(v_x_862_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v_x_862_);
if (v_isSharedCheck_872_ == 0)
{
v___x_866_ = v_x_862_;
v_isShared_867_ = v_isSharedCheck_872_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v_x_862_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_872_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_871_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_870_; 
v___x_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
return v___x_870_;
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_883_; 
v_a_873_ = lean_ctor_get(v_x_862_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v_x_862_);
if (v_isSharedCheck_883_ == 0)
{
v___x_875_ = v_x_862_;
v_isShared_876_ = v_isSharedCheck_883_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v_x_862_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_883_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_877_; lean_object* v___x_879_; 
v___x_877_ = l_Std_CancellationContext_fork(v_a_873_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v___x_877_);
v___x_879_ = v___x_875_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_877_);
v___x_879_ = v_reuseFailAlloc_882_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
v___x_881_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_859_, v___x_860_, v___x_880_, v___f_861_);
return v___x_881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16___boxed(lean_object* v___x_884_, lean_object* v___x_885_, lean_object* v___f_886_, lean_object* v_x_887_, lean_object* v___y_888_){
_start:
{
uint8_t v___x_13862__boxed_889_; lean_object* v_res_890_; 
v___x_13862__boxed_889_ = lean_unbox(v___x_885_);
v_res_890_ = l_Std_Http_Server_serve___redArg___lam__16(v___x_884_, v___x_13862__boxed_889_, v___f_886_, v_x_887_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17(lean_object* v___x_891_, lean_object* v___f_892_, lean_object* v___f_893_, lean_object* v_activeConnections_894_, uint8_t v_permitAcquired_895_, lean_object* v___x_896_, lean_object* v_connectionLimit_897_, uint8_t v___x_898_, lean_object* v___f_899_, lean_object* v___x_900_, lean_object* v_inst_901_, lean_object* v_val_902_, lean_object* v_handler_903_, lean_object* v_config_904_, lean_object* v___f_905_, lean_object* v___f_906_, lean_object* v_extensions_907_, lean_object* v___y_908_){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___f_913_; lean_object* v___x_914_; lean_object* v___f_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_910_ = lean_unsigned_to_nat(0u);
v___x_911_ = lean_box(v_permitAcquired_895_);
v___x_912_ = lean_box(v___x_898_);
v___f_913_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__15___boxed), 19, 17);
lean_closure_set(v___f_913_, 0, v___x_891_);
lean_closure_set(v___f_913_, 1, v___f_892_);
lean_closure_set(v___f_913_, 2, v___f_893_);
lean_closure_set(v___f_913_, 3, v_activeConnections_894_);
lean_closure_set(v___f_913_, 4, v___x_911_);
lean_closure_set(v___f_913_, 5, v___x_896_);
lean_closure_set(v___f_913_, 6, v_connectionLimit_897_);
lean_closure_set(v___f_913_, 7, v___x_910_);
lean_closure_set(v___f_913_, 8, v___x_912_);
lean_closure_set(v___f_913_, 9, v___f_899_);
lean_closure_set(v___f_913_, 10, v___x_900_);
lean_closure_set(v___f_913_, 11, v_inst_901_);
lean_closure_set(v___f_913_, 12, v_val_902_);
lean_closure_set(v___f_913_, 13, v_handler_903_);
lean_closure_set(v___f_913_, 14, v_config_904_);
lean_closure_set(v___f_913_, 15, v_extensions_907_);
lean_closure_set(v___f_913_, 16, v___f_905_);
v___x_914_ = lean_box(v___x_898_);
v___f_915_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__16___boxed), 5, 3);
lean_closure_set(v___f_915_, 0, v___x_910_);
lean_closure_set(v___f_915_, 1, v___x_914_);
lean_closure_set(v___f_915_, 2, v___f_913_);
lean_inc_ref(v___y_908_);
v___x_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_916_, 0, v___y_908_);
v___x_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
v___x_918_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_910_, v___x_898_, v___x_917_, v___f_915_);
v___x_919_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_910_, v___x_898_, v___x_918_, v___f_906_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17___boxed(lean_object** _args){
lean_object* v___x_920_ = _args[0];
lean_object* v___f_921_ = _args[1];
lean_object* v___f_922_ = _args[2];
lean_object* v_activeConnections_923_ = _args[3];
lean_object* v_permitAcquired_924_ = _args[4];
lean_object* v___x_925_ = _args[5];
lean_object* v_connectionLimit_926_ = _args[6];
lean_object* v___x_927_ = _args[7];
lean_object* v___f_928_ = _args[8];
lean_object* v___x_929_ = _args[9];
lean_object* v_inst_930_ = _args[10];
lean_object* v_val_931_ = _args[11];
lean_object* v_handler_932_ = _args[12];
lean_object* v_config_933_ = _args[13];
lean_object* v___f_934_ = _args[14];
lean_object* v___f_935_ = _args[15];
lean_object* v_extensions_936_ = _args[16];
lean_object* v___y_937_ = _args[17];
lean_object* v___y_938_ = _args[18];
_start:
{
uint8_t v_permitAcquired_boxed_939_; uint8_t v___x_13920__boxed_940_; lean_object* v_res_941_; 
v_permitAcquired_boxed_939_ = lean_unbox(v_permitAcquired_924_);
v___x_13920__boxed_940_ = lean_unbox(v___x_927_);
v_res_941_ = l_Std_Http_Server_serve___redArg___lam__17(v___x_920_, v___f_921_, v___f_922_, v_activeConnections_923_, v_permitAcquired_boxed_939_, v___x_925_, v_connectionLimit_926_, v___x_13920__boxed_940_, v___f_928_, v___x_929_, v_inst_930_, v_val_931_, v_handler_932_, v_config_933_, v___f_934_, v___f_935_, v_extensions_936_, v___y_937_);
lean_dec_ref(v___y_937_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18(lean_object* v___f_942_, lean_object* v___y_943_, lean_object* v_x_944_){
_start:
{
if (lean_obj_tag(v_x_944_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_954_; 
lean_dec_ref(v___f_942_);
v_a_946_ = lean_ctor_get(v_x_944_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v_x_944_);
if (v_isSharedCheck_954_ == 0)
{
v___x_948_ = v_x_944_;
v_isShared_949_ = v_isSharedCheck_954_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v_x_944_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_954_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_953_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_952_; 
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
return v___x_952_;
}
}
}
else
{
lean_object* v_a_955_; lean_object* v___x_956_; 
v_a_955_ = lean_ctor_get(v_x_944_, 0);
lean_inc(v_a_955_);
lean_dec_ref_known(v_x_944_, 1);
lean_inc_ref(v___y_943_);
v___x_956_ = lean_apply_3(v___f_942_, v_a_955_, v___y_943_, lean_box(0));
return v___x_956_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18___boxed(lean_object* v___f_957_, lean_object* v___y_958_, lean_object* v_x_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Std_Http_Server_serve___redArg___lam__18(v___f_957_, v___y_958_, v_x_959_);
lean_dec_ref(v___y_958_);
return v_res_961_;
}
}
static lean_object* _init_l_Std_Http_Server_serve___redArg___lam__20___closed__0(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = l_Std_Http_Extensions_empty;
v___x_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
return v___x_963_;
}
}
static lean_object* _init_l_Std_Http_Server_serve___redArg___lam__20___closed__1(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = lean_obj_once(&l_Std_Http_Server_serve___redArg___lam__20___closed__0, &l_Std_Http_Server_serve___redArg___lam__20___closed__0_once, _init_l_Std_Http_Server_serve___redArg___lam__20___closed__0);
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20(uint8_t v___x_967_, lean_object* v___f_968_, lean_object* v___x_969_, lean_object* v___f_970_, lean_object* v_x_971_){
_start:
{
if (lean_obj_tag(v_x_971_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_981_; 
lean_dec_ref(v___f_970_);
lean_dec(v___x_969_);
lean_dec_ref(v___f_968_);
v_a_973_ = lean_ctor_get(v_x_971_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v_x_971_);
if (v_isSharedCheck_981_ == 0)
{
v___x_975_ = v_x_971_;
v_isShared_976_ = v_isSharedCheck_981_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v_x_971_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_981_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_980_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_979_; 
v___x_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
return v___x_979_;
}
}
}
else
{
lean_object* v_a_982_; 
v_a_982_ = lean_ctor_get(v_x_971_, 0);
lean_inc(v_a_982_);
lean_dec_ref_known(v_x_971_, 1);
if (lean_obj_tag(v_a_982_) == 0)
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
lean_dec_ref_known(v_a_982_, 1);
lean_dec_ref(v___f_970_);
lean_dec(v___x_969_);
v___x_983_ = lean_unsigned_to_nat(0u);
v___x_984_ = lean_obj_once(&l_Std_Http_Server_serve___redArg___lam__20___closed__1, &l_Std_Http_Server_serve___redArg___lam__20___closed__1_once, _init_l_Std_Http_Server_serve___redArg___lam__20___closed__1);
v___x_985_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_983_, v___x_967_, v___x_984_, v___f_968_);
return v___x_985_;
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1001_; 
lean_dec_ref(v___f_968_);
v_a_986_ = lean_ctor_get(v_a_982_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v_a_982_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_988_ = v_a_982_;
v_isShared_989_ = v_isSharedCheck_1001_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v_a_982_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1001_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; lean_object* v_dyn_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_990_ = l_Std_Http_Extensions_empty;
v_dyn_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_991_, 0, v___x_969_);
lean_ctor_set(v_dyn_991_, 1, v_a_986_);
v___x_992_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__20___closed__2));
v___x_993_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_991_);
v___x_994_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_992_, v___x_993_, v_dyn_991_, v___x_990_);
v___x_995_ = lean_unsigned_to_nat(0u);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_994_);
v___x_997_ = v___x_988_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_994_);
v___x_997_ = v_reuseFailAlloc_1000_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
v___x_999_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_995_, v___x_967_, v___x_998_, v___f_970_);
return v___x_999_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20___boxed(lean_object* v___x_1002_, lean_object* v___f_1003_, lean_object* v___x_1004_, lean_object* v___f_1005_, lean_object* v_x_1006_, lean_object* v___y_1007_){
_start:
{
uint8_t v___x_14019__boxed_1008_; lean_object* v_res_1009_; 
v___x_14019__boxed_1008_ = lean_unbox(v___x_1002_);
v_res_1009_ = l_Std_Http_Server_serve___redArg___lam__20(v___x_14019__boxed_1008_, v___f_1003_, v___x_1004_, v___f_1005_, v_x_1006_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__19(uint8_t v_permitAcquired_1010_, lean_object* v___f_1011_, lean_object* v___x_1012_, lean_object* v___y_1013_, lean_object* v_connectionLimit_1014_, uint8_t v___x_1015_, lean_object* v___f_1016_, lean_object* v___x_1017_, lean_object* v___f_1018_, lean_object* v___f_1019_, lean_object* v_activeConnections_1020_, lean_object* v___f_1021_, lean_object* v___x_1022_, lean_object* v_inst_1023_, lean_object* v_handler_1024_, lean_object* v_config_1025_, lean_object* v___f_1026_, lean_object* v___f_1027_, lean_object* v___x_1028_, lean_object* v_x_1029_){
_start:
{
if (lean_obj_tag(v_x_1029_) == 0)
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1039_; 
lean_dec(v___x_1028_);
lean_dec_ref(v___f_1027_);
lean_dec_ref(v___f_1026_);
lean_dec_ref(v_config_1025_);
lean_dec(v_handler_1024_);
lean_dec_ref(v_inst_1023_);
lean_dec_ref(v___x_1022_);
lean_dec_ref(v___f_1021_);
lean_dec_ref(v_activeConnections_1020_);
lean_dec_ref(v___f_1019_);
lean_dec_ref(v___f_1018_);
lean_dec_ref(v___x_1017_);
lean_dec_ref(v___f_1016_);
lean_dec(v_connectionLimit_1014_);
lean_dec_ref(v___f_1011_);
v_a_1031_ = lean_ctor_get(v_x_1029_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_x_1029_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1033_ = v_x_1029_;
v_isShared_1034_ = v_isSharedCheck_1039_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v_x_1029_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1039_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
lean_object* v___x_1037_; 
v___x_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
return v___x_1037_;
}
}
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1098_; 
v_a_1040_ = lean_ctor_get(v_x_1029_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_x_1029_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1042_ = v_x_1029_;
v_isShared_1043_ = v_isSharedCheck_1098_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v_x_1029_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1098_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
if (lean_obj_tag(v_a_1040_) == 0)
{
lean_dec(v___x_1028_);
lean_dec_ref(v___f_1027_);
lean_dec_ref(v___f_1026_);
lean_dec_ref(v_config_1025_);
lean_dec(v_handler_1024_);
lean_dec_ref(v_inst_1023_);
lean_dec_ref(v___x_1022_);
lean_dec_ref(v___f_1021_);
lean_dec_ref(v_activeConnections_1020_);
lean_dec_ref(v___f_1019_);
lean_dec_ref(v___f_1018_);
lean_dec_ref(v___x_1017_);
if (v_permitAcquired_1010_ == 0)
{
lean_object* v___x_1044_; 
lean_del_object(v___x_1042_);
lean_dec_ref(v___f_1016_);
lean_dec(v_connectionLimit_1014_);
lean_inc_ref(v___y_1013_);
v___x_1044_ = lean_apply_3(v___f_1011_, v___x_1012_, v___y_1013_, lean_box(0));
return v___x_1044_;
}
else
{
if (lean_obj_tag(v_connectionLimit_1014_) == 1)
{
lean_object* v_val_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1058_; 
lean_dec_ref(v___f_1011_);
v_val_1045_ = lean_ctor_get(v_connectionLimit_1014_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_connectionLimit_1014_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1047_ = v_connectionLimit_1014_;
v_isShared_1048_ = v_isSharedCheck_1058_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_val_1045_);
lean_dec(v_connectionLimit_1014_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1058_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1049_ = lean_unsigned_to_nat(0u);
v___x_1050_ = l_Std_Semaphore_release(v_val_1045_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v___x_1050_);
v___x_1052_ = v___x_1042_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1054_; 
if (v_isShared_1048_ == 0)
{
lean_ctor_set_tag(v___x_1047_, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1052_);
v___x_1054_ = v___x_1047_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1052_);
v___x_1054_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1055_; 
v___x_1055_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1049_, v___x_1015_, v___x_1054_, v___f_1016_);
return v___x_1055_;
}
}
}
}
else
{
lean_object* v___x_1059_; 
lean_del_object(v___x_1042_);
lean_dec_ref(v___f_1016_);
lean_dec(v_connectionLimit_1014_);
lean_inc_ref(v___y_1013_);
v___x_1059_ = lean_apply_3(v___f_1011_, v___x_1012_, v___y_1013_, lean_box(0));
return v___x_1059_;
}
}
}
else
{
lean_object* v_val_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1097_; 
lean_dec_ref(v___f_1016_);
lean_dec_ref(v___f_1011_);
v_val_1060_ = lean_ctor_get(v_a_1040_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_a_1040_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1062_ = v_a_1040_;
v_isShared_1063_ = v_isSharedCheck_1097_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_val_1060_);
lean_dec(v_a_1040_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1097_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___f_1066_; lean_object* v___f_1067_; lean_object* v___x_1068_; lean_object* v___f_1069_; lean_object* v___x_1070_; lean_object* v_val_1072_; lean_object* v___x_1080_; 
v___x_1064_ = lean_box(v_permitAcquired_1010_);
v___x_1065_ = lean_box(v___x_1015_);
lean_inc(v_val_1060_);
v___f_1066_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__17___boxed), 19, 16);
lean_closure_set(v___f_1066_, 0, v___x_1017_);
lean_closure_set(v___f_1066_, 1, v___f_1018_);
lean_closure_set(v___f_1066_, 2, v___f_1019_);
lean_closure_set(v___f_1066_, 3, v_activeConnections_1020_);
lean_closure_set(v___f_1066_, 4, v___x_1064_);
lean_closure_set(v___f_1066_, 5, v___x_1012_);
lean_closure_set(v___f_1066_, 6, v_connectionLimit_1014_);
lean_closure_set(v___f_1066_, 7, v___x_1065_);
lean_closure_set(v___f_1066_, 8, v___f_1021_);
lean_closure_set(v___f_1066_, 9, v___x_1022_);
lean_closure_set(v___f_1066_, 10, v_inst_1023_);
lean_closure_set(v___f_1066_, 11, v_val_1060_);
lean_closure_set(v___f_1066_, 12, v_handler_1024_);
lean_closure_set(v___f_1066_, 13, v_config_1025_);
lean_closure_set(v___f_1066_, 14, v___f_1026_);
lean_closure_set(v___f_1066_, 15, v___f_1027_);
lean_inc_ref(v___y_1013_);
v___f_1067_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__18___boxed), 4, 2);
lean_closure_set(v___f_1067_, 0, v___f_1066_);
lean_closure_set(v___f_1067_, 1, v___y_1013_);
v___x_1068_ = lean_box(v___x_1015_);
lean_inc_ref(v___f_1067_);
v___f_1069_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__20___boxed), 6, 4);
lean_closure_set(v___f_1069_, 0, v___x_1068_);
lean_closure_set(v___f_1069_, 1, v___f_1067_);
lean_closure_set(v___f_1069_, 2, v___x_1028_);
lean_closure_set(v___f_1069_, 3, v___f_1067_);
v___x_1070_ = lean_unsigned_to_nat(0u);
v___x_1080_ = lean_uv_tcp_getpeername(v_val_1060_);
lean_dec(v_val_1060_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
lean_ctor_set_tag(v___x_1083_, 1);
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
v_val_1072_ = v___x_1086_;
goto v___jp_1071_;
}
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
v_a_1089_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1080_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1080_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set_tag(v___x_1091_, 0);
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
v_val_1072_ = v___x_1094_;
goto v___jp_1071_;
}
}
}
v___jp_1071_:
{
lean_object* v___x_1074_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v_val_1072_);
v___x_1074_ = v___x_1042_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_val_1072_);
v___x_1074_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1076_; 
if (v_isShared_1063_ == 0)
{
lean_ctor_set_tag(v___x_1062_, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1074_);
v___x_1076_ = v___x_1062_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1077_; 
v___x_1077_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1070_, v___x_1015_, v___x_1076_, v___f_1069_);
return v___x_1077_;
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
lean_object* v_permitAcquired_1099_ = _args[0];
lean_object* v___f_1100_ = _args[1];
lean_object* v___x_1101_ = _args[2];
lean_object* v___y_1102_ = _args[3];
lean_object* v_connectionLimit_1103_ = _args[4];
lean_object* v___x_1104_ = _args[5];
lean_object* v___f_1105_ = _args[6];
lean_object* v___x_1106_ = _args[7];
lean_object* v___f_1107_ = _args[8];
lean_object* v___f_1108_ = _args[9];
lean_object* v_activeConnections_1109_ = _args[10];
lean_object* v___f_1110_ = _args[11];
lean_object* v___x_1111_ = _args[12];
lean_object* v_inst_1112_ = _args[13];
lean_object* v_handler_1113_ = _args[14];
lean_object* v_config_1114_ = _args[15];
lean_object* v___f_1115_ = _args[16];
lean_object* v___f_1116_ = _args[17];
lean_object* v___x_1117_ = _args[18];
lean_object* v_x_1118_ = _args[19];
lean_object* v___y_1119_ = _args[20];
_start:
{
uint8_t v_permitAcquired_boxed_1120_; uint8_t v___x_14102__boxed_1121_; lean_object* v_res_1122_; 
v_permitAcquired_boxed_1120_ = lean_unbox(v_permitAcquired_1099_);
v___x_14102__boxed_1121_ = lean_unbox(v___x_1104_);
v_res_1122_ = l_Std_Http_Server_serve___redArg___lam__19(v_permitAcquired_boxed_1120_, v___f_1100_, v___x_1101_, v___y_1102_, v_connectionLimit_1103_, v___x_14102__boxed_1121_, v___f_1105_, v___x_1106_, v___f_1107_, v___f_1108_, v_activeConnections_1109_, v___f_1110_, v___x_1111_, v_inst_1112_, v_handler_1113_, v_config_1114_, v___f_1115_, v___f_1116_, v___x_1117_, v_x_1118_);
lean_dec_ref(v___y_1102_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21(lean_object* v_a_1123_, lean_object* v___f_1124_, lean_object* v___f_1125_, uint8_t v___x_1126_, lean_object* v___f_1127_, lean_object* v_x_1128_){
_start:
{
if (lean_obj_tag(v_x_1128_) == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1138_; 
lean_dec_ref(v___f_1127_);
lean_dec_ref(v___f_1125_);
lean_dec_ref(v___f_1124_);
lean_dec(v_a_1123_);
v_a_1130_ = lean_ctor_get(v_x_1128_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_x_1128_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1132_ = v_x_1128_;
v_isShared_1133_ = v_isSharedCheck_1138_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v_x_1128_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1138_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
return v___x_1136_;
}
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v_a_1139_ = lean_ctor_get(v_x_1128_, 0);
lean_inc(v_a_1139_);
lean_dec_ref_known(v_x_1128_, 1);
v___x_1140_ = l_Std_Async_TCP_Socket_Server_acceptSelector(v_a_1123_);
v___x_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
lean_ctor_set(v___x_1141_, 1, v___f_1124_);
v___x_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1142_, 0, v_a_1139_);
lean_ctor_set(v___x_1142_, 1, v___f_1125_);
v___x_1143_ = lean_unsigned_to_nat(2u);
v___x_1144_ = lean_mk_empty_array_with_capacity(v___x_1143_);
v___x_1145_ = lean_array_push(v___x_1144_, v___x_1141_);
v___x_1146_ = lean_array_push(v___x_1145_, v___x_1142_);
v___x_1147_ = lean_unsigned_to_nat(0u);
v___x_1148_ = l_Std_Async_Selectable_one___redArg(v___x_1146_);
v___x_1149_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1147_, v___x_1126_, v___x_1148_, v___f_1127_);
return v___x_1149_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21___boxed(lean_object* v_a_1150_, lean_object* v___f_1151_, lean_object* v___f_1152_, lean_object* v___x_1153_, lean_object* v___f_1154_, lean_object* v_x_1155_, lean_object* v___y_1156_){
_start:
{
uint8_t v___x_14286__boxed_1157_; lean_object* v_res_1158_; 
v___x_14286__boxed_1157_ = lean_unbox(v___x_1153_);
v_res_1158_ = l_Std_Http_Server_serve___redArg___lam__21(v_a_1150_, v___f_1151_, v___f_1152_, v___x_14286__boxed_1157_, v___f_1154_, v_x_1155_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22(lean_object* v___f_1159_, lean_object* v___x_1160_, lean_object* v_connectionLimit_1161_, uint8_t v___x_1162_, lean_object* v___x_1163_, lean_object* v___f_1164_, lean_object* v___f_1165_, lean_object* v_activeConnections_1166_, lean_object* v___f_1167_, lean_object* v___x_1168_, lean_object* v_inst_1169_, lean_object* v_handler_1170_, lean_object* v_config_1171_, lean_object* v___f_1172_, lean_object* v___f_1173_, lean_object* v___x_1174_, lean_object* v_a_1175_, lean_object* v___f_1176_, lean_object* v___f_1177_, lean_object* v___f_1178_, uint8_t v_permitAcquired_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v___f_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___f_1185_; lean_object* v___x_1186_; lean_object* v___f_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
lean_inc_ref_n(v___y_1180_, 3);
lean_inc_ref(v___f_1159_);
v___f_1182_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__8___boxed), 4, 2);
lean_closure_set(v___f_1182_, 0, v___f_1159_);
lean_closure_set(v___f_1182_, 1, v___y_1180_);
v___x_1183_ = lean_box(v_permitAcquired_1179_);
v___x_1184_ = lean_box(v___x_1162_);
v___f_1185_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__19___boxed), 21, 19);
lean_closure_set(v___f_1185_, 0, v___x_1183_);
lean_closure_set(v___f_1185_, 1, v___f_1159_);
lean_closure_set(v___f_1185_, 2, v___x_1160_);
lean_closure_set(v___f_1185_, 3, v___y_1180_);
lean_closure_set(v___f_1185_, 4, v_connectionLimit_1161_);
lean_closure_set(v___f_1185_, 5, v___x_1184_);
lean_closure_set(v___f_1185_, 6, v___f_1182_);
lean_closure_set(v___f_1185_, 7, v___x_1163_);
lean_closure_set(v___f_1185_, 8, v___f_1164_);
lean_closure_set(v___f_1185_, 9, v___f_1165_);
lean_closure_set(v___f_1185_, 10, v_activeConnections_1166_);
lean_closure_set(v___f_1185_, 11, v___f_1167_);
lean_closure_set(v___f_1185_, 12, v___x_1168_);
lean_closure_set(v___f_1185_, 13, v_inst_1169_);
lean_closure_set(v___f_1185_, 14, v_handler_1170_);
lean_closure_set(v___f_1185_, 15, v_config_1171_);
lean_closure_set(v___f_1185_, 16, v___f_1172_);
lean_closure_set(v___f_1185_, 17, v___f_1173_);
lean_closure_set(v___f_1185_, 18, v___x_1174_);
v___x_1186_ = lean_box(v___x_1162_);
v___f_1187_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__21___boxed), 7, 5);
lean_closure_set(v___f_1187_, 0, v_a_1175_);
lean_closure_set(v___f_1187_, 1, v___f_1176_);
lean_closure_set(v___f_1187_, 2, v___f_1177_);
lean_closure_set(v___f_1187_, 3, v___x_1186_);
lean_closure_set(v___f_1187_, 4, v___f_1185_);
v___x_1188_ = lean_unsigned_to_nat(0u);
v___x_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___y_1180_);
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
v___x_1191_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1188_, v___x_1162_, v___x_1190_, v___f_1178_);
v___x_1192_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1188_, v___x_1162_, v___x_1191_, v___f_1187_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22___boxed(lean_object** _args){
lean_object* v___f_1193_ = _args[0];
lean_object* v___x_1194_ = _args[1];
lean_object* v_connectionLimit_1195_ = _args[2];
lean_object* v___x_1196_ = _args[3];
lean_object* v___x_1197_ = _args[4];
lean_object* v___f_1198_ = _args[5];
lean_object* v___f_1199_ = _args[6];
lean_object* v_activeConnections_1200_ = _args[7];
lean_object* v___f_1201_ = _args[8];
lean_object* v___x_1202_ = _args[9];
lean_object* v_inst_1203_ = _args[10];
lean_object* v_handler_1204_ = _args[11];
lean_object* v_config_1205_ = _args[12];
lean_object* v___f_1206_ = _args[13];
lean_object* v___f_1207_ = _args[14];
lean_object* v___x_1208_ = _args[15];
lean_object* v_a_1209_ = _args[16];
lean_object* v___f_1210_ = _args[17];
lean_object* v___f_1211_ = _args[18];
lean_object* v___f_1212_ = _args[19];
lean_object* v_permitAcquired_1213_ = _args[20];
lean_object* v___y_1214_ = _args[21];
lean_object* v___y_1215_ = _args[22];
_start:
{
uint8_t v___x_14346__boxed_1216_; uint8_t v_permitAcquired_boxed_1217_; lean_object* v_res_1218_; 
v___x_14346__boxed_1216_ = lean_unbox(v___x_1196_);
v_permitAcquired_boxed_1217_ = lean_unbox(v_permitAcquired_1213_);
v_res_1218_ = l_Std_Http_Server_serve___redArg___lam__22(v___f_1193_, v___x_1194_, v_connectionLimit_1195_, v___x_14346__boxed_1216_, v___x_1197_, v___f_1198_, v___f_1199_, v_activeConnections_1200_, v___f_1201_, v___x_1202_, v_inst_1203_, v_handler_1204_, v_config_1205_, v___f_1206_, v___f_1207_, v___x_1208_, v_a_1209_, v___f_1210_, v___f_1211_, v___f_1212_, v_permitAcquired_boxed_1217_, v___y_1214_);
lean_dec_ref(v___y_1214_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23(lean_object* v___f_1219_, lean_object* v___y_1220_, lean_object* v_x_1221_){
_start:
{
if (lean_obj_tag(v_x_1221_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1231_; 
lean_dec_ref(v___f_1219_);
v_a_1223_ = lean_ctor_get(v_x_1221_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_x_1221_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1225_ = v_x_1221_;
v_isShared_1226_ = v_isSharedCheck_1231_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v_x_1221_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1231_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
lean_object* v___x_1229_; 
v___x_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
return v___x_1229_;
}
}
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1233_; 
v_a_1232_ = lean_ctor_get(v_x_1221_, 0);
lean_inc(v_a_1232_);
lean_dec_ref_known(v_x_1221_, 1);
lean_inc_ref(v___y_1220_);
v___x_1233_ = lean_apply_3(v___f_1219_, v_a_1232_, v___y_1220_, lean_box(0));
return v___x_1233_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23___boxed(lean_object* v___f_1234_, lean_object* v___y_1235_, lean_object* v_x_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Std_Http_Server_serve___redArg___lam__23(v___f_1234_, v___y_1235_, v_x_1236_);
lean_dec_ref(v___y_1235_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24(uint8_t v___x_1239_, lean_object* v___x_1240_, uint8_t v___x_1241_, lean_object* v___f_1242_, lean_object* v_x_1243_){
_start:
{
if (lean_obj_tag(v_x_1243_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1253_; 
lean_dec_ref(v___f_1242_);
lean_dec(v___x_1240_);
v_a_1245_ = lean_ctor_get(v_x_1243_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_x_1243_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1247_ = v_x_1243_;
v_isShared_1248_ = v_isSharedCheck_1253_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v_x_1243_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1253_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1251_; 
v___x_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
return v___x_1251_;
}
}
}
else
{
lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1263_; 
v_isSharedCheck_1263_ = !lean_is_exclusive(v_x_1243_);
if (v_isSharedCheck_1263_ == 0)
{
lean_object* v_unused_1264_; 
v_unused_1264_ = lean_ctor_get(v_x_1243_, 0);
lean_dec(v_unused_1264_);
v___x_1255_ = v_x_1243_;
v_isShared_1256_ = v_isSharedCheck_1263_;
goto v_resetjp_1254_;
}
else
{
lean_dec(v_x_1243_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1263_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1257_ = lean_box(v___x_1239_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 0, v___x_1257_);
v___x_1259_ = v___x_1255_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
v___x_1261_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1240_, v___x_1241_, v___x_1260_, v___f_1242_);
return v___x_1261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24___boxed(lean_object* v___x_1265_, lean_object* v___x_1266_, lean_object* v___x_1267_, lean_object* v___f_1268_, lean_object* v_x_1269_, lean_object* v___y_1270_){
_start:
{
uint8_t v___x_14454__boxed_1271_; uint8_t v___x_14456__boxed_1272_; lean_object* v_res_1273_; 
v___x_14454__boxed_1271_ = lean_unbox(v___x_1265_);
v___x_14456__boxed_1272_ = lean_unbox(v___x_1267_);
v_res_1273_ = l_Std_Http_Server_serve___redArg___lam__24(v___x_14454__boxed_1271_, v___x_1266_, v___x_14456__boxed_1272_, v___f_1268_, v_x_1269_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25(lean_object* v___f_1274_, lean_object* v___x_1275_, uint8_t v___x_1276_, lean_object* v___f_1277_, lean_object* v_x_1278_){
_start:
{
if (lean_obj_tag(v_x_1278_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1288_; 
lean_dec_ref(v___f_1277_);
lean_dec(v___x_1275_);
lean_dec_ref(v___f_1274_);
v_a_1280_ = lean_ctor_get(v_x_1278_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_x_1278_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1282_ = v_x_1278_;
v_isShared_1283_ = v_isSharedCheck_1288_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v_x_1278_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1288_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
return v___x_1286_;
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v_a_1289_ = lean_ctor_get(v_x_1278_, 0);
lean_inc(v_a_1289_);
lean_dec_ref_known(v_x_1278_, 1);
v___x_1290_ = l_IO_Promise_result_x21___redArg(v_a_1289_);
lean_dec(v_a_1289_);
lean_inc(v___x_1275_);
v___x_1291_ = lean_task_map(v___f_1274_, v___x_1290_, v___x_1275_, v___x_1276_);
v___x_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
v___x_1293_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1275_, v___x_1276_, v___x_1292_, v___f_1277_);
return v___x_1293_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25___boxed(lean_object* v___f_1294_, lean_object* v___x_1295_, lean_object* v___x_1296_, lean_object* v___f_1297_, lean_object* v_x_1298_, lean_object* v___y_1299_){
_start:
{
uint8_t v___x_14515__boxed_1300_; lean_object* v_res_1301_; 
v___x_14515__boxed_1300_ = lean_unbox(v___x_1296_);
v_res_1301_ = l_Std_Http_Server_serve___redArg___lam__25(v___f_1294_, v___x_1295_, v___x_14515__boxed_1300_, v___f_1297_, v_x_1298_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27(uint8_t v___x_1302_, lean_object* v___f_1303_, lean_object* v_connectionLimit_1304_, lean_object* v___f_1305_, lean_object* v___f_1306_, lean_object* v_b_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v___x_1310_; lean_object* v___y_1312_; 
v___x_1310_ = lean_unsigned_to_nat(0u);
if (lean_obj_tag(v_connectionLimit_1304_) == 1)
{
lean_object* v_val_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1331_; 
v_val_1314_ = lean_ctor_get(v_connectionLimit_1304_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_connectionLimit_1304_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1316_ = v_connectionLimit_1304_;
v_isShared_1317_ = v_isSharedCheck_1331_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_val_1314_);
lean_dec(v_connectionLimit_1304_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1331_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___f_1318_; uint8_t v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___f_1322_; lean_object* v___x_1323_; lean_object* v___f_1324_; lean_object* v___x_1325_; lean_object* v___x_1327_; 
lean_inc_ref(v___y_1308_);
v___f_1318_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__23___boxed), 4, 2);
lean_closure_set(v___f_1318_, 0, v___f_1305_);
lean_closure_set(v___f_1318_, 1, v___y_1308_);
v___x_1319_ = 1;
v___x_1320_ = lean_box(v___x_1319_);
v___x_1321_ = lean_box(v___x_1302_);
v___f_1322_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__24___boxed), 6, 4);
lean_closure_set(v___f_1322_, 0, v___x_1320_);
lean_closure_set(v___f_1322_, 1, v___x_1310_);
lean_closure_set(v___f_1322_, 2, v___x_1321_);
lean_closure_set(v___f_1322_, 3, v___f_1318_);
v___x_1323_ = lean_box(v___x_1302_);
v___f_1324_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__25___boxed), 6, 4);
lean_closure_set(v___f_1324_, 0, v___f_1306_);
lean_closure_set(v___f_1324_, 1, v___x_1310_);
lean_closure_set(v___f_1324_, 2, v___x_1323_);
lean_closure_set(v___f_1324_, 3, v___f_1322_);
v___x_1325_ = l_Std_Semaphore_acquire(v_val_1314_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v___x_1325_);
v___x_1327_ = v___x_1316_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1325_);
v___x_1327_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
v___x_1329_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1310_, v___x_1302_, v___x_1328_, v___f_1324_);
v___y_1312_ = v___x_1329_;
goto v___jp_1311_;
}
}
}
else
{
lean_object* v___f_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
lean_dec_ref(v___f_1306_);
lean_dec(v_connectionLimit_1304_);
lean_inc_ref(v___y_1308_);
v___f_1332_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__23___boxed), 4, 2);
lean_closure_set(v___f_1332_, 0, v___f_1305_);
lean_closure_set(v___f_1332_, 1, v___y_1308_);
v___x_1333_ = lean_box(v___x_1302_);
v___x_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
v___x_1336_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1310_, v___x_1302_, v___x_1335_, v___f_1332_);
v___y_1312_ = v___x_1336_;
goto v___jp_1311_;
}
v___jp_1311_:
{
lean_object* v___x_1313_; 
v___x_1313_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1310_, v___x_1302_, v___y_1312_, v___f_1303_);
return v___x_1313_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27___boxed(lean_object* v___x_1337_, lean_object* v___f_1338_, lean_object* v_connectionLimit_1339_, lean_object* v___f_1340_, lean_object* v___f_1341_, lean_object* v_b_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
uint8_t v___x_14559__boxed_1345_; lean_object* v_res_1346_; 
v___x_14559__boxed_1345_ = lean_unbox(v___x_1337_);
v_res_1346_ = l_Std_Http_Server_serve___redArg___lam__27(v___x_14559__boxed_1345_, v___f_1338_, v_connectionLimit_1339_, v___f_1340_, v___f_1341_, v_b_1342_, v___y_1343_);
lean_dec_ref(v___y_1343_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26(lean_object* v___x_1347_, lean_object* v___f_1348_, lean_object* v___x_1349_, uint8_t v___x_1350_, lean_object* v___f_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_13007__overap_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1354_ = lean_unsigned_to_nat(0u);
v___x_13007__overap_1355_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_1347_, v___f_1348_, v___x_1349_);
v___x_1356_ = lean_apply_2(v___x_13007__overap_1355_, v___y_1352_, lean_box(0));
v___x_1357_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1354_, v___x_1350_, v___x_1356_, v___f_1351_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26___boxed(lean_object* v___x_1358_, lean_object* v___f_1359_, lean_object* v___x_1360_, lean_object* v___x_1361_, lean_object* v___f_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
uint8_t v___x_14634__boxed_1365_; lean_object* v_res_1366_; 
v___x_14634__boxed_1365_ = lean_unbox(v___x_1361_);
v_res_1366_ = l_Std_Http_Server_serve___redArg___lam__26(v___x_1358_, v___f_1359_, v___x_1360_, v___x_14634__boxed_1365_, v___f_1362_, v___y_1363_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28(lean_object* v___x_1371_, lean_object* v___f_1372_, lean_object* v___f_1373_, lean_object* v___x_1374_, lean_object* v_inst_1375_, lean_object* v_handler_1376_, lean_object* v_config_1377_, lean_object* v___f_1378_, lean_object* v___x_1379_, lean_object* v_a_1380_, lean_object* v___f_1381_, lean_object* v___f_1382_, lean_object* v___f_1383_, lean_object* v___f_1384_, lean_object* v___f_1385_, lean_object* v___f_1386_, lean_object* v_x_1387_){
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
lean_dec_ref(v___f_1381_);
lean_dec(v_a_1380_);
lean_dec(v___x_1379_);
lean_dec_ref(v___f_1378_);
lean_dec_ref(v_config_1377_);
lean_dec(v_handler_1376_);
lean_dec_ref(v_inst_1375_);
lean_dec_ref(v___x_1374_);
lean_dec_ref(v___f_1373_);
lean_dec_ref(v___f_1372_);
lean_dec_ref(v___x_1371_);
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v_x_1387_);
return v___x_1389_;
}
else
{
lean_object* v_a_1390_; lean_object* v_context_1391_; lean_object* v_activeConnections_1392_; lean_object* v_connectionLimit_1393_; lean_object* v_shutdownPromise_1394_; lean_object* v___f_1395_; lean_object* v___f_1396_; lean_object* v___f_1397_; uint8_t v___x_1398_; lean_object* v___x_1399_; lean_object* v___f_1400_; lean_object* v___f_1401_; lean_object* v___x_1402_; lean_object* v___f_1403_; lean_object* v___x_1404_; lean_object* v___f_1405_; lean_object* v___x_1406_; lean_object* v___f_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v_a_1390_ = lean_ctor_get(v_x_1387_, 0);
lean_inc(v_a_1390_);
v_context_1391_ = lean_ctor_get(v_a_1390_, 0);
lean_inc_ref_n(v_context_1391_, 2);
v_activeConnections_1392_ = lean_ctor_get(v_a_1390_, 1);
v_connectionLimit_1393_ = lean_ctor_get(v_a_1390_, 2);
v_shutdownPromise_1394_ = lean_ctor_get(v_a_1390_, 3);
v___f_1395_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__6___boxed), 3, 1);
lean_closure_set(v___f_1395_, 0, v_x_1387_);
lean_inc_ref(v_shutdownPromise_1394_);
v___f_1396_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1396_, 0, v_context_1391_);
lean_closure_set(v___f_1396_, 1, v_shutdownPromise_1394_);
v___f_1397_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed), 5, 1);
lean_closure_set(v___f_1397_, 0, v___f_1396_);
v___x_1398_ = 0;
v___x_1399_ = lean_box(0);
v___f_1400_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__28___closed__0));
v___f_1401_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__28___closed__1));
v___x_1402_ = lean_box(v___x_1398_);
lean_inc_ref(v_activeConnections_1392_);
lean_inc_ref(v___x_1371_);
lean_inc_n(v_connectionLimit_1393_, 2);
v___f_1403_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__22___boxed), 23, 20);
lean_closure_set(v___f_1403_, 0, v___f_1401_);
lean_closure_set(v___f_1403_, 1, v___x_1399_);
lean_closure_set(v___f_1403_, 2, v_connectionLimit_1393_);
lean_closure_set(v___f_1403_, 3, v___x_1402_);
lean_closure_set(v___f_1403_, 4, v___x_1371_);
lean_closure_set(v___f_1403_, 5, v___f_1372_);
lean_closure_set(v___f_1403_, 6, v___f_1397_);
lean_closure_set(v___f_1403_, 7, v_activeConnections_1392_);
lean_closure_set(v___f_1403_, 8, v___f_1373_);
lean_closure_set(v___f_1403_, 9, v___x_1374_);
lean_closure_set(v___f_1403_, 10, v_inst_1375_);
lean_closure_set(v___f_1403_, 11, v_handler_1376_);
lean_closure_set(v___f_1403_, 12, v_config_1377_);
lean_closure_set(v___f_1403_, 13, v___f_1378_);
lean_closure_set(v___f_1403_, 14, v___f_1400_);
lean_closure_set(v___f_1403_, 15, v___x_1379_);
lean_closure_set(v___f_1403_, 16, v_a_1380_);
lean_closure_set(v___f_1403_, 17, v___f_1381_);
lean_closure_set(v___f_1403_, 18, v___f_1382_);
lean_closure_set(v___f_1403_, 19, v___f_1383_);
v___x_1404_ = lean_box(v___x_1398_);
v___f_1405_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__27___boxed), 8, 5);
lean_closure_set(v___f_1405_, 0, v___x_1404_);
lean_closure_set(v___f_1405_, 1, v___f_1384_);
lean_closure_set(v___f_1405_, 2, v_connectionLimit_1393_);
lean_closure_set(v___f_1405_, 3, v___f_1403_);
lean_closure_set(v___f_1405_, 4, v___f_1385_);
v___x_1406_ = lean_box(v___x_1398_);
v___f_1407_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__26___boxed), 7, 5);
lean_closure_set(v___f_1407_, 0, v___x_1371_);
lean_closure_set(v___f_1407_, 1, v___f_1405_);
lean_closure_set(v___f_1407_, 2, v___x_1399_);
lean_closure_set(v___f_1407_, 3, v___x_1406_);
lean_closure_set(v___f_1407_, 4, v___f_1386_);
v___x_1408_ = lean_box(v___x_1398_);
v___x_1409_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___boxed), 6, 5);
lean_closure_set(v___x_1409_, 0, lean_box(0));
lean_closure_set(v___x_1409_, 1, v_a_1390_);
lean_closure_set(v___x_1409_, 2, v___x_1408_);
lean_closure_set(v___x_1409_, 3, v___f_1407_);
lean_closure_set(v___x_1409_, 4, v_context_1391_);
v___x_1410_ = lean_unsigned_to_nat(0u);
v___x_1411_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1411_, 0, lean_box(0));
lean_closure_set(v___x_1411_, 1, v___x_1409_);
v___x_1412_ = lean_io_as_task(v___x_1411_, v___x_1410_);
lean_dec_ref(v___x_1412_);
v___x_1413_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
v___x_1414_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1410_, v___x_1398_, v___x_1413_, v___f_1395_);
return v___x_1414_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28___boxed(lean_object** _args){
lean_object* v___x_1415_ = _args[0];
lean_object* v___f_1416_ = _args[1];
lean_object* v___f_1417_ = _args[2];
lean_object* v___x_1418_ = _args[3];
lean_object* v_inst_1419_ = _args[4];
lean_object* v_handler_1420_ = _args[5];
lean_object* v_config_1421_ = _args[6];
lean_object* v___f_1422_ = _args[7];
lean_object* v___x_1423_ = _args[8];
lean_object* v_a_1424_ = _args[9];
lean_object* v___f_1425_ = _args[10];
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
v_res_1433_ = l_Std_Http_Server_serve___redArg___lam__28(v___x_1415_, v___f_1416_, v___f_1417_, v___x_1418_, v_inst_1419_, v_handler_1420_, v_config_1421_, v___f_1422_, v___x_1423_, v_a_1424_, v___f_1425_, v___f_1426_, v___f_1427_, v___f_1428_, v___f_1429_, v___f_1430_, v_x_1431_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29(lean_object* v___f_1434_, lean_object* v_config_1435_, lean_object* v_x_1436_){
_start:
{
if (lean_obj_tag(v_x_1436_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1446_; 
lean_dec_ref(v_config_1435_);
lean_dec_ref(v___f_1434_);
v_a_1438_ = lean_ctor_get(v_x_1436_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_x_1436_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1440_ = v_x_1436_;
v_isShared_1441_ = v_isSharedCheck_1446_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v_x_1436_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1446_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
return v___x_1444_;
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1463_; 
v_a_1447_ = lean_ctor_get(v_x_1436_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_x_1436_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1449_ = v_x_1436_;
v_isShared_1450_ = v_isSharedCheck_1463_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v_x_1436_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1463_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; uint8_t v___x_1453_; lean_object* v_val_1455_; lean_object* v___x_1458_; lean_object* v_a_1459_; lean_object* v___x_1461_; 
v___x_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1451_, 0, v_a_1447_);
v___x_1452_ = lean_unsigned_to_nat(0u);
v___x_1453_ = 0;
v___x_1458_ = l_Std_Http_Server_new(v_config_1435_, v___x_1451_);
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1459_);
lean_dec_ref(v___x_1458_);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 0, v_a_1459_);
v___x_1461_ = v___x_1449_;
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
v___jp_1454_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1456_, 0, v_val_1455_);
v___x_1457_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1452_, v___x_1453_, v___x_1456_, v___f_1434_);
return v___x_1457_;
}
v_reusejp_1460_:
{
v_val_1455_ = v___x_1461_;
goto v___jp_1454_;
}
}
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
if (lean_obj_tag(v_x_1471_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1481_; 
lean_dec_ref(v___f_1469_);
v_a_1473_ = lean_ctor_get(v_x_1471_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_x_1471_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1475_ = v_x_1471_;
v_isShared_1476_ = v_isSharedCheck_1481_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v_x_1471_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1481_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v___x_1479_; 
v___x_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
return v___x_1479_;
}
}
}
else
{
lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1500_; 
v_isSharedCheck_1500_ = !lean_is_exclusive(v_x_1471_);
if (v_isSharedCheck_1500_ == 0)
{
lean_object* v_unused_1501_; 
v_unused_1501_ = lean_ctor_get(v_x_1471_, 0);
lean_dec(v_unused_1501_);
v___x_1483_ = v_x_1471_;
v_isShared_1484_ = v_isSharedCheck_1500_;
goto v_resetjp_1482_;
}
else
{
lean_dec(v_x_1471_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1500_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1485_; uint8_t v___x_1486_; lean_object* v_val_1488_; lean_object* v___x_1491_; 
v___x_1485_ = lean_unsigned_to_nat(0u);
v___x_1486_ = 0;
v___x_1491_ = lean_uv_tcp_getsockname(v_a_1470_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v___x_1494_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1492_);
lean_dec_ref_known(v___x_1491_, 1);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v_a_1492_);
v___x_1494_ = v___x_1483_;
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
v_val_1488_ = v___x_1494_;
goto v___jp_1487_;
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; 
v_a_1496_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1496_);
lean_dec_ref_known(v___x_1491_, 1);
if (v_isShared_1484_ == 0)
{
lean_ctor_set_tag(v___x_1483_, 0);
lean_ctor_set(v___x_1483_, 0, v_a_1496_);
v___x_1498_ = v___x_1483_;
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
v_val_1488_ = v___x_1498_;
goto v___jp_1487_;
}
}
v___jp_1487_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1489_, 0, v_val_1488_);
v___x_1490_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1485_, v___x_1486_, v___x_1489_, v___f_1469_);
return v___x_1490_;
}
}
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
if (lean_obj_tag(v_x_1509_) == 0)
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1519_; 
lean_dec_ref(v___f_1507_);
v_a_1511_ = lean_ctor_get(v_x_1509_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_x_1509_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1513_ = v_x_1509_;
v_isShared_1514_ = v_isSharedCheck_1519_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v_x_1509_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1519_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v___x_1517_; 
v___x_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
return v___x_1517_;
}
}
}
else
{
lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1538_; 
v_isSharedCheck_1538_ = !lean_is_exclusive(v_x_1509_);
if (v_isSharedCheck_1538_ == 0)
{
lean_object* v_unused_1539_; 
v_unused_1539_ = lean_ctor_get(v_x_1509_, 0);
lean_dec(v_unused_1539_);
v___x_1521_ = v_x_1509_;
v_isShared_1522_ = v_isSharedCheck_1538_;
goto v_resetjp_1520_;
}
else
{
lean_dec(v_x_1509_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1538_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; uint8_t v___x_1524_; lean_object* v_val_1526_; lean_object* v___x_1529_; 
v___x_1523_ = lean_unsigned_to_nat(0u);
v___x_1524_ = 0;
v___x_1529_ = lean_uv_tcp_nodelay(v_a_1508_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1532_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1529_, 1);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 0, v_a_1530_);
v___x_1532_ = v___x_1521_;
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
v_val_1526_ = v___x_1532_;
goto v___jp_1525_;
}
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; 
v_a_1534_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1534_);
lean_dec_ref_known(v___x_1529_, 1);
if (v_isShared_1522_ == 0)
{
lean_ctor_set_tag(v___x_1521_, 0);
lean_ctor_set(v___x_1521_, 0, v_a_1534_);
v___x_1536_ = v___x_1521_;
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
v_val_1526_ = v___x_1536_;
goto v___jp_1525_;
}
}
v___jp_1525_:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1527_, 0, v_val_1526_);
v___x_1528_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1523_, v___x_1524_, v___x_1527_, v___f_1507_);
return v___x_1528_;
}
}
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
if (lean_obj_tag(v_x_1548_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1558_; 
lean_dec_ref(v___f_1545_);
v_a_1550_ = lean_ctor_get(v_x_1548_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v_x_1548_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1552_ = v_x_1548_;
v_isShared_1553_ = v_isSharedCheck_1558_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v_x_1548_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1558_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1556_; 
v___x_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
return v___x_1556_;
}
}
}
else
{
lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1577_; 
v_isSharedCheck_1577_ = !lean_is_exclusive(v_x_1548_);
if (v_isSharedCheck_1577_ == 0)
{
lean_object* v_unused_1578_; 
v_unused_1578_ = lean_ctor_get(v_x_1548_, 0);
lean_dec(v_unused_1578_);
v___x_1560_ = v_x_1548_;
v_isShared_1561_ = v_isSharedCheck_1577_;
goto v_resetjp_1559_;
}
else
{
lean_dec(v_x_1548_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1577_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1562_; uint8_t v___x_1563_; lean_object* v_val_1565_; lean_object* v___x_1568_; 
v___x_1562_ = lean_unsigned_to_nat(0u);
v___x_1563_ = 0;
v___x_1568_ = lean_uv_tcp_listen(v_a_1546_, v_backlog_1547_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1571_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
lean_dec_ref_known(v___x_1568_, 1);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 0, v_a_1569_);
v___x_1571_ = v___x_1560_;
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
v_val_1565_ = v___x_1571_;
goto v___jp_1564_;
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; 
v_a_1573_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1573_);
lean_dec_ref_known(v___x_1568_, 1);
if (v_isShared_1561_ == 0)
{
lean_ctor_set_tag(v___x_1560_, 0);
lean_ctor_set(v___x_1560_, 0, v_a_1573_);
v___x_1575_ = v___x_1560_;
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
v_val_1565_ = v___x_1575_;
goto v___jp_1564_;
}
}
v___jp_1564_:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1566_, 0, v_val_1565_);
v___x_1567_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1562_, v___x_1563_, v___x_1566_, v___f_1545_);
return v___x_1567_;
}
}
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
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__33(lean_object* v___x_1586_, lean_object* v___f_1587_, lean_object* v___f_1588_, lean_object* v___x_1589_, lean_object* v_inst_1590_, lean_object* v_handler_1591_, lean_object* v_config_1592_, lean_object* v___f_1593_, lean_object* v___x_1594_, lean_object* v___f_1595_, lean_object* v___f_1596_, lean_object* v___f_1597_, lean_object* v___f_1598_, lean_object* v___f_1599_, lean_object* v___f_1600_, uint32_t v_backlog_1601_, lean_object* v_addr_1602_, lean_object* v_x_1603_){
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
lean_dec_ref(v___f_1595_);
lean_dec(v___x_1594_);
lean_dec_ref(v___f_1593_);
lean_dec_ref(v_config_1592_);
lean_dec(v_handler_1591_);
lean_dec_ref(v_inst_1590_);
lean_dec_ref(v___x_1589_);
lean_dec_ref(v___f_1588_);
lean_dec_ref(v___f_1587_);
lean_dec_ref(v___x_1586_);
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
lean_object* v___f_1618_; lean_object* v___f_1619_; lean_object* v___f_1620_; lean_object* v___f_1621_; lean_object* v___x_1622_; lean_object* v___f_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; lean_object* v_val_1627_; lean_object* v___x_1630_; 
lean_inc_n(v_a_1614_, 4);
lean_inc_ref(v_config_1592_);
v___f_1618_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__28___boxed), 18, 16);
lean_closure_set(v___f_1618_, 0, v___x_1586_);
lean_closure_set(v___f_1618_, 1, v___f_1587_);
lean_closure_set(v___f_1618_, 2, v___f_1588_);
lean_closure_set(v___f_1618_, 3, v___x_1589_);
lean_closure_set(v___f_1618_, 4, v_inst_1590_);
lean_closure_set(v___f_1618_, 5, v_handler_1591_);
lean_closure_set(v___f_1618_, 6, v_config_1592_);
lean_closure_set(v___f_1618_, 7, v___f_1593_);
lean_closure_set(v___f_1618_, 8, v___x_1594_);
lean_closure_set(v___f_1618_, 9, v_a_1614_);
lean_closure_set(v___f_1618_, 10, v___f_1595_);
lean_closure_set(v___f_1618_, 11, v___f_1596_);
lean_closure_set(v___f_1618_, 12, v___f_1597_);
lean_closure_set(v___f_1618_, 13, v___f_1598_);
lean_closure_set(v___f_1618_, 14, v___f_1599_);
lean_closure_set(v___f_1618_, 15, v___f_1600_);
v___f_1619_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__29___boxed), 4, 2);
lean_closure_set(v___f_1619_, 0, v___f_1618_);
lean_closure_set(v___f_1619_, 1, v_config_1592_);
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
v___x_1624_ = lean_unsigned_to_nat(0u);
v___x_1625_ = 0;
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
v_val_1627_ = v___x_1633_;
goto v___jp_1626_;
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
v_val_1627_ = v___x_1637_;
goto v___jp_1626_;
}
}
v___jp_1626_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1628_, 0, v_val_1627_);
v___x_1629_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1624_, v___x_1625_, v___x_1628_, v___f_1623_);
return v___x_1629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__33___boxed(lean_object** _args){
lean_object* v___x_1640_ = _args[0];
lean_object* v___f_1641_ = _args[1];
lean_object* v___f_1642_ = _args[2];
lean_object* v___x_1643_ = _args[3];
lean_object* v_inst_1644_ = _args[4];
lean_object* v_handler_1645_ = _args[5];
lean_object* v_config_1646_ = _args[6];
lean_object* v___f_1647_ = _args[7];
lean_object* v___x_1648_ = _args[8];
lean_object* v___f_1649_ = _args[9];
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
v_res_1660_ = l_Std_Http_Server_serve___redArg___lam__33(v___x_1640_, v___f_1641_, v___f_1642_, v___x_1643_, v_inst_1644_, v_handler_1645_, v_config_1646_, v___f_1647_, v___x_1648_, v___f_1649_, v___f_1650_, v___f_1651_, v___f_1652_, v___f_1653_, v___f_1654_, v_backlog_boxed_1659_, v_addr_1656_, v_x_1657_);
lean_dec_ref(v_addr_1656_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg(lean_object* v_inst_1667_, lean_object* v_addr_1668_, lean_object* v_handler_1669_, lean_object* v_config_1670_, uint32_t v_backlog_1671_){
_start:
{
lean_object* v___f_1673_; lean_object* v___f_1674_; lean_object* v___f_1675_; lean_object* v___f_1676_; lean_object* v___f_1677_; lean_object* v___f_1678_; lean_object* v___f_1679_; lean_object* v___f_1680_; lean_object* v___f_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___f_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; lean_object* v_val_1690_; lean_object* v___x_1693_; 
v___f_1673_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__0));
v___f_1674_ = ((lean_object*)(l_Std_Http_Server_waitShutdown___closed__0));
v___f_1675_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__1));
v___f_1676_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__2));
v___f_1677_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2));
v___f_1678_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__3));
v___f_1679_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0));
v___f_1680_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__4));
v___f_1681_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__5));
v___x_1682_ = l_Std_Async_ContextAsync_instMonad;
v___x_1683_ = l_Std_Http_instTransportClient;
v___x_1684_ = l_Std_Http_Server_instImpl_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8_;
v___x_1685_ = lean_box_uint32(v_backlog_1671_);
v___f_1686_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__33___boxed), 19, 17);
lean_closure_set(v___f_1686_, 0, v___x_1682_);
lean_closure_set(v___f_1686_, 1, v___f_1677_);
lean_closure_set(v___f_1686_, 2, v___f_1678_);
lean_closure_set(v___f_1686_, 3, v___x_1683_);
lean_closure_set(v___f_1686_, 4, v_inst_1667_);
lean_closure_set(v___f_1686_, 5, v_handler_1669_);
lean_closure_set(v___f_1686_, 6, v_config_1670_);
lean_closure_set(v___f_1686_, 7, v___f_1679_);
lean_closure_set(v___f_1686_, 8, v___x_1684_);
lean_closure_set(v___f_1686_, 9, v___f_1675_);
lean_closure_set(v___f_1686_, 10, v___f_1676_);
lean_closure_set(v___f_1686_, 11, v___f_1680_);
lean_closure_set(v___f_1686_, 12, v___f_1681_);
lean_closure_set(v___f_1686_, 13, v___f_1674_);
lean_closure_set(v___f_1686_, 14, v___f_1673_);
lean_closure_set(v___f_1686_, 15, v___x_1685_);
lean_closure_set(v___f_1686_, 16, v_addr_1668_);
v___x_1687_ = lean_unsigned_to_nat(0u);
v___x_1688_ = 0;
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
v_val_1690_ = v___x_1699_;
goto v___jp_1689_;
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
v_val_1690_ = v___x_1707_;
goto v___jp_1689_;
}
}
}
v___jp_1689_:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1691_, 0, v_val_1690_);
v___x_1692_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1687_, v___x_1688_, v___x_1691_, v___f_1686_);
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
