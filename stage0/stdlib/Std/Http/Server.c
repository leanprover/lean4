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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Channel_send___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Std_Http_instTransportClient;
lean_object* l_Std_CancellationContext_cancel(lean_object*, lean_object*);
lean_object* l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_ContextAsync_instMonadFinally___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Mutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonad___aux__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Server_serveConnection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_BaseAsync_toRawBaseIO___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* l_Std_CancellationContext_fork(lean_object*);
extern lean_object* l_Std_Http_Extensions_empty;
extern lean_object* l_Std_Http_Server_instImpl_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8_;
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5___boxed(lean_object*);
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
static const lean_closure_object l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5 = (const lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5_value;
static const lean_closure_object l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6 = (const lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3___boxed(lean_object*);
static const lean_ctor_object l_Std_Http_Server_serve___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Server_serve___redArg___lam__4___closed__0 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__4___closed__0_value;
static const lean_ctor_object l_Std_Http_Server_serve___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Server_serve___redArg___lam__4___closed__0_value)}};
static const lean_object* l_Std_Http_Server_serve___redArg___lam__4___closed__1 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__4___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Server_serve___redArg___lam__19___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Server_serve___redArg___lam__19___closed__0;
static lean_once_cell_t l_Std_Http_Server_serve___redArg___lam__19___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Server_serve___redArg___lam__19___closed__1;
static const lean_closure_object l_Std_Http_Server_serve___redArg___lam__19___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Extensions_compareName___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___lam__19___closed__2 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__19___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__19(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32(lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__33___boxed(lean_object**);
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__0 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__0_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__1 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__1_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__2 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__2_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__4___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__3 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__3_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__4 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__4_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__5___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
v___x_126_ = lean_st_ref_set(v___y_120_, v___x_125_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1(lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_135_ = lean_st_ref_take(v___y_132_);
v___x_136_ = lean_unsigned_to_nat(1u);
v___x_137_ = lean_nat_sub(v___x_135_, v___x_136_);
lean_dec(v___x_135_);
v___x_138_ = lean_st_ref_set(v___y_132_, v___x_137_);
v___x_139_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1___boxed(lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1(v___y_140_, v___y_141_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2(lean_object* v_a_144_, lean_object* v_shutdownPromise_145_, lean_object* v_x_146_){
_start:
{
if (lean_obj_tag(v_x_146_) == 0)
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_158_; 
lean_dec_ref(v_shutdownPromise_145_);
v_a_150_ = lean_ctor_get(v_x_146_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v_x_146_);
if (v_isSharedCheck_158_ == 0)
{
v___x_152_ = v_x_146_;
v_isShared_153_ = v_isSharedCheck_158_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v_x_146_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_158_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_150_);
v___x_155_ = v_reuseFailAlloc_157_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_156_; 
v___x_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
return v___x_156_;
}
}
}
else
{
lean_object* v_a_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v_a_159_ = lean_ctor_get(v_x_146_, 0);
lean_inc(v_a_159_);
lean_dec_ref_known(v_x_146_, 1);
v___x_160_ = lean_unsigned_to_nat(0u);
v___x_161_ = lean_nat_dec_eq(v_a_144_, v___x_160_);
if (v___x_161_ == 0)
{
lean_dec(v_a_159_);
lean_dec_ref(v_shutdownPromise_145_);
goto v___jp_148_;
}
else
{
uint8_t v___x_162_; 
v___x_162_ = lean_unbox(v_a_159_);
lean_dec(v_a_159_);
if (v___x_162_ == 0)
{
lean_dec_ref(v_shutdownPromise_145_);
goto v___jp_148_;
}
else
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = lean_box(0);
v___x_164_ = l_Std_Channel_send___redArg(v_shutdownPromise_145_, v___x_163_);
lean_dec_ref(v___x_164_);
v___x_165_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_165_;
}
}
}
v___jp_148_:
{
lean_object* v___x_149_; 
v___x_149_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_149_;
}
}
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3(lean_object* v_context_171_, lean_object* v_shutdownPromise_172_, lean_object* v_x_173_){
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
lean_object* v_token_188_; uint8_t v___x_189_; lean_object* v___f_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
v_token_188_ = lean_ctor_get(v_context_171_, 1);
lean_inc_ref(v_token_188_);
lean_dec_ref(v_context_171_);
v___x_189_ = l_Std_CancellationToken_isCancelled(v_token_188_);
v___f_190_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_190_, 0, v_a_184_);
lean_closure_set(v___f_190_, 1, v_shutdownPromise_172_);
v___x_191_ = lean_box(v___x_189_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_191_);
v___x_193_ = v___x_186_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_198_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; lean_object* v___x_197_; 
v___x_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = 0;
v___x_197_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_195_, v___x_196_, v___x_194_, v___f_190_);
return v___x_197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed(lean_object* v_context_200_, lean_object* v_shutdownPromise_201_, lean_object* v_x_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3(v_context_200_, v_shutdownPromise_201_, v_x_202_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4(lean_object* v___f_205_, lean_object* v_____r_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; lean_object* v___x_215_; 
v___x_210_ = lean_st_ref_get(v___y_207_);
v___x_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
v___x_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
v___x_213_ = lean_unsigned_to_nat(0u);
v___x_214_ = 0;
v___x_215_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_213_, v___x_214_, v___x_212_, v___f_205_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed(lean_object* v___f_216_, lean_object* v_____r_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4(v___f_216_, v_____r_217_, v___y_218_, v___y_219_);
lean_dec_ref(v___y_219_);
lean_dec(v___y_218_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5(lean_object* v_x_222_){
_start:
{
lean_object* v_fst_223_; 
v_fst_223_ = lean_ctor_get(v_x_222_, 0);
lean_inc(v_fst_223_);
return v_fst_223_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5___boxed(lean_object* v_x_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5(v_x_224_);
lean_dec_ref(v_x_224_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6(lean_object* v___x_226_, lean_object* v___f_227_, lean_object* v___f_228_, lean_object* v___f_229_, lean_object* v___f_230_, lean_object* v_activeConnections_231_, lean_object* v_____r_232_, lean_object* v___y_233_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_2353__overap_236_; lean_object* v___x_237_; 
lean_inc_ref(v___x_226_);
v___x_235_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_235_, 0, lean_box(0));
lean_closure_set(v___x_235_, 1, lean_box(0));
lean_closure_set(v___x_235_, 2, lean_box(0));
lean_closure_set(v___x_235_, 3, v___x_226_);
lean_closure_set(v___x_235_, 4, lean_box(0));
lean_closure_set(v___x_235_, 5, lean_box(0));
lean_closure_set(v___x_235_, 6, v___f_227_);
lean_closure_set(v___x_235_, 7, v___f_228_);
v___x_2353__overap_236_ = l_Std_Mutex_atomically___redArg(v___x_226_, v___f_229_, v___f_230_, v_activeConnections_231_, v___x_235_);
lean_inc_ref(v___y_233_);
v___x_237_ = lean_apply_2(v___x_2353__overap_236_, v___y_233_, lean_box(0));
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
lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_273_ = l_Std_Semaphore_release(v_val_269_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_273_);
v___x_275_ = v___x_271_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_280_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; lean_object* v___x_279_; 
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = 0;
v___x_279_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_277_, v___x_278_, v___x_276_, v___f_264_);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9(lean_object* v_action_293_, lean_object* v_a_294_, lean_object* v___f_295_, lean_object* v___f_296_, lean_object* v_x_297_){
_start:
{
if (lean_obj_tag(v_x_297_) == 0)
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_307_; 
lean_dec(v___f_296_);
lean_dec_ref(v___f_295_);
lean_dec_ref(v_action_293_);
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
lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___y_313_; 
lean_dec_ref_known(v_x_297_, 1);
lean_inc_ref(v_a_294_);
v___x_308_ = lean_apply_1(v_action_293_, v_a_294_);
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = 0;
v___x_311_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_308_, v___f_295_, v___x_309_, v___x_310_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_315_; 
lean_dec(v___f_296_);
v_a_315_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_315_);
lean_dec_ref_known(v___x_311_, 1);
if (lean_obj_tag(v_a_315_) == 0)
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
v_a_316_ = lean_ctor_get(v_a_315_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v_a_315_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v_a_315_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v_a_315_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
v___y_313_ = v___x_321_;
goto v___jp_312_;
}
}
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_332_; 
v_a_324_ = lean_ctor_get(v_a_315_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v_a_315_);
if (v_isSharedCheck_332_ == 0)
{
v___x_326_ = v_a_315_;
v_isShared_327_ = v_isSharedCheck_332_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v_a_315_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_332_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v_fst_328_; lean_object* v___x_330_; 
v_fst_328_ = lean_ctor_get(v_a_324_, 0);
lean_inc(v_fst_328_);
lean_dec(v_a_324_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 0, v_fst_328_);
v___x_330_ = v___x_326_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_fst_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
v___y_313_ = v___x_330_;
goto v___jp_312_;
}
}
}
}
else
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_342_; 
v_a_333_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_342_ == 0)
{
v___x_335_ = v___x_311_;
v_isShared_336_ = v_isSharedCheck_342_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_311_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_342_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_337_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_337_, 0, lean_box(0));
lean_closure_set(v___x_337_, 1, lean_box(0));
lean_closure_set(v___x_337_, 2, lean_box(0));
lean_closure_set(v___x_337_, 3, v___f_296_);
v___x_338_ = lean_task_map(v___x_337_, v_a_333_, v___x_309_, v___x_310_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_338_);
v___x_340_ = v___x_335_;
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
v___jp_312_:
{
lean_object* v___x_314_; 
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v___y_313_);
return v___x_314_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed(lean_object* v_action_343_, lean_object* v_a_344_, lean_object* v___f_345_, lean_object* v___f_346_, lean_object* v_x_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9(v_action_343_, v_a_344_, v___f_345_, v___f_346_, v_x_347_);
lean_dec_ref(v_a_344_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg(lean_object* v_s_359_, uint8_t v_releaseConnectionPermit_360_, lean_object* v_action_361_, lean_object* v_a_362_){
_start:
{
lean_object* v___x_364_; lean_object* v_context_365_; lean_object* v_activeConnections_366_; lean_object* v_connectionLimit_367_; lean_object* v_shutdownPromise_368_; lean_object* v___f_369_; lean_object* v___f_370_; lean_object* v___f_371_; lean_object* v___x_1520__overap_372_; lean_object* v___x_373_; lean_object* v___f_374_; lean_object* v___f_375_; lean_object* v___f_376_; lean_object* v___f_377_; lean_object* v___f_378_; lean_object* v___f_379_; lean_object* v___x_380_; lean_object* v___f_381_; lean_object* v___f_382_; lean_object* v___x_383_; uint8_t v___x_384_; lean_object* v___x_385_; 
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
v___f_370_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3));
v___f_371_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4));
v___x_1520__overap_372_ = l_Std_Mutex_atomically___redArg(v___x_364_, v___f_370_, v___f_371_, v_activeConnections_366_, v___f_369_);
lean_inc_ref_n(v_a_362_, 4);
v___x_373_ = lean_apply_2(v___x_1520__overap_372_, v_a_362_, lean_box(0));
v___f_374_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5));
v___f_375_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_375_, 0, v_context_365_);
lean_closure_set(v___f_375_, 1, v_shutdownPromise_368_);
v___f_376_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed), 5, 1);
lean_closure_set(v___f_376_, 0, v___f_375_);
v___f_377_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6));
v___f_378_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed), 9, 6);
lean_closure_set(v___f_378_, 0, v___x_364_);
lean_closure_set(v___f_378_, 1, v___f_374_);
lean_closure_set(v___f_378_, 2, v___f_376_);
lean_closure_set(v___f_378_, 3, v___f_370_);
lean_closure_set(v___f_378_, 4, v___f_371_);
lean_closure_set(v___f_378_, 5, v_activeConnections_366_);
lean_inc_ref(v___f_378_);
v___f_379_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_379_, 0, v___f_378_);
lean_closure_set(v___f_379_, 1, v_a_362_);
v___x_380_ = lean_box(v_releaseConnectionPermit_360_);
v___f_381_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed), 7, 5);
lean_closure_set(v___f_381_, 0, v___x_380_);
lean_closure_set(v___f_381_, 1, v___f_378_);
lean_closure_set(v___f_381_, 2, v_a_362_);
lean_closure_set(v___f_381_, 3, v_connectionLimit_367_);
lean_closure_set(v___f_381_, 4, v___f_379_);
v___f_382_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed), 6, 4);
lean_closure_set(v___f_382_, 0, v_action_361_);
lean_closure_set(v___f_382_, 1, v_a_362_);
lean_closure_set(v___f_382_, 2, v___f_381_);
lean_closure_set(v___f_382_, 3, v___f_377_);
v___x_383_ = lean_unsigned_to_nat(0u);
v___x_384_ = 0;
v___x_385_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_383_, v___x_384_, v___x_373_, v___f_382_);
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
lean_object* v___x_399_; lean_object* v_context_400_; lean_object* v_activeConnections_401_; lean_object* v_connectionLimit_402_; lean_object* v_shutdownPromise_403_; lean_object* v___f_404_; lean_object* v___f_405_; lean_object* v___f_406_; lean_object* v___x_2130__overap_407_; lean_object* v___x_408_; lean_object* v___f_409_; lean_object* v___f_410_; lean_object* v___f_411_; lean_object* v___f_412_; lean_object* v___f_413_; lean_object* v___f_414_; lean_object* v___x_415_; lean_object* v___f_416_; lean_object* v___f_417_; lean_object* v___x_418_; uint8_t v___x_419_; lean_object* v___x_420_; 
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
v___f_405_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3));
v___f_406_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4));
v___x_2130__overap_407_ = l_Std_Mutex_atomically___redArg(v___x_399_, v___f_405_, v___f_406_, v_activeConnections_401_, v___f_404_);
lean_inc_ref_n(v_a_397_, 4);
v___x_408_ = lean_apply_2(v___x_2130__overap_407_, v_a_397_, lean_box(0));
v___f_409_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5));
v___f_410_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_410_, 0, v_context_400_);
lean_closure_set(v___f_410_, 1, v_shutdownPromise_403_);
v___f_411_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed), 5, 1);
lean_closure_set(v___f_411_, 0, v___f_410_);
v___f_412_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6));
v___f_413_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed), 9, 6);
lean_closure_set(v___f_413_, 0, v___x_399_);
lean_closure_set(v___f_413_, 1, v___f_409_);
lean_closure_set(v___f_413_, 2, v___f_411_);
lean_closure_set(v___f_413_, 3, v___f_405_);
lean_closure_set(v___f_413_, 4, v___f_406_);
lean_closure_set(v___f_413_, 5, v_activeConnections_401_);
lean_inc_ref(v___f_413_);
v___f_414_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_414_, 0, v___f_413_);
lean_closure_set(v___f_414_, 1, v_a_397_);
v___x_415_ = lean_box(v_releaseConnectionPermit_395_);
v___f_416_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed), 7, 5);
lean_closure_set(v___f_416_, 0, v___x_415_);
lean_closure_set(v___f_416_, 1, v___f_413_);
lean_closure_set(v___f_416_, 2, v_a_397_);
lean_closure_set(v___f_416_, 3, v_connectionLimit_402_);
lean_closure_set(v___f_416_, 4, v___f_414_);
v___f_417_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed), 6, 4);
lean_closure_set(v___f_417_, 0, v_action_396_);
lean_closure_set(v___f_417_, 1, v_a_397_);
lean_closure_set(v___f_417_, 2, v___f_416_);
lean_closure_set(v___f_417_, 3, v___f_412_);
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = 0;
v___x_420_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_418_, v___x_419_, v___x_408_, v___f_417_);
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
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__0(lean_object* v_x_429_){
_start:
{
if (lean_obj_tag(v_x_429_) == 0)
{
lean_object* v___x_431_; 
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v_x_429_);
return v___x_431_;
}
else
{
lean_object* v___x_432_; 
lean_dec_ref_known(v_x_429_, 1);
v___x_432_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_432_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__0___boxed(lean_object* v_x_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Std_Http_Server_serve___redArg___lam__0(v_x_433_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1(lean_object* v_x_436_){
_start:
{
if (lean_obj_tag(v_x_436_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_446_; 
v_a_438_ = lean_ctor_get(v_x_436_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v_x_436_);
if (v_isSharedCheck_446_ == 0)
{
v___x_440_ = v_x_436_;
v_isShared_441_ = v_isSharedCheck_446_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v_x_436_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_446_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_445_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_444_; 
v___x_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
return v___x_444_;
}
}
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_475_; 
v_a_447_ = lean_ctor_get(v_x_436_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v_x_436_);
if (v_isSharedCheck_475_ == 0)
{
v___x_449_ = v_x_436_;
v_isShared_450_ = v_isSharedCheck_475_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v_x_436_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_475_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
if (lean_obj_tag(v_a_447_) == 0)
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_462_; 
v_a_451_ = lean_ctor_get(v_a_447_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v_a_447_);
if (v_isSharedCheck_462_ == 0)
{
v___x_453_ = v_a_447_;
v_isShared_454_ = v_isSharedCheck_462_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v_a_447_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_462_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set_tag(v___x_453_, 1);
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_461_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_458_; 
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_456_);
v___x_458_ = v___x_449_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_456_);
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
}
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_474_; 
v_a_463_ = lean_ctor_get(v_a_447_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v_a_447_);
if (v_isSharedCheck_474_ == 0)
{
v___x_465_ = v_a_447_;
v_isShared_466_ = v_isSharedCheck_474_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v_a_447_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_474_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
lean_ctor_set_tag(v___x_465_, 0);
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_473_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_470_; 
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_468_);
v___x_470_ = v___x_449_;
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
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1___boxed(lean_object* v_x_476_, lean_object* v___y_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Std_Http_Server_serve___redArg___lam__1(v_x_476_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3(lean_object* v_x_479_){
_start:
{
lean_object* v_fst_480_; 
v_fst_480_ = lean_ctor_get(v_x_479_, 0);
lean_inc(v_fst_480_);
return v_fst_480_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3___boxed(lean_object* v_x_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_Http_Server_serve___redArg___lam__3(v_x_481_);
lean_dec_ref(v_x_481_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4(lean_object* v_x_487_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__4___closed__1));
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4___boxed(lean_object* v_x_490_, lean_object* v___y_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Std_Http_Server_serve___redArg___lam__4(v_x_490_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2(lean_object* v_x_493_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_495_, 0, v_x_493_);
v___x_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2___boxed(lean_object* v_x_498_, lean_object* v___y_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Std_Http_Server_serve___redArg___lam__2(v_x_498_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5(lean_object* v_x_501_){
_start:
{
if (lean_obj_tag(v_x_501_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_511_; 
v_a_503_ = lean_ctor_get(v_x_501_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v_x_501_);
if (v_isSharedCheck_511_ == 0)
{
v___x_505_ = v_x_501_;
v_isShared_506_ = v_isSharedCheck_511_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v_x_501_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_511_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_510_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_509_; 
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_522_; 
v_a_512_ = lean_ctor_get(v_x_501_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v_x_501_);
if (v_isSharedCheck_522_ == 0)
{
v___x_514_ = v_x_501_;
v_isShared_515_ = v_isSharedCheck_522_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v_x_501_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_522_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v_token_516_; lean_object* v___x_517_; lean_object* v___x_519_; 
v_token_516_ = lean_ctor_get(v_a_512_, 1);
lean_inc_ref(v_token_516_);
lean_dec(v_a_512_);
v___x_517_ = l_Std_CancellationToken_selector(v_token_516_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_517_);
v___x_519_ = v___x_514_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_521_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
lean_object* v___x_520_; 
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5___boxed(lean_object* v_x_523_, lean_object* v___y_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Std_Http_Server_serve___redArg___lam__5(v_x_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10(lean_object* v___x_526_, lean_object* v_____r_527_, lean_object* v___y_528_){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_526_);
v___x_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10___boxed(lean_object* v___x_533_, lean_object* v_____r_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Std_Http_Server_serve___redArg___lam__10(v___x_533_, v_____r_534_, v___y_535_);
lean_dec_ref(v___y_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6(lean_object* v___x_538_, lean_object* v_x_539_){
_start:
{
if (lean_obj_tag(v_x_539_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_549_; 
v_a_541_ = lean_ctor_get(v_x_539_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v_x_539_);
if (v_isSharedCheck_549_ == 0)
{
v___x_543_ = v_x_539_;
v_isShared_544_ = v_isSharedCheck_549_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v_x_539_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_549_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_548_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
lean_object* v___x_547_; 
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
}
}
else
{
lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_558_; 
v_isSharedCheck_558_ = !lean_is_exclusive(v_x_539_);
if (v_isSharedCheck_558_ == 0)
{
lean_object* v_unused_559_; 
v_unused_559_ = lean_ctor_get(v_x_539_, 0);
lean_dec(v_unused_559_);
v___x_551_ = v_x_539_;
v_isShared_552_ = v_isSharedCheck_558_;
goto v_resetjp_550_;
}
else
{
lean_dec(v_x_539_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_558_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_538_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_553_);
v___x_555_ = v___x_551_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_553_);
v___x_555_ = v_reuseFailAlloc_557_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_556_; 
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6___boxed(lean_object* v___x_560_, lean_object* v_x_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Std_Http_Server_serve___redArg___lam__6(v___x_560_, v_x_561_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7(lean_object* v___f_564_, lean_object* v___y_565_, lean_object* v_x_566_){
_start:
{
if (lean_obj_tag(v_x_566_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_576_; 
lean_dec_ref(v___f_564_);
v_a_568_ = lean_ctor_get(v_x_566_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v_x_566_);
if (v_isSharedCheck_576_ == 0)
{
v___x_570_ = v_x_566_;
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v_x_566_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_568_);
v___x_573_ = v_reuseFailAlloc_575_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
lean_object* v___x_574_; 
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
}
}
else
{
lean_object* v_a_577_; lean_object* v___x_578_; 
v_a_577_ = lean_ctor_get(v_x_566_, 0);
lean_inc(v_a_577_);
lean_dec_ref_known(v_x_566_, 1);
lean_inc_ref(v___y_565_);
v___x_578_ = lean_apply_3(v___f_564_, v_a_577_, v___y_565_, lean_box(0));
return v___x_578_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7___boxed(lean_object* v___f_579_, lean_object* v___y_580_, lean_object* v_x_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_Http_Server_serve___redArg___lam__7(v___f_579_, v___y_580_, v_x_581_);
lean_dec_ref(v___y_580_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8(lean_object* v_a_584_, lean_object* v_x_585_){
_start:
{
if (lean_obj_tag(v_x_585_) == 0)
{
lean_object* v___x_587_; 
lean_dec_ref(v_a_584_);
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v_x_585_);
return v___x_587_;
}
else
{
lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_597_; 
v_isSharedCheck_597_ = !lean_is_exclusive(v_x_585_);
if (v_isSharedCheck_597_ == 0)
{
lean_object* v_unused_598_; 
v_unused_598_ = lean_ctor_get(v_x_585_, 0);
lean_dec(v_unused_598_);
v___x_589_ = v_x_585_;
v_isShared_590_ = v_isSharedCheck_597_;
goto v_resetjp_588_;
}
else
{
lean_dec(v_x_585_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_597_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_591_ = lean_box(2);
v___x_592_ = l_Std_CancellationContext_cancel(v_a_584_, v___x_591_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v___x_592_);
v___x_594_ = v___x_589_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_592_);
v___x_594_ = v_reuseFailAlloc_596_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; 
v___x_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
return v___x_595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8___boxed(lean_object* v_a_599_, lean_object* v_x_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Std_Http_Server_serve___redArg___lam__8(v_a_599_, v_x_600_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11(lean_object* v___f_603_, lean_object* v_a_604_, lean_object* v_x_605_){
_start:
{
if (lean_obj_tag(v_x_605_) == 0)
{
lean_object* v___x_607_; 
lean_dec_ref(v_a_604_);
lean_dec_ref(v___f_603_);
v___x_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_607_, 0, v_x_605_);
return v___x_607_;
}
else
{
lean_object* v_a_608_; lean_object* v___x_609_; 
v_a_608_ = lean_ctor_get(v_x_605_, 0);
lean_inc(v_a_608_);
lean_dec_ref_known(v_x_605_, 1);
v___x_609_ = lean_apply_3(v___f_603_, v_a_608_, v_a_604_, lean_box(0));
return v___x_609_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11___boxed(lean_object* v___f_610_, lean_object* v_a_611_, lean_object* v_x_612_, lean_object* v___y_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Std_Http_Server_serve___redArg___lam__11(v___f_610_, v_a_611_, v_x_612_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9(uint8_t v_permitAcquired_615_, lean_object* v___f_616_, lean_object* v___x_617_, lean_object* v_a_618_, lean_object* v_connectionLimit_619_, lean_object* v___x_620_, uint8_t v___x_621_, lean_object* v___f_622_, lean_object* v_opt_623_){
_start:
{
if (v_permitAcquired_615_ == 0)
{
lean_object* v___x_625_; 
lean_dec_ref(v___f_622_);
lean_dec(v___x_620_);
lean_dec(v_connectionLimit_619_);
v___x_625_ = lean_apply_3(v___f_616_, v___x_617_, v_a_618_, lean_box(0));
return v___x_625_;
}
else
{
if (lean_obj_tag(v_connectionLimit_619_) == 1)
{
lean_object* v_val_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_636_; 
lean_dec_ref(v_a_618_);
lean_dec_ref(v___f_616_);
v_val_626_ = lean_ctor_get(v_connectionLimit_619_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v_connectionLimit_619_);
if (v_isSharedCheck_636_ == 0)
{
v___x_628_ = v_connectionLimit_619_;
v_isShared_629_ = v_isSharedCheck_636_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_val_626_);
lean_dec(v_connectionLimit_619_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_636_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_630_ = l_Std_Semaphore_release(v_val_626_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v___x_630_);
v___x_632_ = v___x_628_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_630_);
v___x_632_ = v_reuseFailAlloc_635_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
v___x_634_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_620_, v___x_621_, v___x_633_, v___f_622_);
return v___x_634_;
}
}
}
else
{
lean_object* v___x_637_; 
lean_dec_ref(v___f_622_);
lean_dec(v___x_620_);
lean_dec(v_connectionLimit_619_);
v___x_637_ = lean_apply_3(v___f_616_, v___x_617_, v_a_618_, lean_box(0));
return v___x_637_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9___boxed(lean_object* v_permitAcquired_638_, lean_object* v___f_639_, lean_object* v___x_640_, lean_object* v_a_641_, lean_object* v_connectionLimit_642_, lean_object* v___x_643_, lean_object* v___x_644_, lean_object* v___f_645_, lean_object* v_opt_646_, lean_object* v___y_647_){
_start:
{
uint8_t v_permitAcquired_boxed_648_; uint8_t v___x_13775__boxed_649_; lean_object* v_res_650_; 
v_permitAcquired_boxed_648_ = lean_unbox(v_permitAcquired_638_);
v___x_13775__boxed_649_ = lean_unbox(v___x_644_);
v_res_650_ = l_Std_Http_Server_serve___redArg___lam__9(v_permitAcquired_boxed_648_, v___f_639_, v___x_640_, v_a_641_, v_connectionLimit_642_, v___x_643_, v___x_13775__boxed_649_, v___f_645_, v_opt_646_);
lean_dec(v_opt_646_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12(lean_object* v___x_651_, lean_object* v_inst_652_, lean_object* v_val_653_, lean_object* v_handler_654_, lean_object* v_config_655_, lean_object* v_extensions_656_, lean_object* v_a_657_, lean_object* v___f_658_, lean_object* v___x_659_, uint8_t v___x_660_, lean_object* v___f_661_, lean_object* v_x_662_){
_start:
{
if (lean_obj_tag(v_x_662_) == 0)
{
lean_object* v___x_664_; 
lean_dec_ref(v___f_661_);
lean_dec(v___x_659_);
lean_dec_ref(v___f_658_);
lean_dec_ref(v_a_657_);
lean_dec(v_extensions_656_);
lean_dec_ref(v_config_655_);
lean_dec(v_handler_654_);
lean_dec(v_val_653_);
lean_dec_ref(v_inst_652_);
lean_dec_ref(v___x_651_);
v___x_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_664_, 0, v_x_662_);
return v___x_664_;
}
else
{
lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_703_; 
v_isSharedCheck_703_ = !lean_is_exclusive(v_x_662_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; 
v_unused_704_ = lean_ctor_get(v_x_662_, 0);
lean_dec(v_unused_704_);
v___x_666_ = v_x_662_;
v_isShared_667_ = v_isSharedCheck_703_;
goto v_resetjp_665_;
}
else
{
lean_dec(v_x_662_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_703_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___y_671_; 
v___x_668_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___boxed), 10, 9);
lean_closure_set(v___x_668_, 0, lean_box(0));
lean_closure_set(v___x_668_, 1, lean_box(0));
lean_closure_set(v___x_668_, 2, v___x_651_);
lean_closure_set(v___x_668_, 3, v_inst_652_);
lean_closure_set(v___x_668_, 4, v_val_653_);
lean_closure_set(v___x_668_, 5, v_handler_654_);
lean_closure_set(v___x_668_, 6, v_config_655_);
lean_closure_set(v___x_668_, 7, v_extensions_656_);
lean_closure_set(v___x_668_, 8, v_a_657_);
lean_inc(v___x_659_);
v___x_669_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_668_, v___f_658_, v___x_659_, v___x_660_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_675_; 
lean_dec_ref(v___f_661_);
lean_dec(v___x_659_);
v_a_675_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_675_);
lean_dec_ref_known(v___x_669_, 1);
if (lean_obj_tag(v_a_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
v_a_676_ = lean_ctor_get(v_a_675_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v_a_675_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v_a_675_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v_a_675_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
v___y_671_ = v___x_681_;
goto v___jp_670_;
}
}
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_692_; 
v_a_684_ = lean_ctor_get(v_a_675_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v_a_675_);
if (v_isSharedCheck_692_ == 0)
{
v___x_686_ = v_a_675_;
v_isShared_687_ = v_isSharedCheck_692_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v_a_675_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_692_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v_fst_688_; lean_object* v___x_690_; 
v_fst_688_ = lean_ctor_get(v_a_684_, 0);
lean_inc(v_fst_688_);
lean_dec(v_a_684_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v_fst_688_);
v___x_690_ = v___x_686_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_fst_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
v___y_671_ = v___x_690_;
goto v___jp_670_;
}
}
}
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_702_; 
lean_del_object(v___x_666_);
v_a_693_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_702_ == 0)
{
v___x_695_ = v___x_669_;
v_isShared_696_ = v_isSharedCheck_702_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_669_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_702_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_697_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_697_, 0, lean_box(0));
lean_closure_set(v___x_697_, 1, lean_box(0));
lean_closure_set(v___x_697_, 2, lean_box(0));
lean_closure_set(v___x_697_, 3, v___f_661_);
v___x_698_ = lean_task_map(v___x_697_, v_a_693_, v___x_659_, v___x_660_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_698_);
v___x_700_ = v___x_695_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
v___jp_670_:
{
lean_object* v___x_673_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set_tag(v___x_666_, 0);
lean_ctor_set(v___x_666_, 0, v___y_671_);
v___x_673_ = v___x_666_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___y_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12___boxed(lean_object* v___x_705_, lean_object* v_inst_706_, lean_object* v_val_707_, lean_object* v_handler_708_, lean_object* v_config_709_, lean_object* v_extensions_710_, lean_object* v_a_711_, lean_object* v___f_712_, lean_object* v___x_713_, lean_object* v___x_714_, lean_object* v___f_715_, lean_object* v_x_716_, lean_object* v___y_717_){
_start:
{
uint8_t v___x_13824__boxed_718_; lean_object* v_res_719_; 
v___x_13824__boxed_718_ = lean_unbox(v___x_714_);
v_res_719_ = l_Std_Http_Server_serve___redArg___lam__12(v___x_705_, v_inst_706_, v_val_707_, v_handler_708_, v_config_709_, v_extensions_710_, v_a_711_, v___f_712_, v___x_713_, v___x_13824__boxed_718_, v___f_715_, v_x_716_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13(lean_object* v___x_720_, lean_object* v_activeConnections_721_, lean_object* v___f_722_, lean_object* v_a_723_, lean_object* v___f_724_, lean_object* v___f_725_, uint8_t v_permitAcquired_726_, lean_object* v___x_727_, lean_object* v_connectionLimit_728_, lean_object* v___x_729_, uint8_t v___x_730_, lean_object* v___x_731_, lean_object* v_inst_732_, lean_object* v_val_733_, lean_object* v_handler_734_, lean_object* v_config_735_, lean_object* v_extensions_736_, lean_object* v___f_737_, lean_object* v___f_738_){
_start:
{
lean_object* v___f_740_; lean_object* v___f_741_; lean_object* v___x_12955__overap_742_; lean_object* v___x_743_; lean_object* v___f_744_; lean_object* v___f_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___f_748_; lean_object* v___x_749_; lean_object* v___f_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___f_740_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3));
v___f_741_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4));
lean_inc_ref(v_activeConnections_721_);
lean_inc_ref(v___x_720_);
v___x_12955__overap_742_ = l_Std_Mutex_atomically___redArg(v___x_720_, v___f_740_, v___f_741_, v_activeConnections_721_, v___f_722_);
lean_inc_ref_n(v_a_723_, 3);
v___x_743_ = lean_apply_2(v___x_12955__overap_742_, v_a_723_, lean_box(0));
v___f_744_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed), 9, 6);
lean_closure_set(v___f_744_, 0, v___x_720_);
lean_closure_set(v___f_744_, 1, v___f_724_);
lean_closure_set(v___f_744_, 2, v___f_725_);
lean_closure_set(v___f_744_, 3, v___f_740_);
lean_closure_set(v___f_744_, 4, v___f_741_);
lean_closure_set(v___f_744_, 5, v_activeConnections_721_);
lean_inc_ref(v___f_744_);
v___f_745_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__11___boxed), 4, 2);
lean_closure_set(v___f_745_, 0, v___f_744_);
lean_closure_set(v___f_745_, 1, v_a_723_);
v___x_746_ = lean_box(v_permitAcquired_726_);
v___x_747_ = lean_box(v___x_730_);
lean_inc_n(v___x_729_, 3);
v___f_748_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__9___boxed), 10, 8);
lean_closure_set(v___f_748_, 0, v___x_746_);
lean_closure_set(v___f_748_, 1, v___f_744_);
lean_closure_set(v___f_748_, 2, v___x_727_);
lean_closure_set(v___f_748_, 3, v_a_723_);
lean_closure_set(v___f_748_, 4, v_connectionLimit_728_);
lean_closure_set(v___f_748_, 5, v___x_729_);
lean_closure_set(v___f_748_, 6, v___x_747_);
lean_closure_set(v___f_748_, 7, v___f_745_);
v___x_749_ = lean_box(v___x_730_);
v___f_750_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__12___boxed), 13, 11);
lean_closure_set(v___f_750_, 0, v___x_731_);
lean_closure_set(v___f_750_, 1, v_inst_732_);
lean_closure_set(v___f_750_, 2, v_val_733_);
lean_closure_set(v___f_750_, 3, v_handler_734_);
lean_closure_set(v___f_750_, 4, v_config_735_);
lean_closure_set(v___f_750_, 5, v_extensions_736_);
lean_closure_set(v___f_750_, 6, v_a_723_);
lean_closure_set(v___f_750_, 7, v___f_748_);
lean_closure_set(v___f_750_, 8, v___x_729_);
lean_closure_set(v___f_750_, 9, v___x_749_);
lean_closure_set(v___f_750_, 10, v___f_737_);
v___x_751_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_729_, v___x_730_, v___x_743_, v___f_750_);
v___x_752_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_729_, v___x_730_, v___x_751_, v___f_738_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13___boxed(lean_object** _args){
lean_object* v___x_753_ = _args[0];
lean_object* v_activeConnections_754_ = _args[1];
lean_object* v___f_755_ = _args[2];
lean_object* v_a_756_ = _args[3];
lean_object* v___f_757_ = _args[4];
lean_object* v___f_758_ = _args[5];
lean_object* v_permitAcquired_759_ = _args[6];
lean_object* v___x_760_ = _args[7];
lean_object* v_connectionLimit_761_ = _args[8];
lean_object* v___x_762_ = _args[9];
lean_object* v___x_763_ = _args[10];
lean_object* v___x_764_ = _args[11];
lean_object* v_inst_765_ = _args[12];
lean_object* v_val_766_ = _args[13];
lean_object* v_handler_767_ = _args[14];
lean_object* v_config_768_ = _args[15];
lean_object* v_extensions_769_ = _args[16];
lean_object* v___f_770_ = _args[17];
lean_object* v___f_771_ = _args[18];
lean_object* v___y_772_ = _args[19];
_start:
{
uint8_t v_permitAcquired_boxed_773_; uint8_t v___x_13943__boxed_774_; lean_object* v_res_775_; 
v_permitAcquired_boxed_773_ = lean_unbox(v_permitAcquired_759_);
v___x_13943__boxed_774_ = lean_unbox(v___x_763_);
v_res_775_ = l_Std_Http_Server_serve___redArg___lam__13(v___x_753_, v_activeConnections_754_, v___f_755_, v_a_756_, v___f_757_, v___f_758_, v_permitAcquired_boxed_773_, v___x_760_, v_connectionLimit_761_, v___x_762_, v___x_13943__boxed_774_, v___x_764_, v_inst_765_, v_val_766_, v_handler_767_, v_config_768_, v_extensions_769_, v___f_770_, v___f_771_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14(lean_object* v___x_776_, lean_object* v_activeConnections_777_, lean_object* v___f_778_, lean_object* v___f_779_, lean_object* v___f_780_, uint8_t v_permitAcquired_781_, lean_object* v___x_782_, lean_object* v_connectionLimit_783_, lean_object* v___x_784_, uint8_t v___x_785_, lean_object* v___x_786_, lean_object* v_inst_787_, lean_object* v_val_788_, lean_object* v_handler_789_, lean_object* v_config_790_, lean_object* v_extensions_791_, lean_object* v___f_792_, lean_object* v_x_793_){
_start:
{
if (lean_obj_tag(v_x_793_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_803_; 
lean_dec_ref(v___f_792_);
lean_dec(v_extensions_791_);
lean_dec_ref(v_config_790_);
lean_dec(v_handler_789_);
lean_dec(v_val_788_);
lean_dec_ref(v_inst_787_);
lean_dec_ref(v___x_786_);
lean_dec(v___x_784_);
lean_dec(v_connectionLimit_783_);
lean_dec_ref(v___f_780_);
lean_dec_ref(v___f_779_);
lean_dec_ref(v___f_778_);
lean_dec_ref(v_activeConnections_777_);
lean_dec_ref(v___x_776_);
v_a_795_ = lean_ctor_get(v_x_793_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v_x_793_);
if (v_isSharedCheck_803_ == 0)
{
v___x_797_ = v_x_793_;
v_isShared_798_ = v_isSharedCheck_803_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v_x_793_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_803_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_802_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; 
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
return v___x_801_;
}
}
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_818_; 
v_a_804_ = lean_ctor_get(v_x_793_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v_x_793_);
if (v_isSharedCheck_818_ == 0)
{
v___x_806_ = v_x_793_;
v_isShared_807_ = v_isSharedCheck_818_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v_x_793_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_818_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___f_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___f_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_815_; 
lean_inc(v_a_804_);
v___f_808_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__8___boxed), 3, 1);
lean_closure_set(v___f_808_, 0, v_a_804_);
v___x_809_ = lean_box(v_permitAcquired_781_);
v___x_810_ = lean_box(v___x_785_);
lean_inc(v___x_784_);
v___f_811_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__13___boxed), 20, 19);
lean_closure_set(v___f_811_, 0, v___x_776_);
lean_closure_set(v___f_811_, 1, v_activeConnections_777_);
lean_closure_set(v___f_811_, 2, v___f_778_);
lean_closure_set(v___f_811_, 3, v_a_804_);
lean_closure_set(v___f_811_, 4, v___f_779_);
lean_closure_set(v___f_811_, 5, v___f_780_);
lean_closure_set(v___f_811_, 6, v___x_809_);
lean_closure_set(v___f_811_, 7, v___x_782_);
lean_closure_set(v___f_811_, 8, v_connectionLimit_783_);
lean_closure_set(v___f_811_, 9, v___x_784_);
lean_closure_set(v___f_811_, 10, v___x_810_);
lean_closure_set(v___f_811_, 11, v___x_786_);
lean_closure_set(v___f_811_, 12, v_inst_787_);
lean_closure_set(v___f_811_, 13, v_val_788_);
lean_closure_set(v___f_811_, 14, v_handler_789_);
lean_closure_set(v___f_811_, 15, v_config_790_);
lean_closure_set(v___f_811_, 16, v_extensions_791_);
lean_closure_set(v___f_811_, 17, v___f_792_);
lean_closure_set(v___f_811_, 18, v___f_808_);
v___x_812_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_812_, 0, lean_box(0));
lean_closure_set(v___x_812_, 1, v___f_811_);
v___x_813_ = lean_io_as_task(v___x_812_, v___x_784_);
lean_dec_ref(v___x_813_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v___x_782_);
v___x_815_ = v___x_806_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_782_);
v___x_815_ = v_reuseFailAlloc_817_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_816_; 
v___x_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
return v___x_816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14___boxed(lean_object** _args){
lean_object* v___x_819_ = _args[0];
lean_object* v_activeConnections_820_ = _args[1];
lean_object* v___f_821_ = _args[2];
lean_object* v___f_822_ = _args[3];
lean_object* v___f_823_ = _args[4];
lean_object* v_permitAcquired_824_ = _args[5];
lean_object* v___x_825_ = _args[6];
lean_object* v_connectionLimit_826_ = _args[7];
lean_object* v___x_827_ = _args[8];
lean_object* v___x_828_ = _args[9];
lean_object* v___x_829_ = _args[10];
lean_object* v_inst_830_ = _args[11];
lean_object* v_val_831_ = _args[12];
lean_object* v_handler_832_ = _args[13];
lean_object* v_config_833_ = _args[14];
lean_object* v_extensions_834_ = _args[15];
lean_object* v___f_835_ = _args[16];
lean_object* v_x_836_ = _args[17];
lean_object* v___y_837_ = _args[18];
_start:
{
uint8_t v_permitAcquired_boxed_838_; uint8_t v___x_14010__boxed_839_; lean_object* v_res_840_; 
v_permitAcquired_boxed_838_ = lean_unbox(v_permitAcquired_824_);
v___x_14010__boxed_839_ = lean_unbox(v___x_828_);
v_res_840_ = l_Std_Http_Server_serve___redArg___lam__14(v___x_819_, v_activeConnections_820_, v___f_821_, v___f_822_, v___f_823_, v_permitAcquired_boxed_838_, v___x_825_, v_connectionLimit_826_, v___x_827_, v___x_14010__boxed_839_, v___x_829_, v_inst_830_, v_val_831_, v_handler_832_, v_config_833_, v_extensions_834_, v___f_835_, v_x_836_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15(lean_object* v___x_841_, uint8_t v___x_842_, lean_object* v___f_843_, lean_object* v_x_844_){
_start:
{
if (lean_obj_tag(v_x_844_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_854_; 
lean_dec_ref(v___f_843_);
lean_dec(v___x_841_);
v_a_846_ = lean_ctor_get(v_x_844_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v_x_844_);
if (v_isSharedCheck_854_ == 0)
{
v___x_848_ = v_x_844_;
v_isShared_849_ = v_isSharedCheck_854_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v_x_844_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_854_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_846_);
v___x_851_ = v_reuseFailAlloc_853_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
lean_object* v___x_852_; 
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
return v___x_852_;
}
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_865_; 
v_a_855_ = lean_ctor_get(v_x_844_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v_x_844_);
if (v_isSharedCheck_865_ == 0)
{
v___x_857_ = v_x_844_;
v_isShared_858_ = v_isSharedCheck_865_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v_x_844_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_865_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_859_ = l_Std_CancellationContext_fork(v_a_855_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_859_);
v___x_861_ = v___x_857_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_859_);
v___x_861_ = v_reuseFailAlloc_864_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
v___x_863_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_841_, v___x_842_, v___x_862_, v___f_843_);
return v___x_863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15___boxed(lean_object* v___x_866_, lean_object* v___x_867_, lean_object* v___f_868_, lean_object* v_x_869_, lean_object* v___y_870_){
_start:
{
uint8_t v___x_14092__boxed_871_; lean_object* v_res_872_; 
v___x_14092__boxed_871_ = lean_unbox(v___x_867_);
v_res_872_ = l_Std_Http_Server_serve___redArg___lam__15(v___x_866_, v___x_14092__boxed_871_, v___f_868_, v_x_869_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16(lean_object* v___x_873_, lean_object* v_activeConnections_874_, lean_object* v___f_875_, lean_object* v___f_876_, lean_object* v___f_877_, uint8_t v_permitAcquired_878_, lean_object* v___x_879_, lean_object* v_connectionLimit_880_, uint8_t v___x_881_, lean_object* v_inst_882_, lean_object* v_val_883_, lean_object* v_handler_884_, lean_object* v_config_885_, lean_object* v___f_886_, lean_object* v___f_887_, lean_object* v_extensions_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___f_895_; lean_object* v___x_896_; lean_object* v___f_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_891_ = l_Std_Http_instTransportClient;
v___x_892_ = lean_unsigned_to_nat(0u);
v___x_893_ = lean_box(v_permitAcquired_878_);
v___x_894_ = lean_box(v___x_881_);
v___f_895_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__14___boxed), 19, 17);
lean_closure_set(v___f_895_, 0, v___x_873_);
lean_closure_set(v___f_895_, 1, v_activeConnections_874_);
lean_closure_set(v___f_895_, 2, v___f_875_);
lean_closure_set(v___f_895_, 3, v___f_876_);
lean_closure_set(v___f_895_, 4, v___f_877_);
lean_closure_set(v___f_895_, 5, v___x_893_);
lean_closure_set(v___f_895_, 6, v___x_879_);
lean_closure_set(v___f_895_, 7, v_connectionLimit_880_);
lean_closure_set(v___f_895_, 8, v___x_892_);
lean_closure_set(v___f_895_, 9, v___x_894_);
lean_closure_set(v___f_895_, 10, v___x_891_);
lean_closure_set(v___f_895_, 11, v_inst_882_);
lean_closure_set(v___f_895_, 12, v_val_883_);
lean_closure_set(v___f_895_, 13, v_handler_884_);
lean_closure_set(v___f_895_, 14, v_config_885_);
lean_closure_set(v___f_895_, 15, v_extensions_888_);
lean_closure_set(v___f_895_, 16, v___f_886_);
v___x_896_ = lean_box(v___x_881_);
v___f_897_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__15___boxed), 5, 3);
lean_closure_set(v___f_897_, 0, v___x_892_);
lean_closure_set(v___f_897_, 1, v___x_896_);
lean_closure_set(v___f_897_, 2, v___f_895_);
lean_inc_ref(v___y_889_);
v___x_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_898_, 0, v___y_889_);
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
v___x_900_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_892_, v___x_881_, v___x_899_, v___f_897_);
v___x_901_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_892_, v___x_881_, v___x_900_, v___f_887_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16___boxed(lean_object** _args){
lean_object* v___x_902_ = _args[0];
lean_object* v_activeConnections_903_ = _args[1];
lean_object* v___f_904_ = _args[2];
lean_object* v___f_905_ = _args[3];
lean_object* v___f_906_ = _args[4];
lean_object* v_permitAcquired_907_ = _args[5];
lean_object* v___x_908_ = _args[6];
lean_object* v_connectionLimit_909_ = _args[7];
lean_object* v___x_910_ = _args[8];
lean_object* v_inst_911_ = _args[9];
lean_object* v_val_912_ = _args[10];
lean_object* v_handler_913_ = _args[11];
lean_object* v_config_914_ = _args[12];
lean_object* v___f_915_ = _args[13];
lean_object* v___f_916_ = _args[14];
lean_object* v_extensions_917_ = _args[15];
lean_object* v___y_918_ = _args[16];
lean_object* v___y_919_ = _args[17];
_start:
{
uint8_t v_permitAcquired_boxed_920_; uint8_t v___x_14151__boxed_921_; lean_object* v_res_922_; 
v_permitAcquired_boxed_920_ = lean_unbox(v_permitAcquired_907_);
v___x_14151__boxed_921_ = lean_unbox(v___x_910_);
v_res_922_ = l_Std_Http_Server_serve___redArg___lam__16(v___x_902_, v_activeConnections_903_, v___f_904_, v___f_905_, v___f_906_, v_permitAcquired_boxed_920_, v___x_908_, v_connectionLimit_909_, v___x_14151__boxed_921_, v_inst_911_, v_val_912_, v_handler_913_, v_config_914_, v___f_915_, v___f_916_, v_extensions_917_, v___y_918_);
lean_dec_ref(v___y_918_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17(lean_object* v___f_923_, lean_object* v___y_924_, lean_object* v_x_925_){
_start:
{
if (lean_obj_tag(v_x_925_) == 0)
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_935_; 
lean_dec_ref(v___f_923_);
v_a_927_ = lean_ctor_get(v_x_925_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v_x_925_);
if (v_isSharedCheck_935_ == 0)
{
v___x_929_ = v_x_925_;
v_isShared_930_ = v_isSharedCheck_935_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v_x_925_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_935_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_934_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v___x_933_; 
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
return v___x_933_;
}
}
}
else
{
lean_object* v_a_936_; lean_object* v___x_937_; 
v_a_936_ = lean_ctor_get(v_x_925_, 0);
lean_inc(v_a_936_);
lean_dec_ref_known(v_x_925_, 1);
lean_inc_ref(v___y_924_);
v___x_937_ = lean_apply_3(v___f_923_, v_a_936_, v___y_924_, lean_box(0));
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17___boxed(lean_object* v___f_938_, lean_object* v___y_939_, lean_object* v_x_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Std_Http_Server_serve___redArg___lam__17(v___f_938_, v___y_939_, v_x_940_);
lean_dec_ref(v___y_939_);
return v_res_942_;
}
}
static lean_object* _init_l_Std_Http_Server_serve___redArg___lam__19___closed__0(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = l_Std_Http_Extensions_empty;
v___x_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
return v___x_944_;
}
}
static lean_object* _init_l_Std_Http_Server_serve___redArg___lam__19___closed__1(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = lean_obj_once(&l_Std_Http_Server_serve___redArg___lam__19___closed__0, &l_Std_Http_Server_serve___redArg___lam__19___closed__0_once, _init_l_Std_Http_Server_serve___redArg___lam__19___closed__0);
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__19(uint8_t v___x_948_, lean_object* v___f_949_, lean_object* v___f_950_, lean_object* v_x_951_){
_start:
{
if (lean_obj_tag(v_x_951_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_961_; 
lean_dec_ref(v___f_950_);
lean_dec_ref(v___f_949_);
v_a_953_ = lean_ctor_get(v_x_951_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v_x_951_);
if (v_isSharedCheck_961_ == 0)
{
v___x_955_ = v_x_951_;
v_isShared_956_ = v_isSharedCheck_961_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v_x_951_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_961_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_960_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
lean_object* v___x_959_; 
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
}
}
else
{
lean_object* v_a_962_; 
v_a_962_ = lean_ctor_get(v_x_951_, 0);
lean_inc(v_a_962_);
lean_dec_ref_known(v_x_951_, 1);
if (lean_obj_tag(v_a_962_) == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
lean_dec_ref_known(v_a_962_, 1);
lean_dec_ref(v___f_950_);
v___x_963_ = lean_obj_once(&l_Std_Http_Server_serve___redArg___lam__19___closed__1, &l_Std_Http_Server_serve___redArg___lam__19___closed__1_once, _init_l_Std_Http_Server_serve___redArg___lam__19___closed__1);
v___x_964_ = lean_unsigned_to_nat(0u);
v___x_965_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_964_, v___x_948_, v___x_963_, v___f_949_);
return v___x_965_;
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_982_; 
lean_dec_ref(v___f_949_);
v_a_966_ = lean_ctor_get(v_a_962_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v_a_962_);
if (v_isSharedCheck_982_ == 0)
{
v___x_968_ = v_a_962_;
v_isShared_969_ = v_isSharedCheck_982_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v_a_962_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_982_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v_dyn_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_970_ = l_Std_Http_Extensions_empty;
v___x_971_ = l_Std_Http_Server_instImpl_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8_;
v_dyn_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_972_, 0, v___x_971_);
lean_ctor_set(v_dyn_972_, 1, v_a_966_);
v___x_973_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__19___closed__2));
v___x_974_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_972_);
v___x_975_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_973_, v___x_974_, v_dyn_972_, v___x_970_);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 0, v___x_975_);
v___x_977_ = v___x_968_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_975_);
v___x_977_ = v_reuseFailAlloc_981_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
v___x_979_ = lean_unsigned_to_nat(0u);
v___x_980_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_979_, v___x_948_, v___x_978_, v___f_950_);
return v___x_980_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__19___boxed(lean_object* v___x_983_, lean_object* v___f_984_, lean_object* v___f_985_, lean_object* v_x_986_, lean_object* v___y_987_){
_start:
{
uint8_t v___x_14248__boxed_988_; lean_object* v_res_989_; 
v___x_14248__boxed_988_ = lean_unbox(v___x_983_);
v_res_989_ = l_Std_Http_Server_serve___redArg___lam__19(v___x_14248__boxed_988_, v___f_984_, v___f_985_, v_x_986_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18(uint8_t v_permitAcquired_990_, lean_object* v___f_991_, lean_object* v___x_992_, lean_object* v___y_993_, lean_object* v_connectionLimit_994_, uint8_t v___x_995_, lean_object* v___f_996_, lean_object* v___x_997_, lean_object* v_activeConnections_998_, lean_object* v___f_999_, lean_object* v___f_1000_, lean_object* v___f_1001_, lean_object* v_inst_1002_, lean_object* v_handler_1003_, lean_object* v_config_1004_, lean_object* v___f_1005_, lean_object* v___f_1006_, lean_object* v_x_1007_){
_start:
{
if (lean_obj_tag(v_x_1007_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1017_; 
lean_dec_ref(v___f_1006_);
lean_dec_ref(v___f_1005_);
lean_dec_ref(v_config_1004_);
lean_dec(v_handler_1003_);
lean_dec_ref(v_inst_1002_);
lean_dec_ref(v___f_1001_);
lean_dec_ref(v___f_1000_);
lean_dec_ref(v___f_999_);
lean_dec_ref(v_activeConnections_998_);
lean_dec_ref(v___x_997_);
lean_dec_ref(v___f_996_);
lean_dec(v_connectionLimit_994_);
lean_dec_ref(v___f_991_);
v_a_1009_ = lean_ctor_get(v_x_1007_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_x_1007_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1011_ = v_x_1007_;
v_isShared_1012_ = v_isSharedCheck_1017_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v_x_1007_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1017_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
return v___x_1015_;
}
}
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1076_; 
v_a_1018_ = lean_ctor_get(v_x_1007_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_x_1007_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1020_ = v_x_1007_;
v_isShared_1021_ = v_isSharedCheck_1076_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v_x_1007_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1076_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
if (lean_obj_tag(v_a_1018_) == 0)
{
lean_dec_ref(v___f_1006_);
lean_dec_ref(v___f_1005_);
lean_dec_ref(v_config_1004_);
lean_dec(v_handler_1003_);
lean_dec_ref(v_inst_1002_);
lean_dec_ref(v___f_1001_);
lean_dec_ref(v___f_1000_);
lean_dec_ref(v___f_999_);
lean_dec_ref(v_activeConnections_998_);
lean_dec_ref(v___x_997_);
if (v_permitAcquired_990_ == 0)
{
lean_object* v___x_1022_; 
lean_del_object(v___x_1020_);
lean_dec_ref(v___f_996_);
lean_dec(v_connectionLimit_994_);
lean_inc_ref(v___y_993_);
v___x_1022_ = lean_apply_3(v___f_991_, v___x_992_, v___y_993_, lean_box(0));
return v___x_1022_;
}
else
{
if (lean_obj_tag(v_connectionLimit_994_) == 1)
{
lean_object* v_val_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1036_; 
lean_dec_ref(v___f_991_);
v_val_1023_ = lean_ctor_get(v_connectionLimit_994_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v_connectionLimit_994_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1025_ = v_connectionLimit_994_;
v_isShared_1026_ = v_isSharedCheck_1036_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_val_1023_);
lean_dec(v_connectionLimit_994_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1036_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1027_ = l_Std_Semaphore_release(v_val_1023_);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 0, v___x_1027_);
v___x_1029_ = v___x_1020_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1027_);
v___x_1029_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
lean_object* v___x_1031_; 
if (v_isShared_1026_ == 0)
{
lean_ctor_set_tag(v___x_1025_, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1029_);
v___x_1031_ = v___x_1025_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_unsigned_to_nat(0u);
v___x_1033_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1032_, v___x_995_, v___x_1031_, v___f_996_);
return v___x_1033_;
}
}
}
}
else
{
lean_object* v___x_1037_; 
lean_del_object(v___x_1020_);
lean_dec_ref(v___f_996_);
lean_dec(v_connectionLimit_994_);
lean_inc_ref(v___y_993_);
v___x_1037_ = lean_apply_3(v___f_991_, v___x_992_, v___y_993_, lean_box(0));
return v___x_1037_;
}
}
}
else
{
lean_object* v_val_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1075_; 
lean_dec_ref(v___f_996_);
lean_dec_ref(v___f_991_);
v_val_1038_ = lean_ctor_get(v_a_1018_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_a_1018_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1040_ = v_a_1018_;
v_isShared_1041_ = v_isSharedCheck_1075_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_val_1038_);
lean_dec(v_a_1018_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1075_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___f_1044_; lean_object* v___f_1045_; lean_object* v___x_1046_; lean_object* v___f_1047_; lean_object* v_val_1049_; lean_object* v___x_1058_; 
v___x_1042_ = lean_box(v_permitAcquired_990_);
v___x_1043_ = lean_box(v___x_995_);
lean_inc(v_val_1038_);
v___f_1044_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__16___boxed), 18, 15);
lean_closure_set(v___f_1044_, 0, v___x_997_);
lean_closure_set(v___f_1044_, 1, v_activeConnections_998_);
lean_closure_set(v___f_1044_, 2, v___f_999_);
lean_closure_set(v___f_1044_, 3, v___f_1000_);
lean_closure_set(v___f_1044_, 4, v___f_1001_);
lean_closure_set(v___f_1044_, 5, v___x_1042_);
lean_closure_set(v___f_1044_, 6, v___x_992_);
lean_closure_set(v___f_1044_, 7, v_connectionLimit_994_);
lean_closure_set(v___f_1044_, 8, v___x_1043_);
lean_closure_set(v___f_1044_, 9, v_inst_1002_);
lean_closure_set(v___f_1044_, 10, v_val_1038_);
lean_closure_set(v___f_1044_, 11, v_handler_1003_);
lean_closure_set(v___f_1044_, 12, v_config_1004_);
lean_closure_set(v___f_1044_, 13, v___f_1005_);
lean_closure_set(v___f_1044_, 14, v___f_1006_);
lean_inc_ref(v___y_993_);
v___f_1045_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__17___boxed), 4, 2);
lean_closure_set(v___f_1045_, 0, v___f_1044_);
lean_closure_set(v___f_1045_, 1, v___y_993_);
v___x_1046_ = lean_box(v___x_995_);
lean_inc_ref(v___f_1045_);
v___f_1047_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__19___boxed), 5, 3);
lean_closure_set(v___f_1047_, 0, v___x_1046_);
lean_closure_set(v___f_1047_, 1, v___f_1045_);
lean_closure_set(v___f_1047_, 2, v___f_1045_);
v___x_1058_ = lean_uv_tcp_getpeername(v_val_1038_);
lean_dec(v_val_1038_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1058_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
lean_ctor_set_tag(v___x_1061_, 1);
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
v_val_1049_ = v___x_1064_;
goto v___jp_1048_;
}
}
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
v_a_1067_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_1058_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1058_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
lean_ctor_set_tag(v___x_1069_, 0);
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
v_val_1049_ = v___x_1072_;
goto v___jp_1048_;
}
}
}
v___jp_1048_:
{
lean_object* v___x_1051_; 
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 0, v_val_1049_);
v___x_1051_ = v___x_1020_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_val_1049_);
v___x_1051_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1053_; 
if (v_isShared_1041_ == 0)
{
lean_ctor_set_tag(v___x_1040_, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1051_);
v___x_1053_ = v___x_1040_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1051_);
v___x_1053_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = lean_unsigned_to_nat(0u);
v___x_1055_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1054_, v___x_995_, v___x_1053_, v___f_1047_);
return v___x_1055_;
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
lean_object* v_permitAcquired_1077_ = _args[0];
lean_object* v___f_1078_ = _args[1];
lean_object* v___x_1079_ = _args[2];
lean_object* v___y_1080_ = _args[3];
lean_object* v_connectionLimit_1081_ = _args[4];
lean_object* v___x_1082_ = _args[5];
lean_object* v___f_1083_ = _args[6];
lean_object* v___x_1084_ = _args[7];
lean_object* v_activeConnections_1085_ = _args[8];
lean_object* v___f_1086_ = _args[9];
lean_object* v___f_1087_ = _args[10];
lean_object* v___f_1088_ = _args[11];
lean_object* v_inst_1089_ = _args[12];
lean_object* v_handler_1090_ = _args[13];
lean_object* v_config_1091_ = _args[14];
lean_object* v___f_1092_ = _args[15];
lean_object* v___f_1093_ = _args[16];
lean_object* v_x_1094_ = _args[17];
lean_object* v___y_1095_ = _args[18];
_start:
{
uint8_t v_permitAcquired_boxed_1096_; uint8_t v___x_14330__boxed_1097_; lean_object* v_res_1098_; 
v_permitAcquired_boxed_1096_ = lean_unbox(v_permitAcquired_1077_);
v___x_14330__boxed_1097_ = lean_unbox(v___x_1082_);
v_res_1098_ = l_Std_Http_Server_serve___redArg___lam__18(v_permitAcquired_boxed_1096_, v___f_1078_, v___x_1079_, v___y_1080_, v_connectionLimit_1081_, v___x_14330__boxed_1097_, v___f_1083_, v___x_1084_, v_activeConnections_1085_, v___f_1086_, v___f_1087_, v___f_1088_, v_inst_1089_, v_handler_1090_, v_config_1091_, v___f_1092_, v___f_1093_, v_x_1094_);
lean_dec_ref(v___y_1080_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20(lean_object* v_a_1099_, lean_object* v___f_1100_, lean_object* v___f_1101_, uint8_t v___x_1102_, lean_object* v___f_1103_, lean_object* v_x_1104_){
_start:
{
if (lean_obj_tag(v_x_1104_) == 0)
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1114_; 
lean_dec_ref(v___f_1103_);
lean_dec_ref(v___f_1101_);
lean_dec_ref(v___f_1100_);
lean_dec(v_a_1099_);
v_a_1106_ = lean_ctor_get(v_x_1104_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_x_1104_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1108_ = v_x_1104_;
v_isShared_1109_ = v_isSharedCheck_1114_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v_x_1104_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1114_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_object* v___x_1112_; 
v___x_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
return v___x_1112_;
}
}
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v_a_1115_ = lean_ctor_get(v_x_1104_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v_x_1104_, 1);
v___x_1116_ = l_Std_Async_TCP_Socket_Server_acceptSelector(v_a_1099_);
v___x_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
lean_ctor_set(v___x_1117_, 1, v___f_1100_);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v_a_1115_);
lean_ctor_set(v___x_1118_, 1, v___f_1101_);
v___x_1119_ = lean_unsigned_to_nat(2u);
v___x_1120_ = lean_mk_empty_array_with_capacity(v___x_1119_);
v___x_1121_ = lean_array_push(v___x_1120_, v___x_1117_);
v___x_1122_ = lean_array_push(v___x_1121_, v___x_1118_);
v___x_1123_ = l_Std_Async_Selectable_one___redArg(v___x_1122_);
v___x_1124_ = lean_unsigned_to_nat(0u);
v___x_1125_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1124_, v___x_1102_, v___x_1123_, v___f_1103_);
return v___x_1125_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20___boxed(lean_object* v_a_1126_, lean_object* v___f_1127_, lean_object* v___f_1128_, lean_object* v___x_1129_, lean_object* v___f_1130_, lean_object* v_x_1131_, lean_object* v___y_1132_){
_start:
{
uint8_t v___x_14508__boxed_1133_; lean_object* v_res_1134_; 
v___x_14508__boxed_1133_ = lean_unbox(v___x_1129_);
v_res_1134_ = l_Std_Http_Server_serve___redArg___lam__20(v_a_1126_, v___f_1127_, v___f_1128_, v___x_14508__boxed_1133_, v___f_1130_, v_x_1131_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21(uint8_t v___x_1135_, lean_object* v___f_1136_, lean_object* v___f_1137_, lean_object* v___x_1138_, lean_object* v_connectionLimit_1139_, lean_object* v___x_1140_, lean_object* v_activeConnections_1141_, lean_object* v___f_1142_, lean_object* v___f_1143_, lean_object* v___f_1144_, lean_object* v_inst_1145_, lean_object* v_handler_1146_, lean_object* v_config_1147_, lean_object* v___f_1148_, lean_object* v___f_1149_, lean_object* v_a_1150_, lean_object* v___f_1151_, lean_object* v___f_1152_, uint8_t v_permitAcquired_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___f_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___f_1163_; lean_object* v___x_1164_; lean_object* v___f_1165_; lean_object* v___x_1166_; 
lean_inc_ref_n(v___y_1154_, 3);
v___x_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___y_1154_);
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
v___x_1158_ = lean_unsigned_to_nat(0u);
v___x_1159_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1158_, v___x_1135_, v___x_1157_, v___f_1136_);
lean_inc_ref(v___f_1137_);
v___f_1160_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_1160_, 0, v___f_1137_);
lean_closure_set(v___f_1160_, 1, v___y_1154_);
v___x_1161_ = lean_box(v_permitAcquired_1153_);
v___x_1162_ = lean_box(v___x_1135_);
v___f_1163_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__18___boxed), 19, 17);
lean_closure_set(v___f_1163_, 0, v___x_1161_);
lean_closure_set(v___f_1163_, 1, v___f_1137_);
lean_closure_set(v___f_1163_, 2, v___x_1138_);
lean_closure_set(v___f_1163_, 3, v___y_1154_);
lean_closure_set(v___f_1163_, 4, v_connectionLimit_1139_);
lean_closure_set(v___f_1163_, 5, v___x_1162_);
lean_closure_set(v___f_1163_, 6, v___f_1160_);
lean_closure_set(v___f_1163_, 7, v___x_1140_);
lean_closure_set(v___f_1163_, 8, v_activeConnections_1141_);
lean_closure_set(v___f_1163_, 9, v___f_1142_);
lean_closure_set(v___f_1163_, 10, v___f_1143_);
lean_closure_set(v___f_1163_, 11, v___f_1144_);
lean_closure_set(v___f_1163_, 12, v_inst_1145_);
lean_closure_set(v___f_1163_, 13, v_handler_1146_);
lean_closure_set(v___f_1163_, 14, v_config_1147_);
lean_closure_set(v___f_1163_, 15, v___f_1148_);
lean_closure_set(v___f_1163_, 16, v___f_1149_);
v___x_1164_ = lean_box(v___x_1135_);
v___f_1165_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__20___boxed), 7, 5);
lean_closure_set(v___f_1165_, 0, v_a_1150_);
lean_closure_set(v___f_1165_, 1, v___f_1151_);
lean_closure_set(v___f_1165_, 2, v___f_1152_);
lean_closure_set(v___f_1165_, 3, v___x_1164_);
lean_closure_set(v___f_1165_, 4, v___f_1163_);
v___x_1166_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1158_, v___x_1135_, v___x_1159_, v___f_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21___boxed(lean_object** _args){
lean_object* v___x_1167_ = _args[0];
lean_object* v___f_1168_ = _args[1];
lean_object* v___f_1169_ = _args[2];
lean_object* v___x_1170_ = _args[3];
lean_object* v_connectionLimit_1171_ = _args[4];
lean_object* v___x_1172_ = _args[5];
lean_object* v_activeConnections_1173_ = _args[6];
lean_object* v___f_1174_ = _args[7];
lean_object* v___f_1175_ = _args[8];
lean_object* v___f_1176_ = _args[9];
lean_object* v_inst_1177_ = _args[10];
lean_object* v_handler_1178_ = _args[11];
lean_object* v_config_1179_ = _args[12];
lean_object* v___f_1180_ = _args[13];
lean_object* v___f_1181_ = _args[14];
lean_object* v_a_1182_ = _args[15];
lean_object* v___f_1183_ = _args[16];
lean_object* v___f_1184_ = _args[17];
lean_object* v_permitAcquired_1185_ = _args[18];
lean_object* v___y_1186_ = _args[19];
lean_object* v___y_1187_ = _args[20];
_start:
{
uint8_t v___x_14566__boxed_1188_; uint8_t v_permitAcquired_boxed_1189_; lean_object* v_res_1190_; 
v___x_14566__boxed_1188_ = lean_unbox(v___x_1167_);
v_permitAcquired_boxed_1189_ = lean_unbox(v_permitAcquired_1185_);
v_res_1190_ = l_Std_Http_Server_serve___redArg___lam__21(v___x_14566__boxed_1188_, v___f_1168_, v___f_1169_, v___x_1170_, v_connectionLimit_1171_, v___x_1172_, v_activeConnections_1173_, v___f_1174_, v___f_1175_, v___f_1176_, v_inst_1177_, v_handler_1178_, v_config_1179_, v___f_1180_, v___f_1181_, v_a_1182_, v___f_1183_, v___f_1184_, v_permitAcquired_boxed_1189_, v___y_1186_);
lean_dec_ref(v___y_1186_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22(lean_object* v___f_1191_, lean_object* v___y_1192_, lean_object* v_x_1193_){
_start:
{
if (lean_obj_tag(v_x_1193_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1203_; 
lean_dec_ref(v___f_1191_);
v_a_1195_ = lean_ctor_get(v_x_1193_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_x_1193_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1197_ = v_x_1193_;
v_isShared_1198_ = v_isSharedCheck_1203_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v_x_1193_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1203_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1201_; 
v___x_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
return v___x_1201_;
}
}
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1205_; 
v_a_1204_ = lean_ctor_get(v_x_1193_, 0);
lean_inc(v_a_1204_);
lean_dec_ref_known(v_x_1193_, 1);
lean_inc_ref(v___y_1192_);
v___x_1205_ = lean_apply_3(v___f_1191_, v_a_1204_, v___y_1192_, lean_box(0));
return v___x_1205_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22___boxed(lean_object* v___f_1206_, lean_object* v___y_1207_, lean_object* v_x_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Std_Http_Server_serve___redArg___lam__22(v___f_1206_, v___y_1207_, v_x_1208_);
lean_dec_ref(v___y_1207_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23(uint8_t v___x_1211_, uint8_t v___x_1212_, lean_object* v___f_1213_, lean_object* v_x_1214_){
_start:
{
if (lean_obj_tag(v_x_1214_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1224_; 
lean_dec_ref(v___f_1213_);
v_a_1216_ = lean_ctor_get(v_x_1214_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_x_1214_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1218_ = v_x_1214_;
v_isShared_1219_ = v_isSharedCheck_1224_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v_x_1214_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1224_;
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
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1222_; 
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
return v___x_1222_;
}
}
}
else
{
lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1235_; 
v_isSharedCheck_1235_ = !lean_is_exclusive(v_x_1214_);
if (v_isSharedCheck_1235_ == 0)
{
lean_object* v_unused_1236_; 
v_unused_1236_ = lean_ctor_get(v_x_1214_, 0);
lean_dec(v_unused_1236_);
v___x_1226_ = v_x_1214_;
v_isShared_1227_ = v_isSharedCheck_1235_;
goto v_resetjp_1225_;
}
else
{
lean_dec(v_x_1214_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1235_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1228_; lean_object* v___x_1230_; 
v___x_1228_ = lean_box(v___x_1211_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 0, v___x_1228_);
v___x_1230_ = v___x_1226_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1228_);
v___x_1230_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
v___x_1232_ = lean_unsigned_to_nat(0u);
v___x_1233_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1232_, v___x_1212_, v___x_1231_, v___f_1213_);
return v___x_1233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23___boxed(lean_object* v___x_1237_, lean_object* v___x_1238_, lean_object* v___f_1239_, lean_object* v_x_1240_, lean_object* v___y_1241_){
_start:
{
uint8_t v___x_14670__boxed_1242_; uint8_t v___x_14671__boxed_1243_; lean_object* v_res_1244_; 
v___x_14670__boxed_1242_ = lean_unbox(v___x_1237_);
v___x_14671__boxed_1243_ = lean_unbox(v___x_1238_);
v_res_1244_ = l_Std_Http_Server_serve___redArg___lam__23(v___x_14670__boxed_1242_, v___x_14671__boxed_1243_, v___f_1239_, v_x_1240_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24(lean_object* v___f_1245_, uint8_t v___x_1246_, lean_object* v___f_1247_, lean_object* v_x_1248_){
_start:
{
if (lean_obj_tag(v_x_1248_) == 0)
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1258_; 
lean_dec_ref(v___f_1247_);
lean_dec_ref(v___f_1245_);
v_a_1250_ = lean_ctor_get(v_x_1248_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_x_1248_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1252_ = v_x_1248_;
v_isShared_1253_ = v_isSharedCheck_1258_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v_x_1248_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1258_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1256_; 
v___x_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
return v___x_1256_;
}
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v_a_1259_ = lean_ctor_get(v_x_1248_, 0);
lean_inc(v_a_1259_);
lean_dec_ref_known(v_x_1248_, 1);
v___x_1260_ = l_IO_Promise_result_x21___redArg(v_a_1259_);
lean_dec(v_a_1259_);
v___x_1261_ = lean_unsigned_to_nat(0u);
v___x_1262_ = lean_task_map(v___f_1245_, v___x_1260_, v___x_1261_, v___x_1246_);
v___x_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
v___x_1264_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1261_, v___x_1246_, v___x_1263_, v___f_1247_);
return v___x_1264_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24___boxed(lean_object* v___f_1265_, lean_object* v___x_1266_, lean_object* v___f_1267_, lean_object* v_x_1268_, lean_object* v___y_1269_){
_start:
{
uint8_t v___x_14729__boxed_1270_; lean_object* v_res_1271_; 
v___x_14729__boxed_1270_ = lean_unbox(v___x_1266_);
v_res_1271_ = l_Std_Http_Server_serve___redArg___lam__24(v___f_1265_, v___x_14729__boxed_1270_, v___f_1267_, v_x_1268_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26(uint8_t v___x_1272_, lean_object* v___f_1273_, lean_object* v_connectionLimit_1274_, lean_object* v___f_1275_, lean_object* v___f_1276_, lean_object* v_b_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v___y_1281_; 
if (lean_obj_tag(v_connectionLimit_1274_) == 1)
{
lean_object* v_val_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1302_; 
v_val_1284_ = lean_ctor_get(v_connectionLimit_1274_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v_connectionLimit_1274_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1286_ = v_connectionLimit_1274_;
v_isShared_1287_ = v_isSharedCheck_1302_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_val_1284_);
lean_dec(v_connectionLimit_1274_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1302_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1288_; lean_object* v___f_1289_; uint8_t v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___f_1293_; lean_object* v___x_1294_; lean_object* v___f_1295_; lean_object* v___x_1297_; 
v___x_1288_ = l_Std_Semaphore_acquire(v_val_1284_);
lean_inc_ref(v___y_1278_);
v___f_1289_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__22___boxed), 4, 2);
lean_closure_set(v___f_1289_, 0, v___f_1275_);
lean_closure_set(v___f_1289_, 1, v___y_1278_);
v___x_1290_ = 1;
v___x_1291_ = lean_box(v___x_1290_);
v___x_1292_ = lean_box(v___x_1272_);
v___f_1293_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__23___boxed), 5, 3);
lean_closure_set(v___f_1293_, 0, v___x_1291_);
lean_closure_set(v___f_1293_, 1, v___x_1292_);
lean_closure_set(v___f_1293_, 2, v___f_1289_);
v___x_1294_ = lean_box(v___x_1272_);
v___f_1295_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__24___boxed), 5, 3);
lean_closure_set(v___f_1295_, 0, v___f_1276_);
lean_closure_set(v___f_1295_, 1, v___x_1294_);
lean_closure_set(v___f_1295_, 2, v___f_1293_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 0, v___x_1288_);
v___x_1297_ = v___x_1286_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1288_);
v___x_1297_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
v___x_1299_ = lean_unsigned_to_nat(0u);
v___x_1300_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1299_, v___x_1272_, v___x_1298_, v___f_1295_);
v___y_1281_ = v___x_1300_;
goto v___jp_1280_;
}
}
}
else
{
lean_object* v___f_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
lean_dec_ref(v___f_1276_);
lean_dec(v_connectionLimit_1274_);
lean_inc_ref(v___y_1278_);
v___f_1303_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__22___boxed), 4, 2);
lean_closure_set(v___f_1303_, 0, v___f_1275_);
lean_closure_set(v___f_1303_, 1, v___y_1278_);
v___x_1304_ = lean_box(v___x_1272_);
v___x_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
v___x_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
v___x_1307_ = lean_unsigned_to_nat(0u);
v___x_1308_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1307_, v___x_1272_, v___x_1306_, v___f_1303_);
v___y_1281_ = v___x_1308_;
goto v___jp_1280_;
}
v___jp_1280_:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = lean_unsigned_to_nat(0u);
v___x_1283_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1282_, v___x_1272_, v___y_1281_, v___f_1273_);
return v___x_1283_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26___boxed(lean_object* v___x_1309_, lean_object* v___f_1310_, lean_object* v_connectionLimit_1311_, lean_object* v___f_1312_, lean_object* v___f_1313_, lean_object* v_b_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
uint8_t v___x_14773__boxed_1317_; lean_object* v_res_1318_; 
v___x_14773__boxed_1317_ = lean_unbox(v___x_1309_);
v_res_1318_ = l_Std_Http_Server_serve___redArg___lam__26(v___x_14773__boxed_1317_, v___f_1310_, v_connectionLimit_1311_, v___f_1312_, v___f_1313_, v_b_1314_, v___y_1315_);
lean_dec_ref(v___y_1315_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25(lean_object* v___x_1319_, lean_object* v___f_1320_, lean_object* v___x_1321_, uint8_t v___x_1322_, lean_object* v___f_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v___x_13260__overap_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_13260__overap_1326_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_1319_, v___f_1320_, v___x_1321_);
v___x_1327_ = lean_apply_2(v___x_13260__overap_1326_, v___y_1324_, lean_box(0));
v___x_1328_ = lean_unsigned_to_nat(0u);
v___x_1329_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1328_, v___x_1322_, v___x_1327_, v___f_1323_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25___boxed(lean_object* v___x_1330_, lean_object* v___f_1331_, lean_object* v___x_1332_, lean_object* v___x_1333_, lean_object* v___f_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
uint8_t v___x_14852__boxed_1337_; lean_object* v_res_1338_; 
v___x_14852__boxed_1337_ = lean_unbox(v___x_1333_);
v_res_1338_ = l_Std_Http_Server_serve___redArg___lam__25(v___x_1330_, v___f_1331_, v___x_1332_, v___x_14852__boxed_1337_, v___f_1334_, v___y_1335_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27(lean_object* v_x_1339_, lean_object* v_x_1340_){
_start:
{
if (lean_obj_tag(v_x_1340_) == 0)
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1350_; 
lean_dec_ref(v_x_1339_);
v_a_1342_ = lean_ctor_get(v_x_1340_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_x_1340_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1344_ = v_x_1340_;
v_isShared_1345_ = v_isSharedCheck_1350_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v_x_1340_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1350_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
lean_object* v___x_1348_; 
v___x_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
return v___x_1348_;
}
}
}
else
{
lean_object* v___x_1351_; 
lean_dec_ref_known(v_x_1340_, 1);
v___x_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1351_, 0, v_x_1339_);
return v___x_1351_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27___boxed(lean_object* v_x_1352_, lean_object* v_x_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Std_Http_Server_serve___redArg___lam__27(v_x_1352_, v_x_1353_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28(lean_object* v___f_1360_, lean_object* v___x_1361_, lean_object* v___f_1362_, lean_object* v___f_1363_, lean_object* v_inst_1364_, lean_object* v_handler_1365_, lean_object* v_config_1366_, lean_object* v___f_1367_, lean_object* v_a_1368_, lean_object* v___f_1369_, lean_object* v___f_1370_, lean_object* v___f_1371_, lean_object* v___f_1372_, lean_object* v___f_1373_, lean_object* v_x_1374_){
_start:
{
if (lean_obj_tag(v_x_1374_) == 0)
{
lean_object* v___x_1376_; 
lean_dec_ref(v___f_1373_);
lean_dec_ref(v___f_1372_);
lean_dec_ref(v___f_1371_);
lean_dec_ref(v___f_1370_);
lean_dec_ref(v___f_1369_);
lean_dec(v_a_1368_);
lean_dec_ref(v___f_1367_);
lean_dec_ref(v_config_1366_);
lean_dec(v_handler_1365_);
lean_dec_ref(v_inst_1364_);
lean_dec_ref(v___f_1363_);
lean_dec_ref(v___f_1362_);
lean_dec_ref(v___x_1361_);
lean_dec_ref(v___f_1360_);
v___x_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1376_, 0, v_x_1374_);
return v___x_1376_;
}
else
{
lean_object* v_a_1377_; lean_object* v_context_1378_; lean_object* v_activeConnections_1379_; lean_object* v_connectionLimit_1380_; lean_object* v_shutdownPromise_1381_; lean_object* v___f_1382_; lean_object* v___f_1383_; uint8_t v___x_1384_; lean_object* v___x_1385_; lean_object* v___f_1386_; lean_object* v___f_1387_; lean_object* v___x_1388_; lean_object* v___f_1389_; lean_object* v___x_1390_; lean_object* v___f_1391_; lean_object* v___x_1392_; lean_object* v___f_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___f_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v_a_1377_ = lean_ctor_get(v_x_1374_, 0);
v_context_1378_ = lean_ctor_get(v_a_1377_, 0);
v_activeConnections_1379_ = lean_ctor_get(v_a_1377_, 1);
v_connectionLimit_1380_ = lean_ctor_get(v_a_1377_, 2);
v_shutdownPromise_1381_ = lean_ctor_get(v_a_1377_, 3);
lean_inc_ref(v_shutdownPromise_1381_);
lean_inc_ref_n(v_context_1378_, 2);
v___f_1382_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1382_, 0, v_context_1378_);
lean_closure_set(v___f_1382_, 1, v_shutdownPromise_1381_);
v___f_1383_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed), 5, 1);
lean_closure_set(v___f_1383_, 0, v___f_1382_);
v___x_1384_ = 0;
v___x_1385_ = lean_box(0);
v___f_1386_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__28___closed__0));
v___f_1387_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__28___closed__1));
v___x_1388_ = lean_box(v___x_1384_);
lean_inc_ref(v_activeConnections_1379_);
lean_inc_ref(v___x_1361_);
lean_inc_n(v_connectionLimit_1380_, 2);
v___f_1389_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__21___boxed), 21, 18);
lean_closure_set(v___f_1389_, 0, v___x_1388_);
lean_closure_set(v___f_1389_, 1, v___f_1360_);
lean_closure_set(v___f_1389_, 2, v___f_1386_);
lean_closure_set(v___f_1389_, 3, v___x_1385_);
lean_closure_set(v___f_1389_, 4, v_connectionLimit_1380_);
lean_closure_set(v___f_1389_, 5, v___x_1361_);
lean_closure_set(v___f_1389_, 6, v_activeConnections_1379_);
lean_closure_set(v___f_1389_, 7, v___f_1362_);
lean_closure_set(v___f_1389_, 8, v___f_1363_);
lean_closure_set(v___f_1389_, 9, v___f_1383_);
lean_closure_set(v___f_1389_, 10, v_inst_1364_);
lean_closure_set(v___f_1389_, 11, v_handler_1365_);
lean_closure_set(v___f_1389_, 12, v_config_1366_);
lean_closure_set(v___f_1389_, 13, v___f_1367_);
lean_closure_set(v___f_1389_, 14, v___f_1387_);
lean_closure_set(v___f_1389_, 15, v_a_1368_);
lean_closure_set(v___f_1389_, 16, v___f_1369_);
lean_closure_set(v___f_1389_, 17, v___f_1370_);
v___x_1390_ = lean_box(v___x_1384_);
v___f_1391_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__26___boxed), 8, 5);
lean_closure_set(v___f_1391_, 0, v___x_1390_);
lean_closure_set(v___f_1391_, 1, v___f_1371_);
lean_closure_set(v___f_1391_, 2, v_connectionLimit_1380_);
lean_closure_set(v___f_1391_, 3, v___f_1389_);
lean_closure_set(v___f_1391_, 4, v___f_1372_);
v___x_1392_ = lean_box(v___x_1384_);
v___f_1393_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__25___boxed), 7, 5);
lean_closure_set(v___f_1393_, 0, v___x_1361_);
lean_closure_set(v___f_1393_, 1, v___f_1391_);
lean_closure_set(v___f_1393_, 2, v___x_1385_);
lean_closure_set(v___f_1393_, 3, v___x_1392_);
lean_closure_set(v___f_1393_, 4, v___f_1373_);
v___x_1394_ = lean_box(v___x_1384_);
lean_inc(v_a_1377_);
v___x_1395_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___boxed), 6, 5);
lean_closure_set(v___x_1395_, 0, lean_box(0));
lean_closure_set(v___x_1395_, 1, v_a_1377_);
lean_closure_set(v___x_1395_, 2, v___x_1394_);
lean_closure_set(v___x_1395_, 3, v___f_1393_);
lean_closure_set(v___x_1395_, 4, v_context_1378_);
v___x_1396_ = lean_unsigned_to_nat(0u);
v___x_1397_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1397_, 0, lean_box(0));
lean_closure_set(v___x_1397_, 1, v___x_1395_);
v___x_1398_ = lean_io_as_task(v___x_1397_, v___x_1396_);
lean_dec_ref(v___x_1398_);
v___f_1399_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__27___boxed), 3, 1);
lean_closure_set(v___f_1399_, 0, v_x_1374_);
v___x_1400_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
v___x_1401_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1396_, v___x_1384_, v___x_1400_, v___f_1399_);
return v___x_1401_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28___boxed(lean_object* v___f_1402_, lean_object* v___x_1403_, lean_object* v___f_1404_, lean_object* v___f_1405_, lean_object* v_inst_1406_, lean_object* v_handler_1407_, lean_object* v_config_1408_, lean_object* v___f_1409_, lean_object* v_a_1410_, lean_object* v___f_1411_, lean_object* v___f_1412_, lean_object* v___f_1413_, lean_object* v___f_1414_, lean_object* v___f_1415_, lean_object* v_x_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Std_Http_Server_serve___redArg___lam__28(v___f_1402_, v___x_1403_, v___f_1404_, v___f_1405_, v_inst_1406_, v_handler_1407_, v_config_1408_, v___f_1409_, v_a_1410_, v___f_1411_, v___f_1412_, v___f_1413_, v___f_1414_, v___f_1415_, v_x_1416_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29(lean_object* v___f_1419_, lean_object* v_config_1420_, lean_object* v_x_1421_){
_start:
{
lean_object* v_val_1424_; 
if (lean_obj_tag(v_x_1421_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1437_; 
lean_dec_ref(v_config_1420_);
lean_dec_ref(v___f_1419_);
v_a_1429_ = lean_ctor_get(v_x_1421_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_x_1421_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1431_ = v_x_1421_;
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v_x_1421_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1434_);
return v___x_1435_;
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1448_; 
v_a_1438_ = lean_ctor_get(v_x_1421_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_x_1421_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1440_ = v_x_1421_;
v_isShared_1441_ = v_isSharedCheck_1448_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v_x_1421_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1448_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v_a_1444_; lean_object* v___x_1446_; 
v___x_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1442_, 0, v_a_1438_);
v___x_1443_ = l_Std_Http_Server_new(v_config_1420_, v___x_1442_);
v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
lean_inc(v_a_1444_);
lean_dec_ref(v___x_1443_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v_a_1444_);
v___x_1446_ = v___x_1440_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1444_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
v_val_1424_ = v___x_1446_;
goto v___jp_1423_;
}
}
}
v___jp_1423_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; lean_object* v___x_1428_; 
v___x_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1425_, 0, v_val_1424_);
v___x_1426_ = lean_unsigned_to_nat(0u);
v___x_1427_ = 0;
v___x_1428_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1426_, v___x_1427_, v___x_1425_, v___f_1419_);
return v___x_1428_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29___boxed(lean_object* v___f_1449_, lean_object* v_config_1450_, lean_object* v_x_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Std_Http_Server_serve___redArg___lam__29(v___f_1449_, v_config_1450_, v_x_1451_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30(lean_object* v___f_1454_, lean_object* v_a_1455_, lean_object* v_x_1456_){
_start:
{
lean_object* v_val_1459_; 
if (lean_obj_tag(v_x_1456_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1472_; 
lean_dec_ref(v___f_1454_);
v_a_1464_ = lean_ctor_get(v_x_1456_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v_x_1456_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1466_ = v_x_1456_;
v_isShared_1467_ = v_isSharedCheck_1472_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v_x_1456_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1472_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
lean_object* v___x_1470_; 
v___x_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
return v___x_1470_;
}
}
}
else
{
lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1485_; 
v_isSharedCheck_1485_ = !lean_is_exclusive(v_x_1456_);
if (v_isSharedCheck_1485_ == 0)
{
lean_object* v_unused_1486_; 
v_unused_1486_ = lean_ctor_get(v_x_1456_, 0);
lean_dec(v_unused_1486_);
v___x_1474_ = v_x_1456_;
v_isShared_1475_ = v_isSharedCheck_1485_;
goto v_resetjp_1473_;
}
else
{
lean_dec(v_x_1456_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1485_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1476_; 
v___x_1476_ = lean_uv_tcp_getsockname(v_a_1455_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v___x_1479_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
lean_dec_ref_known(v___x_1476_, 1);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 0, v_a_1477_);
v___x_1479_ = v___x_1474_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1477_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
v_val_1459_ = v___x_1479_;
goto v___jp_1458_;
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; 
v_a_1481_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1481_);
lean_dec_ref_known(v___x_1476_, 1);
if (v_isShared_1475_ == 0)
{
lean_ctor_set_tag(v___x_1474_, 0);
lean_ctor_set(v___x_1474_, 0, v_a_1481_);
v___x_1483_ = v___x_1474_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1481_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
v_val_1459_ = v___x_1483_;
goto v___jp_1458_;
}
}
}
}
v___jp_1458_:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; lean_object* v___x_1463_; 
v___x_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1460_, 0, v_val_1459_);
v___x_1461_ = lean_unsigned_to_nat(0u);
v___x_1462_ = 0;
v___x_1463_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1461_, v___x_1462_, v___x_1460_, v___f_1454_);
return v___x_1463_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30___boxed(lean_object* v___f_1487_, lean_object* v_a_1488_, lean_object* v_x_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Std_Http_Server_serve___redArg___lam__30(v___f_1487_, v_a_1488_, v_x_1489_);
lean_dec(v_a_1488_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31(lean_object* v___f_1492_, lean_object* v_a_1493_, lean_object* v_x_1494_){
_start:
{
lean_object* v_val_1497_; 
if (lean_obj_tag(v_x_1494_) == 0)
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1510_; 
lean_dec_ref(v___f_1492_);
v_a_1502_ = lean_ctor_get(v_x_1494_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v_x_1494_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1504_ = v_x_1494_;
v_isShared_1505_ = v_isSharedCheck_1510_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v_x_1494_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1510_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1502_);
v___x_1507_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1508_; 
v___x_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
return v___x_1508_;
}
}
}
else
{
lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1523_; 
v_isSharedCheck_1523_ = !lean_is_exclusive(v_x_1494_);
if (v_isSharedCheck_1523_ == 0)
{
lean_object* v_unused_1524_; 
v_unused_1524_ = lean_ctor_get(v_x_1494_, 0);
lean_dec(v_unused_1524_);
v___x_1512_ = v_x_1494_;
v_isShared_1513_ = v_isSharedCheck_1523_;
goto v_resetjp_1511_;
}
else
{
lean_dec(v_x_1494_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1523_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_uv_tcp_nodelay(v_a_1493_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1517_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
lean_dec_ref_known(v___x_1514_, 1);
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 0, v_a_1515_);
v___x_1517_ = v___x_1512_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1515_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
v_val_1497_ = v___x_1517_;
goto v___jp_1496_;
}
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; 
v_a_1519_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1519_);
lean_dec_ref_known(v___x_1514_, 1);
if (v_isShared_1513_ == 0)
{
lean_ctor_set_tag(v___x_1512_, 0);
lean_ctor_set(v___x_1512_, 0, v_a_1519_);
v___x_1521_ = v___x_1512_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1519_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
v_val_1497_ = v___x_1521_;
goto v___jp_1496_;
}
}
}
}
v___jp_1496_:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; lean_object* v___x_1501_; 
v___x_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1498_, 0, v_val_1497_);
v___x_1499_ = lean_unsigned_to_nat(0u);
v___x_1500_ = 0;
v___x_1501_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1499_, v___x_1500_, v___x_1498_, v___f_1492_);
return v___x_1501_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31___boxed(lean_object* v___f_1525_, lean_object* v_a_1526_, lean_object* v_x_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Std_Http_Server_serve___redArg___lam__31(v___f_1525_, v_a_1526_, v_x_1527_);
lean_dec(v_a_1526_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32(lean_object* v___f_1530_, lean_object* v_a_1531_, uint32_t v_backlog_1532_, lean_object* v_x_1533_){
_start:
{
lean_object* v_val_1536_; 
if (lean_obj_tag(v_x_1533_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1549_; 
lean_dec_ref(v___f_1530_);
v_a_1541_ = lean_ctor_get(v_x_1533_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v_x_1533_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1543_ = v_x_1533_;
v_isShared_1544_ = v_isSharedCheck_1549_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v_x_1533_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1549_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
lean_object* v___x_1547_; 
v___x_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
return v___x_1547_;
}
}
}
else
{
lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1562_; 
v_isSharedCheck_1562_ = !lean_is_exclusive(v_x_1533_);
if (v_isSharedCheck_1562_ == 0)
{
lean_object* v_unused_1563_; 
v_unused_1563_ = lean_ctor_get(v_x_1533_, 0);
lean_dec(v_unused_1563_);
v___x_1551_ = v_x_1533_;
v_isShared_1552_ = v_isSharedCheck_1562_;
goto v_resetjp_1550_;
}
else
{
lean_dec(v_x_1533_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1562_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1553_; 
v___x_1553_ = lean_uv_tcp_listen(v_a_1531_, v_backlog_1532_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v___x_1556_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
lean_dec_ref_known(v___x_1553_, 1);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v_a_1554_);
v___x_1556_ = v___x_1551_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1554_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
v_val_1536_ = v___x_1556_;
goto v___jp_1535_;
}
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; 
v_a_1558_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1558_);
lean_dec_ref_known(v___x_1553_, 1);
if (v_isShared_1552_ == 0)
{
lean_ctor_set_tag(v___x_1551_, 0);
lean_ctor_set(v___x_1551_, 0, v_a_1558_);
v___x_1560_ = v___x_1551_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1558_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
v_val_1536_ = v___x_1560_;
goto v___jp_1535_;
}
}
}
}
v___jp_1535_:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; lean_object* v___x_1540_; 
v___x_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1537_, 0, v_val_1536_);
v___x_1538_ = lean_unsigned_to_nat(0u);
v___x_1539_ = 0;
v___x_1540_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1538_, v___x_1539_, v___x_1537_, v___f_1530_);
return v___x_1540_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32___boxed(lean_object* v___f_1564_, lean_object* v_a_1565_, lean_object* v_backlog_1566_, lean_object* v_x_1567_, lean_object* v___y_1568_){
_start:
{
uint32_t v_backlog_boxed_1569_; lean_object* v_res_1570_; 
v_backlog_boxed_1569_ = lean_unbox_uint32(v_backlog_1566_);
lean_dec(v_backlog_1566_);
v_res_1570_ = l_Std_Http_Server_serve___redArg___lam__32(v___f_1564_, v_a_1565_, v_backlog_boxed_1569_, v_x_1567_);
lean_dec(v_a_1565_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__33(lean_object* v___f_1571_, lean_object* v___x_1572_, lean_object* v___f_1573_, lean_object* v___f_1574_, lean_object* v_inst_1575_, lean_object* v_handler_1576_, lean_object* v_config_1577_, lean_object* v___f_1578_, lean_object* v___f_1579_, lean_object* v___f_1580_, lean_object* v___f_1581_, lean_object* v___f_1582_, lean_object* v___f_1583_, uint32_t v_backlog_1584_, lean_object* v_addr_1585_, lean_object* v_x_1586_){
_start:
{
if (lean_obj_tag(v_x_1586_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1596_; 
lean_dec_ref(v___f_1583_);
lean_dec_ref(v___f_1582_);
lean_dec_ref(v___f_1581_);
lean_dec_ref(v___f_1580_);
lean_dec_ref(v___f_1579_);
lean_dec_ref(v___f_1578_);
lean_dec_ref(v_config_1577_);
lean_dec(v_handler_1576_);
lean_dec_ref(v_inst_1575_);
lean_dec_ref(v___f_1574_);
lean_dec_ref(v___f_1573_);
lean_dec_ref(v___x_1572_);
lean_dec_ref(v___f_1571_);
v_a_1588_ = lean_ctor_get(v_x_1586_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_x_1586_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1590_ = v_x_1586_;
v_isShared_1591_ = v_isSharedCheck_1596_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v_x_1586_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1596_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
return v___x_1594_;
}
}
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1622_; 
v_a_1597_ = lean_ctor_get(v_x_1586_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_x_1586_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1599_ = v_x_1586_;
v_isShared_1600_ = v_isSharedCheck_1622_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v_x_1586_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1622_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___f_1601_; lean_object* v___f_1602_; lean_object* v___f_1603_; lean_object* v___f_1604_; lean_object* v___x_1605_; lean_object* v___f_1606_; lean_object* v_val_1608_; lean_object* v___x_1613_; 
lean_inc_n(v_a_1597_, 4);
lean_inc_ref(v_config_1577_);
v___f_1601_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__28___boxed), 16, 14);
lean_closure_set(v___f_1601_, 0, v___f_1571_);
lean_closure_set(v___f_1601_, 1, v___x_1572_);
lean_closure_set(v___f_1601_, 2, v___f_1573_);
lean_closure_set(v___f_1601_, 3, v___f_1574_);
lean_closure_set(v___f_1601_, 4, v_inst_1575_);
lean_closure_set(v___f_1601_, 5, v_handler_1576_);
lean_closure_set(v___f_1601_, 6, v_config_1577_);
lean_closure_set(v___f_1601_, 7, v___f_1578_);
lean_closure_set(v___f_1601_, 8, v_a_1597_);
lean_closure_set(v___f_1601_, 9, v___f_1579_);
lean_closure_set(v___f_1601_, 10, v___f_1580_);
lean_closure_set(v___f_1601_, 11, v___f_1581_);
lean_closure_set(v___f_1601_, 12, v___f_1582_);
lean_closure_set(v___f_1601_, 13, v___f_1583_);
v___f_1602_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__29___boxed), 4, 2);
lean_closure_set(v___f_1602_, 0, v___f_1601_);
lean_closure_set(v___f_1602_, 1, v_config_1577_);
v___f_1603_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__30___boxed), 4, 2);
lean_closure_set(v___f_1603_, 0, v___f_1602_);
lean_closure_set(v___f_1603_, 1, v_a_1597_);
v___f_1604_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__31___boxed), 4, 2);
lean_closure_set(v___f_1604_, 0, v___f_1603_);
lean_closure_set(v___f_1604_, 1, v_a_1597_);
v___x_1605_ = lean_box_uint32(v_backlog_1584_);
v___f_1606_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__32___boxed), 5, 3);
lean_closure_set(v___f_1606_, 0, v___f_1604_);
lean_closure_set(v___f_1606_, 1, v_a_1597_);
lean_closure_set(v___f_1606_, 2, v___x_1605_);
v___x_1613_ = lean_uv_tcp_bind(v_a_1597_, v_addr_1585_);
lean_dec(v_a_1597_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___x_1616_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref_known(v___x_1613_, 1);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v_a_1614_);
v___x_1616_ = v___x_1599_;
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
v_val_1608_ = v___x_1616_;
goto v___jp_1607_;
}
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1620_; 
v_a_1618_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1618_);
lean_dec_ref_known(v___x_1613_, 1);
if (v_isShared_1600_ == 0)
{
lean_ctor_set_tag(v___x_1599_, 0);
lean_ctor_set(v___x_1599_, 0, v_a_1618_);
v___x_1620_ = v___x_1599_;
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
v_val_1608_ = v___x_1620_;
goto v___jp_1607_;
}
}
v___jp_1607_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; uint8_t v___x_1611_; lean_object* v___x_1612_; 
v___x_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1609_, 0, v_val_1608_);
v___x_1610_ = lean_unsigned_to_nat(0u);
v___x_1611_ = 0;
v___x_1612_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1610_, v___x_1611_, v___x_1609_, v___f_1606_);
return v___x_1612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__33___boxed(lean_object** _args){
lean_object* v___f_1623_ = _args[0];
lean_object* v___x_1624_ = _args[1];
lean_object* v___f_1625_ = _args[2];
lean_object* v___f_1626_ = _args[3];
lean_object* v_inst_1627_ = _args[4];
lean_object* v_handler_1628_ = _args[5];
lean_object* v_config_1629_ = _args[6];
lean_object* v___f_1630_ = _args[7];
lean_object* v___f_1631_ = _args[8];
lean_object* v___f_1632_ = _args[9];
lean_object* v___f_1633_ = _args[10];
lean_object* v___f_1634_ = _args[11];
lean_object* v___f_1635_ = _args[12];
lean_object* v_backlog_1636_ = _args[13];
lean_object* v_addr_1637_ = _args[14];
lean_object* v_x_1638_ = _args[15];
lean_object* v___y_1639_ = _args[16];
_start:
{
uint32_t v_backlog_boxed_1640_; lean_object* v_res_1641_; 
v_backlog_boxed_1640_ = lean_unbox_uint32(v_backlog_1636_);
lean_dec(v_backlog_1636_);
v_res_1641_ = l_Std_Http_Server_serve___redArg___lam__33(v___f_1623_, v___x_1624_, v___f_1625_, v___f_1626_, v_inst_1627_, v_handler_1628_, v_config_1629_, v___f_1630_, v___f_1631_, v___f_1632_, v___f_1633_, v___f_1634_, v___f_1635_, v_backlog_boxed_1640_, v_addr_1637_, v_x_1638_);
lean_dec_ref(v_addr_1637_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg(lean_object* v_inst_1648_, lean_object* v_addr_1649_, lean_object* v_handler_1650_, lean_object* v_config_1651_, uint32_t v_backlog_1652_){
_start:
{
lean_object* v___f_1654_; lean_object* v___f_1655_; lean_object* v___f_1656_; lean_object* v___f_1657_; lean_object* v___f_1658_; lean_object* v___f_1659_; lean_object* v___f_1660_; lean_object* v___f_1661_; lean_object* v___f_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___f_1665_; lean_object* v_val_1667_; lean_object* v___x_1672_; 
v___f_1654_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__0));
v___f_1655_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__1));
v___f_1656_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0));
v___f_1657_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__2));
v___f_1658_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5));
v___f_1659_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__3));
v___f_1660_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__4));
v___f_1661_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__5));
v___f_1662_ = ((lean_object*)(l_Std_Http_Server_waitShutdown___closed__0));
v___x_1663_ = l_Std_Async_ContextAsync_instMonad;
v___x_1664_ = lean_box_uint32(v_backlog_1652_);
v___f_1665_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__33___boxed), 17, 15);
lean_closure_set(v___f_1665_, 0, v___f_1661_);
lean_closure_set(v___f_1665_, 1, v___x_1663_);
lean_closure_set(v___f_1665_, 2, v___f_1656_);
lean_closure_set(v___f_1665_, 3, v___f_1658_);
lean_closure_set(v___f_1665_, 4, v_inst_1648_);
lean_closure_set(v___f_1665_, 5, v_handler_1650_);
lean_closure_set(v___f_1665_, 6, v_config_1651_);
lean_closure_set(v___f_1665_, 7, v___f_1657_);
lean_closure_set(v___f_1665_, 8, v___f_1660_);
lean_closure_set(v___f_1665_, 9, v___f_1659_);
lean_closure_set(v___f_1665_, 10, v___f_1655_);
lean_closure_set(v___f_1665_, 11, v___f_1662_);
lean_closure_set(v___f_1665_, 12, v___f_1654_);
lean_closure_set(v___f_1665_, 13, v___x_1664_);
lean_closure_set(v___f_1665_, 14, v_addr_1649_);
v___x_1672_ = lean_uv_tcp_new();
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
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
v_val_1667_ = v___x_1678_;
goto v___jp_1666_;
}
}
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
v_a_1681_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1672_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1672_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
lean_ctor_set_tag(v___x_1683_, 0);
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
v_val_1667_ = v___x_1686_;
goto v___jp_1666_;
}
}
}
v___jp_1666_:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; uint8_t v___x_1670_; lean_object* v___x_1671_; 
v___x_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1668_, 0, v_val_1667_);
v___x_1669_ = lean_unsigned_to_nat(0u);
v___x_1670_ = 0;
v___x_1671_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1669_, v___x_1670_, v___x_1668_, v___f_1665_);
return v___x_1671_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___boxed(lean_object* v_inst_1689_, lean_object* v_addr_1690_, lean_object* v_handler_1691_, lean_object* v_config_1692_, lean_object* v_backlog_1693_, lean_object* v_a_1694_){
_start:
{
uint32_t v_backlog_boxed_1695_; lean_object* v_res_1696_; 
v_backlog_boxed_1695_ = lean_unbox_uint32(v_backlog_1693_);
lean_dec(v_backlog_1693_);
v_res_1696_ = l_Std_Http_Server_serve___redArg(v_inst_1689_, v_addr_1690_, v_handler_1691_, v_config_1692_, v_backlog_boxed_1695_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve(lean_object* v_00_u03c3_1697_, lean_object* v_inst_1698_, lean_object* v_addr_1699_, lean_object* v_handler_1700_, lean_object* v_config_1701_, uint32_t v_backlog_1702_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Std_Http_Server_serve___redArg(v_inst_1698_, v_addr_1699_, v_handler_1700_, v_config_1701_, v_backlog_1702_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___boxed(lean_object* v_00_u03c3_1705_, lean_object* v_inst_1706_, lean_object* v_addr_1707_, lean_object* v_handler_1708_, lean_object* v_config_1709_, lean_object* v_backlog_1710_, lean_object* v_a_1711_){
_start:
{
uint32_t v_backlog_boxed_1712_; lean_object* v_res_1713_; 
v_backlog_boxed_1712_ = lean_unbox_uint32(v_backlog_1710_);
lean_dec(v_backlog_1710_);
v_res_1713_ = l_Std_Http_Server_serve(v_00_u03c3_1705_, v_inst_1706_, v_addr_1707_, v_handler_1708_, v_config_1709_, v_backlog_boxed_1712_);
return v_res_1713_;
}
}
lean_object* runtime_initialize_Std_Async(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_TCP(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_CancellationToken(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_Semaphore(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Server_Config(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Server_Handler(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Server_Connection(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Server(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
