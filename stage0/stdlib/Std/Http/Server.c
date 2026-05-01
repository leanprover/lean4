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
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_selector(lean_object*);
extern lean_object* l_Std_Async_ContextAsync_instMonad;
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
lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_tcp_nodelay(lean_object*);
lean_object* lean_uv_tcp_listen(lean_object*, uint32_t);
lean_object* lean_uv_tcp_bind(lean_object*, lean_object*);
lean_object* lean_uv_tcp_new();
lean_object* l_Std_CancellationContext_new();
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* l_Std_CloseableChannel_new___redArg(lean_object*);
lean_object* l_Std_Semaphore_new(lean_object*);
lean_object* l_Std_Channel_recv___redArg(lean_object*, lean_object*);
lean_object* l_Std_Channel_recvSelector___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_new(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_new___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2___boxed(lean_object*);
static const lean_ctor_object l_Std_Http_Server_serve___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Server_serve___redArg___lam__3___closed__0 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Std_Http_Server_serve___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Server_serve___redArg___lam__3___closed__0_value)}};
static const lean_object* l_Std_Http_Server_serve___redArg___lam__3___closed__1 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Server_serve___redArg___lam__20___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Server_serve___redArg___lam__20___closed__0;
static lean_once_cell_t l_Std_Http_Server_serve___redArg___lam__20___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Server_serve___redArg___lam__20___closed__1;
static const lean_closure_object l_Std_Http_Server_serve___redArg___lam__20___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Extensions_compareName___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___lam__20___closed__2 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__20___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__19(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__19___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Server_serve___redArg___lam__28___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__8___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Server_serve___redArg___lam__28___closed__0 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__28___closed__0_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___lam__28___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__5___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Server_serve___redArg___lam__28___closed__1 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__28___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30(lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__0 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__0_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__1 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__1_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__2 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__2_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__3 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__3_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__4___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__4 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_new(lean_object* v_config_1_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v_connectionLimit_7_; lean_object* v_maxConnections_12_; uint8_t v___x_13_; 
v___x_3_ = l_Std_CancellationContext_new();
v___x_4_ = lean_unsigned_to_nat(0u);
v___x_5_ = l_Std_Mutex_new___redArg(v___x_4_);
v_maxConnections_12_ = lean_ctor_get(v_config_1_, 0);
v___x_13_ = lean_nat_dec_eq(v_maxConnections_12_, v___x_4_);
if (v___x_13_ == 0)
{
lean_object* v___x_14_; lean_object* v___x_15_; 
lean_inc(v_maxConnections_12_);
v___x_14_ = l_Std_Semaphore_new(v_maxConnections_12_);
v___x_15_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
v_connectionLimit_7_ = v___x_15_;
goto v___jp_6_;
}
else
{
lean_object* v___x_16_; 
v___x_16_ = lean_box(0);
v_connectionLimit_7_ = v___x_16_;
goto v___jp_6_;
}
v___jp_6_:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_8_ = lean_box(0);
v___x_9_ = l_Std_CloseableChannel_new___redArg(v___x_8_);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v___x_3_);
lean_ctor_set(v___x_10_, 1, v___x_5_);
lean_ctor_set(v___x_10_, 2, v_connectionLimit_7_);
lean_ctor_set(v___x_10_, 3, v___x_9_);
lean_ctor_set(v___x_10_, 4, v_config_1_);
v___x_11_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_new___boxed(lean_object* v_config_17_, lean_object* v_a_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Std_Http_Server_new(v_config_17_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdown(lean_object* v_s_20_){
_start:
{
lean_object* v_context_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v_context_22_ = lean_ctor_get(v_s_20_, 0);
lean_inc_ref(v_context_22_);
lean_dec_ref(v_s_20_);
v___x_23_ = lean_box(1);
v___x_24_ = l_Std_CancellationContext_cancel(v_context_22_, v___x_23_);
v___x_25_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdown___boxed(lean_object* v_s_27_, lean_object* v_a_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Std_Http_Server_shutdown(v_s_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___lam__0(lean_object* v_a_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_31_, 0, v_a_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___lam__1(lean_object* v___f_32_, lean_object* v_x_33_){
_start:
{
if (lean_obj_tag(v_x_33_) == 0)
{
lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_43_; 
lean_dec_ref(v___f_32_);
v_a_35_ = lean_ctor_get(v_x_33_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v_x_33_);
if (v_isSharedCheck_43_ == 0)
{
v___x_37_ = v_x_33_;
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_dec(v_x_33_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_40_; 
if (v_isShared_38_ == 0)
{
v___x_40_ = v___x_37_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_a_35_);
v___x_40_ = v_reuseFailAlloc_42_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
lean_object* v___x_41_; 
v___x_41_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
return v___x_41_;
}
}
}
else
{
lean_object* v_a_44_; lean_object* v___x_45_; uint8_t v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v_a_44_ = lean_ctor_get(v_x_33_, 0);
lean_inc(v_a_44_);
lean_dec_ref(v_x_33_);
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = 0;
v___x_47_ = lean_task_map(v___f_32_, v_a_44_, v___x_45_, v___x_46_);
v___x_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___lam__1___boxed(lean_object* v___f_49_, lean_object* v_x_50_, lean_object* v___y_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Std_Http_Server_waitShutdown___lam__1(v___f_49_, v_x_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown(lean_object* v_s_56_){
_start:
{
lean_object* v_shutdownPromise_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___f_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; uint8_t v___x_65_; lean_object* v___x_66_; 
v_shutdownPromise_58_ = lean_ctor_get(v_s_56_, 3);
lean_inc_ref(v_shutdownPromise_58_);
lean_dec_ref(v_s_56_);
v___x_59_ = lean_box(0);
v___x_60_ = l_Std_Channel_recv___redArg(v___x_59_, v_shutdownPromise_58_);
v___f_61_ = ((lean_object*)(l_Std_Http_Server_waitShutdown___closed__1));
v___x_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_62_, 0, v___x_60_);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
v___x_64_ = lean_unsigned_to_nat(0u);
v___x_65_ = 0;
v___x_66_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_64_, v___x_65_, v___x_63_, v___f_61_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___boxed(lean_object* v_s_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Std_Http_Server_waitShutdown(v_s_67_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdownSelector(lean_object* v_s_70_){
_start:
{
lean_object* v_shutdownPromise_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_shutdownPromise_71_ = lean_ctor_get(v_s_70_, 3);
lean_inc_ref(v_shutdownPromise_71_);
lean_dec_ref(v_s_70_);
v___x_72_ = lean_box(0);
v___x_73_ = l_Std_Channel_recvSelector___redArg(v___x_72_, v_shutdownPromise_71_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait___lam__2(lean_object* v_shutdownPromise_74_, lean_object* v___f_75_, lean_object* v_x_76_){
_start:
{
if (lean_obj_tag(v_x_76_) == 0)
{
lean_object* v___x_78_; 
lean_dec_ref(v___f_75_);
lean_dec_ref(v_shutdownPromise_74_);
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v_x_76_);
return v___x_78_;
}
else
{
lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_91_; 
v_isSharedCheck_91_ = !lean_is_exclusive(v_x_76_);
if (v_isSharedCheck_91_ == 0)
{
lean_object* v_unused_92_; 
v_unused_92_ = lean_ctor_get(v_x_76_, 0);
lean_dec(v_unused_92_);
v___x_80_ = v_x_76_;
v_isShared_81_ = v_isSharedCheck_91_;
goto v_resetjp_79_;
}
else
{
lean_dec(v_x_76_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_91_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_85_; 
v___x_82_ = lean_box(0);
v___x_83_ = l_Std_Channel_recv___redArg(v___x_82_, v_shutdownPromise_74_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 0, v___x_83_);
v___x_85_ = v___x_80_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_83_);
v___x_85_ = v_reuseFailAlloc_90_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; 
v___x_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = 0;
v___x_89_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_87_, v___x_88_, v___x_86_, v___f_75_);
return v___x_89_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait___lam__2___boxed(lean_object* v_shutdownPromise_93_, lean_object* v___f_94_, lean_object* v_x_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Std_Http_Server_shutdownAndWait___lam__2(v_shutdownPromise_93_, v___f_94_, v_x_95_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait(lean_object* v_s_98_){
_start:
{
lean_object* v_context_100_; lean_object* v_shutdownPromise_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___f_104_; lean_object* v___f_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; lean_object* v___x_110_; 
v_context_100_ = lean_ctor_get(v_s_98_, 0);
lean_inc_ref(v_context_100_);
v_shutdownPromise_101_ = lean_ctor_get(v_s_98_, 3);
lean_inc_ref(v_shutdownPromise_101_);
lean_dec_ref(v_s_98_);
v___x_102_ = lean_box(1);
v___x_103_ = l_Std_CancellationContext_cancel(v_context_100_, v___x_102_);
v___f_104_ = ((lean_object*)(l_Std_Http_Server_waitShutdown___closed__1));
v___f_105_ = lean_alloc_closure((void*)(l_Std_Http_Server_shutdownAndWait___lam__2___boxed), 4, 2);
lean_closure_set(v___f_105_, 0, v_shutdownPromise_101_);
lean_closure_set(v___f_105_, 1, v___f_104_);
v___x_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_103_);
v___x_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
v___x_108_ = lean_unsigned_to_nat(0u);
v___x_109_ = 0;
v___x_110_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_108_, v___x_109_, v___x_107_, v___f_105_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait___boxed(lean_object* v_s_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Std_Http_Server_shutdownAndWait(v_s_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0(lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_121_ = lean_st_ref_take(v___y_118_);
v___x_122_ = lean_unsigned_to_nat(1u);
v___x_123_ = lean_nat_add(v___x_121_, v___x_122_);
lean_dec(v___x_121_);
v___x_124_ = lean_st_ref_set(v___y_118_, v___x_123_);
v___x_125_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___boxed(lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0(v___y_126_, v___y_127_);
lean_dec_ref(v___y_127_);
lean_dec(v___y_126_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1(lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_133_ = lean_st_ref_take(v___y_130_);
v___x_134_ = lean_unsigned_to_nat(1u);
v___x_135_ = lean_nat_sub(v___x_133_, v___x_134_);
lean_dec(v___x_133_);
v___x_136_ = lean_st_ref_set(v___y_130_, v___x_135_);
v___x_137_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1___boxed(lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1(v___y_138_, v___y_139_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2(lean_object* v_a_142_, lean_object* v_shutdownPromise_143_, lean_object* v_x_144_){
_start:
{
if (lean_obj_tag(v_x_144_) == 0)
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_156_; 
lean_dec_ref(v_shutdownPromise_143_);
v_a_148_ = lean_ctor_get(v_x_144_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v_x_144_);
if (v_isSharedCheck_156_ == 0)
{
v___x_150_ = v_x_144_;
v_isShared_151_ = v_isSharedCheck_156_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v_x_144_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_156_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_148_);
v___x_153_ = v_reuseFailAlloc_155_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_154_; 
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
}
}
else
{
lean_object* v_a_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v_a_157_ = lean_ctor_get(v_x_144_, 0);
lean_inc(v_a_157_);
lean_dec_ref(v_x_144_);
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = lean_nat_dec_eq(v_a_142_, v___x_158_);
if (v___x_159_ == 0)
{
lean_dec(v_a_157_);
lean_dec_ref(v_shutdownPromise_143_);
goto v___jp_146_;
}
else
{
uint8_t v___x_160_; 
v___x_160_ = lean_unbox(v_a_157_);
lean_dec(v_a_157_);
if (v___x_160_ == 0)
{
lean_dec_ref(v_shutdownPromise_143_);
goto v___jp_146_;
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = lean_box(0);
v___x_162_ = l_Std_Channel_send___redArg(v_shutdownPromise_143_, v___x_161_);
lean_dec_ref(v___x_162_);
v___x_163_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_163_;
}
}
}
v___jp_146_:
{
lean_object* v___x_147_; 
v___x_147_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2___boxed(lean_object* v_a_164_, lean_object* v_shutdownPromise_165_, lean_object* v_x_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2(v_a_164_, v_shutdownPromise_165_, v_x_166_);
lean_dec(v_a_164_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3(lean_object* v_context_169_, lean_object* v_shutdownPromise_170_, lean_object* v_x_171_){
_start:
{
if (lean_obj_tag(v_x_171_) == 0)
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_181_; 
lean_dec_ref(v_shutdownPromise_170_);
lean_dec_ref(v_context_169_);
v_a_173_ = lean_ctor_get(v_x_171_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v_x_171_);
if (v_isSharedCheck_181_ == 0)
{
v___x_175_ = v_x_171_;
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v_x_171_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_a_173_);
v___x_178_ = v_reuseFailAlloc_180_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_179_; 
v___x_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
return v___x_179_;
}
}
}
else
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_197_; 
v_a_182_ = lean_ctor_get(v_x_171_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v_x_171_);
if (v_isSharedCheck_197_ == 0)
{
v___x_184_ = v_x_171_;
v_isShared_185_ = v_isSharedCheck_197_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v_x_171_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_197_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v_token_186_; uint8_t v___x_187_; lean_object* v___f_188_; lean_object* v___x_189_; lean_object* v___x_191_; 
v_token_186_ = lean_ctor_get(v_context_169_, 1);
lean_inc_ref(v_token_186_);
lean_dec_ref(v_context_169_);
v___x_187_ = l_Std_CancellationToken_isCancelled(v_token_186_);
v___f_188_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_188_, 0, v_a_182_);
lean_closure_set(v___f_188_, 1, v_shutdownPromise_170_);
v___x_189_ = lean_box(v___x_187_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 0, v___x_189_);
v___x_191_ = v___x_184_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_189_);
v___x_191_ = v_reuseFailAlloc_196_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; lean_object* v___x_195_; 
v___x_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = 0;
v___x_195_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_193_, v___x_194_, v___x_192_, v___f_188_);
return v___x_195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed(lean_object* v_context_198_, lean_object* v_shutdownPromise_199_, lean_object* v_x_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3(v_context_198_, v_shutdownPromise_199_, v_x_200_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4(lean_object* v___f_203_, lean_object* v_____r_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; lean_object* v___x_213_; 
v___x_208_ = lean_st_ref_get(v___y_205_);
v___x_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = 0;
v___x_213_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_211_, v___x_212_, v___x_210_, v___f_203_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed(lean_object* v___f_214_, lean_object* v_____r_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4(v___f_214_, v_____r_215_, v___y_216_, v___y_217_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5(lean_object* v_x_220_){
_start:
{
lean_object* v_fst_221_; 
v_fst_221_ = lean_ctor_get(v_x_220_, 0);
lean_inc(v_fst_221_);
return v_fst_221_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5___boxed(lean_object* v_x_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5(v_x_222_);
lean_dec_ref(v_x_222_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6(lean_object* v___x_224_, lean_object* v___f_225_, lean_object* v___f_226_, lean_object* v___f_227_, lean_object* v___f_228_, lean_object* v_activeConnections_229_, lean_object* v_____r_230_, lean_object* v___y_231_){
_start:
{
lean_object* v___x_233_; lean_object* v___x_2353__overap_234_; lean_object* v___x_235_; 
lean_inc_ref(v___x_224_);
v___x_233_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_233_, 0, lean_box(0));
lean_closure_set(v___x_233_, 1, lean_box(0));
lean_closure_set(v___x_233_, 2, lean_box(0));
lean_closure_set(v___x_233_, 3, v___x_224_);
lean_closure_set(v___x_233_, 4, lean_box(0));
lean_closure_set(v___x_233_, 5, lean_box(0));
lean_closure_set(v___x_233_, 6, v___f_225_);
lean_closure_set(v___x_233_, 7, v___f_226_);
v___x_2353__overap_234_ = l_Std_Mutex_atomically___redArg(v___x_224_, v___f_227_, v___f_228_, v_activeConnections_229_, v___x_233_);
lean_inc_ref(v___y_231_);
v___x_235_ = lean_apply_2(v___x_2353__overap_234_, v___y_231_, lean_box(0));
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed(lean_object* v___x_236_, lean_object* v___f_237_, lean_object* v___f_238_, lean_object* v___f_239_, lean_object* v___f_240_, lean_object* v_activeConnections_241_, lean_object* v_____r_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6(v___x_236_, v___f_237_, v___f_238_, v___f_239_, v___f_240_, v_activeConnections_241_, v_____r_242_, v___y_243_);
lean_dec_ref(v___y_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7(lean_object* v___f_246_, lean_object* v_a_247_, lean_object* v_x_248_){
_start:
{
if (lean_obj_tag(v_x_248_) == 0)
{
lean_object* v___x_250_; 
lean_dec_ref(v___f_246_);
v___x_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_250_, 0, v_x_248_);
return v___x_250_;
}
else
{
lean_object* v_a_251_; lean_object* v___x_252_; 
v_a_251_ = lean_ctor_get(v_x_248_, 0);
lean_inc(v_a_251_);
lean_dec_ref(v_x_248_);
lean_inc_ref(v_a_247_);
v___x_252_ = lean_apply_3(v___f_246_, v_a_251_, v_a_247_, lean_box(0));
return v___x_252_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed(lean_object* v___f_253_, lean_object* v_a_254_, lean_object* v_x_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7(v___f_253_, v_a_254_, v_x_255_);
lean_dec_ref(v_a_254_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8(uint8_t v_releaseConnectionPermit_258_, lean_object* v___f_259_, lean_object* v_a_260_, lean_object* v_connectionLimit_261_, lean_object* v___f_262_, lean_object* v_opt_263_){
_start:
{
if (v_releaseConnectionPermit_258_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec_ref(v___f_262_);
lean_dec(v_connectionLimit_261_);
v___x_265_ = lean_box(0);
lean_inc_ref(v_a_260_);
v___x_266_ = lean_apply_3(v___f_259_, v___x_265_, v_a_260_, lean_box(0));
return v___x_266_;
}
else
{
if (lean_obj_tag(v_connectionLimit_261_) == 1)
{
lean_object* v_val_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_279_; 
lean_dec_ref(v___f_259_);
v_val_267_ = lean_ctor_get(v_connectionLimit_261_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v_connectionLimit_261_);
if (v_isSharedCheck_279_ == 0)
{
v___x_269_ = v_connectionLimit_261_;
v_isShared_270_ = v_isSharedCheck_279_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_val_267_);
lean_dec(v_connectionLimit_261_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_279_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_271_ = l_Std_Semaphore_release(v_val_267_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_271_);
v___x_273_ = v___x_269_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_271_);
v___x_273_ = v_reuseFailAlloc_278_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; lean_object* v___x_277_; 
v___x_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
v___x_275_ = lean_unsigned_to_nat(0u);
v___x_276_ = 0;
v___x_277_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_275_, v___x_276_, v___x_274_, v___f_262_);
return v___x_277_;
}
}
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; 
lean_dec_ref(v___f_262_);
lean_dec(v_connectionLimit_261_);
v___x_280_ = lean_box(0);
lean_inc_ref(v_a_260_);
v___x_281_ = lean_apply_3(v___f_259_, v___x_280_, v_a_260_, lean_box(0));
return v___x_281_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed(lean_object* v_releaseConnectionPermit_282_, lean_object* v___f_283_, lean_object* v_a_284_, lean_object* v_connectionLimit_285_, lean_object* v___f_286_, lean_object* v_opt_287_, lean_object* v___y_288_){
_start:
{
uint8_t v_releaseConnectionPermit_boxed_289_; lean_object* v_res_290_; 
v_releaseConnectionPermit_boxed_289_ = lean_unbox(v_releaseConnectionPermit_282_);
v_res_290_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8(v_releaseConnectionPermit_boxed_289_, v___f_283_, v_a_284_, v_connectionLimit_285_, v___f_286_, v_opt_287_);
lean_dec(v_opt_287_);
lean_dec_ref(v_a_284_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9(lean_object* v_action_291_, lean_object* v_a_292_, lean_object* v___f_293_, lean_object* v___f_294_, lean_object* v_x_295_){
_start:
{
if (lean_obj_tag(v_x_295_) == 0)
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_305_; 
lean_dec(v___f_294_);
lean_dec_ref(v___f_293_);
lean_dec_ref(v_action_291_);
v_a_297_ = lean_ctor_get(v_x_295_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v_x_295_);
if (v_isSharedCheck_305_ == 0)
{
v___x_299_ = v_x_295_;
v_isShared_300_ = v_isSharedCheck_305_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v_x_295_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_305_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_304_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_303_; 
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
}
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; lean_object* v___x_309_; lean_object* v___y_311_; 
lean_dec_ref(v_x_295_);
lean_inc_ref(v_a_292_);
v___x_306_ = lean_apply_1(v_action_291_, v_a_292_);
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = 0;
v___x_309_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_306_, v___f_293_, v___x_307_, v___x_308_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_313_; 
lean_dec(v___f_294_);
v_a_313_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_a_313_);
lean_dec_ref(v___x_309_);
if (lean_obj_tag(v_a_313_) == 0)
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
v_a_314_ = lean_ctor_get(v_a_313_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v_a_313_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v_a_313_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v_a_313_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
v___y_311_ = v___x_319_;
goto v___jp_310_;
}
}
}
else
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_330_; 
v_a_322_ = lean_ctor_get(v_a_313_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v_a_313_);
if (v_isSharedCheck_330_ == 0)
{
v___x_324_ = v_a_313_;
v_isShared_325_ = v_isSharedCheck_330_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v_a_313_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_330_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v_fst_326_; lean_object* v___x_328_; 
v_fst_326_ = lean_ctor_get(v_a_322_, 0);
lean_inc(v_fst_326_);
lean_dec(v_a_322_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 0, v_fst_326_);
v___x_328_ = v___x_324_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_fst_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
v___y_311_ = v___x_328_;
goto v___jp_310_;
}
}
}
}
else
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_340_; 
v_a_331_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_340_ == 0)
{
v___x_333_ = v___x_309_;
v_isShared_334_ = v_isSharedCheck_340_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_309_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_340_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_335_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_335_, 0, lean_box(0));
lean_closure_set(v___x_335_, 1, lean_box(0));
lean_closure_set(v___x_335_, 2, lean_box(0));
lean_closure_set(v___x_335_, 3, v___f_294_);
v___x_336_ = lean_task_map(v___x_335_, v_a_331_, v___x_307_, v___x_308_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_336_);
v___x_338_ = v___x_333_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
v___jp_310_:
{
lean_object* v___x_312_; 
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v___y_311_);
return v___x_312_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed(lean_object* v_action_341_, lean_object* v_a_342_, lean_object* v___f_343_, lean_object* v___f_344_, lean_object* v_x_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9(v_action_341_, v_a_342_, v___f_343_, v___f_344_, v_x_345_);
lean_dec_ref(v_a_342_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg(lean_object* v_s_357_, uint8_t v_releaseConnectionPermit_358_, lean_object* v_action_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_362_; lean_object* v_context_363_; lean_object* v_activeConnections_364_; lean_object* v_connectionLimit_365_; lean_object* v_shutdownPromise_366_; lean_object* v___f_367_; lean_object* v___f_368_; lean_object* v___f_369_; lean_object* v___x_1520__overap_370_; lean_object* v___x_371_; lean_object* v___f_372_; lean_object* v___f_373_; lean_object* v___f_374_; lean_object* v___f_375_; lean_object* v___f_376_; lean_object* v___f_377_; lean_object* v___x_378_; lean_object* v___f_379_; lean_object* v___f_380_; lean_object* v___x_381_; uint8_t v___x_382_; lean_object* v___x_383_; 
v___x_362_ = l_Std_Async_ContextAsync_instMonad;
v_context_363_ = lean_ctor_get(v_s_357_, 0);
lean_inc_ref(v_context_363_);
v_activeConnections_364_ = lean_ctor_get(v_s_357_, 1);
lean_inc_ref_n(v_activeConnections_364_, 2);
v_connectionLimit_365_ = lean_ctor_get(v_s_357_, 2);
lean_inc(v_connectionLimit_365_);
v_shutdownPromise_366_ = lean_ctor_get(v_s_357_, 3);
lean_inc_ref(v_shutdownPromise_366_);
lean_dec_ref(v_s_357_);
v___f_367_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0));
v___f_368_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3));
v___f_369_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4));
v___x_1520__overap_370_ = l_Std_Mutex_atomically___redArg(v___x_362_, v___f_368_, v___f_369_, v_activeConnections_364_, v___f_367_);
lean_inc_ref_n(v_a_360_, 4);
v___x_371_ = lean_apply_2(v___x_1520__overap_370_, v_a_360_, lean_box(0));
v___f_372_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5));
v___f_373_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_373_, 0, v_context_363_);
lean_closure_set(v___f_373_, 1, v_shutdownPromise_366_);
v___f_374_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed), 5, 1);
lean_closure_set(v___f_374_, 0, v___f_373_);
v___f_375_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6));
v___f_376_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed), 9, 6);
lean_closure_set(v___f_376_, 0, v___x_362_);
lean_closure_set(v___f_376_, 1, v___f_372_);
lean_closure_set(v___f_376_, 2, v___f_374_);
lean_closure_set(v___f_376_, 3, v___f_368_);
lean_closure_set(v___f_376_, 4, v___f_369_);
lean_closure_set(v___f_376_, 5, v_activeConnections_364_);
lean_inc_ref(v___f_376_);
v___f_377_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_377_, 0, v___f_376_);
lean_closure_set(v___f_377_, 1, v_a_360_);
v___x_378_ = lean_box(v_releaseConnectionPermit_358_);
v___f_379_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed), 7, 5);
lean_closure_set(v___f_379_, 0, v___x_378_);
lean_closure_set(v___f_379_, 1, v___f_376_);
lean_closure_set(v___f_379_, 2, v_a_360_);
lean_closure_set(v___f_379_, 3, v_connectionLimit_365_);
lean_closure_set(v___f_379_, 4, v___f_377_);
v___f_380_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed), 6, 4);
lean_closure_set(v___f_380_, 0, v_action_359_);
lean_closure_set(v___f_380_, 1, v_a_360_);
lean_closure_set(v___f_380_, 2, v___f_379_);
lean_closure_set(v___f_380_, 3, v___f_375_);
v___x_381_ = lean_unsigned_to_nat(0u);
v___x_382_ = 0;
v___x_383_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_381_, v___x_382_, v___x_371_, v___f_380_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___boxed(lean_object* v_s_384_, lean_object* v_releaseConnectionPermit_385_, lean_object* v_action_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
uint8_t v_releaseConnectionPermit_boxed_389_; lean_object* v_res_390_; 
v_releaseConnectionPermit_boxed_389_ = lean_unbox(v_releaseConnectionPermit_385_);
v_res_390_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg(v_s_384_, v_releaseConnectionPermit_boxed_389_, v_action_386_, v_a_387_);
lean_dec_ref(v_a_387_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation(lean_object* v_00_u03b1_391_, lean_object* v_s_392_, uint8_t v_releaseConnectionPermit_393_, lean_object* v_action_394_, lean_object* v_a_395_){
_start:
{
lean_object* v___x_397_; lean_object* v_context_398_; lean_object* v_activeConnections_399_; lean_object* v_connectionLimit_400_; lean_object* v_shutdownPromise_401_; lean_object* v___f_402_; lean_object* v___f_403_; lean_object* v___f_404_; lean_object* v___x_2130__overap_405_; lean_object* v___x_406_; lean_object* v___f_407_; lean_object* v___f_408_; lean_object* v___f_409_; lean_object* v___f_410_; lean_object* v___f_411_; lean_object* v___f_412_; lean_object* v___x_413_; lean_object* v___f_414_; lean_object* v___f_415_; lean_object* v___x_416_; uint8_t v___x_417_; lean_object* v___x_418_; 
v___x_397_ = l_Std_Async_ContextAsync_instMonad;
v_context_398_ = lean_ctor_get(v_s_392_, 0);
lean_inc_ref(v_context_398_);
v_activeConnections_399_ = lean_ctor_get(v_s_392_, 1);
lean_inc_ref_n(v_activeConnections_399_, 2);
v_connectionLimit_400_ = lean_ctor_get(v_s_392_, 2);
lean_inc(v_connectionLimit_400_);
v_shutdownPromise_401_ = lean_ctor_get(v_s_392_, 3);
lean_inc_ref(v_shutdownPromise_401_);
lean_dec_ref(v_s_392_);
v___f_402_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0));
v___f_403_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3));
v___f_404_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4));
v___x_2130__overap_405_ = l_Std_Mutex_atomically___redArg(v___x_397_, v___f_403_, v___f_404_, v_activeConnections_399_, v___f_402_);
lean_inc_ref_n(v_a_395_, 4);
v___x_406_ = lean_apply_2(v___x_2130__overap_405_, v_a_395_, lean_box(0));
v___f_407_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5));
v___f_408_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_408_, 0, v_context_398_);
lean_closure_set(v___f_408_, 1, v_shutdownPromise_401_);
v___f_409_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed), 5, 1);
lean_closure_set(v___f_409_, 0, v___f_408_);
v___f_410_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6));
v___f_411_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed), 9, 6);
lean_closure_set(v___f_411_, 0, v___x_397_);
lean_closure_set(v___f_411_, 1, v___f_407_);
lean_closure_set(v___f_411_, 2, v___f_409_);
lean_closure_set(v___f_411_, 3, v___f_403_);
lean_closure_set(v___f_411_, 4, v___f_404_);
lean_closure_set(v___f_411_, 5, v_activeConnections_399_);
lean_inc_ref(v___f_411_);
v___f_412_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_412_, 0, v___f_411_);
lean_closure_set(v___f_412_, 1, v_a_395_);
v___x_413_ = lean_box(v_releaseConnectionPermit_393_);
v___f_414_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed), 7, 5);
lean_closure_set(v___f_414_, 0, v___x_413_);
lean_closure_set(v___f_414_, 1, v___f_411_);
lean_closure_set(v___f_414_, 2, v_a_395_);
lean_closure_set(v___f_414_, 3, v_connectionLimit_400_);
lean_closure_set(v___f_414_, 4, v___f_412_);
v___f_415_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed), 6, 4);
lean_closure_set(v___f_415_, 0, v_action_394_);
lean_closure_set(v___f_415_, 1, v_a_395_);
lean_closure_set(v___f_415_, 2, v___f_414_);
lean_closure_set(v___f_415_, 3, v___f_410_);
v___x_416_ = lean_unsigned_to_nat(0u);
v___x_417_ = 0;
v___x_418_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_416_, v___x_417_, v___x_406_, v___f_415_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___boxed(lean_object* v_00_u03b1_419_, lean_object* v_s_420_, lean_object* v_releaseConnectionPermit_421_, lean_object* v_action_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
uint8_t v_releaseConnectionPermit_boxed_425_; lean_object* v_res_426_; 
v_releaseConnectionPermit_boxed_425_ = lean_unbox(v_releaseConnectionPermit_421_);
v_res_426_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation(v_00_u03b1_419_, v_s_420_, v_releaseConnectionPermit_boxed_425_, v_action_422_, v_a_423_);
lean_dec_ref(v_a_423_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__0(lean_object* v_x_427_){
_start:
{
if (lean_obj_tag(v_x_427_) == 0)
{
lean_object* v___x_429_; 
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v_x_427_);
return v___x_429_;
}
else
{
lean_object* v___x_430_; 
lean_dec_ref(v_x_427_);
v___x_430_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__0___boxed(lean_object* v_x_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_Http_Server_serve___redArg___lam__0(v_x_431_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2(lean_object* v_x_434_){
_start:
{
lean_object* v_fst_435_; 
v_fst_435_ = lean_ctor_get(v_x_434_, 0);
lean_inc(v_fst_435_);
return v_fst_435_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2___boxed(lean_object* v_x_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Std_Http_Server_serve___redArg___lam__2(v_x_436_);
lean_dec_ref(v_x_436_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3(lean_object* v_x_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__3___closed__1));
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3___boxed(lean_object* v_x_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Std_Http_Server_serve___redArg___lam__3(v_x_445_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1(lean_object* v_x_448_){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_450_, 0, v_x_448_);
v___x_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1___boxed(lean_object* v_x_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Std_Http_Server_serve___redArg___lam__1(v_x_453_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4(lean_object* v_x_456_){
_start:
{
if (lean_obj_tag(v_x_456_) == 0)
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_466_; 
v_a_458_ = lean_ctor_get(v_x_456_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v_x_456_);
if (v_isSharedCheck_466_ == 0)
{
v___x_460_ = v_x_456_;
v_isShared_461_ = v_isSharedCheck_466_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v_x_456_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_466_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_458_);
v___x_463_ = v_reuseFailAlloc_465_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_464_; 
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
return v___x_464_;
}
}
}
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_477_; 
v_a_467_ = lean_ctor_get(v_x_456_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v_x_456_);
if (v_isSharedCheck_477_ == 0)
{
v___x_469_ = v_x_456_;
v_isShared_470_ = v_isSharedCheck_477_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v_x_456_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_477_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v_token_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
v_token_471_ = lean_ctor_get(v_a_467_, 1);
lean_inc_ref(v_token_471_);
lean_dec(v_a_467_);
v___x_472_ = l_Std_CancellationToken_selector(v_token_471_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v___x_472_);
v___x_474_ = v___x_469_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_472_);
v___x_474_ = v_reuseFailAlloc_476_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
lean_object* v___x_475_; 
v___x_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
return v___x_475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4___boxed(lean_object* v_x_478_, lean_object* v___y_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Std_Http_Server_serve___redArg___lam__4(v_x_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6(lean_object* v_x_481_, lean_object* v_x_482_){
_start:
{
if (lean_obj_tag(v_x_482_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_492_; 
lean_dec_ref(v_x_481_);
v_a_484_ = lean_ctor_get(v_x_482_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v_x_482_);
if (v_isSharedCheck_492_ == 0)
{
v___x_486_ = v_x_482_;
v_isShared_487_ = v_isSharedCheck_492_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v_x_482_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_492_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_491_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_490_; 
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
}
else
{
lean_object* v___x_493_; 
lean_dec_ref(v_x_482_);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v_x_481_);
return v___x_493_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6___boxed(lean_object* v_x_494_, lean_object* v_x_495_, lean_object* v___y_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Std_Http_Server_serve___redArg___lam__6(v_x_494_, v_x_495_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7(lean_object* v_a_498_, lean_object* v_x_499_){
_start:
{
if (lean_obj_tag(v_x_499_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_509_; 
lean_dec_ref(v_a_498_);
v_a_501_ = lean_ctor_get(v_x_499_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v_x_499_);
if (v_isSharedCheck_509_ == 0)
{
v___x_503_ = v_x_499_;
v_isShared_504_ = v_isSharedCheck_509_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v_x_499_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_509_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_501_);
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
else
{
lean_object* v_context_510_; lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_527_; 
v_context_510_ = lean_ctor_get(v_a_498_, 0);
lean_inc_ref(v_context_510_);
v_a_511_ = lean_ctor_get(v_x_499_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v_x_499_);
if (v_isSharedCheck_527_ == 0)
{
v___x_513_ = v_x_499_;
v_isShared_514_ = v_isSharedCheck_527_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v_x_499_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_527_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v_shutdownPromise_515_; lean_object* v_token_516_; uint8_t v___x_517_; lean_object* v___f_518_; lean_object* v___x_519_; lean_object* v___x_521_; 
v_shutdownPromise_515_ = lean_ctor_get(v_a_498_, 3);
lean_inc_ref(v_shutdownPromise_515_);
lean_dec_ref(v_a_498_);
v_token_516_ = lean_ctor_get(v_context_510_, 1);
lean_inc_ref(v_token_516_);
lean_dec_ref(v_context_510_);
v___x_517_ = l_Std_CancellationToken_isCancelled(v_token_516_);
v___f_518_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_518_, 0, v_a_511_);
lean_closure_set(v___f_518_, 1, v_shutdownPromise_515_);
v___x_519_ = lean_box(v___x_517_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v___x_519_);
v___x_521_ = v___x_513_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_526_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; lean_object* v___x_525_; 
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
v___x_523_ = lean_unsigned_to_nat(0u);
v___x_524_ = 0;
v___x_525_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_523_, v___x_524_, v___x_522_, v___f_518_);
return v___x_525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7___boxed(lean_object* v_a_528_, lean_object* v_x_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Std_Http_Server_serve___redArg___lam__7(v_a_528_, v_x_529_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8(lean_object* v___x_532_, lean_object* v_____r_533_, lean_object* v___y_534_){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_532_);
v___x_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8___boxed(lean_object* v___x_539_, lean_object* v_____r_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Std_Http_Server_serve___redArg___lam__8(v___x_539_, v_____r_540_, v___y_541_);
lean_dec_ref(v___y_541_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5(lean_object* v___x_544_, lean_object* v_x_545_){
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
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5___boxed(lean_object* v___x_566_, lean_object* v_x_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Std_Http_Server_serve___redArg___lam__5(v___x_566_, v_x_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9(lean_object* v___f_570_, lean_object* v___y_571_, lean_object* v_x_572_){
_start:
{
if (lean_obj_tag(v_x_572_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_582_; 
lean_dec_ref(v___f_570_);
v_a_574_ = lean_ctor_get(v_x_572_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v_x_572_);
if (v_isSharedCheck_582_ == 0)
{
v___x_576_ = v_x_572_;
v_isShared_577_ = v_isSharedCheck_582_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v_x_572_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_582_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_581_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_580_; 
v___x_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
return v___x_580_;
}
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_584_; 
v_a_583_ = lean_ctor_get(v_x_572_, 0);
lean_inc(v_a_583_);
lean_dec_ref(v_x_572_);
lean_inc_ref(v___y_571_);
v___x_584_ = lean_apply_3(v___f_570_, v_a_583_, v___y_571_, lean_box(0));
return v___x_584_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9___boxed(lean_object* v___f_585_, lean_object* v___y_586_, lean_object* v_x_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Std_Http_Server_serve___redArg___lam__9(v___f_585_, v___y_586_, v_x_587_);
lean_dec_ref(v___y_586_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10(lean_object* v_a_590_, lean_object* v_x_591_){
_start:
{
if (lean_obj_tag(v_x_591_) == 0)
{
lean_object* v___x_593_; 
lean_dec_ref(v_a_590_);
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v_x_591_);
return v___x_593_;
}
else
{
lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_603_; 
v_isSharedCheck_603_ = !lean_is_exclusive(v_x_591_);
if (v_isSharedCheck_603_ == 0)
{
lean_object* v_unused_604_; 
v_unused_604_ = lean_ctor_get(v_x_591_, 0);
lean_dec(v_unused_604_);
v___x_595_ = v_x_591_;
v_isShared_596_ = v_isSharedCheck_603_;
goto v_resetjp_594_;
}
else
{
lean_dec(v_x_591_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_603_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_597_ = lean_box(2);
v___x_598_ = l_Std_CancellationContext_cancel(v_a_590_, v___x_597_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_598_);
v___x_600_ = v___x_595_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_602_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_601_; 
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
return v___x_601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10___boxed(lean_object* v_a_605_, lean_object* v_x_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Std_Http_Server_serve___redArg___lam__10(v_a_605_, v_x_606_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12(lean_object* v___f_609_, lean_object* v_a_610_, lean_object* v_x_611_){
_start:
{
if (lean_obj_tag(v_x_611_) == 0)
{
lean_object* v___x_613_; 
lean_dec_ref(v_a_610_);
lean_dec_ref(v___f_609_);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v_x_611_);
return v___x_613_;
}
else
{
lean_object* v_a_614_; lean_object* v___x_615_; 
v_a_614_ = lean_ctor_get(v_x_611_, 0);
lean_inc(v_a_614_);
lean_dec_ref(v_x_611_);
v___x_615_ = lean_apply_3(v___f_609_, v_a_614_, v_a_610_, lean_box(0));
return v___x_615_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12___boxed(lean_object* v___f_616_, lean_object* v_a_617_, lean_object* v_x_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Std_Http_Server_serve___redArg___lam__12(v___f_616_, v_a_617_, v_x_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11(uint8_t v_permitAcquired_621_, lean_object* v___f_622_, lean_object* v___x_623_, lean_object* v_a_624_, lean_object* v_connectionLimit_625_, lean_object* v___x_626_, uint8_t v___x_627_, lean_object* v___f_628_, lean_object* v_opt_629_){
_start:
{
if (v_permitAcquired_621_ == 0)
{
lean_object* v___x_631_; 
lean_dec_ref(v___f_628_);
lean_dec(v___x_626_);
lean_dec(v_connectionLimit_625_);
v___x_631_ = lean_apply_3(v___f_622_, v___x_623_, v_a_624_, lean_box(0));
return v___x_631_;
}
else
{
if (lean_obj_tag(v_connectionLimit_625_) == 1)
{
lean_object* v_val_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_642_; 
lean_dec_ref(v_a_624_);
lean_dec_ref(v___f_622_);
v_val_632_ = lean_ctor_get(v_connectionLimit_625_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v_connectionLimit_625_);
if (v_isSharedCheck_642_ == 0)
{
v___x_634_ = v_connectionLimit_625_;
v_isShared_635_ = v_isSharedCheck_642_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_val_632_);
lean_dec(v_connectionLimit_625_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_642_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_636_ = l_Std_Semaphore_release(v_val_632_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v___x_636_);
v___x_638_ = v___x_634_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_636_);
v___x_638_ = v_reuseFailAlloc_641_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
v___x_640_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_626_, v___x_627_, v___x_639_, v___f_628_);
return v___x_640_;
}
}
}
else
{
lean_object* v___x_643_; 
lean_dec_ref(v___f_628_);
lean_dec(v___x_626_);
lean_dec(v_connectionLimit_625_);
v___x_643_ = lean_apply_3(v___f_622_, v___x_623_, v_a_624_, lean_box(0));
return v___x_643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11___boxed(lean_object* v_permitAcquired_644_, lean_object* v___f_645_, lean_object* v___x_646_, lean_object* v_a_647_, lean_object* v_connectionLimit_648_, lean_object* v___x_649_, lean_object* v___x_650_, lean_object* v___f_651_, lean_object* v_opt_652_, lean_object* v___y_653_){
_start:
{
uint8_t v_permitAcquired_boxed_654_; uint8_t v___x_11148__boxed_655_; lean_object* v_res_656_; 
v_permitAcquired_boxed_654_ = lean_unbox(v_permitAcquired_644_);
v___x_11148__boxed_655_ = lean_unbox(v___x_650_);
v_res_656_ = l_Std_Http_Server_serve___redArg___lam__11(v_permitAcquired_boxed_654_, v___f_645_, v___x_646_, v_a_647_, v_connectionLimit_648_, v___x_649_, v___x_11148__boxed_655_, v___f_651_, v_opt_652_);
lean_dec(v_opt_652_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13(lean_object* v___x_657_, lean_object* v_inst_658_, lean_object* v_val_659_, lean_object* v_handler_660_, lean_object* v_config_661_, lean_object* v_extensions_662_, lean_object* v_a_663_, lean_object* v___f_664_, lean_object* v___x_665_, uint8_t v___x_666_, lean_object* v___f_667_, lean_object* v_x_668_){
_start:
{
if (lean_obj_tag(v_x_668_) == 0)
{
lean_object* v___x_670_; 
lean_dec_ref(v___f_667_);
lean_dec(v___x_665_);
lean_dec_ref(v___f_664_);
lean_dec_ref(v_a_663_);
lean_dec(v_extensions_662_);
lean_dec_ref(v_config_661_);
lean_dec(v_handler_660_);
lean_dec(v_val_659_);
lean_dec_ref(v_inst_658_);
lean_dec_ref(v___x_657_);
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v_x_668_);
return v___x_670_;
}
else
{
lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_709_; 
v_isSharedCheck_709_ = !lean_is_exclusive(v_x_668_);
if (v_isSharedCheck_709_ == 0)
{
lean_object* v_unused_710_; 
v_unused_710_ = lean_ctor_get(v_x_668_, 0);
lean_dec(v_unused_710_);
v___x_672_ = v_x_668_;
v_isShared_673_ = v_isSharedCheck_709_;
goto v_resetjp_671_;
}
else
{
lean_dec(v_x_668_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_709_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___y_677_; 
v___x_674_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___boxed), 10, 9);
lean_closure_set(v___x_674_, 0, lean_box(0));
lean_closure_set(v___x_674_, 1, lean_box(0));
lean_closure_set(v___x_674_, 2, v___x_657_);
lean_closure_set(v___x_674_, 3, v_inst_658_);
lean_closure_set(v___x_674_, 4, v_val_659_);
lean_closure_set(v___x_674_, 5, v_handler_660_);
lean_closure_set(v___x_674_, 6, v_config_661_);
lean_closure_set(v___x_674_, 7, v_extensions_662_);
lean_closure_set(v___x_674_, 8, v_a_663_);
lean_inc(v___x_665_);
v___x_675_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_674_, v___f_664_, v___x_665_, v___x_666_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_681_; 
lean_dec_ref(v___f_667_);
lean_dec(v___x_665_);
v_a_681_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_681_);
lean_dec_ref(v___x_675_);
if (lean_obj_tag(v_a_681_) == 0)
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
v_a_682_ = lean_ctor_get(v_a_681_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v_a_681_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v_a_681_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v_a_681_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
v___y_677_ = v___x_687_;
goto v___jp_676_;
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_698_; 
v_a_690_ = lean_ctor_get(v_a_681_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v_a_681_);
if (v_isSharedCheck_698_ == 0)
{
v___x_692_ = v_a_681_;
v_isShared_693_ = v_isSharedCheck_698_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v_a_681_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_698_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_fst_694_; lean_object* v___x_696_; 
v_fst_694_ = lean_ctor_get(v_a_690_, 0);
lean_inc(v_fst_694_);
lean_dec(v_a_690_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v_fst_694_);
v___x_696_ = v___x_692_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_fst_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
v___y_677_ = v___x_696_;
goto v___jp_676_;
}
}
}
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_708_; 
lean_del_object(v___x_672_);
v_a_699_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_708_ == 0)
{
v___x_701_ = v___x_675_;
v_isShared_702_ = v_isSharedCheck_708_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_675_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_708_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_703_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_703_, 0, lean_box(0));
lean_closure_set(v___x_703_, 1, lean_box(0));
lean_closure_set(v___x_703_, 2, lean_box(0));
lean_closure_set(v___x_703_, 3, v___f_667_);
v___x_704_ = lean_task_map(v___x_703_, v_a_699_, v___x_665_, v___x_666_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_704_);
v___x_706_ = v___x_701_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
v___jp_676_:
{
lean_object* v___x_679_; 
if (v_isShared_673_ == 0)
{
lean_ctor_set_tag(v___x_672_, 0);
lean_ctor_set(v___x_672_, 0, v___y_677_);
v___x_679_ = v___x_672_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___y_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13___boxed(lean_object* v___x_711_, lean_object* v_inst_712_, lean_object* v_val_713_, lean_object* v_handler_714_, lean_object* v_config_715_, lean_object* v_extensions_716_, lean_object* v_a_717_, lean_object* v___f_718_, lean_object* v___x_719_, lean_object* v___x_720_, lean_object* v___f_721_, lean_object* v_x_722_, lean_object* v___y_723_){
_start:
{
uint8_t v___x_11197__boxed_724_; lean_object* v_res_725_; 
v___x_11197__boxed_724_ = lean_unbox(v___x_720_);
v_res_725_ = l_Std_Http_Server_serve___redArg___lam__13(v___x_711_, v_inst_712_, v_val_713_, v_handler_714_, v_config_715_, v_extensions_716_, v_a_717_, v___f_718_, v___x_719_, v___x_11197__boxed_724_, v___f_721_, v_x_722_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14(lean_object* v___x_726_, lean_object* v_activeConnections_727_, lean_object* v___f_728_, lean_object* v_a_729_, lean_object* v___f_730_, lean_object* v___f_731_, uint8_t v_permitAcquired_732_, lean_object* v___x_733_, lean_object* v_connectionLimit_734_, lean_object* v___x_735_, uint8_t v___x_736_, lean_object* v___x_737_, lean_object* v_inst_738_, lean_object* v_val_739_, lean_object* v_handler_740_, lean_object* v_config_741_, lean_object* v_extensions_742_, lean_object* v___f_743_, lean_object* v___f_744_){
_start:
{
lean_object* v___f_746_; lean_object* v___f_747_; lean_object* v___x_10350__overap_748_; lean_object* v___x_749_; lean_object* v___f_750_; lean_object* v___f_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___f_754_; lean_object* v___x_755_; lean_object* v___f_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___f_746_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3));
v___f_747_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4));
lean_inc_ref(v_activeConnections_727_);
lean_inc_ref(v___x_726_);
v___x_10350__overap_748_ = l_Std_Mutex_atomically___redArg(v___x_726_, v___f_746_, v___f_747_, v_activeConnections_727_, v___f_728_);
lean_inc_ref_n(v_a_729_, 3);
v___x_749_ = lean_apply_2(v___x_10350__overap_748_, v_a_729_, lean_box(0));
v___f_750_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed), 9, 6);
lean_closure_set(v___f_750_, 0, v___x_726_);
lean_closure_set(v___f_750_, 1, v___f_730_);
lean_closure_set(v___f_750_, 2, v___f_731_);
lean_closure_set(v___f_750_, 3, v___f_746_);
lean_closure_set(v___f_750_, 4, v___f_747_);
lean_closure_set(v___f_750_, 5, v_activeConnections_727_);
lean_inc_ref(v___f_750_);
v___f_751_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__12___boxed), 4, 2);
lean_closure_set(v___f_751_, 0, v___f_750_);
lean_closure_set(v___f_751_, 1, v_a_729_);
v___x_752_ = lean_box(v_permitAcquired_732_);
v___x_753_ = lean_box(v___x_736_);
lean_inc_n(v___x_735_, 3);
v___f_754_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__11___boxed), 10, 8);
lean_closure_set(v___f_754_, 0, v___x_752_);
lean_closure_set(v___f_754_, 1, v___f_750_);
lean_closure_set(v___f_754_, 2, v___x_733_);
lean_closure_set(v___f_754_, 3, v_a_729_);
lean_closure_set(v___f_754_, 4, v_connectionLimit_734_);
lean_closure_set(v___f_754_, 5, v___x_735_);
lean_closure_set(v___f_754_, 6, v___x_753_);
lean_closure_set(v___f_754_, 7, v___f_751_);
v___x_755_ = lean_box(v___x_736_);
v___f_756_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__13___boxed), 13, 11);
lean_closure_set(v___f_756_, 0, v___x_737_);
lean_closure_set(v___f_756_, 1, v_inst_738_);
lean_closure_set(v___f_756_, 2, v_val_739_);
lean_closure_set(v___f_756_, 3, v_handler_740_);
lean_closure_set(v___f_756_, 4, v_config_741_);
lean_closure_set(v___f_756_, 5, v_extensions_742_);
lean_closure_set(v___f_756_, 6, v_a_729_);
lean_closure_set(v___f_756_, 7, v___f_754_);
lean_closure_set(v___f_756_, 8, v___x_735_);
lean_closure_set(v___f_756_, 9, v___x_755_);
lean_closure_set(v___f_756_, 10, v___f_743_);
v___x_757_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_735_, v___x_736_, v___x_749_, v___f_756_);
v___x_758_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_735_, v___x_736_, v___x_757_, v___f_744_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14___boxed(lean_object** _args){
lean_object* v___x_759_ = _args[0];
lean_object* v_activeConnections_760_ = _args[1];
lean_object* v___f_761_ = _args[2];
lean_object* v_a_762_ = _args[3];
lean_object* v___f_763_ = _args[4];
lean_object* v___f_764_ = _args[5];
lean_object* v_permitAcquired_765_ = _args[6];
lean_object* v___x_766_ = _args[7];
lean_object* v_connectionLimit_767_ = _args[8];
lean_object* v___x_768_ = _args[9];
lean_object* v___x_769_ = _args[10];
lean_object* v___x_770_ = _args[11];
lean_object* v_inst_771_ = _args[12];
lean_object* v_val_772_ = _args[13];
lean_object* v_handler_773_ = _args[14];
lean_object* v_config_774_ = _args[15];
lean_object* v_extensions_775_ = _args[16];
lean_object* v___f_776_ = _args[17];
lean_object* v___f_777_ = _args[18];
lean_object* v___y_778_ = _args[19];
_start:
{
uint8_t v_permitAcquired_boxed_779_; uint8_t v___x_11316__boxed_780_; lean_object* v_res_781_; 
v_permitAcquired_boxed_779_ = lean_unbox(v_permitAcquired_765_);
v___x_11316__boxed_780_ = lean_unbox(v___x_769_);
v_res_781_ = l_Std_Http_Server_serve___redArg___lam__14(v___x_759_, v_activeConnections_760_, v___f_761_, v_a_762_, v___f_763_, v___f_764_, v_permitAcquired_boxed_779_, v___x_766_, v_connectionLimit_767_, v___x_768_, v___x_11316__boxed_780_, v___x_770_, v_inst_771_, v_val_772_, v_handler_773_, v_config_774_, v_extensions_775_, v___f_776_, v___f_777_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15(lean_object* v___x_782_, lean_object* v_activeConnections_783_, lean_object* v___f_784_, lean_object* v___f_785_, lean_object* v___f_786_, uint8_t v_permitAcquired_787_, lean_object* v___x_788_, lean_object* v_connectionLimit_789_, lean_object* v___x_790_, uint8_t v___x_791_, lean_object* v___x_792_, lean_object* v_inst_793_, lean_object* v_val_794_, lean_object* v_handler_795_, lean_object* v_config_796_, lean_object* v_extensions_797_, lean_object* v___f_798_, lean_object* v_x_799_){
_start:
{
if (lean_obj_tag(v_x_799_) == 0)
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_809_; 
lean_dec_ref(v___f_798_);
lean_dec(v_extensions_797_);
lean_dec_ref(v_config_796_);
lean_dec(v_handler_795_);
lean_dec(v_val_794_);
lean_dec_ref(v_inst_793_);
lean_dec_ref(v___x_792_);
lean_dec(v___x_790_);
lean_dec(v_connectionLimit_789_);
lean_dec_ref(v___f_786_);
lean_dec_ref(v___f_785_);
lean_dec_ref(v___f_784_);
lean_dec_ref(v_activeConnections_783_);
lean_dec_ref(v___x_782_);
v_a_801_ = lean_ctor_get(v_x_799_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v_x_799_);
if (v_isSharedCheck_809_ == 0)
{
v___x_803_ = v_x_799_;
v_isShared_804_ = v_isSharedCheck_809_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v_x_799_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_809_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_801_);
v___x_806_ = v_reuseFailAlloc_808_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_807_; 
v___x_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
return v___x_807_;
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_824_; 
v_a_810_ = lean_ctor_get(v_x_799_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v_x_799_);
if (v_isSharedCheck_824_ == 0)
{
v___x_812_ = v_x_799_;
v_isShared_813_ = v_isSharedCheck_824_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v_x_799_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_824_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___f_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___f_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
lean_inc(v_a_810_);
v___f_814_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__10___boxed), 3, 1);
lean_closure_set(v___f_814_, 0, v_a_810_);
v___x_815_ = lean_box(v_permitAcquired_787_);
v___x_816_ = lean_box(v___x_791_);
lean_inc(v___x_790_);
v___f_817_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__14___boxed), 20, 19);
lean_closure_set(v___f_817_, 0, v___x_782_);
lean_closure_set(v___f_817_, 1, v_activeConnections_783_);
lean_closure_set(v___f_817_, 2, v___f_784_);
lean_closure_set(v___f_817_, 3, v_a_810_);
lean_closure_set(v___f_817_, 4, v___f_785_);
lean_closure_set(v___f_817_, 5, v___f_786_);
lean_closure_set(v___f_817_, 6, v___x_815_);
lean_closure_set(v___f_817_, 7, v___x_788_);
lean_closure_set(v___f_817_, 8, v_connectionLimit_789_);
lean_closure_set(v___f_817_, 9, v___x_790_);
lean_closure_set(v___f_817_, 10, v___x_816_);
lean_closure_set(v___f_817_, 11, v___x_792_);
lean_closure_set(v___f_817_, 12, v_inst_793_);
lean_closure_set(v___f_817_, 13, v_val_794_);
lean_closure_set(v___f_817_, 14, v_handler_795_);
lean_closure_set(v___f_817_, 15, v_config_796_);
lean_closure_set(v___f_817_, 16, v_extensions_797_);
lean_closure_set(v___f_817_, 17, v___f_798_);
lean_closure_set(v___f_817_, 18, v___f_814_);
v___x_818_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_818_, 0, lean_box(0));
lean_closure_set(v___x_818_, 1, v___f_817_);
v___x_819_ = lean_io_as_task(v___x_818_, v___x_790_);
lean_dec_ref(v___x_819_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v___x_788_);
v___x_821_ = v___x_812_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_788_);
v___x_821_ = v_reuseFailAlloc_823_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_822_; 
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
return v___x_822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15___boxed(lean_object** _args){
lean_object* v___x_825_ = _args[0];
lean_object* v_activeConnections_826_ = _args[1];
lean_object* v___f_827_ = _args[2];
lean_object* v___f_828_ = _args[3];
lean_object* v___f_829_ = _args[4];
lean_object* v_permitAcquired_830_ = _args[5];
lean_object* v___x_831_ = _args[6];
lean_object* v_connectionLimit_832_ = _args[7];
lean_object* v___x_833_ = _args[8];
lean_object* v___x_834_ = _args[9];
lean_object* v___x_835_ = _args[10];
lean_object* v_inst_836_ = _args[11];
lean_object* v_val_837_ = _args[12];
lean_object* v_handler_838_ = _args[13];
lean_object* v_config_839_ = _args[14];
lean_object* v_extensions_840_ = _args[15];
lean_object* v___f_841_ = _args[16];
lean_object* v_x_842_ = _args[17];
lean_object* v___y_843_ = _args[18];
_start:
{
uint8_t v_permitAcquired_boxed_844_; uint8_t v___x_11383__boxed_845_; lean_object* v_res_846_; 
v_permitAcquired_boxed_844_ = lean_unbox(v_permitAcquired_830_);
v___x_11383__boxed_845_ = lean_unbox(v___x_834_);
v_res_846_ = l_Std_Http_Server_serve___redArg___lam__15(v___x_825_, v_activeConnections_826_, v___f_827_, v___f_828_, v___f_829_, v_permitAcquired_boxed_844_, v___x_831_, v_connectionLimit_832_, v___x_833_, v___x_11383__boxed_845_, v___x_835_, v_inst_836_, v_val_837_, v_handler_838_, v_config_839_, v_extensions_840_, v___f_841_, v_x_842_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16(lean_object* v___x_847_, uint8_t v___x_848_, lean_object* v___f_849_, lean_object* v_x_850_){
_start:
{
if (lean_obj_tag(v_x_850_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_860_; 
lean_dec_ref(v___f_849_);
lean_dec(v___x_847_);
v_a_852_ = lean_ctor_get(v_x_850_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v_x_850_);
if (v_isSharedCheck_860_ == 0)
{
v___x_854_ = v_x_850_;
v_isShared_855_ = v_isSharedCheck_860_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v_x_850_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_860_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_859_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; 
v___x_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
return v___x_858_;
}
}
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_871_; 
v_a_861_ = lean_ctor_get(v_x_850_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v_x_850_);
if (v_isSharedCheck_871_ == 0)
{
v___x_863_ = v_x_850_;
v_isShared_864_ = v_isSharedCheck_871_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v_x_850_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_871_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v___x_867_; 
v___x_865_ = l_Std_CancellationContext_fork(v_a_861_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_865_);
v___x_867_ = v___x_863_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_865_);
v___x_867_ = v_reuseFailAlloc_870_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
v___x_869_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_847_, v___x_848_, v___x_868_, v___f_849_);
return v___x_869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16___boxed(lean_object* v___x_872_, lean_object* v___x_873_, lean_object* v___f_874_, lean_object* v_x_875_, lean_object* v___y_876_){
_start:
{
uint8_t v___x_11465__boxed_877_; lean_object* v_res_878_; 
v___x_11465__boxed_877_ = lean_unbox(v___x_873_);
v_res_878_ = l_Std_Http_Server_serve___redArg___lam__16(v___x_872_, v___x_11465__boxed_877_, v___f_874_, v_x_875_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17(lean_object* v___x_879_, lean_object* v_activeConnections_880_, lean_object* v___f_881_, lean_object* v___f_882_, lean_object* v___f_883_, uint8_t v_permitAcquired_884_, lean_object* v___x_885_, lean_object* v_connectionLimit_886_, uint8_t v___x_887_, lean_object* v_inst_888_, lean_object* v_val_889_, lean_object* v_handler_890_, lean_object* v_config_891_, lean_object* v___f_892_, lean_object* v___f_893_, lean_object* v_extensions_894_, lean_object* v___y_895_){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___f_901_; lean_object* v___x_902_; lean_object* v___f_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_897_ = l_Std_Http_instTransportClient;
v___x_898_ = lean_unsigned_to_nat(0u);
v___x_899_ = lean_box(v_permitAcquired_884_);
v___x_900_ = lean_box(v___x_887_);
v___f_901_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__15___boxed), 19, 17);
lean_closure_set(v___f_901_, 0, v___x_879_);
lean_closure_set(v___f_901_, 1, v_activeConnections_880_);
lean_closure_set(v___f_901_, 2, v___f_881_);
lean_closure_set(v___f_901_, 3, v___f_882_);
lean_closure_set(v___f_901_, 4, v___f_883_);
lean_closure_set(v___f_901_, 5, v___x_899_);
lean_closure_set(v___f_901_, 6, v___x_885_);
lean_closure_set(v___f_901_, 7, v_connectionLimit_886_);
lean_closure_set(v___f_901_, 8, v___x_898_);
lean_closure_set(v___f_901_, 9, v___x_900_);
lean_closure_set(v___f_901_, 10, v___x_897_);
lean_closure_set(v___f_901_, 11, v_inst_888_);
lean_closure_set(v___f_901_, 12, v_val_889_);
lean_closure_set(v___f_901_, 13, v_handler_890_);
lean_closure_set(v___f_901_, 14, v_config_891_);
lean_closure_set(v___f_901_, 15, v_extensions_894_);
lean_closure_set(v___f_901_, 16, v___f_892_);
v___x_902_ = lean_box(v___x_887_);
v___f_903_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__16___boxed), 5, 3);
lean_closure_set(v___f_903_, 0, v___x_898_);
lean_closure_set(v___f_903_, 1, v___x_902_);
lean_closure_set(v___f_903_, 2, v___f_901_);
lean_inc_ref(v___y_895_);
v___x_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_904_, 0, v___y_895_);
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
v___x_906_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_898_, v___x_887_, v___x_905_, v___f_903_);
v___x_907_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_898_, v___x_887_, v___x_906_, v___f_893_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17___boxed(lean_object** _args){
lean_object* v___x_908_ = _args[0];
lean_object* v_activeConnections_909_ = _args[1];
lean_object* v___f_910_ = _args[2];
lean_object* v___f_911_ = _args[3];
lean_object* v___f_912_ = _args[4];
lean_object* v_permitAcquired_913_ = _args[5];
lean_object* v___x_914_ = _args[6];
lean_object* v_connectionLimit_915_ = _args[7];
lean_object* v___x_916_ = _args[8];
lean_object* v_inst_917_ = _args[9];
lean_object* v_val_918_ = _args[10];
lean_object* v_handler_919_ = _args[11];
lean_object* v_config_920_ = _args[12];
lean_object* v___f_921_ = _args[13];
lean_object* v___f_922_ = _args[14];
lean_object* v_extensions_923_ = _args[15];
lean_object* v___y_924_ = _args[16];
lean_object* v___y_925_ = _args[17];
_start:
{
uint8_t v_permitAcquired_boxed_926_; uint8_t v___x_11524__boxed_927_; lean_object* v_res_928_; 
v_permitAcquired_boxed_926_ = lean_unbox(v_permitAcquired_913_);
v___x_11524__boxed_927_ = lean_unbox(v___x_916_);
v_res_928_ = l_Std_Http_Server_serve___redArg___lam__17(v___x_908_, v_activeConnections_909_, v___f_910_, v___f_911_, v___f_912_, v_permitAcquired_boxed_926_, v___x_914_, v_connectionLimit_915_, v___x_11524__boxed_927_, v_inst_917_, v_val_918_, v_handler_919_, v_config_920_, v___f_921_, v___f_922_, v_extensions_923_, v___y_924_);
lean_dec_ref(v___y_924_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18(lean_object* v___f_929_, lean_object* v___y_930_, lean_object* v_x_931_){
_start:
{
if (lean_obj_tag(v_x_931_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_941_; 
lean_dec_ref(v___f_929_);
v_a_933_ = lean_ctor_get(v_x_931_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v_x_931_);
if (v_isSharedCheck_941_ == 0)
{
v___x_935_ = v_x_931_;
v_isShared_936_ = v_isSharedCheck_941_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v_x_931_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_941_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_940_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_939_; 
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
return v___x_939_;
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_943_; 
v_a_942_ = lean_ctor_get(v_x_931_, 0);
lean_inc(v_a_942_);
lean_dec_ref(v_x_931_);
lean_inc_ref(v___y_930_);
v___x_943_ = lean_apply_3(v___f_929_, v_a_942_, v___y_930_, lean_box(0));
return v___x_943_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18___boxed(lean_object* v___f_944_, lean_object* v___y_945_, lean_object* v_x_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Std_Http_Server_serve___redArg___lam__18(v___f_944_, v___y_945_, v_x_946_);
lean_dec_ref(v___y_945_);
return v_res_948_;
}
}
static lean_object* _init_l_Std_Http_Server_serve___redArg___lam__20___closed__0(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = l_Std_Http_Extensions_empty;
v___x_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
return v___x_950_;
}
}
static lean_object* _init_l_Std_Http_Server_serve___redArg___lam__20___closed__1(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = lean_obj_once(&l_Std_Http_Server_serve___redArg___lam__20___closed__0, &l_Std_Http_Server_serve___redArg___lam__20___closed__0_once, _init_l_Std_Http_Server_serve___redArg___lam__20___closed__0);
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20(uint8_t v___x_954_, lean_object* v___f_955_, lean_object* v___f_956_, lean_object* v_x_957_){
_start:
{
if (lean_obj_tag(v_x_957_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_967_; 
lean_dec_ref(v___f_956_);
lean_dec_ref(v___f_955_);
v_a_959_ = lean_ctor_get(v_x_957_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v_x_957_);
if (v_isSharedCheck_967_ == 0)
{
v___x_961_ = v_x_957_;
v_isShared_962_ = v_isSharedCheck_967_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v_x_957_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_967_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_959_);
v___x_964_ = v_reuseFailAlloc_966_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_965_; 
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
return v___x_965_;
}
}
}
else
{
lean_object* v_a_968_; 
v_a_968_ = lean_ctor_get(v_x_957_, 0);
lean_inc(v_a_968_);
lean_dec_ref(v_x_957_);
if (lean_obj_tag(v_a_968_) == 0)
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
lean_dec_ref(v_a_968_);
lean_dec_ref(v___f_956_);
v___x_969_ = lean_obj_once(&l_Std_Http_Server_serve___redArg___lam__20___closed__1, &l_Std_Http_Server_serve___redArg___lam__20___closed__1_once, _init_l_Std_Http_Server_serve___redArg___lam__20___closed__1);
v___x_970_ = lean_unsigned_to_nat(0u);
v___x_971_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_970_, v___x_954_, v___x_969_, v___f_955_);
return v___x_971_;
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_988_; 
lean_dec_ref(v___f_955_);
v_a_972_ = lean_ctor_get(v_a_968_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v_a_968_);
if (v_isSharedCheck_988_ == 0)
{
v___x_974_ = v_a_968_;
v_isShared_975_ = v_isSharedCheck_988_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v_a_968_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_988_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v_dyn_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_983_; 
v___x_976_ = l_Std_Http_Extensions_empty;
v___x_977_ = l_Std_Http_Server_instImpl_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8_;
v_dyn_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_978_, 0, v___x_977_);
lean_ctor_set(v_dyn_978_, 1, v_a_972_);
v___x_979_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__20___closed__2));
v___x_980_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_978_);
v___x_981_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_979_, v___x_980_, v_dyn_978_, v___x_976_);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v___x_981_);
v___x_983_ = v___x_974_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_981_);
v___x_983_ = v_reuseFailAlloc_987_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
v___x_985_ = lean_unsigned_to_nat(0u);
v___x_986_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_985_, v___x_954_, v___x_984_, v___f_956_);
return v___x_986_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20___boxed(lean_object* v___x_989_, lean_object* v___f_990_, lean_object* v___f_991_, lean_object* v_x_992_, lean_object* v___y_993_){
_start:
{
uint8_t v___x_11621__boxed_994_; lean_object* v_res_995_; 
v___x_11621__boxed_994_ = lean_unbox(v___x_989_);
v_res_995_ = l_Std_Http_Server_serve___redArg___lam__20(v___x_11621__boxed_994_, v___f_990_, v___f_991_, v_x_992_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__19(uint8_t v_permitAcquired_996_, lean_object* v___f_997_, lean_object* v___x_998_, lean_object* v___y_999_, lean_object* v_connectionLimit_1000_, uint8_t v___x_1001_, lean_object* v___f_1002_, lean_object* v___x_1003_, lean_object* v_activeConnections_1004_, lean_object* v___f_1005_, lean_object* v___f_1006_, lean_object* v___f_1007_, lean_object* v_inst_1008_, lean_object* v_handler_1009_, lean_object* v_config_1010_, lean_object* v___f_1011_, lean_object* v___f_1012_, lean_object* v_x_1013_){
_start:
{
if (lean_obj_tag(v_x_1013_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1023_; 
lean_dec_ref(v___f_1012_);
lean_dec_ref(v___f_1011_);
lean_dec_ref(v_config_1010_);
lean_dec(v_handler_1009_);
lean_dec_ref(v_inst_1008_);
lean_dec_ref(v___f_1007_);
lean_dec_ref(v___f_1006_);
lean_dec_ref(v___f_1005_);
lean_dec_ref(v_activeConnections_1004_);
lean_dec_ref(v___x_1003_);
lean_dec_ref(v___f_1002_);
lean_dec(v_connectionLimit_1000_);
lean_dec_ref(v___f_997_);
v_a_1015_ = lean_ctor_get(v_x_1013_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v_x_1013_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1017_ = v_x_1013_;
v_isShared_1018_ = v_isSharedCheck_1023_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v_x_1013_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1023_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
return v___x_1021_;
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1082_; 
v_a_1024_ = lean_ctor_get(v_x_1013_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_x_1013_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1026_ = v_x_1013_;
v_isShared_1027_ = v_isSharedCheck_1082_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v_x_1013_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1082_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
if (lean_obj_tag(v_a_1024_) == 0)
{
lean_dec_ref(v___f_1012_);
lean_dec_ref(v___f_1011_);
lean_dec_ref(v_config_1010_);
lean_dec(v_handler_1009_);
lean_dec_ref(v_inst_1008_);
lean_dec_ref(v___f_1007_);
lean_dec_ref(v___f_1006_);
lean_dec_ref(v___f_1005_);
lean_dec_ref(v_activeConnections_1004_);
lean_dec_ref(v___x_1003_);
if (v_permitAcquired_996_ == 0)
{
lean_object* v___x_1028_; 
lean_del_object(v___x_1026_);
lean_dec_ref(v___f_1002_);
lean_dec(v_connectionLimit_1000_);
lean_inc_ref(v___y_999_);
v___x_1028_ = lean_apply_3(v___f_997_, v___x_998_, v___y_999_, lean_box(0));
return v___x_1028_;
}
else
{
if (lean_obj_tag(v_connectionLimit_1000_) == 1)
{
lean_object* v_val_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1042_; 
lean_dec_ref(v___f_997_);
v_val_1029_ = lean_ctor_get(v_connectionLimit_1000_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v_connectionLimit_1000_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1031_ = v_connectionLimit_1000_;
v_isShared_1032_ = v_isSharedCheck_1042_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_val_1029_);
lean_dec(v_connectionLimit_1000_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1042_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; lean_object* v___x_1035_; 
v___x_1033_ = l_Std_Semaphore_release(v_val_1029_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1033_);
v___x_1035_ = v___x_1026_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1037_; 
if (v_isShared_1032_ == 0)
{
lean_ctor_set_tag(v___x_1031_, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1035_);
v___x_1037_ = v___x_1031_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = lean_unsigned_to_nat(0u);
v___x_1039_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1038_, v___x_1001_, v___x_1037_, v___f_1002_);
return v___x_1039_;
}
}
}
}
else
{
lean_object* v___x_1043_; 
lean_del_object(v___x_1026_);
lean_dec_ref(v___f_1002_);
lean_dec(v_connectionLimit_1000_);
lean_inc_ref(v___y_999_);
v___x_1043_ = lean_apply_3(v___f_997_, v___x_998_, v___y_999_, lean_box(0));
return v___x_1043_;
}
}
}
else
{
lean_object* v_val_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1081_; 
lean_dec_ref(v___f_1002_);
lean_dec_ref(v___f_997_);
v_val_1044_ = lean_ctor_get(v_a_1024_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_a_1024_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1046_ = v_a_1024_;
v_isShared_1047_ = v_isSharedCheck_1081_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_val_1044_);
lean_dec(v_a_1024_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1081_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___f_1050_; lean_object* v___f_1051_; lean_object* v___x_1052_; lean_object* v___f_1053_; lean_object* v_val_1055_; lean_object* v___x_1064_; 
v___x_1048_ = lean_box(v_permitAcquired_996_);
v___x_1049_ = lean_box(v___x_1001_);
lean_inc(v_val_1044_);
v___f_1050_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__17___boxed), 18, 15);
lean_closure_set(v___f_1050_, 0, v___x_1003_);
lean_closure_set(v___f_1050_, 1, v_activeConnections_1004_);
lean_closure_set(v___f_1050_, 2, v___f_1005_);
lean_closure_set(v___f_1050_, 3, v___f_1006_);
lean_closure_set(v___f_1050_, 4, v___f_1007_);
lean_closure_set(v___f_1050_, 5, v___x_1048_);
lean_closure_set(v___f_1050_, 6, v___x_998_);
lean_closure_set(v___f_1050_, 7, v_connectionLimit_1000_);
lean_closure_set(v___f_1050_, 8, v___x_1049_);
lean_closure_set(v___f_1050_, 9, v_inst_1008_);
lean_closure_set(v___f_1050_, 10, v_val_1044_);
lean_closure_set(v___f_1050_, 11, v_handler_1009_);
lean_closure_set(v___f_1050_, 12, v_config_1010_);
lean_closure_set(v___f_1050_, 13, v___f_1011_);
lean_closure_set(v___f_1050_, 14, v___f_1012_);
lean_inc_ref(v___y_999_);
v___f_1051_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__18___boxed), 4, 2);
lean_closure_set(v___f_1051_, 0, v___f_1050_);
lean_closure_set(v___f_1051_, 1, v___y_999_);
v___x_1052_ = lean_box(v___x_1001_);
lean_inc_ref(v___f_1051_);
v___f_1053_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__20___boxed), 5, 3);
lean_closure_set(v___f_1053_, 0, v___x_1052_);
lean_closure_set(v___f_1053_, 1, v___f_1051_);
lean_closure_set(v___f_1053_, 2, v___f_1051_);
v___x_1064_ = lean_uv_tcp_getpeername(v_val_1044_);
lean_dec(v_val_1044_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1064_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1064_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
lean_ctor_set_tag(v___x_1067_, 1);
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
v_val_1055_ = v___x_1070_;
goto v___jp_1054_;
}
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
v_a_1073_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1064_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1064_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
lean_ctor_set_tag(v___x_1075_, 0);
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
v_val_1055_ = v___x_1078_;
goto v___jp_1054_;
}
}
}
v___jp_1054_:
{
lean_object* v___x_1057_; 
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v_val_1055_);
v___x_1057_ = v___x_1026_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_val_1055_);
v___x_1057_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1059_; 
if (v_isShared_1047_ == 0)
{
lean_ctor_set_tag(v___x_1046_, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1057_);
v___x_1059_ = v___x_1046_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_unsigned_to_nat(0u);
v___x_1061_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1060_, v___x_1001_, v___x_1059_, v___f_1053_);
return v___x_1061_;
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
lean_object* v_permitAcquired_1083_ = _args[0];
lean_object* v___f_1084_ = _args[1];
lean_object* v___x_1085_ = _args[2];
lean_object* v___y_1086_ = _args[3];
lean_object* v_connectionLimit_1087_ = _args[4];
lean_object* v___x_1088_ = _args[5];
lean_object* v___f_1089_ = _args[6];
lean_object* v___x_1090_ = _args[7];
lean_object* v_activeConnections_1091_ = _args[8];
lean_object* v___f_1092_ = _args[9];
lean_object* v___f_1093_ = _args[10];
lean_object* v___f_1094_ = _args[11];
lean_object* v_inst_1095_ = _args[12];
lean_object* v_handler_1096_ = _args[13];
lean_object* v_config_1097_ = _args[14];
lean_object* v___f_1098_ = _args[15];
lean_object* v___f_1099_ = _args[16];
lean_object* v_x_1100_ = _args[17];
lean_object* v___y_1101_ = _args[18];
_start:
{
uint8_t v_permitAcquired_boxed_1102_; uint8_t v___x_11703__boxed_1103_; lean_object* v_res_1104_; 
v_permitAcquired_boxed_1102_ = lean_unbox(v_permitAcquired_1083_);
v___x_11703__boxed_1103_ = lean_unbox(v___x_1088_);
v_res_1104_ = l_Std_Http_Server_serve___redArg___lam__19(v_permitAcquired_boxed_1102_, v___f_1084_, v___x_1085_, v___y_1086_, v_connectionLimit_1087_, v___x_11703__boxed_1103_, v___f_1089_, v___x_1090_, v_activeConnections_1091_, v___f_1092_, v___f_1093_, v___f_1094_, v_inst_1095_, v_handler_1096_, v_config_1097_, v___f_1098_, v___f_1099_, v_x_1100_);
lean_dec_ref(v___y_1086_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21(lean_object* v_a_1105_, lean_object* v___f_1106_, lean_object* v___f_1107_, uint8_t v___x_1108_, lean_object* v___f_1109_, lean_object* v_x_1110_){
_start:
{
if (lean_obj_tag(v_x_1110_) == 0)
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1120_; 
lean_dec_ref(v___f_1109_);
lean_dec_ref(v___f_1107_);
lean_dec_ref(v___f_1106_);
lean_dec(v_a_1105_);
v_a_1112_ = lean_ctor_get(v_x_1110_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_x_1110_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1114_ = v_x_1110_;
v_isShared_1115_ = v_isSharedCheck_1120_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v_x_1110_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1120_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1118_; 
v___x_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
return v___x_1118_;
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v_a_1121_ = lean_ctor_get(v_x_1110_, 0);
lean_inc(v_a_1121_);
lean_dec_ref(v_x_1110_);
v___x_1122_ = l_Std_Async_TCP_Socket_Server_acceptSelector(v_a_1105_);
v___x_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
lean_ctor_set(v___x_1123_, 1, v___f_1106_);
v___x_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1124_, 0, v_a_1121_);
lean_ctor_set(v___x_1124_, 1, v___f_1107_);
v___x_1125_ = lean_unsigned_to_nat(2u);
v___x_1126_ = lean_mk_empty_array_with_capacity(v___x_1125_);
v___x_1127_ = lean_array_push(v___x_1126_, v___x_1123_);
v___x_1128_ = lean_array_push(v___x_1127_, v___x_1124_);
v___x_1129_ = l_Std_Async_Selectable_one___redArg(v___x_1128_);
v___x_1130_ = lean_unsigned_to_nat(0u);
v___x_1131_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1130_, v___x_1108_, v___x_1129_, v___f_1109_);
return v___x_1131_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21___boxed(lean_object* v_a_1132_, lean_object* v___f_1133_, lean_object* v___f_1134_, lean_object* v___x_1135_, lean_object* v___f_1136_, lean_object* v_x_1137_, lean_object* v___y_1138_){
_start:
{
uint8_t v___x_11881__boxed_1139_; lean_object* v_res_1140_; 
v___x_11881__boxed_1139_ = lean_unbox(v___x_1135_);
v_res_1140_ = l_Std_Http_Server_serve___redArg___lam__21(v_a_1132_, v___f_1133_, v___f_1134_, v___x_11881__boxed_1139_, v___f_1136_, v_x_1137_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22(uint8_t v___x_1141_, lean_object* v___f_1142_, lean_object* v___f_1143_, lean_object* v___x_1144_, lean_object* v_connectionLimit_1145_, lean_object* v___x_1146_, lean_object* v_activeConnections_1147_, lean_object* v___f_1148_, lean_object* v___f_1149_, lean_object* v___f_1150_, lean_object* v_inst_1151_, lean_object* v_handler_1152_, lean_object* v_config_1153_, lean_object* v___f_1154_, lean_object* v___f_1155_, lean_object* v_a_1156_, lean_object* v___f_1157_, lean_object* v___f_1158_, uint8_t v_permitAcquired_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___f_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___f_1169_; lean_object* v___x_1170_; lean_object* v___f_1171_; lean_object* v___x_1172_; 
lean_inc_ref_n(v___y_1160_, 3);
v___x_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___y_1160_);
v___x_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
v___x_1164_ = lean_unsigned_to_nat(0u);
v___x_1165_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1164_, v___x_1141_, v___x_1163_, v___f_1142_);
lean_inc_ref(v___f_1143_);
v___f_1166_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__9___boxed), 4, 2);
lean_closure_set(v___f_1166_, 0, v___f_1143_);
lean_closure_set(v___f_1166_, 1, v___y_1160_);
v___x_1167_ = lean_box(v_permitAcquired_1159_);
v___x_1168_ = lean_box(v___x_1141_);
v___f_1169_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__19___boxed), 19, 17);
lean_closure_set(v___f_1169_, 0, v___x_1167_);
lean_closure_set(v___f_1169_, 1, v___f_1143_);
lean_closure_set(v___f_1169_, 2, v___x_1144_);
lean_closure_set(v___f_1169_, 3, v___y_1160_);
lean_closure_set(v___f_1169_, 4, v_connectionLimit_1145_);
lean_closure_set(v___f_1169_, 5, v___x_1168_);
lean_closure_set(v___f_1169_, 6, v___f_1166_);
lean_closure_set(v___f_1169_, 7, v___x_1146_);
lean_closure_set(v___f_1169_, 8, v_activeConnections_1147_);
lean_closure_set(v___f_1169_, 9, v___f_1148_);
lean_closure_set(v___f_1169_, 10, v___f_1149_);
lean_closure_set(v___f_1169_, 11, v___f_1150_);
lean_closure_set(v___f_1169_, 12, v_inst_1151_);
lean_closure_set(v___f_1169_, 13, v_handler_1152_);
lean_closure_set(v___f_1169_, 14, v_config_1153_);
lean_closure_set(v___f_1169_, 15, v___f_1154_);
lean_closure_set(v___f_1169_, 16, v___f_1155_);
v___x_1170_ = lean_box(v___x_1141_);
v___f_1171_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__21___boxed), 7, 5);
lean_closure_set(v___f_1171_, 0, v_a_1156_);
lean_closure_set(v___f_1171_, 1, v___f_1157_);
lean_closure_set(v___f_1171_, 2, v___f_1158_);
lean_closure_set(v___f_1171_, 3, v___x_1170_);
lean_closure_set(v___f_1171_, 4, v___f_1169_);
v___x_1172_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1164_, v___x_1141_, v___x_1165_, v___f_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22___boxed(lean_object** _args){
lean_object* v___x_1173_ = _args[0];
lean_object* v___f_1174_ = _args[1];
lean_object* v___f_1175_ = _args[2];
lean_object* v___x_1176_ = _args[3];
lean_object* v_connectionLimit_1177_ = _args[4];
lean_object* v___x_1178_ = _args[5];
lean_object* v_activeConnections_1179_ = _args[6];
lean_object* v___f_1180_ = _args[7];
lean_object* v___f_1181_ = _args[8];
lean_object* v___f_1182_ = _args[9];
lean_object* v_inst_1183_ = _args[10];
lean_object* v_handler_1184_ = _args[11];
lean_object* v_config_1185_ = _args[12];
lean_object* v___f_1186_ = _args[13];
lean_object* v___f_1187_ = _args[14];
lean_object* v_a_1188_ = _args[15];
lean_object* v___f_1189_ = _args[16];
lean_object* v___f_1190_ = _args[17];
lean_object* v_permitAcquired_1191_ = _args[18];
lean_object* v___y_1192_ = _args[19];
lean_object* v___y_1193_ = _args[20];
_start:
{
uint8_t v___x_11939__boxed_1194_; uint8_t v_permitAcquired_boxed_1195_; lean_object* v_res_1196_; 
v___x_11939__boxed_1194_ = lean_unbox(v___x_1173_);
v_permitAcquired_boxed_1195_ = lean_unbox(v_permitAcquired_1191_);
v_res_1196_ = l_Std_Http_Server_serve___redArg___lam__22(v___x_11939__boxed_1194_, v___f_1174_, v___f_1175_, v___x_1176_, v_connectionLimit_1177_, v___x_1178_, v_activeConnections_1179_, v___f_1180_, v___f_1181_, v___f_1182_, v_inst_1183_, v_handler_1184_, v_config_1185_, v___f_1186_, v___f_1187_, v_a_1188_, v___f_1189_, v___f_1190_, v_permitAcquired_boxed_1195_, v___y_1192_);
lean_dec_ref(v___y_1192_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23(lean_object* v___f_1197_, lean_object* v___y_1198_, lean_object* v_x_1199_){
_start:
{
if (lean_obj_tag(v_x_1199_) == 0)
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1209_; 
lean_dec_ref(v___f_1197_);
v_a_1201_ = lean_ctor_get(v_x_1199_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_x_1199_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1203_ = v_x_1199_;
v_isShared_1204_ = v_isSharedCheck_1209_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v_x_1199_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1209_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
return v___x_1207_;
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1211_; 
v_a_1210_ = lean_ctor_get(v_x_1199_, 0);
lean_inc(v_a_1210_);
lean_dec_ref(v_x_1199_);
lean_inc_ref(v___y_1198_);
v___x_1211_ = lean_apply_3(v___f_1197_, v_a_1210_, v___y_1198_, lean_box(0));
return v___x_1211_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23___boxed(lean_object* v___f_1212_, lean_object* v___y_1213_, lean_object* v_x_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Std_Http_Server_serve___redArg___lam__23(v___f_1212_, v___y_1213_, v_x_1214_);
lean_dec_ref(v___y_1213_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24(uint8_t v___x_1217_, uint8_t v___x_1218_, lean_object* v___f_1219_, lean_object* v_x_1220_){
_start:
{
if (lean_obj_tag(v_x_1220_) == 0)
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1230_; 
lean_dec_ref(v___f_1219_);
v_a_1222_ = lean_ctor_get(v_x_1220_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_x_1220_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1224_ = v_x_1220_;
v_isShared_1225_ = v_isSharedCheck_1230_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v_x_1220_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1230_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
lean_object* v___x_1228_; 
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
return v___x_1228_;
}
}
}
else
{
lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1241_; 
v_isSharedCheck_1241_ = !lean_is_exclusive(v_x_1220_);
if (v_isSharedCheck_1241_ == 0)
{
lean_object* v_unused_1242_; 
v_unused_1242_ = lean_ctor_get(v_x_1220_, 0);
lean_dec(v_unused_1242_);
v___x_1232_ = v_x_1220_;
v_isShared_1233_ = v_isSharedCheck_1241_;
goto v_resetjp_1231_;
}
else
{
lean_dec(v_x_1220_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1241_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1234_; lean_object* v___x_1236_; 
v___x_1234_ = lean_box(v___x_1217_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 0, v___x_1234_);
v___x_1236_ = v___x_1232_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1234_);
v___x_1236_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
v___x_1238_ = lean_unsigned_to_nat(0u);
v___x_1239_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1238_, v___x_1218_, v___x_1237_, v___f_1219_);
return v___x_1239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24___boxed(lean_object* v___x_1243_, lean_object* v___x_1244_, lean_object* v___f_1245_, lean_object* v_x_1246_, lean_object* v___y_1247_){
_start:
{
uint8_t v___x_12043__boxed_1248_; uint8_t v___x_12044__boxed_1249_; lean_object* v_res_1250_; 
v___x_12043__boxed_1248_ = lean_unbox(v___x_1243_);
v___x_12044__boxed_1249_ = lean_unbox(v___x_1244_);
v_res_1250_ = l_Std_Http_Server_serve___redArg___lam__24(v___x_12043__boxed_1248_, v___x_12044__boxed_1249_, v___f_1245_, v_x_1246_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25(lean_object* v___f_1251_, uint8_t v___x_1252_, lean_object* v___f_1253_, lean_object* v_x_1254_){
_start:
{
if (lean_obj_tag(v_x_1254_) == 0)
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1264_; 
lean_dec_ref(v___f_1253_);
lean_dec_ref(v___f_1251_);
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
lean_object* v_a_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v_a_1265_ = lean_ctor_get(v_x_1254_, 0);
lean_inc(v_a_1265_);
lean_dec_ref(v_x_1254_);
v___x_1266_ = l_IO_Promise_result_x21___redArg(v_a_1265_);
lean_dec(v_a_1265_);
v___x_1267_ = lean_unsigned_to_nat(0u);
v___x_1268_ = lean_task_map(v___f_1251_, v___x_1266_, v___x_1267_, v___x_1252_);
v___x_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
v___x_1270_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1267_, v___x_1252_, v___x_1269_, v___f_1253_);
return v___x_1270_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25___boxed(lean_object* v___f_1271_, lean_object* v___x_1272_, lean_object* v___f_1273_, lean_object* v_x_1274_, lean_object* v___y_1275_){
_start:
{
uint8_t v___x_12102__boxed_1276_; lean_object* v_res_1277_; 
v___x_12102__boxed_1276_ = lean_unbox(v___x_1272_);
v_res_1277_ = l_Std_Http_Server_serve___redArg___lam__25(v___f_1271_, v___x_12102__boxed_1276_, v___f_1273_, v_x_1274_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27(lean_object* v_connectionLimit_1278_, lean_object* v___f_1279_, uint8_t v___x_1280_, lean_object* v___f_1281_, lean_object* v_x_1282_, lean_object* v_____s_1283_, lean_object* v___y_1284_){
_start:
{
if (lean_obj_tag(v_connectionLimit_1278_) == 1)
{
lean_object* v_val_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1304_; 
v_val_1286_ = lean_ctor_get(v_connectionLimit_1278_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v_connectionLimit_1278_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1288_ = v_connectionLimit_1278_;
v_isShared_1289_ = v_isSharedCheck_1304_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_val_1286_);
lean_dec(v_connectionLimit_1278_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1304_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; lean_object* v___f_1291_; uint8_t v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___f_1295_; lean_object* v___x_1296_; lean_object* v___f_1297_; lean_object* v___x_1299_; 
v___x_1290_ = l_Std_Semaphore_acquire(v_val_1286_);
lean_inc_ref(v___y_1284_);
v___f_1291_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__23___boxed), 4, 2);
lean_closure_set(v___f_1291_, 0, v___f_1279_);
lean_closure_set(v___f_1291_, 1, v___y_1284_);
v___x_1292_ = 1;
v___x_1293_ = lean_box(v___x_1292_);
v___x_1294_ = lean_box(v___x_1280_);
v___f_1295_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__24___boxed), 5, 3);
lean_closure_set(v___f_1295_, 0, v___x_1293_);
lean_closure_set(v___f_1295_, 1, v___x_1294_);
lean_closure_set(v___f_1295_, 2, v___f_1291_);
v___x_1296_ = lean_box(v___x_1280_);
v___f_1297_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__25___boxed), 5, 3);
lean_closure_set(v___f_1297_, 0, v___f_1281_);
lean_closure_set(v___f_1297_, 1, v___x_1296_);
lean_closure_set(v___f_1297_, 2, v___f_1295_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 0, v___x_1290_);
v___x_1299_ = v___x_1288_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1290_);
v___x_1299_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1302_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1301_, v___x_1280_, v___x_1300_, v___f_1297_);
return v___x_1302_;
}
}
}
else
{
lean_object* v___f_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_dec_ref(v___f_1281_);
lean_dec(v_connectionLimit_1278_);
lean_inc_ref(v___y_1284_);
v___f_1305_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__23___boxed), 4, 2);
lean_closure_set(v___f_1305_, 0, v___f_1279_);
lean_closure_set(v___f_1305_, 1, v___y_1284_);
v___x_1306_ = lean_box(v___x_1280_);
v___x_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
v___x_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
v___x_1309_ = lean_unsigned_to_nat(0u);
v___x_1310_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1309_, v___x_1280_, v___x_1308_, v___f_1305_);
return v___x_1310_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27___boxed(lean_object* v_connectionLimit_1311_, lean_object* v___f_1312_, lean_object* v___x_1313_, lean_object* v___f_1314_, lean_object* v_x_1315_, lean_object* v_____s_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
uint8_t v___x_12147__boxed_1319_; lean_object* v_res_1320_; 
v___x_12147__boxed_1319_ = lean_unbox(v___x_1313_);
v_res_1320_ = l_Std_Http_Server_serve___redArg___lam__27(v_connectionLimit_1311_, v___f_1312_, v___x_12147__boxed_1319_, v___f_1314_, v_x_1315_, v_____s_1316_, v___y_1317_);
lean_dec_ref(v___y_1317_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26(lean_object* v___x_1321_, lean_object* v___f_1322_, lean_object* v___x_1323_, uint8_t v___x_1324_, lean_object* v___f_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___x_10650__overap_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_10650__overap_1328_ = l___private_Init_While_0__Lean_Loop_forIn_loop(lean_box(0), lean_box(0), v___x_1321_, v___f_1322_, v___x_1323_);
v___x_1329_ = lean_apply_2(v___x_10650__overap_1328_, v___y_1326_, lean_box(0));
v___x_1330_ = lean_unsigned_to_nat(0u);
v___x_1331_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1330_, v___x_1324_, v___x_1329_, v___f_1325_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26___boxed(lean_object* v___x_1332_, lean_object* v___f_1333_, lean_object* v___x_1334_, lean_object* v___x_1335_, lean_object* v___f_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
uint8_t v___x_12220__boxed_1339_; lean_object* v_res_1340_; 
v___x_12220__boxed_1339_ = lean_unbox(v___x_1335_);
v_res_1340_ = l_Std_Http_Server_serve___redArg___lam__26(v___x_1332_, v___f_1333_, v___x_1334_, v___x_12220__boxed_1339_, v___f_1336_, v___y_1337_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28(lean_object* v_a_1345_, lean_object* v___f_1346_, lean_object* v___x_1347_, lean_object* v___f_1348_, lean_object* v___f_1349_, lean_object* v___f_1350_, lean_object* v_inst_1351_, lean_object* v_handler_1352_, lean_object* v_config_1353_, lean_object* v___f_1354_, lean_object* v_a_1355_, lean_object* v___f_1356_, lean_object* v___f_1357_, lean_object* v___f_1358_, lean_object* v___f_1359_, lean_object* v___f_1360_, lean_object* v_x_1361_){
_start:
{
if (lean_obj_tag(v_x_1361_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1371_; 
lean_dec_ref(v___f_1360_);
lean_dec_ref(v___f_1359_);
lean_dec_ref(v___f_1358_);
lean_dec_ref(v___f_1357_);
lean_dec_ref(v___f_1356_);
lean_dec(v_a_1355_);
lean_dec_ref(v___f_1354_);
lean_dec_ref(v_config_1353_);
lean_dec(v_handler_1352_);
lean_dec_ref(v_inst_1351_);
lean_dec_ref(v___f_1350_);
lean_dec_ref(v___f_1349_);
lean_dec_ref(v___f_1348_);
lean_dec_ref(v___x_1347_);
lean_dec_ref(v___f_1346_);
lean_dec_ref(v_a_1345_);
v_a_1363_ = lean_ctor_get(v_x_1361_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_x_1361_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1365_ = v_x_1361_;
v_isShared_1366_ = v_isSharedCheck_1371_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v_x_1361_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1371_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1369_; 
v___x_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
return v___x_1369_;
}
}
}
else
{
lean_object* v_context_1372_; lean_object* v_activeConnections_1373_; lean_object* v_connectionLimit_1374_; uint8_t v___x_1375_; lean_object* v___x_1376_; lean_object* v___f_1377_; lean_object* v___f_1378_; lean_object* v___x_1379_; lean_object* v___f_1380_; lean_object* v___x_1381_; lean_object* v___f_1382_; lean_object* v___x_1383_; lean_object* v___f_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
lean_dec_ref(v_x_1361_);
v_context_1372_ = lean_ctor_get(v_a_1345_, 0);
lean_inc_ref(v_context_1372_);
v_activeConnections_1373_ = lean_ctor_get(v_a_1345_, 1);
v_connectionLimit_1374_ = lean_ctor_get(v_a_1345_, 2);
v___x_1375_ = 0;
v___x_1376_ = lean_box(0);
v___f_1377_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__28___closed__0));
v___f_1378_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__28___closed__1));
v___x_1379_ = lean_box(v___x_1375_);
lean_inc_ref(v_activeConnections_1373_);
lean_inc_ref(v___x_1347_);
lean_inc_n(v_connectionLimit_1374_, 2);
v___f_1380_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__22___boxed), 21, 18);
lean_closure_set(v___f_1380_, 0, v___x_1379_);
lean_closure_set(v___f_1380_, 1, v___f_1346_);
lean_closure_set(v___f_1380_, 2, v___f_1377_);
lean_closure_set(v___f_1380_, 3, v___x_1376_);
lean_closure_set(v___f_1380_, 4, v_connectionLimit_1374_);
lean_closure_set(v___f_1380_, 5, v___x_1347_);
lean_closure_set(v___f_1380_, 6, v_activeConnections_1373_);
lean_closure_set(v___f_1380_, 7, v___f_1348_);
lean_closure_set(v___f_1380_, 8, v___f_1349_);
lean_closure_set(v___f_1380_, 9, v___f_1350_);
lean_closure_set(v___f_1380_, 10, v_inst_1351_);
lean_closure_set(v___f_1380_, 11, v_handler_1352_);
lean_closure_set(v___f_1380_, 12, v_config_1353_);
lean_closure_set(v___f_1380_, 13, v___f_1354_);
lean_closure_set(v___f_1380_, 14, v___f_1378_);
lean_closure_set(v___f_1380_, 15, v_a_1355_);
lean_closure_set(v___f_1380_, 16, v___f_1356_);
lean_closure_set(v___f_1380_, 17, v___f_1357_);
v___x_1381_ = lean_box(v___x_1375_);
v___f_1382_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__27___boxed), 8, 4);
lean_closure_set(v___f_1382_, 0, v_connectionLimit_1374_);
lean_closure_set(v___f_1382_, 1, v___f_1380_);
lean_closure_set(v___f_1382_, 2, v___x_1381_);
lean_closure_set(v___f_1382_, 3, v___f_1358_);
v___x_1383_ = lean_box(v___x_1375_);
v___f_1384_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__26___boxed), 7, 5);
lean_closure_set(v___f_1384_, 0, v___x_1347_);
lean_closure_set(v___f_1384_, 1, v___f_1382_);
lean_closure_set(v___f_1384_, 2, v___x_1376_);
lean_closure_set(v___f_1384_, 3, v___x_1383_);
lean_closure_set(v___f_1384_, 4, v___f_1359_);
v___x_1385_ = lean_box(v___x_1375_);
v___x_1386_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___boxed), 6, 5);
lean_closure_set(v___x_1386_, 0, lean_box(0));
lean_closure_set(v___x_1386_, 1, v_a_1345_);
lean_closure_set(v___x_1386_, 2, v___x_1385_);
lean_closure_set(v___x_1386_, 3, v___f_1384_);
lean_closure_set(v___x_1386_, 4, v_context_1372_);
v___x_1387_ = lean_unsigned_to_nat(0u);
v___x_1388_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1388_, 0, lean_box(0));
lean_closure_set(v___x_1388_, 1, v___x_1386_);
v___x_1389_ = lean_io_as_task(v___x_1388_, v___x_1387_);
lean_dec_ref(v___x_1389_);
v___x_1390_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
v___x_1391_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1387_, v___x_1375_, v___x_1390_, v___f_1360_);
return v___x_1391_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28___boxed(lean_object** _args){
lean_object* v_a_1392_ = _args[0];
lean_object* v___f_1393_ = _args[1];
lean_object* v___x_1394_ = _args[2];
lean_object* v___f_1395_ = _args[3];
lean_object* v___f_1396_ = _args[4];
lean_object* v___f_1397_ = _args[5];
lean_object* v_inst_1398_ = _args[6];
lean_object* v_handler_1399_ = _args[7];
lean_object* v_config_1400_ = _args[8];
lean_object* v___f_1401_ = _args[9];
lean_object* v_a_1402_ = _args[10];
lean_object* v___f_1403_ = _args[11];
lean_object* v___f_1404_ = _args[12];
lean_object* v___f_1405_ = _args[13];
lean_object* v___f_1406_ = _args[14];
lean_object* v___f_1407_ = _args[15];
lean_object* v_x_1408_ = _args[16];
lean_object* v___y_1409_ = _args[17];
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Std_Http_Server_serve___redArg___lam__28(v_a_1392_, v___f_1393_, v___x_1394_, v___f_1395_, v___f_1396_, v___f_1397_, v_inst_1398_, v_handler_1399_, v_config_1400_, v___f_1401_, v_a_1402_, v___f_1403_, v___f_1404_, v___f_1405_, v___f_1406_, v___f_1407_, v_x_1408_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29(lean_object* v___f_1411_, lean_object* v_a_1412_, lean_object* v_x_1413_){
_start:
{
lean_object* v_val_1416_; 
if (lean_obj_tag(v_x_1413_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1429_; 
lean_dec_ref(v___f_1411_);
v_a_1421_ = lean_ctor_get(v_x_1413_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_x_1413_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1423_ = v_x_1413_;
v_isShared_1424_ = v_isSharedCheck_1429_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v_x_1413_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1429_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1427_; 
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
return v___x_1427_;
}
}
}
else
{
lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1442_; 
v_isSharedCheck_1442_ = !lean_is_exclusive(v_x_1413_);
if (v_isSharedCheck_1442_ == 0)
{
lean_object* v_unused_1443_; 
v_unused_1443_ = lean_ctor_get(v_x_1413_, 0);
lean_dec(v_unused_1443_);
v___x_1431_ = v_x_1413_;
v_isShared_1432_ = v_isSharedCheck_1442_;
goto v_resetjp_1430_;
}
else
{
lean_dec(v_x_1413_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1442_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_uv_tcp_nodelay(v_a_1412_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1436_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref(v___x_1433_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v_a_1434_);
v___x_1436_ = v___x_1431_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
v_val_1416_ = v___x_1436_;
goto v___jp_1415_;
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; 
v_a_1438_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1438_);
lean_dec_ref(v___x_1433_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set_tag(v___x_1431_, 0);
lean_ctor_set(v___x_1431_, 0, v_a_1438_);
v___x_1440_ = v___x_1431_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
v_val_1416_ = v___x_1440_;
goto v___jp_1415_;
}
}
}
}
v___jp_1415_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; lean_object* v___x_1420_; 
v___x_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1417_, 0, v_val_1416_);
v___x_1418_ = lean_unsigned_to_nat(0u);
v___x_1419_ = 0;
v___x_1420_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1418_, v___x_1419_, v___x_1417_, v___f_1411_);
return v___x_1420_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29___boxed(lean_object* v___f_1444_, lean_object* v_a_1445_, lean_object* v_x_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Std_Http_Server_serve___redArg___lam__29(v___f_1444_, v_a_1445_, v_x_1446_);
lean_dec(v_a_1445_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30(lean_object* v___f_1449_, lean_object* v_a_1450_, uint32_t v_backlog_1451_, lean_object* v_x_1452_){
_start:
{
lean_object* v_val_1455_; 
if (lean_obj_tag(v_x_1452_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1468_; 
lean_dec_ref(v___f_1449_);
v_a_1460_ = lean_ctor_get(v_x_1452_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_x_1452_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1462_ = v_x_1452_;
v_isShared_1463_ = v_isSharedCheck_1468_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v_x_1452_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1468_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
lean_object* v___x_1466_; 
v___x_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
return v___x_1466_;
}
}
}
else
{
lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1481_; 
v_isSharedCheck_1481_ = !lean_is_exclusive(v_x_1452_);
if (v_isSharedCheck_1481_ == 0)
{
lean_object* v_unused_1482_; 
v_unused_1482_ = lean_ctor_get(v_x_1452_, 0);
lean_dec(v_unused_1482_);
v___x_1470_ = v_x_1452_;
v_isShared_1471_ = v_isSharedCheck_1481_;
goto v_resetjp_1469_;
}
else
{
lean_dec(v_x_1452_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1481_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; 
v___x_1472_ = lean_uv_tcp_listen(v_a_1450_, v_backlog_1451_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1475_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref(v___x_1472_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 0, v_a_1473_);
v___x_1475_ = v___x_1470_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1473_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
v_val_1455_ = v___x_1475_;
goto v___jp_1454_;
}
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1479_; 
v_a_1477_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1477_);
lean_dec_ref(v___x_1472_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set_tag(v___x_1470_, 0);
lean_ctor_set(v___x_1470_, 0, v_a_1477_);
v___x_1479_ = v___x_1470_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1477_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
v_val_1455_ = v___x_1479_;
goto v___jp_1454_;
}
}
}
}
v___jp_1454_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; lean_object* v___x_1459_; 
v___x_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1456_, 0, v_val_1455_);
v___x_1457_ = lean_unsigned_to_nat(0u);
v___x_1458_ = 0;
v___x_1459_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1457_, v___x_1458_, v___x_1456_, v___f_1449_);
return v___x_1459_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30___boxed(lean_object* v___f_1483_, lean_object* v_a_1484_, lean_object* v_backlog_1485_, lean_object* v_x_1486_, lean_object* v___y_1487_){
_start:
{
uint32_t v_backlog_boxed_1488_; lean_object* v_res_1489_; 
v_backlog_boxed_1488_ = lean_unbox_uint32(v_backlog_1485_);
lean_dec(v_backlog_1485_);
v_res_1489_ = l_Std_Http_Server_serve___redArg___lam__30(v___f_1483_, v_a_1484_, v_backlog_boxed_1488_, v_x_1486_);
lean_dec(v_a_1484_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31(lean_object* v_a_1490_, lean_object* v___f_1491_, lean_object* v___x_1492_, lean_object* v___f_1493_, lean_object* v___f_1494_, lean_object* v___f_1495_, lean_object* v_inst_1496_, lean_object* v_handler_1497_, lean_object* v_config_1498_, lean_object* v___f_1499_, lean_object* v___f_1500_, lean_object* v___f_1501_, lean_object* v___f_1502_, lean_object* v___f_1503_, lean_object* v___f_1504_, uint32_t v_backlog_1505_, lean_object* v_addr_1506_, lean_object* v_x_1507_){
_start:
{
if (lean_obj_tag(v_x_1507_) == 0)
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1517_; 
lean_dec_ref(v___f_1504_);
lean_dec_ref(v___f_1503_);
lean_dec_ref(v___f_1502_);
lean_dec_ref(v___f_1501_);
lean_dec_ref(v___f_1500_);
lean_dec_ref(v___f_1499_);
lean_dec_ref(v_config_1498_);
lean_dec(v_handler_1497_);
lean_dec_ref(v_inst_1496_);
lean_dec_ref(v___f_1495_);
lean_dec_ref(v___f_1494_);
lean_dec_ref(v___f_1493_);
lean_dec_ref(v___x_1492_);
lean_dec_ref(v___f_1491_);
lean_dec_ref(v_a_1490_);
v_a_1509_ = lean_ctor_get(v_x_1507_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_x_1507_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1511_ = v_x_1507_;
v_isShared_1512_ = v_isSharedCheck_1517_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v_x_1507_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1517_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1515_; 
v___x_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
return v___x_1515_;
}
}
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1541_; 
v_a_1518_ = lean_ctor_get(v_x_1507_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_x_1507_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1520_ = v_x_1507_;
v_isShared_1521_ = v_isSharedCheck_1541_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v_x_1507_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1541_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___f_1522_; lean_object* v___f_1523_; lean_object* v___x_1524_; lean_object* v___f_1525_; lean_object* v_val_1527_; lean_object* v___x_1532_; 
lean_inc_n(v_a_1518_, 3);
v___f_1522_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__28___boxed), 18, 16);
lean_closure_set(v___f_1522_, 0, v_a_1490_);
lean_closure_set(v___f_1522_, 1, v___f_1491_);
lean_closure_set(v___f_1522_, 2, v___x_1492_);
lean_closure_set(v___f_1522_, 3, v___f_1493_);
lean_closure_set(v___f_1522_, 4, v___f_1494_);
lean_closure_set(v___f_1522_, 5, v___f_1495_);
lean_closure_set(v___f_1522_, 6, v_inst_1496_);
lean_closure_set(v___f_1522_, 7, v_handler_1497_);
lean_closure_set(v___f_1522_, 8, v_config_1498_);
lean_closure_set(v___f_1522_, 9, v___f_1499_);
lean_closure_set(v___f_1522_, 10, v_a_1518_);
lean_closure_set(v___f_1522_, 11, v___f_1500_);
lean_closure_set(v___f_1522_, 12, v___f_1501_);
lean_closure_set(v___f_1522_, 13, v___f_1502_);
lean_closure_set(v___f_1522_, 14, v___f_1503_);
lean_closure_set(v___f_1522_, 15, v___f_1504_);
v___f_1523_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__29___boxed), 4, 2);
lean_closure_set(v___f_1523_, 0, v___f_1522_);
lean_closure_set(v___f_1523_, 1, v_a_1518_);
v___x_1524_ = lean_box_uint32(v_backlog_1505_);
v___f_1525_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__30___boxed), 5, 3);
lean_closure_set(v___f_1525_, 0, v___f_1523_);
lean_closure_set(v___f_1525_, 1, v_a_1518_);
lean_closure_set(v___f_1525_, 2, v___x_1524_);
v___x_1532_ = lean_uv_tcp_bind(v_a_1518_, v_addr_1506_);
lean_dec(v_a_1518_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v___x_1535_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref(v___x_1532_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v_a_1533_);
v___x_1535_ = v___x_1520_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
v_val_1527_ = v___x_1535_;
goto v___jp_1526_;
}
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; 
v_a_1537_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1537_);
lean_dec_ref(v___x_1532_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set_tag(v___x_1520_, 0);
lean_ctor_set(v___x_1520_, 0, v_a_1537_);
v___x_1539_ = v___x_1520_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1537_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
v_val_1527_ = v___x_1539_;
goto v___jp_1526_;
}
}
v___jp_1526_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; lean_object* v___x_1531_; 
v___x_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1528_, 0, v_val_1527_);
v___x_1529_ = lean_unsigned_to_nat(0u);
v___x_1530_ = 0;
v___x_1531_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1529_, v___x_1530_, v___x_1528_, v___f_1525_);
return v___x_1531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31___boxed(lean_object** _args){
lean_object* v_a_1542_ = _args[0];
lean_object* v___f_1543_ = _args[1];
lean_object* v___x_1544_ = _args[2];
lean_object* v___f_1545_ = _args[3];
lean_object* v___f_1546_ = _args[4];
lean_object* v___f_1547_ = _args[5];
lean_object* v_inst_1548_ = _args[6];
lean_object* v_handler_1549_ = _args[7];
lean_object* v_config_1550_ = _args[8];
lean_object* v___f_1551_ = _args[9];
lean_object* v___f_1552_ = _args[10];
lean_object* v___f_1553_ = _args[11];
lean_object* v___f_1554_ = _args[12];
lean_object* v___f_1555_ = _args[13];
lean_object* v___f_1556_ = _args[14];
lean_object* v_backlog_1557_ = _args[15];
lean_object* v_addr_1558_ = _args[16];
lean_object* v_x_1559_ = _args[17];
lean_object* v___y_1560_ = _args[18];
_start:
{
uint32_t v_backlog_boxed_1561_; lean_object* v_res_1562_; 
v_backlog_boxed_1561_ = lean_unbox_uint32(v_backlog_1557_);
lean_dec(v_backlog_1557_);
v_res_1562_ = l_Std_Http_Server_serve___redArg___lam__31(v_a_1542_, v___f_1543_, v___x_1544_, v___f_1545_, v___f_1546_, v___f_1547_, v_inst_1548_, v_handler_1549_, v_config_1550_, v___f_1551_, v___f_1552_, v___f_1553_, v___f_1554_, v___f_1555_, v___f_1556_, v_backlog_boxed_1561_, v_addr_1558_, v_x_1559_);
lean_dec_ref(v_addr_1558_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32(lean_object* v___f_1563_, lean_object* v___x_1564_, lean_object* v___f_1565_, lean_object* v___f_1566_, lean_object* v_inst_1567_, lean_object* v_handler_1568_, lean_object* v_config_1569_, lean_object* v___f_1570_, lean_object* v___f_1571_, lean_object* v___f_1572_, lean_object* v___f_1573_, lean_object* v___f_1574_, uint32_t v_backlog_1575_, lean_object* v_addr_1576_, lean_object* v_x_1577_){
_start:
{
if (lean_obj_tag(v_x_1577_) == 0)
{
lean_object* v___x_1579_; 
lean_dec_ref(v_addr_1576_);
lean_dec_ref(v___f_1574_);
lean_dec_ref(v___f_1573_);
lean_dec_ref(v___f_1572_);
lean_dec_ref(v___f_1571_);
lean_dec_ref(v___f_1570_);
lean_dec_ref(v_config_1569_);
lean_dec(v_handler_1568_);
lean_dec_ref(v_inst_1567_);
lean_dec_ref(v___f_1566_);
lean_dec_ref(v___f_1565_);
lean_dec_ref(v___x_1564_);
lean_dec_ref(v___f_1563_);
v___x_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1579_, 0, v_x_1577_);
return v___x_1579_;
}
else
{
lean_object* v_a_1580_; lean_object* v___f_1581_; lean_object* v___f_1582_; lean_object* v___f_1583_; lean_object* v___x_1584_; lean_object* v___f_1585_; lean_object* v_val_1587_; lean_object* v___x_1592_; 
v_a_1580_ = lean_ctor_get(v_x_1577_, 0);
lean_inc_n(v_a_1580_, 2);
v___f_1581_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__6___boxed), 3, 1);
lean_closure_set(v___f_1581_, 0, v_x_1577_);
v___f_1582_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_1582_, 0, v_a_1580_);
v___f_1583_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed), 5, 1);
lean_closure_set(v___f_1583_, 0, v___f_1582_);
v___x_1584_ = lean_box_uint32(v_backlog_1575_);
v___f_1585_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__31___boxed), 19, 17);
lean_closure_set(v___f_1585_, 0, v_a_1580_);
lean_closure_set(v___f_1585_, 1, v___f_1563_);
lean_closure_set(v___f_1585_, 2, v___x_1564_);
lean_closure_set(v___f_1585_, 3, v___f_1565_);
lean_closure_set(v___f_1585_, 4, v___f_1566_);
lean_closure_set(v___f_1585_, 5, v___f_1583_);
lean_closure_set(v___f_1585_, 6, v_inst_1567_);
lean_closure_set(v___f_1585_, 7, v_handler_1568_);
lean_closure_set(v___f_1585_, 8, v_config_1569_);
lean_closure_set(v___f_1585_, 9, v___f_1570_);
lean_closure_set(v___f_1585_, 10, v___f_1571_);
lean_closure_set(v___f_1585_, 11, v___f_1572_);
lean_closure_set(v___f_1585_, 12, v___f_1573_);
lean_closure_set(v___f_1585_, 13, v___f_1574_);
lean_closure_set(v___f_1585_, 14, v___f_1581_);
lean_closure_set(v___f_1585_, 15, v___x_1584_);
lean_closure_set(v___f_1585_, 16, v_addr_1576_);
v___x_1592_ = lean_uv_tcp_new();
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1592_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1592_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
lean_ctor_set_tag(v___x_1595_, 1);
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
v_val_1587_ = v___x_1598_;
goto v___jp_1586_;
}
}
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
v_a_1601_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1592_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1592_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
lean_ctor_set_tag(v___x_1603_, 0);
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
v_val_1587_ = v___x_1606_;
goto v___jp_1586_;
}
}
}
v___jp_1586_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; lean_object* v___x_1591_; 
v___x_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1588_, 0, v_val_1587_);
v___x_1589_ = lean_unsigned_to_nat(0u);
v___x_1590_ = 0;
v___x_1591_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1589_, v___x_1590_, v___x_1588_, v___f_1585_);
return v___x_1591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32___boxed(lean_object* v___f_1609_, lean_object* v___x_1610_, lean_object* v___f_1611_, lean_object* v___f_1612_, lean_object* v_inst_1613_, lean_object* v_handler_1614_, lean_object* v_config_1615_, lean_object* v___f_1616_, lean_object* v___f_1617_, lean_object* v___f_1618_, lean_object* v___f_1619_, lean_object* v___f_1620_, lean_object* v_backlog_1621_, lean_object* v_addr_1622_, lean_object* v_x_1623_, lean_object* v___y_1624_){
_start:
{
uint32_t v_backlog_boxed_1625_; lean_object* v_res_1626_; 
v_backlog_boxed_1625_ = lean_unbox_uint32(v_backlog_1621_);
lean_dec(v_backlog_1621_);
v_res_1626_ = l_Std_Http_Server_serve___redArg___lam__32(v___f_1609_, v___x_1610_, v___f_1611_, v___f_1612_, v_inst_1613_, v_handler_1614_, v_config_1615_, v___f_1616_, v___f_1617_, v___f_1618_, v___f_1619_, v___f_1620_, v_backlog_boxed_1625_, v_addr_1622_, v_x_1623_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg(lean_object* v_inst_1632_, lean_object* v_addr_1633_, lean_object* v_handler_1634_, lean_object* v_config_1635_, uint32_t v_backlog_1636_){
_start:
{
lean_object* v___f_1638_; lean_object* v___f_1639_; lean_object* v___f_1640_; lean_object* v___f_1641_; lean_object* v___f_1642_; lean_object* v___f_1643_; lean_object* v___f_1644_; lean_object* v___f_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___f_1648_; lean_object* v_val_1650_; lean_object* v___x_1655_; lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
v___f_1638_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__0));
v___f_1639_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0));
v___f_1640_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__1));
v___f_1641_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5));
v___f_1642_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__2));
v___f_1643_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__3));
v___f_1644_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__4));
v___f_1645_ = ((lean_object*)(l_Std_Http_Server_waitShutdown___closed__0));
v___x_1646_ = l_Std_Async_ContextAsync_instMonad;
v___x_1647_ = lean_box_uint32(v_backlog_1636_);
lean_inc_ref(v_config_1635_);
v___f_1648_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__32___boxed), 16, 14);
lean_closure_set(v___f_1648_, 0, v___f_1644_);
lean_closure_set(v___f_1648_, 1, v___x_1646_);
lean_closure_set(v___f_1648_, 2, v___f_1639_);
lean_closure_set(v___f_1648_, 3, v___f_1641_);
lean_closure_set(v___f_1648_, 4, v_inst_1632_);
lean_closure_set(v___f_1648_, 5, v_handler_1634_);
lean_closure_set(v___f_1648_, 6, v_config_1635_);
lean_closure_set(v___f_1648_, 7, v___f_1640_);
lean_closure_set(v___f_1648_, 8, v___f_1643_);
lean_closure_set(v___f_1648_, 9, v___f_1642_);
lean_closure_set(v___f_1648_, 10, v___f_1645_);
lean_closure_set(v___f_1648_, 11, v___f_1638_);
lean_closure_set(v___f_1648_, 12, v___x_1647_);
lean_closure_set(v___f_1648_, 13, v_addr_1633_);
v___x_1655_ = l_Std_Http_Server_new(v_config_1635_);
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v___jp_1649_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; lean_object* v___x_1654_; 
v___x_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1651_, 0, v_val_1650_);
v___x_1652_ = lean_unsigned_to_nat(0u);
v___x_1653_ = 0;
v___x_1654_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1652_, v___x_1653_, v___x_1651_, v___f_1648_);
return v___x_1654_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
lean_ctor_set_tag(v___x_1658_, 1);
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
v_val_1650_ = v___x_1661_;
goto v___jp_1649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___boxed(lean_object* v_inst_1664_, lean_object* v_addr_1665_, lean_object* v_handler_1666_, lean_object* v_config_1667_, lean_object* v_backlog_1668_, lean_object* v_a_1669_){
_start:
{
uint32_t v_backlog_boxed_1670_; lean_object* v_res_1671_; 
v_backlog_boxed_1670_ = lean_unbox_uint32(v_backlog_1668_);
lean_dec(v_backlog_1668_);
v_res_1671_ = l_Std_Http_Server_serve___redArg(v_inst_1664_, v_addr_1665_, v_handler_1666_, v_config_1667_, v_backlog_boxed_1670_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve(lean_object* v_00_u03c3_1672_, lean_object* v_inst_1673_, lean_object* v_addr_1674_, lean_object* v_handler_1675_, lean_object* v_config_1676_, uint32_t v_backlog_1677_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Std_Http_Server_serve___redArg(v_inst_1673_, v_addr_1674_, v_handler_1675_, v_config_1676_, v_backlog_1677_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___boxed(lean_object* v_00_u03c3_1680_, lean_object* v_inst_1681_, lean_object* v_addr_1682_, lean_object* v_handler_1683_, lean_object* v_config_1684_, lean_object* v_backlog_1685_, lean_object* v_a_1686_){
_start:
{
uint32_t v_backlog_boxed_1687_; lean_object* v_res_1688_; 
v_backlog_boxed_1687_ = lean_unbox_uint32(v_backlog_1685_);
lean_dec(v_backlog_1685_);
v_res_1688_ = l_Std_Http_Server_serve(v_00_u03c3_1680_, v_inst_1681_, v_addr_1682_, v_handler_1683_, v_config_1684_, v_backlog_boxed_1687_);
return v_res_1688_;
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
