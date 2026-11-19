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
extern lean_object* l_Std_Http_Extensions_empty;
lean_object* lean_uv_tcp_getsockname(lean_object*);
lean_object* lean_uv_tcp_listen(lean_object*, uint32_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_selector(lean_object*);
extern lean_object* l_Std_Http_instTransportClient;
extern lean_object* l_Std_Http_Server_instImpl_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8_;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_cancel(lean_object*, lean_object*);
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
lean_object* l_Std_CancellationContext_new();
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* l_Std_CancellationToken_new();
lean_object* l_Std_Semaphore_new(lean_object*);
lean_object* lean_uv_tcp_nodelay(lean_object*);
lean_object* lean_uv_tcp_bind(lean_object*, lean_object*);
lean_object* lean_uv_tcp_new();
lean_object* l_Std_CancellationToken_wait(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_new(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_new___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdown(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdown___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Server_waitShutdown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_waitShutdown___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_waitShutdown___closed__0 = (const lean_object*)&l_Std_Http_Server_waitShutdown___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdownSelector(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Server_serve___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Server_serve___redArg___lam__2___closed__0 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Std_Http_Server_serve___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Server_serve___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Std_Http_Server_serve___redArg___lam__2___closed__1 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Server_serve___redArg___lam__21___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Server_serve___redArg___lam__21___closed__0;
static lean_once_cell_t l_Std_Http_Server_serve___redArg___lam__21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Server_serve___redArg___lam__21___closed__1;
static const lean_closure_object l_Std_Http_Server_serve___redArg___lam__21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Extensions_compareName___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___lam__21___closed__2 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__21___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Server_serve___redArg___lam__31___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__10___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Server_serve___redArg___lam__31___closed__0 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__31___closed__0_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___lam__31___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__6___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Server_serve___redArg___lam__31___closed__1 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__31___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__33(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__34(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__35(lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__36(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__36___boxed(lean_object**);
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__0 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__0_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__1 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__1_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__2 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__2_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__3 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__3_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__7___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v_connectionLimit_8_; lean_object* v_maxConnections_12_; uint8_t v___x_13_; 
v___x_4_ = l_Std_CancellationContext_new();
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = l_Std_Mutex_new___redArg(v___x_5_);
v_maxConnections_12_ = lean_ctor_get(v_config_1_, 0);
v___x_13_ = lean_nat_dec_eq(v_maxConnections_12_, v___x_5_);
if (v___x_13_ == 0)
{
lean_object* v___x_14_; lean_object* v___x_15_; 
lean_inc(v_maxConnections_12_);
v___x_14_ = l_Std_Semaphore_new(v_maxConnections_12_);
v___x_15_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
v_connectionLimit_8_ = v___x_15_;
goto v___jp_7_;
}
else
{
lean_object* v___x_16_; 
v___x_16_ = lean_box(0);
v_connectionLimit_8_ = v___x_16_;
goto v___jp_7_;
}
v___jp_7_:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = l_Std_CancellationToken_new();
v___x_10_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_10_, 0, v___x_4_);
lean_ctor_set(v___x_10_, 1, v___x_6_);
lean_ctor_set(v___x_10_, 2, v_connectionLimit_8_);
lean_ctor_set(v___x_10_, 3, v___x_9_);
lean_ctor_set(v___x_10_, 4, v_config_1_);
lean_ctor_set(v___x_10_, 5, v_localAddr_2_);
v___x_11_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_new___boxed(lean_object* v_config_17_, lean_object* v_localAddr_18_, lean_object* v_a_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Std_Http_Server_new(v_config_17_, v_localAddr_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdown(lean_object* v_s_21_){
_start:
{
lean_object* v_context_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v_context_23_ = lean_ctor_get(v_s_21_, 0);
lean_inc_ref(v_context_23_);
lean_dec_ref(v_s_21_);
v___x_24_ = lean_box(1);
v___x_25_ = l_Std_CancellationContext_cancel(v_context_23_, v___x_24_);
v___x_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
v___x_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdown___boxed(lean_object* v_s_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Std_Http_Server_shutdown(v_s_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___lam__0(lean_object* v_x_31_){
_start:
{
if (lean_obj_tag(v_x_31_) == 0)
{
lean_object* v_a_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_41_; 
v_a_33_ = lean_ctor_get(v_x_31_, 0);
v_isSharedCheck_41_ = !lean_is_exclusive(v_x_31_);
if (v_isSharedCheck_41_ == 0)
{
v___x_35_ = v_x_31_;
v_isShared_36_ = v_isSharedCheck_41_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_a_33_);
lean_dec(v_x_31_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_41_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_38_; 
if (v_isShared_36_ == 0)
{
v___x_38_ = v___x_35_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_a_33_);
v___x_38_ = v_reuseFailAlloc_40_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
lean_object* v___x_39_; 
v___x_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
return v___x_39_;
}
}
}
else
{
lean_object* v_a_42_; lean_object* v___x_43_; 
v_a_42_ = lean_ctor_get(v_x_31_, 0);
lean_inc(v_a_42_);
lean_dec_ref_known(v_x_31_, 1);
v___x_43_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_43_, 0, v_a_42_);
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___lam__0___boxed(lean_object* v_x_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Std_Http_Server_waitShutdown___lam__0(v_x_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown(lean_object* v_s_48_){
_start:
{
lean_object* v_shutdownDone_50_; lean_object* v___f_51_; lean_object* v___x_52_; uint8_t v___x_53_; lean_object* v_val_55_; lean_object* v___x_58_; 
v_shutdownDone_50_ = lean_ctor_get(v_s_48_, 3);
lean_inc_ref(v_shutdownDone_50_);
lean_dec_ref(v_s_48_);
v___f_51_ = ((lean_object*)(l_Std_Http_Server_waitShutdown___closed__0));
v___x_52_ = lean_unsigned_to_nat(0u);
v___x_53_ = 0;
v___x_58_ = l_Std_CancellationToken_wait(v_shutdownDone_50_);
if (lean_obj_tag(v___x_58_) == 0)
{
lean_object* v_a_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_66_; 
v_a_59_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_66_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_66_ == 0)
{
v___x_61_ = v___x_58_;
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_a_59_);
lean_dec(v___x_58_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_64_; 
if (v_isShared_62_ == 0)
{
lean_ctor_set_tag(v___x_61_, 1);
v___x_64_ = v___x_61_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_a_59_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
v_val_55_ = v___x_64_;
goto v___jp_54_;
}
}
}
else
{
lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_74_; 
v_a_67_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_74_ == 0)
{
v___x_69_ = v___x_58_;
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v___x_58_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_72_; 
if (v_isShared_70_ == 0)
{
lean_ctor_set_tag(v___x_69_, 0);
v___x_72_ = v___x_69_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_a_67_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
v_val_55_ = v___x_72_;
goto v___jp_54_;
}
}
}
v___jp_54_:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_56_, 0, v_val_55_);
v___x_57_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_52_, v___x_53_, v___x_56_, v___f_51_);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___boxed(lean_object* v_s_75_, lean_object* v_a_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Std_Http_Server_waitShutdown(v_s_75_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdownSelector(lean_object* v_s_78_){
_start:
{
lean_object* v_shutdownDone_79_; lean_object* v___x_80_; 
v_shutdownDone_79_ = lean_ctor_get(v_s_78_, 3);
lean_inc_ref(v_shutdownDone_79_);
lean_dec_ref(v_s_78_);
v___x_80_ = l_Std_CancellationToken_selector(v_shutdownDone_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait___lam__1(lean_object* v___f_81_, lean_object* v_shutdownDone_82_, lean_object* v_x_83_){
_start:
{
if (lean_obj_tag(v_x_83_) == 0)
{
lean_object* v___x_85_; 
lean_dec_ref(v_shutdownDone_82_);
lean_dec_ref(v___f_81_);
v___x_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_85_, 0, v_x_83_);
return v___x_85_;
}
else
{
lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_104_; 
v_isSharedCheck_104_ = !lean_is_exclusive(v_x_83_);
if (v_isSharedCheck_104_ == 0)
{
lean_object* v_unused_105_; 
v_unused_105_ = lean_ctor_get(v_x_83_, 0);
lean_dec(v_unused_105_);
v___x_87_ = v_x_83_;
v_isShared_88_ = v_isSharedCheck_104_;
goto v_resetjp_86_;
}
else
{
lean_dec(v_x_83_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_104_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v_val_92_; lean_object* v___x_95_; 
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = 0;
v___x_95_ = l_Std_CancellationToken_wait(v_shutdownDone_82_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_a_96_; lean_object* v___x_98_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
lean_inc(v_a_96_);
lean_dec_ref_known(v___x_95_, 1);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 0, v_a_96_);
v___x_98_ = v___x_87_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_a_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
v_val_92_ = v___x_98_;
goto v___jp_91_;
}
}
else
{
lean_object* v_a_100_; lean_object* v___x_102_; 
v_a_100_ = lean_ctor_get(v___x_95_, 0);
lean_inc(v_a_100_);
lean_dec_ref_known(v___x_95_, 1);
if (v_isShared_88_ == 0)
{
lean_ctor_set_tag(v___x_87_, 0);
lean_ctor_set(v___x_87_, 0, v_a_100_);
v___x_102_ = v___x_87_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_a_100_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
v_val_92_ = v___x_102_;
goto v___jp_91_;
}
}
v___jp_91_:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_93_, 0, v_val_92_);
v___x_94_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_89_, v___x_90_, v___x_93_, v___f_81_);
return v___x_94_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait___lam__1___boxed(lean_object* v___f_106_, lean_object* v_shutdownDone_107_, lean_object* v_x_108_, lean_object* v___y_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Std_Http_Server_shutdownAndWait___lam__1(v___f_106_, v_shutdownDone_107_, v_x_108_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait(lean_object* v_s_111_){
_start:
{
lean_object* v_context_113_; lean_object* v_shutdownDone_114_; lean_object* v___f_115_; lean_object* v___f_116_; lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v_context_113_ = lean_ctor_get(v_s_111_, 0);
lean_inc_ref(v_context_113_);
v_shutdownDone_114_ = lean_ctor_get(v_s_111_, 3);
lean_inc_ref(v_shutdownDone_114_);
lean_dec_ref(v_s_111_);
v___f_115_ = ((lean_object*)(l_Std_Http_Server_waitShutdown___closed__0));
v___f_116_ = lean_alloc_closure((void*)(l_Std_Http_Server_shutdownAndWait___lam__1___boxed), 4, 2);
lean_closure_set(v___f_116_, 0, v___f_115_);
lean_closure_set(v___f_116_, 1, v_shutdownDone_114_);
v___x_117_ = lean_box(1);
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = 0;
v___x_120_ = l_Std_CancellationContext_cancel(v_context_113_, v___x_117_);
v___x_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
v___x_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
v___x_123_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_118_, v___x_119_, v___x_122_, v___f_116_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait___boxed(lean_object* v_s_124_, lean_object* v_a_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Std_Http_Server_shutdownAndWait(v_s_124_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0(lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_134_ = lean_st_ref_take(v___y_131_);
v___x_135_ = lean_unsigned_to_nat(1u);
v___x_136_ = lean_nat_add(v___x_134_, v___x_135_);
lean_dec(v___x_134_);
v___x_137_ = lean_st_ref_put(v___y_131_, v___x_136_);
v___x_138_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___boxed(lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0(v___y_139_, v___y_140_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1(lean_object* v_x_143_){
_start:
{
lean_object* v_fst_144_; 
v_fst_144_ = lean_ctor_get(v_x_143_, 0);
lean_inc(v_fst_144_);
return v_fst_144_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1___boxed(lean_object* v_x_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1(v_x_145_);
lean_dec_ref(v_x_145_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2(lean_object* v_a_147_, lean_object* v_shutdownDone_148_, lean_object* v_x_149_){
_start:
{
if (lean_obj_tag(v_x_149_) == 0)
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_161_; 
lean_dec_ref(v_shutdownDone_148_);
v_a_153_ = lean_ctor_get(v_x_149_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v_x_149_);
if (v_isSharedCheck_161_ == 0)
{
v___x_155_ = v_x_149_;
v_isShared_156_ = v_isSharedCheck_161_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v_x_149_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_161_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_158_; 
if (v_isShared_156_ == 0)
{
v___x_158_ = v___x_155_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_153_);
v___x_158_ = v_reuseFailAlloc_160_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
lean_object* v___x_159_; 
v___x_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
return v___x_159_;
}
}
}
else
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_175_; 
v_a_162_ = lean_ctor_get(v_x_149_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v_x_149_);
if (v_isSharedCheck_175_ == 0)
{
v___x_164_ = v_x_149_;
v_isShared_165_ = v_isSharedCheck_175_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v_x_149_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_175_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_166_ = lean_unsigned_to_nat(0u);
v___x_167_ = lean_nat_dec_eq(v_a_147_, v___x_166_);
if (v___x_167_ == 0)
{
lean_del_object(v___x_164_);
lean_dec(v_a_162_);
lean_dec_ref(v_shutdownDone_148_);
goto v___jp_151_;
}
else
{
uint8_t v___x_168_; 
v___x_168_ = lean_unbox(v_a_162_);
lean_dec(v_a_162_);
if (v___x_168_ == 0)
{
lean_del_object(v___x_164_);
lean_dec_ref(v_shutdownDone_148_);
goto v___jp_151_;
}
else
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_169_ = lean_box(1);
v___x_170_ = l_Std_CancellationToken_cancel(v_shutdownDone_148_, v___x_169_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_170_);
v___x_172_ = v___x_164_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_170_);
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
}
}
v___jp_151_:
{
lean_object* v___x_152_; 
v___x_152_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2___boxed(lean_object* v_a_176_, lean_object* v_shutdownDone_177_, lean_object* v_x_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2(v_a_176_, v_shutdownDone_177_, v_x_178_);
lean_dec(v_a_176_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3(lean_object* v_context_181_, lean_object* v_shutdownDone_182_, lean_object* v_x_183_){
_start:
{
if (lean_obj_tag(v_x_183_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_193_; 
lean_dec_ref(v_shutdownDone_182_);
lean_dec_ref(v_context_181_);
v_a_185_ = lean_ctor_get(v_x_183_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v_x_183_);
if (v_isSharedCheck_193_ == 0)
{
v___x_187_ = v_x_183_;
v_isShared_188_ = v_isSharedCheck_193_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v_x_183_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_193_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_192_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; 
v___x_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
return v___x_191_;
}
}
}
else
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_209_; 
v_a_194_ = lean_ctor_get(v_x_183_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v_x_183_);
if (v_isSharedCheck_209_ == 0)
{
v___x_196_ = v_x_183_;
v_isShared_197_ = v_isSharedCheck_209_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v_x_183_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_209_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v_token_198_; lean_object* v___f_199_; lean_object* v___x_200_; uint8_t v___x_201_; uint8_t v___x_202_; lean_object* v___x_203_; lean_object* v___x_205_; 
v_token_198_ = lean_ctor_get(v_context_181_, 1);
lean_inc_ref(v_token_198_);
lean_dec_ref(v_context_181_);
v___f_199_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_199_, 0, v_a_194_);
lean_closure_set(v___f_199_, 1, v_shutdownDone_182_);
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = 0;
v___x_202_ = l_Std_CancellationToken_isCancelled(v_token_198_);
v___x_203_ = lean_box(v___x_202_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_203_);
v___x_205_ = v___x_196_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_203_);
v___x_205_ = v_reuseFailAlloc_208_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
v___x_207_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_200_, v___x_201_, v___x_206_, v___f_199_);
return v___x_207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed(lean_object* v_context_210_, lean_object* v_shutdownDone_211_, lean_object* v_x_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3(v_context_210_, v_shutdownDone_211_, v_x_212_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4(lean_object* v___f_215_, lean_object* v_____r_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v___x_220_; uint8_t v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = 0;
v___x_222_ = lean_st_ref_get(v___y_217_);
v___x_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
v___x_225_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_220_, v___x_221_, v___x_224_, v___f_215_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed(lean_object* v___f_226_, lean_object* v_____r_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4(v___f_226_, v_____r_227_, v___y_228_, v___y_229_);
lean_dec_ref(v___y_229_);
lean_dec(v___y_228_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5(lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_235_ = lean_st_ref_take(v___y_232_);
v___x_236_ = lean_unsigned_to_nat(1u);
v___x_237_ = lean_nat_sub(v___x_235_, v___x_236_);
lean_dec(v___x_235_);
v___x_238_ = lean_st_ref_put(v___y_232_, v___x_237_);
v___x_239_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5___boxed(lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5(v___y_240_, v___y_241_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6(lean_object* v___x_244_, lean_object* v___f_245_, lean_object* v___f_246_, lean_object* v___f_247_, lean_object* v___f_248_, lean_object* v_activeConnections_249_, lean_object* v_____r_250_, lean_object* v___y_251_){
_start:
{
lean_object* v___x_253_; lean_object* v___x_1941__overap_254_; lean_object* v___x_255_; 
lean_inc_ref(v___x_244_);
v___x_253_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_253_, 0, lean_box(0));
lean_closure_set(v___x_253_, 1, lean_box(0));
lean_closure_set(v___x_253_, 2, v___x_244_);
lean_closure_set(v___x_253_, 3, lean_box(0));
lean_closure_set(v___x_253_, 4, lean_box(0));
lean_closure_set(v___x_253_, 5, v___f_245_);
lean_closure_set(v___x_253_, 6, v___f_246_);
v___x_1941__overap_254_ = l_Std_Mutex_atomically___redArg(v___x_244_, v___f_247_, v___f_248_, v_activeConnections_249_, v___x_253_);
lean_inc_ref(v___y_251_);
v___x_255_ = lean_apply_2(v___x_1941__overap_254_, v___y_251_, lean_box(0));
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed(lean_object* v___x_256_, lean_object* v___f_257_, lean_object* v___f_258_, lean_object* v___f_259_, lean_object* v___f_260_, lean_object* v_activeConnections_261_, lean_object* v_____r_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6(v___x_256_, v___f_257_, v___f_258_, v___f_259_, v___f_260_, v_activeConnections_261_, v_____r_262_, v___y_263_);
lean_dec_ref(v___y_263_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7(lean_object* v___f_266_, lean_object* v_a_267_, lean_object* v_x_268_){
_start:
{
if (lean_obj_tag(v_x_268_) == 0)
{
lean_object* v___x_270_; 
lean_dec_ref(v___f_266_);
v___x_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_270_, 0, v_x_268_);
return v___x_270_;
}
else
{
lean_object* v_a_271_; lean_object* v___x_272_; 
v_a_271_ = lean_ctor_get(v_x_268_, 0);
lean_inc(v_a_271_);
lean_dec_ref_known(v_x_268_, 1);
lean_inc_ref(v_a_267_);
v___x_272_ = lean_apply_3(v___f_266_, v_a_271_, v_a_267_, lean_box(0));
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed(lean_object* v___f_273_, lean_object* v_a_274_, lean_object* v_x_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7(v___f_273_, v_a_274_, v_x_275_);
lean_dec_ref(v_a_274_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8(uint8_t v_releaseConnectionPermit_278_, lean_object* v___f_279_, lean_object* v_a_280_, lean_object* v_connectionLimit_281_, lean_object* v___f_282_, lean_object* v_opt_283_){
_start:
{
if (v_releaseConnectionPermit_278_ == 0)
{
lean_object* v___x_285_; lean_object* v___x_286_; 
lean_dec_ref(v___f_282_);
lean_dec(v_connectionLimit_281_);
v___x_285_ = lean_box(0);
lean_inc_ref(v_a_280_);
v___x_286_ = lean_apply_3(v___f_279_, v___x_285_, v_a_280_, lean_box(0));
return v___x_286_;
}
else
{
if (lean_obj_tag(v_connectionLimit_281_) == 1)
{
lean_object* v_val_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_299_; 
lean_dec_ref(v___f_279_);
v_val_287_ = lean_ctor_get(v_connectionLimit_281_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v_connectionLimit_281_);
if (v_isSharedCheck_299_ == 0)
{
v___x_289_ = v_connectionLimit_281_;
v_isShared_290_ = v_isSharedCheck_299_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_val_287_);
lean_dec(v_connectionLimit_281_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_299_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; uint8_t v___x_292_; lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_292_ = 0;
v___x_293_ = l_Std_Semaphore_release(v_val_287_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_293_);
v___x_295_ = v___x_289_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_293_);
v___x_295_ = v_reuseFailAlloc_298_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
v___x_297_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_291_, v___x_292_, v___x_296_, v___f_282_);
return v___x_297_;
}
}
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec_ref(v___f_282_);
lean_dec(v_connectionLimit_281_);
v___x_300_ = lean_box(0);
lean_inc_ref(v_a_280_);
v___x_301_ = lean_apply_3(v___f_279_, v___x_300_, v_a_280_, lean_box(0));
return v___x_301_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed(lean_object* v_releaseConnectionPermit_302_, lean_object* v___f_303_, lean_object* v_a_304_, lean_object* v_connectionLimit_305_, lean_object* v___f_306_, lean_object* v_opt_307_, lean_object* v___y_308_){
_start:
{
uint8_t v_releaseConnectionPermit_boxed_309_; lean_object* v_res_310_; 
v_releaseConnectionPermit_boxed_309_ = lean_unbox(v_releaseConnectionPermit_302_);
v_res_310_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8(v_releaseConnectionPermit_boxed_309_, v___f_303_, v_a_304_, v_connectionLimit_305_, v___f_306_, v_opt_307_);
lean_dec(v_opt_307_);
lean_dec_ref(v_a_304_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9(lean_object* v___f_311_, lean_object* v_action_312_, lean_object* v_a_313_, lean_object* v___f_314_, lean_object* v_x_315_){
_start:
{
if (lean_obj_tag(v_x_315_) == 0)
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_325_; 
lean_dec_ref(v___f_314_);
lean_dec_ref(v_action_312_);
lean_dec(v___f_311_);
v_a_317_ = lean_ctor_get(v_x_315_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v_x_315_);
if (v_isSharedCheck_325_ == 0)
{
v___x_319_ = v_x_315_;
v_isShared_320_ = v_isSharedCheck_325_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v_x_315_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_325_;
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
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_317_);
v___x_322_ = v_reuseFailAlloc_324_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_323_; 
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
return v___x_323_;
}
}
}
else
{
lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___y_332_; 
lean_dec_ref_known(v_x_315_, 1);
v___x_326_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_326_, 0, lean_box(0));
lean_closure_set(v___x_326_, 1, lean_box(0));
lean_closure_set(v___x_326_, 2, lean_box(0));
lean_closure_set(v___x_326_, 3, v___f_311_);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = 0;
lean_inc_ref(v_a_313_);
v___x_329_ = lean_apply_1(v_action_312_, v_a_313_);
v___x_330_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_329_, v___f_314_, v___x_327_, v___x_328_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_334_; 
lean_dec_ref(v___x_326_);
v_a_334_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_334_);
lean_dec_ref_known(v___x_330_, 1);
if (lean_obj_tag(v_a_334_) == 0)
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
v_a_335_ = lean_ctor_get(v_a_334_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v_a_334_);
if (v_isSharedCheck_342_ == 0)
{
v___x_337_ = v_a_334_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v_a_334_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
v___y_332_ = v___x_340_;
goto v___jp_331_;
}
}
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_351_; 
v_a_343_ = lean_ctor_get(v_a_334_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v_a_334_);
if (v_isSharedCheck_351_ == 0)
{
v___x_345_ = v_a_334_;
v_isShared_346_ = v_isSharedCheck_351_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v_a_334_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_351_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v_fst_347_; lean_object* v___x_349_; 
v_fst_347_ = lean_ctor_get(v_a_343_, 0);
lean_inc(v_fst_347_);
lean_dec(v_a_343_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v_fst_347_);
v___x_349_ = v___x_345_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_fst_347_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
v___y_332_ = v___x_349_;
goto v___jp_331_;
}
}
}
}
else
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_360_; 
v_a_352_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_360_ == 0)
{
v___x_354_ = v___x_330_;
v_isShared_355_ = v_isSharedCheck_360_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_330_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_360_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_356_; lean_object* v___x_358_; 
v___x_356_ = lean_task_map(v___x_326_, v_a_352_, v___x_327_, v___x_328_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v___x_356_);
v___x_358_ = v___x_354_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_356_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
v___jp_331_:
{
lean_object* v___x_333_; 
v___x_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_333_, 0, v___y_332_);
return v___x_333_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed(lean_object* v___f_361_, lean_object* v_action_362_, lean_object* v_a_363_, lean_object* v___f_364_, lean_object* v_x_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9(v___f_361_, v_action_362_, v_a_363_, v___f_364_, v_x_365_);
lean_dec_ref(v_a_363_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg(lean_object* v_s_377_, uint8_t v_releaseConnectionPermit_378_, lean_object* v_action_379_, lean_object* v_a_380_){
_start:
{
lean_object* v___x_382_; lean_object* v_context_383_; lean_object* v_activeConnections_384_; lean_object* v_connectionLimit_385_; lean_object* v_shutdownDone_386_; lean_object* v___f_387_; lean_object* v___f_388_; lean_object* v___f_389_; lean_object* v___f_390_; lean_object* v___f_391_; lean_object* v___f_392_; lean_object* v___f_393_; lean_object* v___f_394_; lean_object* v___f_395_; lean_object* v___x_396_; lean_object* v___f_397_; lean_object* v___f_398_; lean_object* v___x_399_; uint8_t v___x_400_; lean_object* v___x_1694__overap_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_382_ = l_Std_Async_ContextAsync_instMonad;
v_context_383_ = lean_ctor_get(v_s_377_, 0);
lean_inc_ref(v_context_383_);
v_activeConnections_384_ = lean_ctor_get(v_s_377_, 1);
lean_inc_ref_n(v_activeConnections_384_, 2);
v_connectionLimit_385_ = lean_ctor_get(v_s_377_, 2);
lean_inc(v_connectionLimit_385_);
v_shutdownDone_386_ = lean_ctor_get(v_s_377_, 3);
lean_inc_ref(v_shutdownDone_386_);
lean_dec_ref(v_s_377_);
v___f_387_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0));
v___f_388_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1));
v___f_389_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_389_, 0, v_context_383_);
lean_closure_set(v___f_389_, 1, v_shutdownDone_386_);
v___f_390_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed), 5, 1);
lean_closure_set(v___f_390_, 0, v___f_389_);
v___f_391_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2));
v___f_392_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5));
v___f_393_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6));
v___f_394_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed), 9, 6);
lean_closure_set(v___f_394_, 0, v___x_382_);
lean_closure_set(v___f_394_, 1, v___f_391_);
lean_closure_set(v___f_394_, 2, v___f_390_);
lean_closure_set(v___f_394_, 3, v___f_392_);
lean_closure_set(v___f_394_, 4, v___f_393_);
lean_closure_set(v___f_394_, 5, v_activeConnections_384_);
lean_inc_ref_n(v_a_380_, 4);
lean_inc_ref(v___f_394_);
v___f_395_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_395_, 0, v___f_394_);
lean_closure_set(v___f_395_, 1, v_a_380_);
v___x_396_ = lean_box(v_releaseConnectionPermit_378_);
v___f_397_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed), 7, 5);
lean_closure_set(v___f_397_, 0, v___x_396_);
lean_closure_set(v___f_397_, 1, v___f_394_);
lean_closure_set(v___f_397_, 2, v_a_380_);
lean_closure_set(v___f_397_, 3, v_connectionLimit_385_);
lean_closure_set(v___f_397_, 4, v___f_395_);
v___f_398_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed), 6, 4);
lean_closure_set(v___f_398_, 0, v___f_388_);
lean_closure_set(v___f_398_, 1, v_action_379_);
lean_closure_set(v___f_398_, 2, v_a_380_);
lean_closure_set(v___f_398_, 3, v___f_397_);
v___x_399_ = lean_unsigned_to_nat(0u);
v___x_400_ = 0;
v___x_1694__overap_401_ = l_Std_Mutex_atomically___redArg(v___x_382_, v___f_392_, v___f_393_, v_activeConnections_384_, v___f_387_);
v___x_402_ = lean_apply_2(v___x_1694__overap_401_, v_a_380_, lean_box(0));
v___x_403_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_399_, v___x_400_, v___x_402_, v___f_398_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___boxed(lean_object* v_s_404_, lean_object* v_releaseConnectionPermit_405_, lean_object* v_action_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
uint8_t v_releaseConnectionPermit_boxed_409_; lean_object* v_res_410_; 
v_releaseConnectionPermit_boxed_409_ = lean_unbox(v_releaseConnectionPermit_405_);
v_res_410_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg(v_s_404_, v_releaseConnectionPermit_boxed_409_, v_action_406_, v_a_407_);
lean_dec_ref(v_a_407_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation(lean_object* v_00_u03b1_411_, lean_object* v_s_412_, uint8_t v_releaseConnectionPermit_413_, lean_object* v_action_414_, lean_object* v_a_415_){
_start:
{
lean_object* v___x_417_; lean_object* v_context_418_; lean_object* v_activeConnections_419_; lean_object* v_connectionLimit_420_; lean_object* v_shutdownDone_421_; lean_object* v___f_422_; lean_object* v___f_423_; lean_object* v___f_424_; lean_object* v___f_425_; lean_object* v___f_426_; lean_object* v___f_427_; lean_object* v___f_428_; lean_object* v___f_429_; lean_object* v___f_430_; lean_object* v___x_431_; lean_object* v___f_432_; lean_object* v___f_433_; lean_object* v___x_434_; uint8_t v___x_435_; lean_object* v___x_1846__overap_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_417_ = l_Std_Async_ContextAsync_instMonad;
v_context_418_ = lean_ctor_get(v_s_412_, 0);
lean_inc_ref(v_context_418_);
v_activeConnections_419_ = lean_ctor_get(v_s_412_, 1);
lean_inc_ref_n(v_activeConnections_419_, 2);
v_connectionLimit_420_ = lean_ctor_get(v_s_412_, 2);
lean_inc(v_connectionLimit_420_);
v_shutdownDone_421_ = lean_ctor_get(v_s_412_, 3);
lean_inc_ref(v_shutdownDone_421_);
lean_dec_ref(v_s_412_);
v___f_422_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0));
v___f_423_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1));
v___f_424_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_424_, 0, v_context_418_);
lean_closure_set(v___f_424_, 1, v_shutdownDone_421_);
v___f_425_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed), 5, 1);
lean_closure_set(v___f_425_, 0, v___f_424_);
v___f_426_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2));
v___f_427_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5));
v___f_428_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6));
v___f_429_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed), 9, 6);
lean_closure_set(v___f_429_, 0, v___x_417_);
lean_closure_set(v___f_429_, 1, v___f_426_);
lean_closure_set(v___f_429_, 2, v___f_425_);
lean_closure_set(v___f_429_, 3, v___f_427_);
lean_closure_set(v___f_429_, 4, v___f_428_);
lean_closure_set(v___f_429_, 5, v_activeConnections_419_);
lean_inc_ref_n(v_a_415_, 4);
lean_inc_ref(v___f_429_);
v___f_430_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_430_, 0, v___f_429_);
lean_closure_set(v___f_430_, 1, v_a_415_);
v___x_431_ = lean_box(v_releaseConnectionPermit_413_);
v___f_432_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed), 7, 5);
lean_closure_set(v___f_432_, 0, v___x_431_);
lean_closure_set(v___f_432_, 1, v___f_429_);
lean_closure_set(v___f_432_, 2, v_a_415_);
lean_closure_set(v___f_432_, 3, v_connectionLimit_420_);
lean_closure_set(v___f_432_, 4, v___f_430_);
v___f_433_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed), 6, 4);
lean_closure_set(v___f_433_, 0, v___f_423_);
lean_closure_set(v___f_433_, 1, v_action_414_);
lean_closure_set(v___f_433_, 2, v_a_415_);
lean_closure_set(v___f_433_, 3, v___f_432_);
v___x_434_ = lean_unsigned_to_nat(0u);
v___x_435_ = 0;
v___x_1846__overap_436_ = l_Std_Mutex_atomically___redArg(v___x_417_, v___f_427_, v___f_428_, v_activeConnections_419_, v___f_422_);
v___x_437_ = lean_apply_2(v___x_1846__overap_436_, v_a_415_, lean_box(0));
v___x_438_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_434_, v___x_435_, v___x_437_, v___f_433_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___boxed(lean_object* v_00_u03b1_439_, lean_object* v_s_440_, lean_object* v_releaseConnectionPermit_441_, lean_object* v_action_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
uint8_t v_releaseConnectionPermit_boxed_445_; lean_object* v_res_446_; 
v_releaseConnectionPermit_boxed_445_ = lean_unbox(v_releaseConnectionPermit_441_);
v_res_446_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation(v_00_u03b1_439_, v_s_440_, v_releaseConnectionPermit_boxed_445_, v_action_442_, v_a_443_);
lean_dec_ref(v_a_443_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__0(lean_object* v_a_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_448_, 0, v_a_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1(lean_object* v_x_449_){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_451_, 0, v_x_449_);
v___x_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1___boxed(lean_object* v_x_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Std_Http_Server_serve___redArg___lam__1(v_x_454_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2(lean_object* v_x_461_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__2___closed__1));
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2___boxed(lean_object* v_x_464_, lean_object* v___y_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Std_Http_Server_serve___redArg___lam__2(v_x_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3(lean_object* v_x_467_){
_start:
{
lean_object* v_fst_468_; 
v_fst_468_ = lean_ctor_get(v_x_467_, 0);
lean_inc(v_fst_468_);
return v_fst_468_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3___boxed(lean_object* v_x_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Std_Http_Server_serve___redArg___lam__3(v_x_469_);
lean_dec_ref(v_x_469_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7(lean_object* v_x_471_){
_start:
{
if (lean_obj_tag(v_x_471_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_481_; 
v_a_473_ = lean_ctor_get(v_x_471_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v_x_471_);
if (v_isSharedCheck_481_ == 0)
{
v___x_475_ = v_x_471_;
v_isShared_476_ = v_isSharedCheck_481_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v_x_471_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_481_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_480_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_479_; 
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
}
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_492_; 
v_a_482_ = lean_ctor_get(v_x_471_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v_x_471_);
if (v_isSharedCheck_492_ == 0)
{
v___x_484_ = v_x_471_;
v_isShared_485_ = v_isSharedCheck_492_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v_x_471_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_492_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v_token_486_; lean_object* v___x_487_; lean_object* v___x_489_; 
v_token_486_ = lean_ctor_get(v_a_482_, 1);
lean_inc_ref(v_token_486_);
lean_dec(v_a_482_);
v___x_487_ = l_Std_CancellationToken_selector(v_token_486_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v___x_487_);
v___x_489_ = v___x_484_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_487_);
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
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7___boxed(lean_object* v_x_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Std_Http_Server_serve___redArg___lam__7(v_x_493_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4(lean_object* v_x_496_){
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
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4___boxed(lean_object* v_x_500_, lean_object* v___y_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Std_Http_Server_serve___redArg___lam__4(v_x_500_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5(lean_object* v_x_503_, lean_object* v_x_504_){
_start:
{
if (lean_obj_tag(v_x_504_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_514_; 
lean_dec_ref(v_x_503_);
v_a_506_ = lean_ctor_get(v_x_504_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v_x_504_);
if (v_isSharedCheck_514_ == 0)
{
v___x_508_ = v_x_504_;
v_isShared_509_ = v_isSharedCheck_514_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v_x_504_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_514_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_506_);
v___x_511_ = v_reuseFailAlloc_513_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_512_; 
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
return v___x_512_;
}
}
}
else
{
lean_object* v___x_515_; 
lean_dec_ref_known(v_x_504_, 1);
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v_x_503_);
return v___x_515_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5___boxed(lean_object* v_x_516_, lean_object* v_x_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Std_Http_Server_serve___redArg___lam__5(v_x_516_, v_x_517_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10(lean_object* v___x_520_, lean_object* v_____r_521_, lean_object* v___y_522_){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_520_);
v___x_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10___boxed(lean_object* v___x_527_, lean_object* v_____r_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Std_Http_Server_serve___redArg___lam__10(v___x_527_, v_____r_528_, v___y_529_);
lean_dec_ref(v___y_529_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6(lean_object* v___x_532_, lean_object* v_x_533_){
_start:
{
if (lean_obj_tag(v_x_533_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_543_; 
v_a_535_ = lean_ctor_get(v_x_533_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v_x_533_);
if (v_isSharedCheck_543_ == 0)
{
v___x_537_ = v_x_533_;
v_isShared_538_ = v_isSharedCheck_543_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v_x_533_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_543_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_542_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_541_; 
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
return v___x_541_;
}
}
}
else
{
lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_552_; 
v_isSharedCheck_552_ = !lean_is_exclusive(v_x_533_);
if (v_isSharedCheck_552_ == 0)
{
lean_object* v_unused_553_; 
v_unused_553_ = lean_ctor_get(v_x_533_, 0);
lean_dec(v_unused_553_);
v___x_545_ = v_x_533_;
v_isShared_546_ = v_isSharedCheck_552_;
goto v_resetjp_544_;
}
else
{
lean_dec(v_x_533_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_552_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_532_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_547_);
v___x_549_ = v___x_545_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_547_);
v___x_549_ = v_reuseFailAlloc_551_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_550_; 
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
return v___x_550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6___boxed(lean_object* v___x_554_, lean_object* v_x_555_, lean_object* v___y_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Std_Http_Server_serve___redArg___lam__6(v___x_554_, v_x_555_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8(lean_object* v___f_558_, lean_object* v___y_559_, lean_object* v_x_560_){
_start:
{
if (lean_obj_tag(v_x_560_) == 0)
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_570_; 
lean_dec_ref(v___f_558_);
v_a_562_ = lean_ctor_get(v_x_560_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v_x_560_);
if (v_isSharedCheck_570_ == 0)
{
v___x_564_ = v_x_560_;
v_isShared_565_ = v_isSharedCheck_570_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v_x_560_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_570_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_569_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_568_; 
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
}
}
else
{
lean_object* v_a_571_; lean_object* v___x_572_; 
v_a_571_ = lean_ctor_get(v_x_560_, 0);
lean_inc(v_a_571_);
lean_dec_ref_known(v_x_560_, 1);
lean_inc_ref(v___y_559_);
v___x_572_ = lean_apply_3(v___f_558_, v_a_571_, v___y_559_, lean_box(0));
return v___x_572_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8___boxed(lean_object* v___f_573_, lean_object* v___y_574_, lean_object* v_x_575_, lean_object* v___y_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Std_Http_Server_serve___redArg___lam__8(v___f_573_, v___y_574_, v_x_575_);
lean_dec_ref(v___y_574_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11(lean_object* v___f_578_, lean_object* v_a_579_, lean_object* v_x_580_){
_start:
{
if (lean_obj_tag(v_x_580_) == 0)
{
lean_object* v___x_582_; 
lean_dec_ref(v_a_579_);
lean_dec_ref(v___f_578_);
v___x_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_582_, 0, v_x_580_);
return v___x_582_;
}
else
{
lean_object* v_a_583_; lean_object* v___x_584_; 
v_a_583_ = lean_ctor_get(v_x_580_, 0);
lean_inc(v_a_583_);
lean_dec_ref_known(v_x_580_, 1);
v___x_584_ = lean_apply_3(v___f_578_, v_a_583_, v_a_579_, lean_box(0));
return v___x_584_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11___boxed(lean_object* v___f_585_, lean_object* v_a_586_, lean_object* v_x_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Std_Http_Server_serve___redArg___lam__11(v___f_585_, v_a_586_, v_x_587_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9(uint8_t v_permitAcquired_590_, lean_object* v___f_591_, lean_object* v___x_592_, lean_object* v_a_593_, lean_object* v_connectionLimit_594_, lean_object* v___x_595_, uint8_t v___x_596_, lean_object* v___f_597_, lean_object* v_opt_598_){
_start:
{
if (v_permitAcquired_590_ == 0)
{
lean_object* v___x_600_; 
lean_dec_ref(v___f_597_);
lean_dec(v___x_595_);
lean_dec(v_connectionLimit_594_);
v___x_600_ = lean_apply_3(v___f_591_, v___x_592_, v_a_593_, lean_box(0));
return v___x_600_;
}
else
{
if (lean_obj_tag(v_connectionLimit_594_) == 1)
{
lean_object* v_val_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_611_; 
lean_dec_ref(v_a_593_);
lean_dec_ref(v___f_591_);
v_val_601_ = lean_ctor_get(v_connectionLimit_594_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v_connectionLimit_594_);
if (v_isSharedCheck_611_ == 0)
{
v___x_603_ = v_connectionLimit_594_;
v_isShared_604_ = v_isSharedCheck_611_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_val_601_);
lean_dec(v_connectionLimit_594_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_611_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_605_ = l_Std_Semaphore_release(v_val_601_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_605_);
v___x_607_ = v___x_603_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_605_);
v___x_607_ = v_reuseFailAlloc_610_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
v___x_609_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_595_, v___x_596_, v___x_608_, v___f_597_);
return v___x_609_;
}
}
}
else
{
lean_object* v___x_612_; 
lean_dec_ref(v___f_597_);
lean_dec(v___x_595_);
lean_dec(v_connectionLimit_594_);
v___x_612_ = lean_apply_3(v___f_591_, v___x_592_, v_a_593_, lean_box(0));
return v___x_612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9___boxed(lean_object* v_permitAcquired_613_, lean_object* v___f_614_, lean_object* v___x_615_, lean_object* v_a_616_, lean_object* v_connectionLimit_617_, lean_object* v___x_618_, lean_object* v___x_619_, lean_object* v___f_620_, lean_object* v_opt_621_, lean_object* v___y_622_){
_start:
{
uint8_t v_permitAcquired_boxed_623_; uint8_t v___x_13071__boxed_624_; lean_object* v_res_625_; 
v_permitAcquired_boxed_623_ = lean_unbox(v_permitAcquired_613_);
v___x_13071__boxed_624_ = lean_unbox(v___x_619_);
v_res_625_ = l_Std_Http_Server_serve___redArg___lam__9(v_permitAcquired_boxed_623_, v___f_614_, v___x_615_, v_a_616_, v_connectionLimit_617_, v___x_618_, v___x_13071__boxed_624_, v___f_620_, v_opt_621_);
lean_dec(v_opt_621_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12(lean_object* v___f_626_, lean_object* v___x_627_, lean_object* v_inst_628_, lean_object* v_val_629_, lean_object* v_handler_630_, lean_object* v_config_631_, lean_object* v_extensions_632_, lean_object* v_a_633_, lean_object* v___f_634_, lean_object* v___x_635_, uint8_t v___x_636_, lean_object* v_x_637_){
_start:
{
if (lean_obj_tag(v_x_637_) == 0)
{
lean_object* v___x_639_; 
lean_dec(v___x_635_);
lean_dec_ref(v___f_634_);
lean_dec_ref(v_a_633_);
lean_dec(v_extensions_632_);
lean_dec_ref(v_config_631_);
lean_dec(v_handler_630_);
lean_dec(v_val_629_);
lean_dec_ref(v_inst_628_);
lean_dec_ref(v___x_627_);
lean_dec_ref(v___f_626_);
v___x_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_639_, 0, v_x_637_);
return v___x_639_;
}
else
{
lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_678_; 
v_isSharedCheck_678_ = !lean_is_exclusive(v_x_637_);
if (v_isSharedCheck_678_ == 0)
{
lean_object* v_unused_679_; 
v_unused_679_ = lean_ctor_get(v_x_637_, 0);
lean_dec(v_unused_679_);
v___x_641_ = v_x_637_;
v_isShared_642_ = v_isSharedCheck_678_;
goto v_resetjp_640_;
}
else
{
lean_dec(v_x_637_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_678_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___y_647_; 
v___x_643_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_643_, 0, lean_box(0));
lean_closure_set(v___x_643_, 1, lean_box(0));
lean_closure_set(v___x_643_, 2, lean_box(0));
lean_closure_set(v___x_643_, 3, v___f_626_);
v___x_644_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___boxed), 10, 9);
lean_closure_set(v___x_644_, 0, lean_box(0));
lean_closure_set(v___x_644_, 1, lean_box(0));
lean_closure_set(v___x_644_, 2, v___x_627_);
lean_closure_set(v___x_644_, 3, v_inst_628_);
lean_closure_set(v___x_644_, 4, v_val_629_);
lean_closure_set(v___x_644_, 5, v_handler_630_);
lean_closure_set(v___x_644_, 6, v_config_631_);
lean_closure_set(v___x_644_, 7, v_extensions_632_);
lean_closure_set(v___x_644_, 8, v_a_633_);
lean_inc(v___x_635_);
v___x_645_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_644_, v___f_634_, v___x_635_, v___x_636_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_651_; 
lean_dec_ref(v___x_643_);
lean_dec(v___x_635_);
v_a_651_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_a_651_);
lean_dec_ref_known(v___x_645_, 1);
if (lean_obj_tag(v_a_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
v_a_652_ = lean_ctor_get(v_a_651_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v_a_651_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v_a_651_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v_a_651_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
v___y_647_ = v___x_657_;
goto v___jp_646_;
}
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_668_; 
v_a_660_ = lean_ctor_get(v_a_651_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v_a_651_);
if (v_isSharedCheck_668_ == 0)
{
v___x_662_ = v_a_651_;
v_isShared_663_ = v_isSharedCheck_668_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v_a_651_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_668_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v_fst_664_; lean_object* v___x_666_; 
v_fst_664_ = lean_ctor_get(v_a_660_, 0);
lean_inc(v_fst_664_);
lean_dec(v_a_660_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v_fst_664_);
v___x_666_ = v___x_662_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_fst_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
v___y_647_ = v___x_666_;
goto v___jp_646_;
}
}
}
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_677_; 
lean_del_object(v___x_641_);
v_a_669_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_677_ == 0)
{
v___x_671_ = v___x_645_;
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_645_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_673_ = lean_task_map(v___x_643_, v_a_669_, v___x_635_, v___x_636_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_673_);
v___x_675_ = v___x_671_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
v___jp_646_:
{
lean_object* v___x_649_; 
if (v_isShared_642_ == 0)
{
lean_ctor_set_tag(v___x_641_, 0);
lean_ctor_set(v___x_641_, 0, v___y_647_);
v___x_649_ = v___x_641_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___y_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12___boxed(lean_object* v___f_680_, lean_object* v___x_681_, lean_object* v_inst_682_, lean_object* v_val_683_, lean_object* v_handler_684_, lean_object* v_config_685_, lean_object* v_extensions_686_, lean_object* v_a_687_, lean_object* v___f_688_, lean_object* v___x_689_, lean_object* v___x_690_, lean_object* v_x_691_, lean_object* v___y_692_){
_start:
{
uint8_t v___x_13121__boxed_693_; lean_object* v_res_694_; 
v___x_13121__boxed_693_ = lean_unbox(v___x_690_);
v_res_694_ = l_Std_Http_Server_serve___redArg___lam__12(v___f_680_, v___x_681_, v_inst_682_, v_val_683_, v_handler_684_, v_config_685_, v_extensions_686_, v_a_687_, v___f_688_, v___x_689_, v___x_13121__boxed_693_, v_x_691_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13(lean_object* v___f_695_, lean_object* v___f_696_, lean_object* v_activeConnections_697_, lean_object* v_a_698_, uint8_t v_permitAcquired_699_, lean_object* v___x_700_, lean_object* v_connectionLimit_701_, lean_object* v___x_702_, uint8_t v___x_703_, lean_object* v___f_704_, lean_object* v___x_705_, lean_object* v_inst_706_, lean_object* v_val_707_, lean_object* v_handler_708_, lean_object* v_config_709_, lean_object* v_extensions_710_, lean_object* v___f_711_){
_start:
{
lean_object* v___x_713_; lean_object* v___f_714_; lean_object* v___f_715_; lean_object* v___f_716_; lean_object* v___f_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___f_720_; lean_object* v___x_721_; lean_object* v___f_722_; lean_object* v___x_12284__overap_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_713_ = l_Std_Async_ContextAsync_instMonad;
v___f_714_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5));
v___f_715_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6));
lean_inc_ref(v_activeConnections_697_);
v___f_716_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed), 9, 6);
lean_closure_set(v___f_716_, 0, v___x_713_);
lean_closure_set(v___f_716_, 1, v___f_695_);
lean_closure_set(v___f_716_, 2, v___f_696_);
lean_closure_set(v___f_716_, 3, v___f_714_);
lean_closure_set(v___f_716_, 4, v___f_715_);
lean_closure_set(v___f_716_, 5, v_activeConnections_697_);
lean_inc_ref_n(v_a_698_, 3);
lean_inc_ref(v___f_716_);
v___f_717_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__11___boxed), 4, 2);
lean_closure_set(v___f_717_, 0, v___f_716_);
lean_closure_set(v___f_717_, 1, v_a_698_);
v___x_718_ = lean_box(v_permitAcquired_699_);
v___x_719_ = lean_box(v___x_703_);
lean_inc_n(v___x_702_, 2);
v___f_720_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__9___boxed), 10, 8);
lean_closure_set(v___f_720_, 0, v___x_718_);
lean_closure_set(v___f_720_, 1, v___f_716_);
lean_closure_set(v___f_720_, 2, v___x_700_);
lean_closure_set(v___f_720_, 3, v_a_698_);
lean_closure_set(v___f_720_, 4, v_connectionLimit_701_);
lean_closure_set(v___f_720_, 5, v___x_702_);
lean_closure_set(v___f_720_, 6, v___x_719_);
lean_closure_set(v___f_720_, 7, v___f_717_);
v___x_721_ = lean_box(v___x_703_);
v___f_722_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__12___boxed), 13, 11);
lean_closure_set(v___f_722_, 0, v___f_704_);
lean_closure_set(v___f_722_, 1, v___x_705_);
lean_closure_set(v___f_722_, 2, v_inst_706_);
lean_closure_set(v___f_722_, 3, v_val_707_);
lean_closure_set(v___f_722_, 4, v_handler_708_);
lean_closure_set(v___f_722_, 5, v_config_709_);
lean_closure_set(v___f_722_, 6, v_extensions_710_);
lean_closure_set(v___f_722_, 7, v_a_698_);
lean_closure_set(v___f_722_, 8, v___f_720_);
lean_closure_set(v___f_722_, 9, v___x_702_);
lean_closure_set(v___f_722_, 10, v___x_721_);
v___x_12284__overap_723_ = l_Std_Mutex_atomically___redArg(v___x_713_, v___f_714_, v___f_715_, v_activeConnections_697_, v___f_711_);
v___x_724_ = lean_apply_2(v___x_12284__overap_723_, v_a_698_, lean_box(0));
v___x_725_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_702_, v___x_703_, v___x_724_, v___f_722_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13___boxed(lean_object** _args){
lean_object* v___f_726_ = _args[0];
lean_object* v___f_727_ = _args[1];
lean_object* v_activeConnections_728_ = _args[2];
lean_object* v_a_729_ = _args[3];
lean_object* v_permitAcquired_730_ = _args[4];
lean_object* v___x_731_ = _args[5];
lean_object* v_connectionLimit_732_ = _args[6];
lean_object* v___x_733_ = _args[7];
lean_object* v___x_734_ = _args[8];
lean_object* v___f_735_ = _args[9];
lean_object* v___x_736_ = _args[10];
lean_object* v_inst_737_ = _args[11];
lean_object* v_val_738_ = _args[12];
lean_object* v_handler_739_ = _args[13];
lean_object* v_config_740_ = _args[14];
lean_object* v_extensions_741_ = _args[15];
lean_object* v___f_742_ = _args[16];
lean_object* v___y_743_ = _args[17];
_start:
{
uint8_t v_permitAcquired_boxed_744_; uint8_t v___x_13237__boxed_745_; lean_object* v_res_746_; 
v_permitAcquired_boxed_744_ = lean_unbox(v_permitAcquired_730_);
v___x_13237__boxed_745_ = lean_unbox(v___x_734_);
v_res_746_ = l_Std_Http_Server_serve___redArg___lam__13(v___f_726_, v___f_727_, v_activeConnections_728_, v_a_729_, v_permitAcquired_boxed_744_, v___x_731_, v_connectionLimit_732_, v___x_733_, v___x_13237__boxed_745_, v___f_735_, v___x_736_, v_inst_737_, v_val_738_, v_handler_739_, v_config_740_, v_extensions_741_, v___f_742_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14(lean_object* v_a_747_, lean_object* v___x_748_, lean_object* v_a_x3f_749_){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_751_ = l_Std_CancellationContext_cancel(v_a_747_, v___x_748_);
v___x_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
v___x_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14___boxed(lean_object* v_a_754_, lean_object* v___x_755_, lean_object* v_a_x3f_756_, lean_object* v___y_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Std_Http_Server_serve___redArg___lam__14(v_a_754_, v___x_755_, v_a_x3f_756_);
lean_dec(v_a_x3f_756_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15(lean_object* v___f_759_, lean_object* v___f_760_, lean_object* v___f_761_, lean_object* v___x_762_, uint8_t v___x_763_){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___y_768_; 
v___x_765_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_765_, 0, lean_box(0));
lean_closure_set(v___x_765_, 1, lean_box(0));
lean_closure_set(v___x_765_, 2, lean_box(0));
lean_closure_set(v___x_765_, 3, v___f_759_);
lean_inc(v___x_762_);
v___x_766_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_760_, v___f_761_, v___x_762_, v___x_763_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_770_; 
lean_dec_ref(v___x_765_);
lean_dec(v___x_762_);
v_a_770_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_770_);
lean_dec_ref_known(v___x_766_, 1);
if (lean_obj_tag(v_a_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
v_a_771_ = lean_ctor_get(v_a_770_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v_a_770_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v_a_770_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v_a_770_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
v___y_768_ = v___x_776_;
goto v___jp_767_;
}
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_787_; 
v_a_779_ = lean_ctor_get(v_a_770_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v_a_770_);
if (v_isSharedCheck_787_ == 0)
{
v___x_781_ = v_a_770_;
v_isShared_782_ = v_isSharedCheck_787_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v_a_770_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_787_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v_fst_783_; lean_object* v___x_785_; 
v_fst_783_ = lean_ctor_get(v_a_779_, 0);
lean_inc(v_fst_783_);
lean_dec(v_a_779_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v_fst_783_);
v___x_785_ = v___x_781_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_fst_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
v___y_768_ = v___x_785_;
goto v___jp_767_;
}
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_796_; 
v_a_788_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_796_ == 0)
{
v___x_790_ = v___x_766_;
v_isShared_791_ = v_isSharedCheck_796_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_766_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_796_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_792_ = lean_task_map(v___x_765_, v_a_788_, v___x_762_, v___x_763_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_792_);
v___x_794_ = v___x_790_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
v___jp_767_:
{
lean_object* v___x_769_; 
v___x_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_769_, 0, v___y_768_);
return v___x_769_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15___boxed(lean_object* v___f_797_, lean_object* v___f_798_, lean_object* v___f_799_, lean_object* v___x_800_, lean_object* v___x_801_, lean_object* v___y_802_){
_start:
{
uint8_t v___x_13313__boxed_803_; lean_object* v_res_804_; 
v___x_13313__boxed_803_ = lean_unbox(v___x_801_);
v_res_804_ = l_Std_Http_Server_serve___redArg___lam__15(v___f_797_, v___f_798_, v___f_799_, v___x_800_, v___x_13313__boxed_803_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16(lean_object* v___f_805_, lean_object* v___f_806_, lean_object* v_activeConnections_807_, uint8_t v_permitAcquired_808_, lean_object* v___x_809_, lean_object* v_connectionLimit_810_, lean_object* v___x_811_, uint8_t v___x_812_, lean_object* v___f_813_, lean_object* v___x_814_, lean_object* v_inst_815_, lean_object* v_val_816_, lean_object* v_handler_817_, lean_object* v_config_818_, lean_object* v_extensions_819_, lean_object* v___f_820_, lean_object* v___f_821_, lean_object* v_x_822_){
_start:
{
if (lean_obj_tag(v_x_822_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_832_; 
lean_dec_ref(v___f_821_);
lean_dec_ref(v___f_820_);
lean_dec(v_extensions_819_);
lean_dec_ref(v_config_818_);
lean_dec(v_handler_817_);
lean_dec(v_val_816_);
lean_dec_ref(v_inst_815_);
lean_dec_ref(v___x_814_);
lean_dec_ref(v___f_813_);
lean_dec(v___x_811_);
lean_dec(v_connectionLimit_810_);
lean_dec_ref(v_activeConnections_807_);
lean_dec_ref(v___f_806_);
lean_dec_ref(v___f_805_);
v_a_824_ = lean_ctor_get(v_x_822_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v_x_822_);
if (v_isSharedCheck_832_ == 0)
{
v___x_826_ = v_x_822_;
v_isShared_827_ = v_isSharedCheck_832_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v_x_822_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_832_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_831_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v___x_830_; 
v___x_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
return v___x_830_;
}
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_850_; 
v_a_833_ = lean_ctor_get(v_x_822_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v_x_822_);
if (v_isSharedCheck_850_ == 0)
{
v___x_835_ = v_x_822_;
v_isShared_836_ = v_isSharedCheck_850_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v_x_822_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_850_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___f_839_; lean_object* v___x_840_; lean_object* v___f_841_; lean_object* v___x_842_; lean_object* v___f_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_837_ = lean_box(v_permitAcquired_808_);
v___x_838_ = lean_box(v___x_812_);
lean_inc_n(v___x_811_, 2);
lean_inc(v_a_833_);
v___f_839_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__13___boxed), 18, 17);
lean_closure_set(v___f_839_, 0, v___f_805_);
lean_closure_set(v___f_839_, 1, v___f_806_);
lean_closure_set(v___f_839_, 2, v_activeConnections_807_);
lean_closure_set(v___f_839_, 3, v_a_833_);
lean_closure_set(v___f_839_, 4, v___x_837_);
lean_closure_set(v___f_839_, 5, v___x_809_);
lean_closure_set(v___f_839_, 6, v_connectionLimit_810_);
lean_closure_set(v___f_839_, 7, v___x_811_);
lean_closure_set(v___f_839_, 8, v___x_838_);
lean_closure_set(v___f_839_, 9, v___f_813_);
lean_closure_set(v___f_839_, 10, v___x_814_);
lean_closure_set(v___f_839_, 11, v_inst_815_);
lean_closure_set(v___f_839_, 12, v_val_816_);
lean_closure_set(v___f_839_, 13, v_handler_817_);
lean_closure_set(v___f_839_, 14, v_config_818_);
lean_closure_set(v___f_839_, 15, v_extensions_819_);
lean_closure_set(v___f_839_, 16, v___f_820_);
v___x_840_ = lean_box(2);
v___f_841_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__14___boxed), 4, 2);
lean_closure_set(v___f_841_, 0, v_a_833_);
lean_closure_set(v___f_841_, 1, v___x_840_);
v___x_842_ = lean_box(v___x_812_);
v___f_843_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__15___boxed), 6, 5);
lean_closure_set(v___f_843_, 0, v___f_821_);
lean_closure_set(v___f_843_, 1, v___f_839_);
lean_closure_set(v___f_843_, 2, v___f_841_);
lean_closure_set(v___f_843_, 3, v___x_811_);
lean_closure_set(v___f_843_, 4, v___x_842_);
v___x_844_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_844_, 0, lean_box(0));
lean_closure_set(v___x_844_, 1, v___f_843_);
v___x_845_ = lean_io_as_task(v___x_844_, v___x_811_);
lean_dec_ref(v___x_845_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 0, v___x_809_);
v___x_847_ = v___x_835_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_809_);
v___x_847_ = v_reuseFailAlloc_849_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_848_; 
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
return v___x_848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16___boxed(lean_object** _args){
lean_object* v___f_851_ = _args[0];
lean_object* v___f_852_ = _args[1];
lean_object* v_activeConnections_853_ = _args[2];
lean_object* v_permitAcquired_854_ = _args[3];
lean_object* v___x_855_ = _args[4];
lean_object* v_connectionLimit_856_ = _args[5];
lean_object* v___x_857_ = _args[6];
lean_object* v___x_858_ = _args[7];
lean_object* v___f_859_ = _args[8];
lean_object* v___x_860_ = _args[9];
lean_object* v_inst_861_ = _args[10];
lean_object* v_val_862_ = _args[11];
lean_object* v_handler_863_ = _args[12];
lean_object* v_config_864_ = _args[13];
lean_object* v_extensions_865_ = _args[14];
lean_object* v___f_866_ = _args[15];
lean_object* v___f_867_ = _args[16];
lean_object* v_x_868_ = _args[17];
lean_object* v___y_869_ = _args[18];
_start:
{
uint8_t v_permitAcquired_boxed_870_; uint8_t v___x_13393__boxed_871_; lean_object* v_res_872_; 
v_permitAcquired_boxed_870_ = lean_unbox(v_permitAcquired_854_);
v___x_13393__boxed_871_ = lean_unbox(v___x_858_);
v_res_872_ = l_Std_Http_Server_serve___redArg___lam__16(v___f_851_, v___f_852_, v_activeConnections_853_, v_permitAcquired_boxed_870_, v___x_855_, v_connectionLimit_856_, v___x_857_, v___x_13393__boxed_871_, v___f_859_, v___x_860_, v_inst_861_, v_val_862_, v_handler_863_, v_config_864_, v_extensions_865_, v___f_866_, v___f_867_, v_x_868_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17(lean_object* v___x_873_, uint8_t v___x_874_, lean_object* v___f_875_, lean_object* v_x_876_){
_start:
{
if (lean_obj_tag(v_x_876_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_886_; 
lean_dec_ref(v___f_875_);
lean_dec(v___x_873_);
v_a_878_ = lean_ctor_get(v_x_876_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v_x_876_);
if (v_isSharedCheck_886_ == 0)
{
v___x_880_ = v_x_876_;
v_isShared_881_ = v_isSharedCheck_886_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v_x_876_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_886_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_885_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_884_; 
v___x_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
return v___x_884_;
}
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_897_; 
v_a_887_ = lean_ctor_get(v_x_876_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v_x_876_);
if (v_isSharedCheck_897_ == 0)
{
v___x_889_ = v_x_876_;
v_isShared_890_ = v_isSharedCheck_897_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v_x_876_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_897_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_891_ = l_Std_CancellationContext_fork(v_a_887_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_891_);
v___x_893_ = v___x_889_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_896_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
v___x_895_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_873_, v___x_874_, v___x_894_, v___f_875_);
return v___x_895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17___boxed(lean_object* v___x_898_, lean_object* v___x_899_, lean_object* v___f_900_, lean_object* v_x_901_, lean_object* v___y_902_){
_start:
{
uint8_t v___x_13483__boxed_903_; lean_object* v_res_904_; 
v___x_13483__boxed_903_ = lean_unbox(v___x_899_);
v_res_904_ = l_Std_Http_Server_serve___redArg___lam__17(v___x_898_, v___x_13483__boxed_903_, v___f_900_, v_x_901_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18(lean_object* v___f_905_, lean_object* v___f_906_, lean_object* v_activeConnections_907_, uint8_t v_permitAcquired_908_, lean_object* v___x_909_, lean_object* v_connectionLimit_910_, uint8_t v___x_911_, lean_object* v___f_912_, lean_object* v___x_913_, lean_object* v_inst_914_, lean_object* v_val_915_, lean_object* v_handler_916_, lean_object* v_config_917_, lean_object* v___f_918_, lean_object* v___f_919_, lean_object* v___f_920_, lean_object* v_extensions_921_, lean_object* v___y_922_){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___f_927_; lean_object* v___x_928_; lean_object* v___f_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_924_ = lean_unsigned_to_nat(0u);
v___x_925_ = lean_box(v_permitAcquired_908_);
v___x_926_ = lean_box(v___x_911_);
v___f_927_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__16___boxed), 19, 17);
lean_closure_set(v___f_927_, 0, v___f_905_);
lean_closure_set(v___f_927_, 1, v___f_906_);
lean_closure_set(v___f_927_, 2, v_activeConnections_907_);
lean_closure_set(v___f_927_, 3, v___x_925_);
lean_closure_set(v___f_927_, 4, v___x_909_);
lean_closure_set(v___f_927_, 5, v_connectionLimit_910_);
lean_closure_set(v___f_927_, 6, v___x_924_);
lean_closure_set(v___f_927_, 7, v___x_926_);
lean_closure_set(v___f_927_, 8, v___f_912_);
lean_closure_set(v___f_927_, 9, v___x_913_);
lean_closure_set(v___f_927_, 10, v_inst_914_);
lean_closure_set(v___f_927_, 11, v_val_915_);
lean_closure_set(v___f_927_, 12, v_handler_916_);
lean_closure_set(v___f_927_, 13, v_config_917_);
lean_closure_set(v___f_927_, 14, v_extensions_921_);
lean_closure_set(v___f_927_, 15, v___f_918_);
lean_closure_set(v___f_927_, 16, v___f_919_);
v___x_928_ = lean_box(v___x_911_);
v___f_929_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__17___boxed), 5, 3);
lean_closure_set(v___f_929_, 0, v___x_924_);
lean_closure_set(v___f_929_, 1, v___x_928_);
lean_closure_set(v___f_929_, 2, v___f_927_);
lean_inc_ref(v___y_922_);
v___x_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_930_, 0, v___y_922_);
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
v___x_932_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_924_, v___x_911_, v___x_931_, v___f_929_);
v___x_933_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_924_, v___x_911_, v___x_932_, v___f_920_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18___boxed(lean_object** _args){
lean_object* v___f_934_ = _args[0];
lean_object* v___f_935_ = _args[1];
lean_object* v_activeConnections_936_ = _args[2];
lean_object* v_permitAcquired_937_ = _args[3];
lean_object* v___x_938_ = _args[4];
lean_object* v_connectionLimit_939_ = _args[5];
lean_object* v___x_940_ = _args[6];
lean_object* v___f_941_ = _args[7];
lean_object* v___x_942_ = _args[8];
lean_object* v_inst_943_ = _args[9];
lean_object* v_val_944_ = _args[10];
lean_object* v_handler_945_ = _args[11];
lean_object* v_config_946_ = _args[12];
lean_object* v___f_947_ = _args[13];
lean_object* v___f_948_ = _args[14];
lean_object* v___f_949_ = _args[15];
lean_object* v_extensions_950_ = _args[16];
lean_object* v___y_951_ = _args[17];
lean_object* v___y_952_ = _args[18];
_start:
{
uint8_t v_permitAcquired_boxed_953_; uint8_t v___x_13540__boxed_954_; lean_object* v_res_955_; 
v_permitAcquired_boxed_953_ = lean_unbox(v_permitAcquired_937_);
v___x_13540__boxed_954_ = lean_unbox(v___x_940_);
v_res_955_ = l_Std_Http_Server_serve___redArg___lam__18(v___f_934_, v___f_935_, v_activeConnections_936_, v_permitAcquired_boxed_953_, v___x_938_, v_connectionLimit_939_, v___x_13540__boxed_954_, v___f_941_, v___x_942_, v_inst_943_, v_val_944_, v_handler_945_, v_config_946_, v___f_947_, v___f_948_, v___f_949_, v_extensions_950_, v___y_951_);
lean_dec_ref(v___y_951_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__19(lean_object* v___f_956_, lean_object* v___y_957_, lean_object* v_x_958_){
_start:
{
if (lean_obj_tag(v_x_958_) == 0)
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_968_; 
lean_dec_ref(v___f_956_);
v_a_960_ = lean_ctor_get(v_x_958_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v_x_958_);
if (v_isSharedCheck_968_ == 0)
{
v___x_962_ = v_x_958_;
v_isShared_963_ = v_isSharedCheck_968_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v_x_958_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_968_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_967_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
lean_object* v___x_966_; 
v___x_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
return v___x_966_;
}
}
}
else
{
lean_object* v_a_969_; lean_object* v___x_970_; 
v_a_969_ = lean_ctor_get(v_x_958_, 0);
lean_inc(v_a_969_);
lean_dec_ref_known(v_x_958_, 1);
lean_inc_ref(v___y_957_);
v___x_970_ = lean_apply_3(v___f_956_, v_a_969_, v___y_957_, lean_box(0));
return v___x_970_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__19___boxed(lean_object* v___f_971_, lean_object* v___y_972_, lean_object* v_x_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Std_Http_Server_serve___redArg___lam__19(v___f_971_, v___y_972_, v_x_973_);
lean_dec_ref(v___y_972_);
return v_res_975_;
}
}
static lean_object* _init_l_Std_Http_Server_serve___redArg___lam__21___closed__0(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = l_Std_Http_Extensions_empty;
v___x_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
return v___x_977_;
}
}
static lean_object* _init_l_Std_Http_Server_serve___redArg___lam__21___closed__1(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = lean_obj_once(&l_Std_Http_Server_serve___redArg___lam__21___closed__0, &l_Std_Http_Server_serve___redArg___lam__21___closed__0_once, _init_l_Std_Http_Server_serve___redArg___lam__21___closed__0);
v___x_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21(uint8_t v___x_981_, lean_object* v___f_982_, lean_object* v___x_983_, lean_object* v___f_984_, lean_object* v_x_985_){
_start:
{
if (lean_obj_tag(v_x_985_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_995_; 
lean_dec_ref(v___f_984_);
lean_dec(v___x_983_);
lean_dec_ref(v___f_982_);
v_a_987_ = lean_ctor_get(v_x_985_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v_x_985_);
if (v_isSharedCheck_995_ == 0)
{
v___x_989_ = v_x_985_;
v_isShared_990_ = v_isSharedCheck_995_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v_x_985_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_995_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_994_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
lean_object* v___x_993_; 
v___x_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
return v___x_993_;
}
}
}
else
{
lean_object* v_a_996_; 
v_a_996_ = lean_ctor_get(v_x_985_, 0);
lean_inc(v_a_996_);
lean_dec_ref_known(v_x_985_, 1);
if (lean_obj_tag(v_a_996_) == 0)
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
lean_dec_ref_known(v_a_996_, 1);
lean_dec_ref(v___f_984_);
lean_dec(v___x_983_);
v___x_997_ = lean_unsigned_to_nat(0u);
v___x_998_ = lean_obj_once(&l_Std_Http_Server_serve___redArg___lam__21___closed__1, &l_Std_Http_Server_serve___redArg___lam__21___closed__1_once, _init_l_Std_Http_Server_serve___redArg___lam__21___closed__1);
v___x_999_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_997_, v___x_981_, v___x_998_, v___f_982_);
return v___x_999_;
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1015_; 
lean_dec_ref(v___f_982_);
v_a_1000_ = lean_ctor_get(v_a_996_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_a_996_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1002_ = v_a_996_;
v_isShared_1003_ = v_isSharedCheck_1015_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v_a_996_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1015_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1004_; lean_object* v_dyn_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1011_; 
v___x_1004_ = l_Std_Http_Extensions_empty;
v_dyn_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_1005_, 0, v___x_983_);
lean_ctor_set(v_dyn_1005_, 1, v_a_1000_);
v___x_1006_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__21___closed__2));
v___x_1007_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_1005_);
v___x_1008_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_1006_, v___x_1007_, v_dyn_1005_, v___x_1004_);
v___x_1009_ = lean_unsigned_to_nat(0u);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v___x_1008_);
v___x_1011_ = v___x_1002_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1008_);
v___x_1011_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
v___x_1013_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1009_, v___x_981_, v___x_1012_, v___f_984_);
return v___x_1013_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21___boxed(lean_object* v___x_1016_, lean_object* v___f_1017_, lean_object* v___x_1018_, lean_object* v___f_1019_, lean_object* v_x_1020_, lean_object* v___y_1021_){
_start:
{
uint8_t v___x_13640__boxed_1022_; lean_object* v_res_1023_; 
v___x_13640__boxed_1022_ = lean_unbox(v___x_1016_);
v_res_1023_ = l_Std_Http_Server_serve___redArg___lam__21(v___x_13640__boxed_1022_, v___f_1017_, v___x_1018_, v___f_1019_, v_x_1020_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20(uint8_t v_permitAcquired_1024_, lean_object* v___f_1025_, lean_object* v___x_1026_, lean_object* v___y_1027_, lean_object* v_connectionLimit_1028_, uint8_t v___x_1029_, lean_object* v___f_1030_, lean_object* v___f_1031_, lean_object* v___f_1032_, lean_object* v_activeConnections_1033_, lean_object* v___f_1034_, lean_object* v___x_1035_, lean_object* v_inst_1036_, lean_object* v_handler_1037_, lean_object* v_config_1038_, lean_object* v___f_1039_, lean_object* v___f_1040_, lean_object* v___f_1041_, lean_object* v___x_1042_, lean_object* v_x_1043_){
_start:
{
if (lean_obj_tag(v_x_1043_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1053_; 
lean_dec(v___x_1042_);
lean_dec_ref(v___f_1041_);
lean_dec_ref(v___f_1040_);
lean_dec_ref(v___f_1039_);
lean_dec_ref(v_config_1038_);
lean_dec(v_handler_1037_);
lean_dec_ref(v_inst_1036_);
lean_dec_ref(v___x_1035_);
lean_dec_ref(v___f_1034_);
lean_dec_ref(v_activeConnections_1033_);
lean_dec_ref(v___f_1032_);
lean_dec_ref(v___f_1031_);
lean_dec_ref(v___f_1030_);
lean_dec(v_connectionLimit_1028_);
lean_dec_ref(v___f_1025_);
v_a_1045_ = lean_ctor_get(v_x_1043_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_x_1043_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1047_ = v_x_1043_;
v_isShared_1048_ = v_isSharedCheck_1053_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v_x_1043_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1053_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
return v___x_1051_;
}
}
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1112_; 
v_a_1054_ = lean_ctor_get(v_x_1043_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v_x_1043_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1056_ = v_x_1043_;
v_isShared_1057_ = v_isSharedCheck_1112_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v_x_1043_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1112_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
if (lean_obj_tag(v_a_1054_) == 0)
{
lean_dec(v___x_1042_);
lean_dec_ref(v___f_1041_);
lean_dec_ref(v___f_1040_);
lean_dec_ref(v___f_1039_);
lean_dec_ref(v_config_1038_);
lean_dec(v_handler_1037_);
lean_dec_ref(v_inst_1036_);
lean_dec_ref(v___x_1035_);
lean_dec_ref(v___f_1034_);
lean_dec_ref(v_activeConnections_1033_);
lean_dec_ref(v___f_1032_);
lean_dec_ref(v___f_1031_);
if (v_permitAcquired_1024_ == 0)
{
lean_object* v___x_1058_; 
lean_del_object(v___x_1056_);
lean_dec_ref(v___f_1030_);
lean_dec(v_connectionLimit_1028_);
lean_inc_ref(v___y_1027_);
v___x_1058_ = lean_apply_3(v___f_1025_, v___x_1026_, v___y_1027_, lean_box(0));
return v___x_1058_;
}
else
{
if (lean_obj_tag(v_connectionLimit_1028_) == 1)
{
lean_object* v_val_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1072_; 
lean_dec_ref(v___f_1025_);
v_val_1059_ = lean_ctor_get(v_connectionLimit_1028_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_connectionLimit_1028_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1061_ = v_connectionLimit_1028_;
v_isShared_1062_ = v_isSharedCheck_1072_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_val_1059_);
lean_dec(v_connectionLimit_1028_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1072_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1066_; 
v___x_1063_ = lean_unsigned_to_nat(0u);
v___x_1064_ = l_Std_Semaphore_release(v_val_1059_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v___x_1064_);
v___x_1066_ = v___x_1056_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1068_; 
if (v_isShared_1062_ == 0)
{
lean_ctor_set_tag(v___x_1061_, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1066_);
v___x_1068_ = v___x_1061_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
lean_object* v___x_1069_; 
v___x_1069_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1063_, v___x_1029_, v___x_1068_, v___f_1030_);
return v___x_1069_;
}
}
}
}
else
{
lean_object* v___x_1073_; 
lean_del_object(v___x_1056_);
lean_dec_ref(v___f_1030_);
lean_dec(v_connectionLimit_1028_);
lean_inc_ref(v___y_1027_);
v___x_1073_ = lean_apply_3(v___f_1025_, v___x_1026_, v___y_1027_, lean_box(0));
return v___x_1073_;
}
}
}
else
{
lean_object* v_val_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1111_; 
lean_dec_ref(v___f_1030_);
lean_dec_ref(v___f_1025_);
v_val_1074_ = lean_ctor_get(v_a_1054_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_a_1054_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1076_ = v_a_1054_;
v_isShared_1077_ = v_isSharedCheck_1111_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_val_1074_);
lean_dec(v_a_1054_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1111_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___f_1080_; lean_object* v___f_1081_; lean_object* v___x_1082_; lean_object* v___f_1083_; lean_object* v___x_1084_; lean_object* v_val_1086_; lean_object* v___x_1094_; 
v___x_1078_ = lean_box(v_permitAcquired_1024_);
v___x_1079_ = lean_box(v___x_1029_);
lean_inc(v_val_1074_);
v___f_1080_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__18___boxed), 19, 16);
lean_closure_set(v___f_1080_, 0, v___f_1031_);
lean_closure_set(v___f_1080_, 1, v___f_1032_);
lean_closure_set(v___f_1080_, 2, v_activeConnections_1033_);
lean_closure_set(v___f_1080_, 3, v___x_1078_);
lean_closure_set(v___f_1080_, 4, v___x_1026_);
lean_closure_set(v___f_1080_, 5, v_connectionLimit_1028_);
lean_closure_set(v___f_1080_, 6, v___x_1079_);
lean_closure_set(v___f_1080_, 7, v___f_1034_);
lean_closure_set(v___f_1080_, 8, v___x_1035_);
lean_closure_set(v___f_1080_, 9, v_inst_1036_);
lean_closure_set(v___f_1080_, 10, v_val_1074_);
lean_closure_set(v___f_1080_, 11, v_handler_1037_);
lean_closure_set(v___f_1080_, 12, v_config_1038_);
lean_closure_set(v___f_1080_, 13, v___f_1039_);
lean_closure_set(v___f_1080_, 14, v___f_1040_);
lean_closure_set(v___f_1080_, 15, v___f_1041_);
lean_inc_ref(v___y_1027_);
v___f_1081_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__19___boxed), 4, 2);
lean_closure_set(v___f_1081_, 0, v___f_1080_);
lean_closure_set(v___f_1081_, 1, v___y_1027_);
v___x_1082_ = lean_box(v___x_1029_);
lean_inc_ref(v___f_1081_);
v___f_1083_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__21___boxed), 6, 4);
lean_closure_set(v___f_1083_, 0, v___x_1082_);
lean_closure_set(v___f_1083_, 1, v___f_1081_);
lean_closure_set(v___f_1083_, 2, v___x_1042_);
lean_closure_set(v___f_1083_, 3, v___f_1081_);
v___x_1084_ = lean_unsigned_to_nat(0u);
v___x_1094_ = lean_uv_tcp_getpeername(v_val_1074_);
lean_dec(v_val_1074_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1094_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1094_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
lean_ctor_set_tag(v___x_1097_, 1);
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
v_val_1086_ = v___x_1100_;
goto v___jp_1085_;
}
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
v_a_1103_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1094_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1094_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
lean_ctor_set_tag(v___x_1105_, 0);
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
v_val_1086_ = v___x_1108_;
goto v___jp_1085_;
}
}
}
v___jp_1085_:
{
lean_object* v___x_1088_; 
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v_val_1086_);
v___x_1088_ = v___x_1056_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_val_1086_);
v___x_1088_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1090_; 
if (v_isShared_1077_ == 0)
{
lean_ctor_set_tag(v___x_1076_, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1088_);
v___x_1090_ = v___x_1076_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
lean_object* v___x_1091_; 
v___x_1091_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1084_, v___x_1029_, v___x_1090_, v___f_1083_);
return v___x_1091_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20___boxed(lean_object** _args){
lean_object* v_permitAcquired_1113_ = _args[0];
lean_object* v___f_1114_ = _args[1];
lean_object* v___x_1115_ = _args[2];
lean_object* v___y_1116_ = _args[3];
lean_object* v_connectionLimit_1117_ = _args[4];
lean_object* v___x_1118_ = _args[5];
lean_object* v___f_1119_ = _args[6];
lean_object* v___f_1120_ = _args[7];
lean_object* v___f_1121_ = _args[8];
lean_object* v_activeConnections_1122_ = _args[9];
lean_object* v___f_1123_ = _args[10];
lean_object* v___x_1124_ = _args[11];
lean_object* v_inst_1125_ = _args[12];
lean_object* v_handler_1126_ = _args[13];
lean_object* v_config_1127_ = _args[14];
lean_object* v___f_1128_ = _args[15];
lean_object* v___f_1129_ = _args[16];
lean_object* v___f_1130_ = _args[17];
lean_object* v___x_1131_ = _args[18];
lean_object* v_x_1132_ = _args[19];
lean_object* v___y_1133_ = _args[20];
_start:
{
uint8_t v_permitAcquired_boxed_1134_; uint8_t v___x_13723__boxed_1135_; lean_object* v_res_1136_; 
v_permitAcquired_boxed_1134_ = lean_unbox(v_permitAcquired_1113_);
v___x_13723__boxed_1135_ = lean_unbox(v___x_1118_);
v_res_1136_ = l_Std_Http_Server_serve___redArg___lam__20(v_permitAcquired_boxed_1134_, v___f_1114_, v___x_1115_, v___y_1116_, v_connectionLimit_1117_, v___x_13723__boxed_1135_, v___f_1119_, v___f_1120_, v___f_1121_, v_activeConnections_1122_, v___f_1123_, v___x_1124_, v_inst_1125_, v_handler_1126_, v_config_1127_, v___f_1128_, v___f_1129_, v___f_1130_, v___x_1131_, v_x_1132_);
lean_dec_ref(v___y_1116_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22(lean_object* v_a_1137_, lean_object* v___f_1138_, lean_object* v___f_1139_, uint8_t v___x_1140_, lean_object* v___f_1141_, lean_object* v_x_1142_){
_start:
{
if (lean_obj_tag(v_x_1142_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1152_; 
lean_dec_ref(v___f_1141_);
lean_dec_ref(v___f_1139_);
lean_dec_ref(v___f_1138_);
lean_dec(v_a_1137_);
v_a_1144_ = lean_ctor_get(v_x_1142_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_x_1142_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1146_ = v_x_1142_;
v_isShared_1147_ = v_isSharedCheck_1152_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v_x_1142_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1152_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1150_; 
v___x_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
return v___x_1150_;
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v_a_1153_ = lean_ctor_get(v_x_1142_, 0);
lean_inc(v_a_1153_);
lean_dec_ref_known(v_x_1142_, 1);
v___x_1154_ = l_Std_Async_TCP_Socket_Server_acceptSelector(v_a_1137_);
v___x_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
lean_ctor_set(v___x_1155_, 1, v___f_1138_);
v___x_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1156_, 0, v_a_1153_);
lean_ctor_set(v___x_1156_, 1, v___f_1139_);
v___x_1157_ = lean_unsigned_to_nat(2u);
v___x_1158_ = lean_mk_empty_array_with_capacity(v___x_1157_);
v___x_1159_ = lean_array_push(v___x_1158_, v___x_1155_);
v___x_1160_ = lean_array_push(v___x_1159_, v___x_1156_);
v___x_1161_ = lean_unsigned_to_nat(0u);
v___x_1162_ = l_Std_Async_Selectable_one___redArg(v___x_1160_);
v___x_1163_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1161_, v___x_1140_, v___x_1162_, v___f_1141_);
return v___x_1163_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22___boxed(lean_object* v_a_1164_, lean_object* v___f_1165_, lean_object* v___f_1166_, lean_object* v___x_1167_, lean_object* v___f_1168_, lean_object* v_x_1169_, lean_object* v___y_1170_){
_start:
{
uint8_t v___x_13907__boxed_1171_; lean_object* v_res_1172_; 
v___x_13907__boxed_1171_ = lean_unbox(v___x_1167_);
v_res_1172_ = l_Std_Http_Server_serve___redArg___lam__22(v_a_1164_, v___f_1165_, v___f_1166_, v___x_13907__boxed_1171_, v___f_1168_, v_x_1169_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23(lean_object* v___f_1173_, lean_object* v___x_1174_, lean_object* v_connectionLimit_1175_, uint8_t v___x_1176_, lean_object* v___f_1177_, lean_object* v___f_1178_, lean_object* v_activeConnections_1179_, lean_object* v___f_1180_, lean_object* v___x_1181_, lean_object* v_inst_1182_, lean_object* v_handler_1183_, lean_object* v_config_1184_, lean_object* v___f_1185_, lean_object* v___f_1186_, lean_object* v___f_1187_, lean_object* v___x_1188_, lean_object* v_a_1189_, lean_object* v___f_1190_, lean_object* v___f_1191_, lean_object* v___f_1192_, uint8_t v_permitAcquired_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v___f_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___f_1199_; lean_object* v___x_1200_; lean_object* v___f_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_inc_ref_n(v___y_1194_, 3);
lean_inc_ref(v___f_1173_);
v___f_1196_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__8___boxed), 4, 2);
lean_closure_set(v___f_1196_, 0, v___f_1173_);
lean_closure_set(v___f_1196_, 1, v___y_1194_);
v___x_1197_ = lean_box(v_permitAcquired_1193_);
v___x_1198_ = lean_box(v___x_1176_);
v___f_1199_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__20___boxed), 21, 19);
lean_closure_set(v___f_1199_, 0, v___x_1197_);
lean_closure_set(v___f_1199_, 1, v___f_1173_);
lean_closure_set(v___f_1199_, 2, v___x_1174_);
lean_closure_set(v___f_1199_, 3, v___y_1194_);
lean_closure_set(v___f_1199_, 4, v_connectionLimit_1175_);
lean_closure_set(v___f_1199_, 5, v___x_1198_);
lean_closure_set(v___f_1199_, 6, v___f_1196_);
lean_closure_set(v___f_1199_, 7, v___f_1177_);
lean_closure_set(v___f_1199_, 8, v___f_1178_);
lean_closure_set(v___f_1199_, 9, v_activeConnections_1179_);
lean_closure_set(v___f_1199_, 10, v___f_1180_);
lean_closure_set(v___f_1199_, 11, v___x_1181_);
lean_closure_set(v___f_1199_, 12, v_inst_1182_);
lean_closure_set(v___f_1199_, 13, v_handler_1183_);
lean_closure_set(v___f_1199_, 14, v_config_1184_);
lean_closure_set(v___f_1199_, 15, v___f_1185_);
lean_closure_set(v___f_1199_, 16, v___f_1186_);
lean_closure_set(v___f_1199_, 17, v___f_1187_);
lean_closure_set(v___f_1199_, 18, v___x_1188_);
v___x_1200_ = lean_box(v___x_1176_);
v___f_1201_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__22___boxed), 7, 5);
lean_closure_set(v___f_1201_, 0, v_a_1189_);
lean_closure_set(v___f_1201_, 1, v___f_1190_);
lean_closure_set(v___f_1201_, 2, v___f_1191_);
lean_closure_set(v___f_1201_, 3, v___x_1200_);
lean_closure_set(v___f_1201_, 4, v___f_1199_);
v___x_1202_ = lean_unsigned_to_nat(0u);
v___x_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1203_, 0, v___y_1194_);
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
v___x_1205_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1202_, v___x_1176_, v___x_1204_, v___f_1192_);
v___x_1206_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1202_, v___x_1176_, v___x_1205_, v___f_1201_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23___boxed(lean_object** _args){
lean_object* v___f_1207_ = _args[0];
lean_object* v___x_1208_ = _args[1];
lean_object* v_connectionLimit_1209_ = _args[2];
lean_object* v___x_1210_ = _args[3];
lean_object* v___f_1211_ = _args[4];
lean_object* v___f_1212_ = _args[5];
lean_object* v_activeConnections_1213_ = _args[6];
lean_object* v___f_1214_ = _args[7];
lean_object* v___x_1215_ = _args[8];
lean_object* v_inst_1216_ = _args[9];
lean_object* v_handler_1217_ = _args[10];
lean_object* v_config_1218_ = _args[11];
lean_object* v___f_1219_ = _args[12];
lean_object* v___f_1220_ = _args[13];
lean_object* v___f_1221_ = _args[14];
lean_object* v___x_1222_ = _args[15];
lean_object* v_a_1223_ = _args[16];
lean_object* v___f_1224_ = _args[17];
lean_object* v___f_1225_ = _args[18];
lean_object* v___f_1226_ = _args[19];
lean_object* v_permitAcquired_1227_ = _args[20];
lean_object* v___y_1228_ = _args[21];
lean_object* v___y_1229_ = _args[22];
_start:
{
uint8_t v___x_13967__boxed_1230_; uint8_t v_permitAcquired_boxed_1231_; lean_object* v_res_1232_; 
v___x_13967__boxed_1230_ = lean_unbox(v___x_1210_);
v_permitAcquired_boxed_1231_ = lean_unbox(v_permitAcquired_1227_);
v_res_1232_ = l_Std_Http_Server_serve___redArg___lam__23(v___f_1207_, v___x_1208_, v_connectionLimit_1209_, v___x_13967__boxed_1230_, v___f_1211_, v___f_1212_, v_activeConnections_1213_, v___f_1214_, v___x_1215_, v_inst_1216_, v_handler_1217_, v_config_1218_, v___f_1219_, v___f_1220_, v___f_1221_, v___x_1222_, v_a_1223_, v___f_1224_, v___f_1225_, v___f_1226_, v_permitAcquired_boxed_1231_, v___y_1228_);
lean_dec_ref(v___y_1228_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24(lean_object* v___f_1233_, lean_object* v___y_1234_, lean_object* v_x_1235_){
_start:
{
if (lean_obj_tag(v_x_1235_) == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1245_; 
lean_dec_ref(v___y_1234_);
lean_dec_ref(v___f_1233_);
v_a_1237_ = lean_ctor_get(v_x_1235_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_x_1235_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1239_ = v_x_1235_;
v_isShared_1240_ = v_isSharedCheck_1245_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v_x_1235_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1245_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1243_; 
v___x_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
return v___x_1243_;
}
}
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1247_; 
v_a_1246_ = lean_ctor_get(v_x_1235_, 0);
lean_inc(v_a_1246_);
lean_dec_ref_known(v_x_1235_, 1);
v___x_1247_ = lean_apply_3(v___f_1233_, v_a_1246_, v___y_1234_, lean_box(0));
return v___x_1247_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24___boxed(lean_object* v___f_1248_, lean_object* v___y_1249_, lean_object* v_x_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Std_Http_Server_serve___redArg___lam__24(v___f_1248_, v___y_1249_, v_x_1250_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26(uint8_t v___x_1253_, uint8_t v___x_1254_, lean_object* v___f_1255_, lean_object* v_x_1256_){
_start:
{
if (lean_obj_tag(v_x_1256_) == 0)
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1266_; 
lean_dec_ref(v___f_1255_);
v_a_1258_ = lean_ctor_get(v_x_1256_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_x_1256_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1260_ = v_x_1256_;
v_isShared_1261_ = v_isSharedCheck_1266_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v_x_1256_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1266_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
lean_object* v___x_1264_; 
v___x_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
return v___x_1264_;
}
}
}
else
{
lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1277_; 
v_isSharedCheck_1277_ = !lean_is_exclusive(v_x_1256_);
if (v_isSharedCheck_1277_ == 0)
{
lean_object* v_unused_1278_; 
v_unused_1278_ = lean_ctor_get(v_x_1256_, 0);
lean_dec(v_unused_1278_);
v___x_1268_ = v_x_1256_;
v_isShared_1269_ = v_isSharedCheck_1277_;
goto v_resetjp_1267_;
}
else
{
lean_dec(v_x_1256_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1277_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1270_ = lean_unsigned_to_nat(0u);
v___x_1271_ = lean_box(v___x_1253_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1271_);
v___x_1273_ = v___x_1268_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
v___x_1275_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1270_, v___x_1254_, v___x_1274_, v___f_1255_);
return v___x_1275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26___boxed(lean_object* v___x_1279_, lean_object* v___x_1280_, lean_object* v___f_1281_, lean_object* v_x_1282_, lean_object* v___y_1283_){
_start:
{
uint8_t v___x_14075__boxed_1284_; uint8_t v___x_14076__boxed_1285_; lean_object* v_res_1286_; 
v___x_14075__boxed_1284_ = lean_unbox(v___x_1279_);
v___x_14076__boxed_1285_ = lean_unbox(v___x_1280_);
v_res_1286_ = l_Std_Http_Server_serve___redArg___lam__26(v___x_14075__boxed_1284_, v___x_14076__boxed_1285_, v___f_1281_, v_x_1282_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25(lean_object* v___f_1287_, uint8_t v___x_1288_, lean_object* v___f_1289_, lean_object* v_x_1290_){
_start:
{
if (lean_obj_tag(v_x_1290_) == 0)
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1300_; 
lean_dec_ref(v___f_1289_);
lean_dec_ref(v___f_1287_);
v_a_1292_ = lean_ctor_get(v_x_1290_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_x_1290_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1294_ = v_x_1290_;
v_isShared_1295_ = v_isSharedCheck_1300_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v_x_1290_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1300_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
lean_object* v___x_1298_; 
v___x_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
return v___x_1298_;
}
}
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v_a_1301_ = lean_ctor_get(v_x_1290_, 0);
lean_inc(v_a_1301_);
lean_dec_ref_known(v_x_1290_, 1);
v___x_1302_ = lean_unsigned_to_nat(0u);
v___x_1303_ = l_IO_Promise_result_x21___redArg(v_a_1301_);
lean_dec(v_a_1301_);
v___x_1304_ = lean_task_map(v___f_1287_, v___x_1303_, v___x_1302_, v___x_1288_);
v___x_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
v___x_1306_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1302_, v___x_1288_, v___x_1305_, v___f_1289_);
return v___x_1306_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25___boxed(lean_object* v___f_1307_, lean_object* v___x_1308_, lean_object* v___f_1309_, lean_object* v_x_1310_, lean_object* v___y_1311_){
_start:
{
uint8_t v___x_14134__boxed_1312_; lean_object* v_res_1313_; 
v___x_14134__boxed_1312_ = lean_unbox(v___x_1308_);
v_res_1313_ = l_Std_Http_Server_serve___redArg___lam__25(v___f_1307_, v___x_14134__boxed_1312_, v___f_1309_, v_x_1310_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27(lean_object* v_connectionLimit_1314_, uint8_t v___x_1315_, lean_object* v___f_1316_, lean_object* v___f_1317_, lean_object* v___f_1318_, lean_object* v_u_1319_, lean_object* v_b_1320_){
_start:
{
if (lean_obj_tag(v_connectionLimit_1314_) == 1)
{
lean_object* v_val_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1339_; 
lean_dec_ref(v___f_1318_);
v_val_1322_ = lean_ctor_get(v_connectionLimit_1314_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v_connectionLimit_1314_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1324_ = v_connectionLimit_1314_;
v_isShared_1325_ = v_isSharedCheck_1339_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_val_1322_);
lean_dec(v_connectionLimit_1314_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1339_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
uint8_t v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___f_1329_; lean_object* v___x_1330_; lean_object* v___f_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1335_; 
v___x_1326_ = 1;
v___x_1327_ = lean_box(v___x_1326_);
v___x_1328_ = lean_box(v___x_1315_);
v___f_1329_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__26___boxed), 5, 3);
lean_closure_set(v___f_1329_, 0, v___x_1327_);
lean_closure_set(v___f_1329_, 1, v___x_1328_);
lean_closure_set(v___f_1329_, 2, v___f_1316_);
v___x_1330_ = lean_box(v___x_1315_);
v___f_1331_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__25___boxed), 5, 3);
lean_closure_set(v___f_1331_, 0, v___f_1317_);
lean_closure_set(v___f_1331_, 1, v___x_1330_);
lean_closure_set(v___f_1331_, 2, v___f_1329_);
v___x_1332_ = lean_unsigned_to_nat(0u);
v___x_1333_ = l_Std_Semaphore_acquire(v_val_1322_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v___x_1333_);
v___x_1335_ = v___x_1324_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
v___x_1337_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1332_, v___x_1315_, v___x_1336_, v___f_1331_);
return v___x_1337_;
}
}
}
else
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
lean_dec_ref(v___f_1317_);
lean_dec_ref(v___f_1316_);
lean_dec(v_connectionLimit_1314_);
v___x_1340_ = lean_unsigned_to_nat(0u);
v___x_1341_ = lean_box(v___x_1315_);
v___x_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
v___x_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
v___x_1344_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1340_, v___x_1315_, v___x_1343_, v___f_1318_);
return v___x_1344_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27___boxed(lean_object* v_connectionLimit_1345_, lean_object* v___x_1346_, lean_object* v___f_1347_, lean_object* v___f_1348_, lean_object* v___f_1349_, lean_object* v_u_1350_, lean_object* v_b_1351_, lean_object* v___y_1352_){
_start:
{
uint8_t v___x_14178__boxed_1353_; lean_object* v_res_1354_; 
v___x_14178__boxed_1353_ = lean_unbox(v___x_1346_);
v_res_1354_ = l_Std_Http_Server_serve___redArg___lam__27(v_connectionLimit_1345_, v___x_14178__boxed_1353_, v___f_1347_, v___f_1348_, v___f_1349_, v_u_1350_, v_b_1351_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28(lean_object* v_a_1355_, lean_object* v_x_1356_){
_start:
{
if (lean_obj_tag(v_x_1356_) == 0)
{
lean_object* v___x_1358_; 
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v_x_1356_);
return v___x_1358_;
}
else
{
lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1366_; 
v_isSharedCheck_1366_ = !lean_is_exclusive(v_x_1356_);
if (v_isSharedCheck_1366_ == 0)
{
lean_object* v_unused_1367_; 
v_unused_1367_ = lean_ctor_get(v_x_1356_, 0);
lean_dec(v_unused_1367_);
v___x_1360_ = v_x_1356_;
v_isShared_1361_ = v_isSharedCheck_1366_;
goto v_resetjp_1359_;
}
else
{
lean_dec(v_x_1356_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1366_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1362_; lean_object* v___x_1364_; 
v___x_1362_ = l_IO_Promise_result_x21___redArg(v_a_1355_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v___x_1362_);
v___x_1364_ = v___x_1360_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1362_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28___boxed(lean_object* v_a_1368_, lean_object* v_x_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Std_Http_Server_serve___redArg___lam__28(v_a_1368_, v_x_1369_);
lean_dec(v_a_1368_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29(lean_object* v___f_1372_, lean_object* v___x_1373_, lean_object* v___x_1374_, uint8_t v___x_1375_, lean_object* v_x_1376_){
_start:
{
if (lean_obj_tag(v_x_1376_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1386_; 
lean_dec(v___x_1373_);
lean_dec_ref(v___f_1372_);
v_a_1378_ = lean_ctor_get(v_x_1376_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v_x_1376_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1380_ = v_x_1376_;
v_isShared_1381_ = v_isSharedCheck_1386_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v_x_1376_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1386_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
lean_object* v___x_1384_; 
v___x_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
return v___x_1384_;
}
}
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1398_; 
v_a_1387_ = lean_ctor_get(v_x_1376_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_x_1376_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1389_ = v_x_1376_;
v_isShared_1390_ = v_isSharedCheck_1398_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v_x_1376_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1398_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___f_1391_; lean_object* v___x_1392_; lean_object* v___x_1394_; 
lean_inc(v_a_1387_);
v___f_1391_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__28___boxed), 3, 1);
lean_closure_set(v___f_1391_, 0, v_a_1387_);
lean_inc(v___x_1373_);
v___x_1392_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_1372_, v___x_1373_, v_a_1387_, v___x_1374_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1392_);
v___x_1394_ = v___x_1389_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
v___x_1396_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1373_, v___x_1375_, v___x_1395_, v___f_1391_);
return v___x_1396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29___boxed(lean_object* v___f_1399_, lean_object* v___x_1400_, lean_object* v___x_1401_, lean_object* v___x_1402_, lean_object* v_x_1403_, lean_object* v___y_1404_){
_start:
{
uint8_t v___x_14273__boxed_1405_; lean_object* v_res_1406_; 
v___x_14273__boxed_1405_ = lean_unbox(v___x_1402_);
v_res_1406_ = l_Std_Http_Server_serve___redArg___lam__29(v___f_1399_, v___x_1400_, v___x_1401_, v___x_14273__boxed_1405_, v_x_1403_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30(lean_object* v___f_1407_, lean_object* v_connectionLimit_1408_, uint8_t v___x_1409_, lean_object* v___f_1410_, lean_object* v___x_1411_, lean_object* v___f_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v___f_1415_; lean_object* v___x_1416_; lean_object* v___f_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___f_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___f_1415_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__24___boxed), 4, 2);
lean_closure_set(v___f_1415_, 0, v___f_1407_);
lean_closure_set(v___f_1415_, 1, v___y_1413_);
v___x_1416_ = lean_box(v___x_1409_);
lean_inc_ref(v___f_1415_);
v___f_1417_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__27___boxed), 8, 5);
lean_closure_set(v___f_1417_, 0, v_connectionLimit_1408_);
lean_closure_set(v___f_1417_, 1, v___x_1416_);
lean_closure_set(v___f_1417_, 2, v___f_1415_);
lean_closure_set(v___f_1417_, 3, v___f_1410_);
lean_closure_set(v___f_1417_, 4, v___f_1415_);
v___x_1418_ = lean_unsigned_to_nat(0u);
v___x_1419_ = lean_box(v___x_1409_);
v___f_1420_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__29___boxed), 6, 4);
lean_closure_set(v___f_1420_, 0, v___f_1417_);
lean_closure_set(v___f_1420_, 1, v___x_1418_);
lean_closure_set(v___f_1420_, 2, v___x_1411_);
lean_closure_set(v___f_1420_, 3, v___x_1419_);
v___x_1421_ = lean_io_promise_new();
v___x_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
v___x_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
v___x_1424_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1418_, v___x_1409_, v___x_1423_, v___f_1420_);
v___x_1425_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1418_, v___x_1409_, v___x_1424_, v___f_1412_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30___boxed(lean_object* v___f_1426_, lean_object* v_connectionLimit_1427_, lean_object* v___x_1428_, lean_object* v___f_1429_, lean_object* v___x_1430_, lean_object* v___f_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
uint8_t v___x_14331__boxed_1434_; lean_object* v_res_1435_; 
v___x_14331__boxed_1434_ = lean_unbox(v___x_1428_);
v_res_1435_ = l_Std_Http_Server_serve___redArg___lam__30(v___f_1426_, v_connectionLimit_1427_, v___x_14331__boxed_1434_, v___f_1429_, v___x_1430_, v___f_1431_, v___y_1432_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31(lean_object* v___f_1440_, lean_object* v___f_1441_, lean_object* v___x_1442_, lean_object* v_inst_1443_, lean_object* v_handler_1444_, lean_object* v_config_1445_, lean_object* v___f_1446_, lean_object* v___f_1447_, lean_object* v___x_1448_, lean_object* v_a_1449_, lean_object* v___f_1450_, lean_object* v___f_1451_, lean_object* v___f_1452_, lean_object* v___f_1453_, lean_object* v___f_1454_, lean_object* v_x_1455_){
_start:
{
if (lean_obj_tag(v_x_1455_) == 0)
{
lean_object* v___x_1457_; 
lean_dec_ref(v___f_1454_);
lean_dec_ref(v___f_1453_);
lean_dec_ref(v___f_1452_);
lean_dec_ref(v___f_1451_);
lean_dec_ref(v___f_1450_);
lean_dec(v_a_1449_);
lean_dec(v___x_1448_);
lean_dec_ref(v___f_1447_);
lean_dec_ref(v___f_1446_);
lean_dec_ref(v_config_1445_);
lean_dec(v_handler_1444_);
lean_dec_ref(v_inst_1443_);
lean_dec_ref(v___x_1442_);
lean_dec_ref(v___f_1441_);
lean_dec_ref(v___f_1440_);
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v_x_1455_);
return v___x_1457_;
}
else
{
lean_object* v_a_1458_; lean_object* v_context_1459_; lean_object* v_activeConnections_1460_; lean_object* v_connectionLimit_1461_; lean_object* v_shutdownDone_1462_; lean_object* v___f_1463_; lean_object* v___f_1464_; lean_object* v___f_1465_; uint8_t v___x_1466_; lean_object* v___x_1467_; lean_object* v___f_1468_; lean_object* v___f_1469_; lean_object* v___x_1470_; lean_object* v___f_1471_; lean_object* v___x_1472_; lean_object* v___f_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v_a_1458_ = lean_ctor_get(v_x_1455_, 0);
lean_inc(v_a_1458_);
v_context_1459_ = lean_ctor_get(v_a_1458_, 0);
lean_inc_ref_n(v_context_1459_, 2);
v_activeConnections_1460_ = lean_ctor_get(v_a_1458_, 1);
v_connectionLimit_1461_ = lean_ctor_get(v_a_1458_, 2);
v_shutdownDone_1462_ = lean_ctor_get(v_a_1458_, 3);
v___f_1463_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_1463_, 0, v_x_1455_);
lean_inc_ref(v_shutdownDone_1462_);
v___f_1464_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1464_, 0, v_context_1459_);
lean_closure_set(v___f_1464_, 1, v_shutdownDone_1462_);
v___f_1465_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed), 5, 1);
lean_closure_set(v___f_1465_, 0, v___f_1464_);
v___x_1466_ = 0;
v___x_1467_ = lean_box(0);
v___f_1468_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__31___closed__0));
v___f_1469_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__31___closed__1));
v___x_1470_ = lean_box(v___x_1466_);
lean_inc_ref(v_activeConnections_1460_);
lean_inc_n(v_connectionLimit_1461_, 2);
v___f_1471_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__23___boxed), 23, 20);
lean_closure_set(v___f_1471_, 0, v___f_1468_);
lean_closure_set(v___f_1471_, 1, v___x_1467_);
lean_closure_set(v___f_1471_, 2, v_connectionLimit_1461_);
lean_closure_set(v___f_1471_, 3, v___x_1470_);
lean_closure_set(v___f_1471_, 4, v___f_1440_);
lean_closure_set(v___f_1471_, 5, v___f_1465_);
lean_closure_set(v___f_1471_, 6, v_activeConnections_1460_);
lean_closure_set(v___f_1471_, 7, v___f_1441_);
lean_closure_set(v___f_1471_, 8, v___x_1442_);
lean_closure_set(v___f_1471_, 9, v_inst_1443_);
lean_closure_set(v___f_1471_, 10, v_handler_1444_);
lean_closure_set(v___f_1471_, 11, v_config_1445_);
lean_closure_set(v___f_1471_, 12, v___f_1446_);
lean_closure_set(v___f_1471_, 13, v___f_1447_);
lean_closure_set(v___f_1471_, 14, v___f_1469_);
lean_closure_set(v___f_1471_, 15, v___x_1448_);
lean_closure_set(v___f_1471_, 16, v_a_1449_);
lean_closure_set(v___f_1471_, 17, v___f_1450_);
lean_closure_set(v___f_1471_, 18, v___f_1451_);
lean_closure_set(v___f_1471_, 19, v___f_1452_);
v___x_1472_ = lean_box(v___x_1466_);
v___f_1473_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__30___boxed), 8, 6);
lean_closure_set(v___f_1473_, 0, v___f_1471_);
lean_closure_set(v___f_1473_, 1, v_connectionLimit_1461_);
lean_closure_set(v___f_1473_, 2, v___x_1472_);
lean_closure_set(v___f_1473_, 3, v___f_1453_);
lean_closure_set(v___f_1473_, 4, v___x_1467_);
lean_closure_set(v___f_1473_, 5, v___f_1454_);
v___x_1474_ = lean_box(v___x_1466_);
v___x_1475_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___boxed), 6, 5);
lean_closure_set(v___x_1475_, 0, lean_box(0));
lean_closure_set(v___x_1475_, 1, v_a_1458_);
lean_closure_set(v___x_1475_, 2, v___x_1474_);
lean_closure_set(v___x_1475_, 3, v___f_1473_);
lean_closure_set(v___x_1475_, 4, v_context_1459_);
v___x_1476_ = lean_unsigned_to_nat(0u);
v___x_1477_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1477_, 0, lean_box(0));
lean_closure_set(v___x_1477_, 1, v___x_1475_);
v___x_1478_ = lean_io_as_task(v___x_1477_, v___x_1476_);
lean_dec_ref(v___x_1478_);
v___x_1479_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
v___x_1480_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1476_, v___x_1466_, v___x_1479_, v___f_1463_);
return v___x_1480_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31___boxed(lean_object** _args){
lean_object* v___f_1481_ = _args[0];
lean_object* v___f_1482_ = _args[1];
lean_object* v___x_1483_ = _args[2];
lean_object* v_inst_1484_ = _args[3];
lean_object* v_handler_1485_ = _args[4];
lean_object* v_config_1486_ = _args[5];
lean_object* v___f_1487_ = _args[6];
lean_object* v___f_1488_ = _args[7];
lean_object* v___x_1489_ = _args[8];
lean_object* v_a_1490_ = _args[9];
lean_object* v___f_1491_ = _args[10];
lean_object* v___f_1492_ = _args[11];
lean_object* v___f_1493_ = _args[12];
lean_object* v___f_1494_ = _args[13];
lean_object* v___f_1495_ = _args[14];
lean_object* v_x_1496_ = _args[15];
lean_object* v___y_1497_ = _args[16];
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Std_Http_Server_serve___redArg___lam__31(v___f_1481_, v___f_1482_, v___x_1483_, v_inst_1484_, v_handler_1485_, v_config_1486_, v___f_1487_, v___f_1488_, v___x_1489_, v_a_1490_, v___f_1491_, v___f_1492_, v___f_1493_, v___f_1494_, v___f_1495_, v_x_1496_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32(lean_object* v___f_1499_, lean_object* v_config_1500_, lean_object* v_x_1501_){
_start:
{
if (lean_obj_tag(v_x_1501_) == 0)
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1511_; 
lean_dec_ref(v_config_1500_);
lean_dec_ref(v___f_1499_);
v_a_1503_ = lean_ctor_get(v_x_1501_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_x_1501_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1505_ = v_x_1501_;
v_isShared_1506_ = v_isSharedCheck_1511_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v_x_1501_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1511_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1503_);
v___x_1508_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
return v___x_1509_;
}
}
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1528_; 
v_a_1512_ = lean_ctor_get(v_x_1501_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v_x_1501_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1514_ = v_x_1501_;
v_isShared_1515_ = v_isSharedCheck_1528_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v_x_1501_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1528_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; lean_object* v_val_1520_; lean_object* v___x_1523_; lean_object* v_a_1524_; lean_object* v___x_1526_; 
v___x_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1516_, 0, v_a_1512_);
v___x_1517_ = lean_unsigned_to_nat(0u);
v___x_1518_ = 0;
v___x_1523_ = l_Std_Http_Server_new(v_config_1500_, v___x_1516_);
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1524_);
lean_dec_ref(v___x_1523_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 0, v_a_1524_);
v___x_1526_ = v___x_1514_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1524_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v___jp_1519_:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1521_, 0, v_val_1520_);
v___x_1522_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1517_, v___x_1518_, v___x_1521_, v___f_1499_);
return v___x_1522_;
}
v_reusejp_1525_:
{
v_val_1520_ = v___x_1526_;
goto v___jp_1519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32___boxed(lean_object* v___f_1529_, lean_object* v_config_1530_, lean_object* v_x_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Std_Http_Server_serve___redArg___lam__32(v___f_1529_, v_config_1530_, v_x_1531_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__33(lean_object* v___f_1534_, lean_object* v_a_1535_, lean_object* v_x_1536_){
_start:
{
if (lean_obj_tag(v_x_1536_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1546_; 
lean_dec_ref(v___f_1534_);
v_a_1538_ = lean_ctor_get(v_x_1536_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_x_1536_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1540_ = v_x_1536_;
v_isShared_1541_ = v_isSharedCheck_1546_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v_x_1536_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1546_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
return v___x_1544_;
}
}
}
else
{
lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1565_; 
v_isSharedCheck_1565_ = !lean_is_exclusive(v_x_1536_);
if (v_isSharedCheck_1565_ == 0)
{
lean_object* v_unused_1566_; 
v_unused_1566_ = lean_ctor_get(v_x_1536_, 0);
lean_dec(v_unused_1566_);
v___x_1548_ = v_x_1536_;
v_isShared_1549_ = v_isSharedCheck_1565_;
goto v_resetjp_1547_;
}
else
{
lean_dec(v_x_1536_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1565_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1550_; uint8_t v___x_1551_; lean_object* v_val_1553_; lean_object* v___x_1556_; 
v___x_1550_ = lean_unsigned_to_nat(0u);
v___x_1551_ = 0;
v___x_1556_ = lean_uv_tcp_getsockname(v_a_1535_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1559_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1556_, 1);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 0, v_a_1557_);
v___x_1559_ = v___x_1548_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
v_val_1553_ = v___x_1559_;
goto v___jp_1552_;
}
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; 
v_a_1561_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1556_, 1);
if (v_isShared_1549_ == 0)
{
lean_ctor_set_tag(v___x_1548_, 0);
lean_ctor_set(v___x_1548_, 0, v_a_1561_);
v___x_1563_ = v___x_1548_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1561_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
v_val_1553_ = v___x_1563_;
goto v___jp_1552_;
}
}
v___jp_1552_:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1554_, 0, v_val_1553_);
v___x_1555_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1550_, v___x_1551_, v___x_1554_, v___f_1534_);
return v___x_1555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__33___boxed(lean_object* v___f_1567_, lean_object* v_a_1568_, lean_object* v_x_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Std_Http_Server_serve___redArg___lam__33(v___f_1567_, v_a_1568_, v_x_1569_);
lean_dec(v_a_1568_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__34(lean_object* v___f_1572_, lean_object* v_a_1573_, lean_object* v_x_1574_){
_start:
{
if (lean_obj_tag(v_x_1574_) == 0)
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1584_; 
lean_dec_ref(v___f_1572_);
v_a_1576_ = lean_ctor_get(v_x_1574_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_x_1574_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1578_ = v_x_1574_;
v_isShared_1579_ = v_isSharedCheck_1584_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v_x_1574_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1584_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
return v___x_1582_;
}
}
}
else
{
lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1603_; 
v_isSharedCheck_1603_ = !lean_is_exclusive(v_x_1574_);
if (v_isSharedCheck_1603_ == 0)
{
lean_object* v_unused_1604_; 
v_unused_1604_ = lean_ctor_get(v_x_1574_, 0);
lean_dec(v_unused_1604_);
v___x_1586_ = v_x_1574_;
v_isShared_1587_ = v_isSharedCheck_1603_;
goto v_resetjp_1585_;
}
else
{
lean_dec(v_x_1574_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1603_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; uint8_t v___x_1589_; lean_object* v_val_1591_; lean_object* v___x_1594_; 
v___x_1588_ = lean_unsigned_to_nat(0u);
v___x_1589_ = 0;
v___x_1594_ = lean_uv_tcp_nodelay(v_a_1573_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v___x_1597_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1595_);
lean_dec_ref_known(v___x_1594_, 1);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v_a_1595_);
v___x_1597_ = v___x_1586_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
v_val_1591_ = v___x_1597_;
goto v___jp_1590_;
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; 
v_a_1599_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1594_, 1);
if (v_isShared_1587_ == 0)
{
lean_ctor_set_tag(v___x_1586_, 0);
lean_ctor_set(v___x_1586_, 0, v_a_1599_);
v___x_1601_ = v___x_1586_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1599_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
v_val_1591_ = v___x_1601_;
goto v___jp_1590_;
}
}
v___jp_1590_:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1592_, 0, v_val_1591_);
v___x_1593_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1588_, v___x_1589_, v___x_1592_, v___f_1572_);
return v___x_1593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__34___boxed(lean_object* v___f_1605_, lean_object* v_a_1606_, lean_object* v_x_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Std_Http_Server_serve___redArg___lam__34(v___f_1605_, v_a_1606_, v_x_1607_);
lean_dec(v_a_1606_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__35(lean_object* v___f_1610_, lean_object* v_a_1611_, uint32_t v_backlog_1612_, lean_object* v_x_1613_){
_start:
{
if (lean_obj_tag(v_x_1613_) == 0)
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1623_; 
lean_dec_ref(v___f_1610_);
v_a_1615_ = lean_ctor_get(v_x_1613_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v_x_1613_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1617_ = v_x_1613_;
v_isShared_1618_ = v_isSharedCheck_1623_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v_x_1613_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1623_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
return v___x_1621_;
}
}
}
else
{
lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1642_; 
v_isSharedCheck_1642_ = !lean_is_exclusive(v_x_1613_);
if (v_isSharedCheck_1642_ == 0)
{
lean_object* v_unused_1643_; 
v_unused_1643_ = lean_ctor_get(v_x_1613_, 0);
lean_dec(v_unused_1643_);
v___x_1625_ = v_x_1613_;
v_isShared_1626_ = v_isSharedCheck_1642_;
goto v_resetjp_1624_;
}
else
{
lean_dec(v_x_1613_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1642_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; uint8_t v___x_1628_; lean_object* v_val_1630_; lean_object* v___x_1633_; 
v___x_1627_ = lean_unsigned_to_nat(0u);
v___x_1628_ = 0;
v___x_1633_ = lean_uv_tcp_listen(v_a_1611_, v_backlog_1612_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1636_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
lean_dec_ref_known(v___x_1633_, 1);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v_a_1634_);
v___x_1636_ = v___x_1625_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1634_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
v_val_1630_ = v___x_1636_;
goto v___jp_1629_;
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; 
v_a_1638_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1638_);
lean_dec_ref_known(v___x_1633_, 1);
if (v_isShared_1626_ == 0)
{
lean_ctor_set_tag(v___x_1625_, 0);
lean_ctor_set(v___x_1625_, 0, v_a_1638_);
v___x_1640_ = v___x_1625_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1638_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
v_val_1630_ = v___x_1640_;
goto v___jp_1629_;
}
}
v___jp_1629_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1631_, 0, v_val_1630_);
v___x_1632_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1627_, v___x_1628_, v___x_1631_, v___f_1610_);
return v___x_1632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__35___boxed(lean_object* v___f_1644_, lean_object* v_a_1645_, lean_object* v_backlog_1646_, lean_object* v_x_1647_, lean_object* v___y_1648_){
_start:
{
uint32_t v_backlog_boxed_1649_; lean_object* v_res_1650_; 
v_backlog_boxed_1649_ = lean_unbox_uint32(v_backlog_1646_);
lean_dec(v_backlog_1646_);
v_res_1650_ = l_Std_Http_Server_serve___redArg___lam__35(v___f_1644_, v_a_1645_, v_backlog_boxed_1649_, v_x_1647_);
lean_dec(v_a_1645_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__36(lean_object* v___f_1651_, lean_object* v___f_1652_, lean_object* v___x_1653_, lean_object* v_inst_1654_, lean_object* v_handler_1655_, lean_object* v_config_1656_, lean_object* v___f_1657_, lean_object* v___f_1658_, lean_object* v___x_1659_, lean_object* v___f_1660_, lean_object* v___f_1661_, lean_object* v___f_1662_, lean_object* v___f_1663_, lean_object* v___f_1664_, uint32_t v_backlog_1665_, lean_object* v_addr_1666_, lean_object* v_x_1667_){
_start:
{
if (lean_obj_tag(v_x_1667_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1677_; 
lean_dec_ref(v___f_1664_);
lean_dec_ref(v___f_1663_);
lean_dec_ref(v___f_1662_);
lean_dec_ref(v___f_1661_);
lean_dec_ref(v___f_1660_);
lean_dec(v___x_1659_);
lean_dec_ref(v___f_1658_);
lean_dec_ref(v___f_1657_);
lean_dec_ref(v_config_1656_);
lean_dec(v_handler_1655_);
lean_dec_ref(v_inst_1654_);
lean_dec_ref(v___x_1653_);
lean_dec_ref(v___f_1652_);
lean_dec_ref(v___f_1651_);
v_a_1669_ = lean_ctor_get(v_x_1667_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_x_1667_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1671_ = v_x_1667_;
v_isShared_1672_ = v_isSharedCheck_1677_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v_x_1667_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1677_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
lean_object* v___x_1675_; 
v___x_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
return v___x_1675_;
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1703_; 
v_a_1678_ = lean_ctor_get(v_x_1667_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_x_1667_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1680_ = v_x_1667_;
v_isShared_1681_ = v_isSharedCheck_1703_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v_x_1667_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1703_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___f_1682_; lean_object* v___f_1683_; lean_object* v___f_1684_; lean_object* v___f_1685_; lean_object* v___x_1686_; lean_object* v___f_1687_; lean_object* v___x_1688_; uint8_t v___x_1689_; lean_object* v_val_1691_; lean_object* v___x_1694_; 
lean_inc_n(v_a_1678_, 4);
lean_inc_ref(v_config_1656_);
v___f_1682_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__31___boxed), 17, 15);
lean_closure_set(v___f_1682_, 0, v___f_1651_);
lean_closure_set(v___f_1682_, 1, v___f_1652_);
lean_closure_set(v___f_1682_, 2, v___x_1653_);
lean_closure_set(v___f_1682_, 3, v_inst_1654_);
lean_closure_set(v___f_1682_, 4, v_handler_1655_);
lean_closure_set(v___f_1682_, 5, v_config_1656_);
lean_closure_set(v___f_1682_, 6, v___f_1657_);
lean_closure_set(v___f_1682_, 7, v___f_1658_);
lean_closure_set(v___f_1682_, 8, v___x_1659_);
lean_closure_set(v___f_1682_, 9, v_a_1678_);
lean_closure_set(v___f_1682_, 10, v___f_1660_);
lean_closure_set(v___f_1682_, 11, v___f_1661_);
lean_closure_set(v___f_1682_, 12, v___f_1662_);
lean_closure_set(v___f_1682_, 13, v___f_1663_);
lean_closure_set(v___f_1682_, 14, v___f_1664_);
v___f_1683_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__32___boxed), 4, 2);
lean_closure_set(v___f_1683_, 0, v___f_1682_);
lean_closure_set(v___f_1683_, 1, v_config_1656_);
v___f_1684_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__33___boxed), 4, 2);
lean_closure_set(v___f_1684_, 0, v___f_1683_);
lean_closure_set(v___f_1684_, 1, v_a_1678_);
v___f_1685_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__34___boxed), 4, 2);
lean_closure_set(v___f_1685_, 0, v___f_1684_);
lean_closure_set(v___f_1685_, 1, v_a_1678_);
v___x_1686_ = lean_box_uint32(v_backlog_1665_);
v___f_1687_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__35___boxed), 5, 3);
lean_closure_set(v___f_1687_, 0, v___f_1685_);
lean_closure_set(v___f_1687_, 1, v_a_1678_);
lean_closure_set(v___f_1687_, 2, v___x_1686_);
v___x_1688_ = lean_unsigned_to_nat(0u);
v___x_1689_ = 0;
v___x_1694_ = lean_uv_tcp_bind(v_a_1678_, v_addr_1666_);
lean_dec(v_a_1678_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; lean_object* v___x_1697_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1695_);
lean_dec_ref_known(v___x_1694_, 1);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v_a_1695_);
v___x_1697_ = v___x_1680_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1695_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
v_val_1691_ = v___x_1697_;
goto v___jp_1690_;
}
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; 
v_a_1699_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1699_);
lean_dec_ref_known(v___x_1694_, 1);
if (v_isShared_1681_ == 0)
{
lean_ctor_set_tag(v___x_1680_, 0);
lean_ctor_set(v___x_1680_, 0, v_a_1699_);
v___x_1701_ = v___x_1680_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
v_val_1691_ = v___x_1701_;
goto v___jp_1690_;
}
}
v___jp_1690_:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1692_, 0, v_val_1691_);
v___x_1693_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1688_, v___x_1689_, v___x_1692_, v___f_1687_);
return v___x_1693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__36___boxed(lean_object** _args){
lean_object* v___f_1704_ = _args[0];
lean_object* v___f_1705_ = _args[1];
lean_object* v___x_1706_ = _args[2];
lean_object* v_inst_1707_ = _args[3];
lean_object* v_handler_1708_ = _args[4];
lean_object* v_config_1709_ = _args[5];
lean_object* v___f_1710_ = _args[6];
lean_object* v___f_1711_ = _args[7];
lean_object* v___x_1712_ = _args[8];
lean_object* v___f_1713_ = _args[9];
lean_object* v___f_1714_ = _args[10];
lean_object* v___f_1715_ = _args[11];
lean_object* v___f_1716_ = _args[12];
lean_object* v___f_1717_ = _args[13];
lean_object* v_backlog_1718_ = _args[14];
lean_object* v_addr_1719_ = _args[15];
lean_object* v_x_1720_ = _args[16];
lean_object* v___y_1721_ = _args[17];
_start:
{
uint32_t v_backlog_boxed_1722_; lean_object* v_res_1723_; 
v_backlog_boxed_1722_ = lean_unbox_uint32(v_backlog_1718_);
lean_dec(v_backlog_1718_);
v_res_1723_ = l_Std_Http_Server_serve___redArg___lam__36(v___f_1704_, v___f_1705_, v___x_1706_, v_inst_1707_, v_handler_1708_, v_config_1709_, v___f_1710_, v___f_1711_, v___x_1712_, v___f_1713_, v___f_1714_, v___f_1715_, v___f_1716_, v___f_1717_, v_backlog_boxed_1722_, v_addr_1719_, v_x_1720_);
lean_dec_ref(v_addr_1719_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg(lean_object* v_inst_1730_, lean_object* v_addr_1731_, lean_object* v_handler_1732_, lean_object* v_config_1733_, uint32_t v_backlog_1734_){
_start:
{
lean_object* v___f_1736_; lean_object* v___f_1737_; lean_object* v___f_1738_; lean_object* v___f_1739_; lean_object* v___f_1740_; lean_object* v___f_1741_; lean_object* v___f_1742_; lean_object* v___f_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___f_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; lean_object* v_val_1751_; lean_object* v___x_1754_; 
v___f_1736_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__0));
v___f_1737_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__1));
v___f_1738_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__2));
v___f_1739_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__3));
v___f_1740_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2));
v___f_1741_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0));
v___f_1742_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__4));
v___f_1743_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__5));
v___x_1744_ = l_Std_Http_instTransportClient;
v___x_1745_ = l_Std_Http_Server_instImpl_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8_;
v___x_1746_ = lean_box_uint32(v_backlog_1734_);
v___f_1747_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__36___boxed), 18, 16);
lean_closure_set(v___f_1747_, 0, v___f_1740_);
lean_closure_set(v___f_1747_, 1, v___f_1739_);
lean_closure_set(v___f_1747_, 2, v___x_1744_);
lean_closure_set(v___f_1747_, 3, v_inst_1730_);
lean_closure_set(v___f_1747_, 4, v_handler_1732_);
lean_closure_set(v___f_1747_, 5, v_config_1733_);
lean_closure_set(v___f_1747_, 6, v___f_1741_);
lean_closure_set(v___f_1747_, 7, v___f_1739_);
lean_closure_set(v___f_1747_, 8, v___x_1745_);
lean_closure_set(v___f_1747_, 9, v___f_1737_);
lean_closure_set(v___f_1747_, 10, v___f_1738_);
lean_closure_set(v___f_1747_, 11, v___f_1742_);
lean_closure_set(v___f_1747_, 12, v___f_1736_);
lean_closure_set(v___f_1747_, 13, v___f_1743_);
lean_closure_set(v___f_1747_, 14, v___x_1746_);
lean_closure_set(v___f_1747_, 15, v_addr_1731_);
v___x_1748_ = lean_unsigned_to_nat(0u);
v___x_1749_ = 0;
v___x_1754_ = lean_uv_tcp_new();
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1754_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1754_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
lean_ctor_set_tag(v___x_1757_, 1);
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
v_val_1751_ = v___x_1760_;
goto v___jp_1750_;
}
}
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
v_a_1763_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1754_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1754_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
lean_ctor_set_tag(v___x_1765_, 0);
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
v_val_1751_ = v___x_1768_;
goto v___jp_1750_;
}
}
}
v___jp_1750_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1752_, 0, v_val_1751_);
v___x_1753_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1748_, v___x_1749_, v___x_1752_, v___f_1747_);
return v___x_1753_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___boxed(lean_object* v_inst_1771_, lean_object* v_addr_1772_, lean_object* v_handler_1773_, lean_object* v_config_1774_, lean_object* v_backlog_1775_, lean_object* v_a_1776_){
_start:
{
uint32_t v_backlog_boxed_1777_; lean_object* v_res_1778_; 
v_backlog_boxed_1777_ = lean_unbox_uint32(v_backlog_1775_);
lean_dec(v_backlog_1775_);
v_res_1778_ = l_Std_Http_Server_serve___redArg(v_inst_1771_, v_addr_1772_, v_handler_1773_, v_config_1774_, v_backlog_boxed_1777_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve(lean_object* v_00_u03c3_1779_, lean_object* v_inst_1780_, lean_object* v_addr_1781_, lean_object* v_handler_1782_, lean_object* v_config_1783_, uint32_t v_backlog_1784_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Std_Http_Server_serve___redArg(v_inst_1780_, v_addr_1781_, v_handler_1782_, v_config_1783_, v_backlog_1784_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___boxed(lean_object* v_00_u03c3_1787_, lean_object* v_inst_1788_, lean_object* v_addr_1789_, lean_object* v_handler_1790_, lean_object* v_config_1791_, lean_object* v_backlog_1792_, lean_object* v_a_1793_){
_start:
{
uint32_t v_backlog_boxed_1794_; lean_object* v_res_1795_; 
v_backlog_boxed_1794_ = lean_unbox_uint32(v_backlog_1792_);
lean_dec(v_backlog_1792_);
v_res_1795_ = l_Std_Http_Server_serve(v_00_u03c3_1787_, v_inst_1788_, v_addr_1789_, v_handler_1790_, v_config_1791_, v_backlog_boxed_1794_);
return v_res_1795_;
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
