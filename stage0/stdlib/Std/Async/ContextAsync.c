// Lean compiler output
// Module: Std.Async.ContextAsync
// Imports: public import Std.Internal.UV public import Std.Async.Timer public import Std.Sync.CancellationContext
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
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_CancellationContext_cancel(lean_object*, lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Async_BaseAsync_toRawBaseIO___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_CancellationContext_fork(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_selector(lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Std_Async_EAsync_instMonad___redArg();
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Function_const___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_CancellationContext_new();
lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_new();
lean_object* l_Std_CancellationToken_getCancellationReason(lean_object*);
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_CancellationToken_wait(lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_CancellationToken_isCancelled(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_runIn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_runIn___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_runIn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_runIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ContextAsync_run___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_run___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_run___redArg___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_run___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_getContext(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_getContext___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_isCancelled___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_isCancelled___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ContextAsync_isCancelled___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_isCancelled___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_isCancelled___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_isCancelled___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_isCancelled(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_isCancelled___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_getCancellationReason___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_getCancellationReason___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ContextAsync_getCancellationReason___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_getCancellationReason___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_getCancellationReason___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_getCancellationReason___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_getCancellationReason(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_getCancellationReason___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_cancel___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_cancel___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_cancel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_cancel___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_doneSelector___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_doneSelector___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ContextAsync_doneSelector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_doneSelector___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_doneSelector___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_doneSelector___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_doneSelector(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_doneSelector___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_awaitCancellation___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_awaitCancellation___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_awaitCancellation___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_awaitCancellation___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ContextAsync_awaitCancellation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_awaitCancellation___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_awaitCancellation___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_awaitCancellation___closed__0_value;
static const lean_closure_object l_Std_Async_ContextAsync_awaitCancellation___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_awaitCancellation___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_ContextAsync_awaitCancellation___closed__0_value)} };
static const lean_object* l_Std_Async_ContextAsync_awaitCancellation___closed__1 = (const lean_object*)&l_Std_Async_ContextAsync_awaitCancellation___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_awaitCancellation(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_awaitCancellation___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ContextAsync_concurrently___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_concurrently___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_concurrently___redArg___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_concurrently___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__0_value;
static const lean_closure_object l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1 = (const lean_object*)&l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1_value;
static lean_once_cell_t l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2;
static lean_once_cell_t l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_ContextAsync_background___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_ContextAsync_background___redArg___lam__3___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_background___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Std_Async_ContextAsync_background___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_ContextAsync_background___redArg___lam__3___closed__0_value)}};
static const lean_object* l_Std_Async_ContextAsync_background___redArg___lam__3___closed__1 = (const lean_object*)&l_Std_Async_ContextAsync_background___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ContextAsync_raceAll___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_raceAll___redArg___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_raceAll___redArg___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_raceAll___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Async_ContextAsync_run___redArg___closed__0_value),((lean_object*)&l_Std_Async_ContextAsync_concurrently___redArg___closed__0_value)} };
static const lean_object* l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_ContextAsync_instMonadAsyncAsyncTask = (const lean_object*)&l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instFunctor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instFunctor___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instFunctor___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ContextAsync_instFunctor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_instFunctor___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_instFunctor___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_instFunctor___closed__0_value;
static const lean_closure_object l_Std_Async_ContextAsync_instFunctor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_instFunctor___lam__1___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_ContextAsync_instFunctor___closed__0_value)} };
static const lean_object* l_Std_Async_ContextAsync_instFunctor___closed__1 = (const lean_object*)&l_Std_Async_ContextAsync_instFunctor___closed__1_value;
static const lean_ctor_object l_Std_Async_ContextAsync_instFunctor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_ContextAsync_instFunctor___closed__0_value),((lean_object*)&l_Std_Async_ContextAsync_instFunctor___closed__1_value)}};
static const lean_object* l_Std_Async_ContextAsync_instFunctor___closed__2 = (const lean_object*)&l_Std_Async_ContextAsync_instFunctor___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_Async_ContextAsync_instFunctor = (const lean_object*)&l_Std_Async_ContextAsync_instFunctor___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ContextAsync_instMonad___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_instMonad___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_instMonad___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_instMonad___closed__0_value;
static const lean_closure_object l_Std_Async_ContextAsync_instMonad___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_instMonad___lam__2___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_instMonad___closed__1 = (const lean_object*)&l_Std_Async_ContextAsync_instMonad___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ContextAsync_instMonadLiftIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_instMonadLiftIO___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_instMonadLiftIO___closed__0_value;
static const lean_closure_object l_Std_Async_ContextAsync_instMonadLiftIO___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_instMonadLiftIO___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_ContextAsync_instMonadLiftIO___closed__0_value)} };
static const lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___closed__1 = (const lean_object*)&l_Std_Async_ContextAsync_instMonadLiftIO___closed__1_value;
static const lean_closure_object l_Std_Async_ContextAsync_instMonadLiftIO___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_instMonadLiftIO___lam__2___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_ContextAsync_instMonadLiftIO___closed__1_value)} };
static const lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___closed__2 = (const lean_object*)&l_Std_Async_ContextAsync_instMonadLiftIO___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_Async_ContextAsync_instMonadLiftIO = (const lean_object*)&l_Std_Async_ContextAsync_instMonadLiftIO___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ContextAsync_instMonadLiftBaseIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_instMonadLiftBaseIO___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_instMonadLiftBaseIO___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_ContextAsync_instMonadLiftBaseIO = (const lean_object*)&l_Std_Async_ContextAsync_instMonadLiftBaseIO___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ContextAsync_instMonadExceptError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_instMonadExceptError___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_instMonadExceptError___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_instMonadExceptError___closed__0_value;
static const lean_closure_object l_Std_Async_ContextAsync_instMonadExceptError___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_instMonadExceptError___lam__2___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_instMonadExceptError___closed__1 = (const lean_object*)&l_Std_Async_ContextAsync_instMonadExceptError___closed__1_value;
static const lean_ctor_object l_Std_Async_ContextAsync_instMonadExceptError___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_ContextAsync_instMonadExceptError___closed__0_value),((lean_object*)&l_Std_Async_ContextAsync_instMonadExceptError___closed__1_value)}};
static const lean_object* l_Std_Async_ContextAsync_instMonadExceptError___closed__2 = (const lean_object*)&l_Std_Async_ContextAsync_instMonadExceptError___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_Async_ContextAsync_instMonadExceptError = (const lean_object*)&l_Std_Async_ContextAsync_instMonadExceptError___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadFinally___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadFinally___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadFinally___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadFinally___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ContextAsync_instMonadFinally___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_instMonadFinally___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_instMonadFinally___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_instMonadFinally___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_ContextAsync_instMonadFinally = (const lean_object*)&l_Std_Async_ContextAsync_instMonadFinally___closed__0_value;
static const lean_string_object l_Std_Async_ContextAsync_instInhabited___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_Std_Async_ContextAsync_instInhabited___redArg___lam__0___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_instInhabited___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Async_ContextAsync_instInhabited___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Std_Async_ContextAsync_instInhabited___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Std_Async_ContextAsync_instInhabited___redArg___lam__0___closed__1 = (const lean_object*)&l_Std_Async_ContextAsync_instInhabited___redArg___lam__0___closed__1_value;
static const lean_ctor_object l_Std_Async_ContextAsync_instInhabited___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_ContextAsync_instInhabited___redArg___lam__0___closed__1_value)}};
static const lean_object* l_Std_Async_ContextAsync_instInhabited___redArg___lam__0___closed__2 = (const lean_object*)&l_Std_Async_ContextAsync_instInhabited___redArg___lam__0___closed__2_value;
static const lean_ctor_object l_Std_Async_ContextAsync_instInhabited___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_ContextAsync_instInhabited___redArg___lam__0___closed__2_value)}};
static const lean_object* l_Std_Async_ContextAsync_instInhabited___redArg___lam__0___closed__3 = (const lean_object*)&l_Std_Async_ContextAsync_instInhabited___redArg___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ContextAsync_instInhabited___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_instInhabited___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_instInhabited___redArg___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_instInhabited___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_ContextAsync_instMonadAwaitAsyncTask = (const lean_object*)&l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_forIn___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_forIn___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_forIn___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_forIn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_forIn___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_forIn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instForInLoopUnit___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instForInLoopUnit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instForInLoopUnit___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instForInLoopUnit___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instForInLoopUnit___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instForInLoopUnit___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ContextAsync_instForInLoopUnit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_instForInLoopUnit___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_instForInLoopUnit___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_instForInLoopUnit___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_ContextAsync_instForInLoopUnit = (const lean_object*)&l_Std_Async_ContextAsync_instForInLoopUnit___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selector_cancelled(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selector_cancelled___boxed(lean_object*, lean_object*);
lean_object* l_Std_Async_ContextAsync_runIn___redArg(lean_object* v_ctx_1_, lean_object* v_x_2_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_2(v_x_2_, v_ctx_1_, lean_box(0));
return v___x_4_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_runIn___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
lean_object* v_res_5_;
v_res_5_ = l_Std_Async_ContextAsync_runIn___redArg(v_ctx_1_, v_x_2_);
stack->m_obj
 = v_res_5_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_runIn___redArg___boxed(lean_object* v_ctx_6_, lean_object* v_x_7_, lean_object* v_a_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Std_Async_ContextAsync_runIn___redArg(v_ctx_6_, v_x_7_);
return v_res_9_;
}
}
lean_object* l_Std_Async_ContextAsync_runIn(lean_object* v_00_u03b1_10_, lean_object* v_ctx_11_, lean_object* v_x_12_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_apply_2(v_x_12_, v_ctx_11_, lean_box(0));
return v___x_14_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_runIn_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_11_ = stack[1].m_obj;
lean_object* v_x_12_ = stack[2].m_obj;
lean_object* v_res_15_;
v_res_15_ = l_Std_Async_ContextAsync_runIn(lean_box(0), v_ctx_11_, v_x_12_);
stack->m_obj
 = v_res_15_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_runIn___boxed(lean_object* v_00_u03b1_16_, lean_object* v_ctx_17_, lean_object* v_x_18_, lean_object* v_a_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Std_Async_ContextAsync_runIn(v_00_u03b1_16_, v_ctx_17_, v_x_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__0(lean_object* v_x_21_){
_start:
{
lean_object* v_fst_22_; 
v_fst_22_ = lean_ctor_get(v_x_21_, 0);
lean_inc(v_fst_22_);
return v_fst_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__0___boxed(lean_object* v_x_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_Async_ContextAsync_run___redArg___lam__0(v_x_23_);
lean_dec_ref(v_x_23_);
return v_res_24_;
}
}
lean_object* l_Std_Async_ContextAsync_run___redArg___lam__1(lean_object* v_a_25_, lean_object* v___x_26_, lean_object* v_x_27_){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = l_Std_CancellationContext_cancel(v_a_25_, v___x_26_);
v___x_30_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
v___x_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_run___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_25_ = stack[0].m_obj;
lean_object* v___x_26_ = stack[1].m_obj;
lean_object* v_x_27_ = stack[2].m_obj;
lean_object* v_res_32_;
v_res_32_ = l_Std_Async_ContextAsync_run___redArg___lam__1(v_a_25_, v___x_26_, v_x_27_);
stack->m_obj
 = v_res_32_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__1___boxed(lean_object* v_a_33_, lean_object* v___x_34_, lean_object* v_x_35_, lean_object* v___y_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Std_Async_ContextAsync_run___redArg___lam__1(v_a_33_, v___x_34_, v_x_35_);
lean_dec(v_x_35_);
return v_res_37_;
}
}
lean_object* l_Std_Async_ContextAsync_run___redArg___lam__2(lean_object* v_x_38_, lean_object* v___f_39_, lean_object* v_x_40_){
_start:
{
if (lean_obj_tag(v_x_40_) == 0)
{
lean_object* v_a_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_50_; 
lean_dec(v___f_39_);
lean_dec_ref(v_x_38_);
v_a_42_ = lean_ctor_get(v_x_40_, 0);
v_isSharedCheck_50_ = !lean_is_exclusive(v_x_40_);
if (v_isSharedCheck_50_ == 0)
{
v___x_44_ = v_x_40_;
v_isShared_45_ = v_isSharedCheck_50_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_a_42_);
lean_dec(v_x_40_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_50_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_47_; 
if (v_isShared_45_ == 0)
{
v___x_47_ = v___x_44_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_a_42_);
v___x_47_ = v_reuseFailAlloc_49_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
lean_object* v___x_48_; 
v___x_48_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
return v___x_48_;
}
}
}
else
{
lean_object* v_a_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___f_54_; lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; lean_object* v___x_58_; lean_object* v___y_60_; 
v_a_51_ = lean_ctor_get(v_x_40_, 0);
lean_inc_n(v_a_51_, 2);
lean_dec_ref_known(v_x_40_, 1);
v___x_52_ = lean_apply_1(v_x_38_, v_a_51_);
v___x_53_ = lean_box(2);
v___f_54_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_run___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_54_, 0, v_a_51_);
lean_closure_set(v___f_54_, 1, v___x_53_);
v___x_55_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_55_, 0, lean_box(0));
lean_closure_set(v___x_55_, 1, lean_box(0));
lean_closure_set(v___x_55_, 2, lean_box(0));
lean_closure_set(v___x_55_, 3, v___f_39_);
v___x_56_ = lean_unsigned_to_nat(0u);
v___x_57_ = 0;
v___x_58_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_52_, v___f_54_, v___x_56_, v___x_57_);
if (lean_obj_tag(v___x_58_) == 0)
{
lean_object* v_a_62_; 
lean_dec_ref(v___x_55_);
v_a_62_ = lean_ctor_get(v___x_58_, 0);
lean_inc(v_a_62_);
lean_dec_ref_known(v___x_58_, 1);
if (lean_obj_tag(v_a_62_) == 0)
{
lean_object* v_a_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_70_; 
v_a_63_ = lean_ctor_get(v_a_62_, 0);
v_isSharedCheck_70_ = !lean_is_exclusive(v_a_62_);
if (v_isSharedCheck_70_ == 0)
{
v___x_65_ = v_a_62_;
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_a_63_);
lean_dec(v_a_62_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_68_; 
if (v_isShared_66_ == 0)
{
v___x_68_ = v___x_65_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_a_63_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
v___y_60_ = v___x_68_;
goto v___jp_59_;
}
}
}
else
{
lean_object* v_a_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_79_; 
v_a_71_ = lean_ctor_get(v_a_62_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v_a_62_);
if (v_isSharedCheck_79_ == 0)
{
v___x_73_ = v_a_62_;
v_isShared_74_ = v_isSharedCheck_79_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_a_71_);
lean_dec(v_a_62_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_79_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v_fst_75_; lean_object* v___x_77_; 
v_fst_75_ = lean_ctor_get(v_a_71_, 0);
lean_inc(v_fst_75_);
lean_dec(v_a_71_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 0, v_fst_75_);
v___x_77_ = v___x_73_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_fst_75_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
v___y_60_ = v___x_77_;
goto v___jp_59_;
}
}
}
}
else
{
lean_object* v_a_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_88_; 
v_a_80_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_88_ == 0)
{
v___x_82_ = v___x_58_;
v_isShared_83_ = v_isSharedCheck_88_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_a_80_);
lean_dec(v___x_58_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_88_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_84_; lean_object* v___x_86_; 
v___x_84_ = lean_task_map(v___x_55_, v_a_80_, v___x_56_, v___x_57_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 0, v___x_84_);
v___x_86_ = v___x_82_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_84_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
v___jp_59_:
{
lean_object* v___x_61_; 
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v___y_60_);
return v___x_61_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_run___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_38_ = stack[0].m_obj;
lean_object* v___f_39_ = stack[1].m_obj;
lean_object* v_x_40_ = stack[2].m_obj;
lean_object* v_res_89_;
v_res_89_ = l_Std_Async_ContextAsync_run___redArg___lam__2(v_x_38_, v___f_39_, v_x_40_);
stack->m_obj
 = v_res_89_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__2___boxed(lean_object* v_x_90_, lean_object* v___f_91_, lean_object* v_x_92_, lean_object* v___y_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Std_Async_ContextAsync_run___redArg___lam__2(v_x_90_, v___f_91_, v_x_92_);
return v_res_94_;
}
}
lean_object* l_Std_Async_ContextAsync_run___redArg(lean_object* v_x_96_){
_start:
{
lean_object* v___f_98_; lean_object* v___f_99_; lean_object* v___x_100_; uint8_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___f_98_ = ((lean_object*)(l_Std_Async_ContextAsync_run___redArg___closed__0));
v___f_99_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_run___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_99_, 0, v_x_96_);
lean_closure_set(v___f_99_, 1, v___f_98_);
v___x_100_ = lean_unsigned_to_nat(0u);
v___x_101_ = 0;
v___x_102_ = l_Std_CancellationContext_new();
v___x_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
v___x_105_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_100_, v___x_101_, v___x_104_, v___f_99_);
return v___x_105_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_96_ = stack[0].m_obj;
lean_object* v_res_106_;
v_res_106_ = l_Std_Async_ContextAsync_run___redArg(v_x_96_);
stack->m_obj
 = v_res_106_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___boxed(lean_object* v_x_107_, lean_object* v_a_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Std_Async_ContextAsync_run___redArg(v_x_107_);
return v_res_109_;
}
}
lean_object* l_Std_Async_ContextAsync_run(lean_object* v_00_u03b1_110_, lean_object* v_x_111_){
_start:
{
lean_object* v___f_113_; lean_object* v___f_114_; lean_object* v___x_115_; uint8_t v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___f_113_ = ((lean_object*)(l_Std_Async_ContextAsync_run___redArg___closed__0));
v___f_114_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_run___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_114_, 0, v_x_111_);
lean_closure_set(v___f_114_, 1, v___f_113_);
v___x_115_ = lean_unsigned_to_nat(0u);
v___x_116_ = 0;
v___x_117_ = l_Std_CancellationContext_new();
v___x_118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
v___x_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
v___x_120_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_115_, v___x_116_, v___x_119_, v___f_114_);
return v___x_120_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_111_ = stack[1].m_obj;
lean_object* v_res_121_;
v_res_121_ = l_Std_Async_ContextAsync_run(lean_box(0), v_x_111_);
stack->m_obj
 = v_res_121_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___boxed(lean_object* v_00_u03b1_122_, lean_object* v_x_123_, lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Std_Async_ContextAsync_run(v_00_u03b1_122_, v_x_123_);
return v_res_125_;
}
}
lean_object* l_Std_Async_ContextAsync_getContext(lean_object* v_ctx_126_){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
lean_inc_ref(v_ctx_126_);
v___x_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_128_, 0, v_ctx_126_);
v___x_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_getContext_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_126_ = stack[0].m_obj;
lean_object* v_res_130_;
v_res_130_ = l_Std_Async_ContextAsync_getContext(v_ctx_126_);
stack->m_obj
 = v_res_130_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_getContext___boxed(lean_object* v_ctx_131_, lean_object* v_a_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Std_Async_ContextAsync_getContext(v_ctx_131_);
lean_dec_ref(v_ctx_131_);
return v_res_133_;
}
}
lean_object* l_Std_Async_ContextAsync_isCancelled___lam__0(lean_object* v_x_134_){
_start:
{
if (lean_obj_tag(v_x_134_) == 0)
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_144_; 
v_a_136_ = lean_ctor_get(v_x_134_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v_x_134_);
if (v_isSharedCheck_144_ == 0)
{
v___x_138_ = v_x_134_;
v_isShared_139_ = v_isSharedCheck_144_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v_x_134_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_144_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_a_136_);
v___x_141_ = v_reuseFailAlloc_143_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_142_; 
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
}
}
else
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_156_; 
v_a_145_ = lean_ctor_get(v_x_134_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v_x_134_);
if (v_isSharedCheck_156_ == 0)
{
v___x_147_ = v_x_134_;
v_isShared_148_ = v_isSharedCheck_156_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v_x_134_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_156_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v_token_149_; uint8_t v___x_150_; lean_object* v___x_151_; lean_object* v___x_153_; 
v_token_149_ = lean_ctor_get(v_a_145_, 1);
lean_inc_ref(v_token_149_);
lean_dec(v_a_145_);
v___x_150_ = l_Std_CancellationToken_isCancelled(v_token_149_);
v___x_151_ = lean_box(v___x_150_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v___x_151_);
v___x_153_ = v___x_147_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_151_);
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
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_isCancelled___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_134_ = stack[0].m_obj;
lean_object* v_res_157_;
v_res_157_ = l_Std_Async_ContextAsync_isCancelled___lam__0(v_x_134_);
stack->m_obj
 = v_res_157_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_isCancelled___lam__0___boxed(lean_object* v_x_158_, lean_object* v___y_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Std_Async_ContextAsync_isCancelled___lam__0(v_x_158_);
return v_res_160_;
}
}
lean_object* l_Std_Async_ContextAsync_isCancelled(lean_object* v_a_162_){
_start:
{
lean_object* v___f_164_; lean_object* v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___f_164_ = ((lean_object*)(l_Std_Async_ContextAsync_isCancelled___closed__0));
v___x_165_ = lean_unsigned_to_nat(0u);
v___x_166_ = 0;
lean_inc_ref(v_a_162_);
v___x_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_167_, 0, v_a_162_);
v___x_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
v___x_169_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_165_, v___x_166_, v___x_168_, v___f_164_);
return v___x_169_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_isCancelled_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_162_ = stack[0].m_obj;
lean_object* v_res_170_;
v_res_170_ = l_Std_Async_ContextAsync_isCancelled(v_a_162_);
stack->m_obj
 = v_res_170_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_isCancelled___boxed(lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Std_Async_ContextAsync_isCancelled(v_a_171_);
lean_dec_ref(v_a_171_);
return v_res_173_;
}
}
lean_object* l_Std_Async_ContextAsync_getCancellationReason___lam__0(lean_object* v_x_174_){
_start:
{
if (lean_obj_tag(v_x_174_) == 0)
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_184_; 
v_a_176_ = lean_ctor_get(v_x_174_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v_x_174_);
if (v_isSharedCheck_184_ == 0)
{
v___x_178_ = v_x_174_;
v_isShared_179_ = v_isSharedCheck_184_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v_x_174_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_184_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_a_176_);
v___x_181_ = v_reuseFailAlloc_183_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_182_; 
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_195_; 
v_a_185_ = lean_ctor_get(v_x_174_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v_x_174_);
if (v_isSharedCheck_195_ == 0)
{
v___x_187_ = v_x_174_;
v_isShared_188_ = v_isSharedCheck_195_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v_x_174_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_195_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v_token_189_; lean_object* v___x_190_; lean_object* v___x_192_; 
v_token_189_ = lean_ctor_get(v_a_185_, 1);
lean_inc_ref(v_token_189_);
lean_dec(v_a_185_);
v___x_190_ = l_Std_CancellationToken_getCancellationReason(v_token_189_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_190_);
v___x_192_ = v___x_187_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_190_);
v___x_192_ = v_reuseFailAlloc_194_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
lean_object* v___x_193_; 
v___x_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
return v___x_193_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_getCancellationReason___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_174_ = stack[0].m_obj;
lean_object* v_res_196_;
v_res_196_ = l_Std_Async_ContextAsync_getCancellationReason___lam__0(v_x_174_);
stack->m_obj
 = v_res_196_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_getCancellationReason___lam__0___boxed(lean_object* v_x_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Std_Async_ContextAsync_getCancellationReason___lam__0(v_x_197_);
return v_res_199_;
}
}
lean_object* l_Std_Async_ContextAsync_getCancellationReason(lean_object* v_a_201_){
_start:
{
lean_object* v___f_203_; lean_object* v___x_204_; uint8_t v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___f_203_ = ((lean_object*)(l_Std_Async_ContextAsync_getCancellationReason___closed__0));
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = 0;
lean_inc_ref(v_a_201_);
v___x_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_206_, 0, v_a_201_);
v___x_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
v___x_208_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_204_, v___x_205_, v___x_207_, v___f_203_);
return v___x_208_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_getCancellationReason_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_201_ = stack[0].m_obj;
lean_object* v_res_209_;
v_res_209_ = l_Std_Async_ContextAsync_getCancellationReason(v_a_201_);
stack->m_obj
 = v_res_209_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_getCancellationReason___boxed(lean_object* v_a_210_, lean_object* v_a_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Std_Async_ContextAsync_getCancellationReason(v_a_210_);
lean_dec_ref(v_a_210_);
return v_res_212_;
}
}
lean_object* l_Std_Async_ContextAsync_cancel___lam__0(lean_object* v_reason_213_, lean_object* v_x_214_){
_start:
{
if (lean_obj_tag(v_x_214_) == 0)
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_224_; 
lean_dec(v_reason_213_);
v_a_216_ = lean_ctor_get(v_x_214_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v_x_214_);
if (v_isSharedCheck_224_ == 0)
{
v___x_218_ = v_x_214_;
v_isShared_219_ = v_isSharedCheck_224_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v_x_214_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_224_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_a_216_);
v___x_221_ = v_reuseFailAlloc_223_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_222_; 
v___x_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
return v___x_222_;
}
}
}
else
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_234_; 
v_a_225_ = lean_ctor_get(v_x_214_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v_x_214_);
if (v_isSharedCheck_234_ == 0)
{
v___x_227_ = v_x_214_;
v_isShared_228_ = v_isSharedCheck_234_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v_x_214_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_234_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_229_ = l_Std_CancellationContext_cancel(v_a_225_, v_reason_213_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___x_229_);
v___x_231_ = v___x_227_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_229_);
v___x_231_ = v_reuseFailAlloc_233_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_232_; 
v___x_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
return v___x_232_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_cancel___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_reason_213_ = stack[0].m_obj;
lean_object* v_x_214_ = stack[1].m_obj;
lean_object* v_res_235_;
v_res_235_ = l_Std_Async_ContextAsync_cancel___lam__0(v_reason_213_, v_x_214_);
stack->m_obj
 = v_res_235_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_cancel___lam__0___boxed(lean_object* v_reason_236_, lean_object* v_x_237_, lean_object* v___y_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Std_Async_ContextAsync_cancel___lam__0(v_reason_236_, v_x_237_);
return v_res_239_;
}
}
lean_object* l_Std_Async_ContextAsync_cancel(lean_object* v_reason_240_, lean_object* v_a_241_){
_start:
{
lean_object* v___f_243_; lean_object* v___x_244_; uint8_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___f_243_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_cancel___lam__0___boxed), 3, 1);
lean_closure_set(v___f_243_, 0, v_reason_240_);
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = 0;
lean_inc_ref(v_a_241_);
v___x_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_246_, 0, v_a_241_);
v___x_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
v___x_248_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_244_, v___x_245_, v___x_247_, v___f_243_);
return v___x_248_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_cancel_0interp(lean_interpreter_value* stack)
{
lean_object* v_reason_240_ = stack[0].m_obj;
lean_object* v_a_241_ = stack[1].m_obj;
lean_object* v_res_249_;
v_res_249_ = l_Std_Async_ContextAsync_cancel(v_reason_240_, v_a_241_);
stack->m_obj
 = v_res_249_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_cancel___boxed(lean_object* v_reason_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Std_Async_ContextAsync_cancel(v_reason_250_, v_a_251_);
lean_dec_ref(v_a_251_);
return v_res_253_;
}
}
lean_object* l_Std_Async_ContextAsync_doneSelector___lam__0(lean_object* v_x_254_){
_start:
{
if (lean_obj_tag(v_x_254_) == 0)
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_264_; 
v_a_256_ = lean_ctor_get(v_x_254_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v_x_254_);
if (v_isSharedCheck_264_ == 0)
{
v___x_258_ = v_x_254_;
v_isShared_259_ = v_isSharedCheck_264_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v_x_254_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_264_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_a_256_);
v___x_261_ = v_reuseFailAlloc_263_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_262_; 
v___x_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
return v___x_262_;
}
}
}
else
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_275_; 
v_a_265_ = lean_ctor_get(v_x_254_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v_x_254_);
if (v_isSharedCheck_275_ == 0)
{
v___x_267_ = v_x_254_;
v_isShared_268_ = v_isSharedCheck_275_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v_x_254_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_275_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v_token_269_; lean_object* v___x_270_; lean_object* v___x_272_; 
v_token_269_ = lean_ctor_get(v_a_265_, 1);
lean_inc_ref(v_token_269_);
lean_dec(v_a_265_);
v___x_270_ = l_Std_CancellationToken_selector(v_token_269_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_270_);
v___x_272_ = v___x_267_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_270_);
v___x_272_ = v_reuseFailAlloc_274_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_273_; 
v___x_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
return v___x_273_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_doneSelector___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_254_ = stack[0].m_obj;
lean_object* v_res_276_;
v_res_276_ = l_Std_Async_ContextAsync_doneSelector___lam__0(v_x_254_);
stack->m_obj
 = v_res_276_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_doneSelector___lam__0___boxed(lean_object* v_x_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Std_Async_ContextAsync_doneSelector___lam__0(v_x_277_);
return v_res_279_;
}
}
lean_object* l_Std_Async_ContextAsync_doneSelector(lean_object* v_a_281_){
_start:
{
lean_object* v___f_283_; lean_object* v___x_284_; uint8_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___f_283_ = ((lean_object*)(l_Std_Async_ContextAsync_doneSelector___closed__0));
v___x_284_ = lean_unsigned_to_nat(0u);
v___x_285_ = 0;
lean_inc_ref(v_a_281_);
v___x_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_286_, 0, v_a_281_);
v___x_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
v___x_288_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_284_, v___x_285_, v___x_287_, v___f_283_);
return v___x_288_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_doneSelector_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_281_ = stack[0].m_obj;
lean_object* v_res_289_;
v_res_289_ = l_Std_Async_ContextAsync_doneSelector(v_a_281_);
stack->m_obj
 = v_res_289_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_doneSelector___boxed(lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Std_Async_ContextAsync_doneSelector(v_a_290_);
lean_dec_ref(v_a_290_);
return v_res_292_;
}
}
lean_object* l_Std_Async_ContextAsync_awaitCancellation___lam__0(lean_object* v_x_293_){
_start:
{
if (lean_obj_tag(v_x_293_) == 0)
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_303_; 
v_a_295_ = lean_ctor_get(v_x_293_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v_x_293_);
if (v_isSharedCheck_303_ == 0)
{
v___x_297_ = v_x_293_;
v_isShared_298_ = v_isSharedCheck_303_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v_x_293_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_303_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_295_);
v___x_300_ = v_reuseFailAlloc_302_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_301_; 
v___x_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
return v___x_301_;
}
}
}
else
{
lean_object* v_a_304_; lean_object* v___x_305_; 
v_a_304_ = lean_ctor_get(v_x_293_, 0);
lean_inc(v_a_304_);
lean_dec_ref_known(v_x_293_, 1);
v___x_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_305_, 0, v_a_304_);
return v___x_305_;
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_awaitCancellation___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_293_ = stack[0].m_obj;
lean_object* v_res_306_;
v_res_306_ = l_Std_Async_ContextAsync_awaitCancellation___lam__0(v_x_293_);
stack->m_obj
 = v_res_306_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_awaitCancellation___lam__0___boxed(lean_object* v_x_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Std_Async_ContextAsync_awaitCancellation___lam__0(v_x_307_);
return v_res_309_;
}
}
lean_object* l_Std_Async_ContextAsync_awaitCancellation___lam__1(lean_object* v___f_310_, lean_object* v_x_311_){
_start:
{
if (lean_obj_tag(v_x_311_) == 0)
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_321_; 
lean_dec_ref(v___f_310_);
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
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_342_; 
v_a_322_ = lean_ctor_get(v_x_311_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v_x_311_);
if (v_isSharedCheck_342_ == 0)
{
v___x_324_ = v_x_311_;
v_isShared_325_ = v_isSharedCheck_342_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v_x_311_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_342_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v_token_326_; lean_object* v___x_327_; uint8_t v___x_328_; lean_object* v_val_330_; lean_object* v___x_333_; 
v_token_326_ = lean_ctor_get(v_a_322_, 1);
lean_inc_ref(v_token_326_);
lean_dec(v_a_322_);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = 0;
v___x_333_ = l_Std_CancellationToken_wait(v_token_326_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v___x_336_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref_known(v___x_333_, 1);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 0, v_a_334_);
v___x_336_ = v___x_324_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_334_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
v_val_330_ = v___x_336_;
goto v___jp_329_;
}
}
else
{
lean_object* v_a_338_; lean_object* v___x_340_; 
v_a_338_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_338_);
lean_dec_ref_known(v___x_333_, 1);
if (v_isShared_325_ == 0)
{
lean_ctor_set_tag(v___x_324_, 0);
lean_ctor_set(v___x_324_, 0, v_a_338_);
v___x_340_ = v___x_324_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_338_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
v_val_330_ = v___x_340_;
goto v___jp_329_;
}
}
v___jp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v_val_330_);
v___x_332_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_327_, v___x_328_, v___x_331_, v___f_310_);
return v___x_332_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_awaitCancellation___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_310_ = stack[0].m_obj;
lean_object* v_x_311_ = stack[1].m_obj;
lean_object* v_res_343_;
v_res_343_ = l_Std_Async_ContextAsync_awaitCancellation___lam__1(v___f_310_, v_x_311_);
stack->m_obj
 = v_res_343_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_awaitCancellation___lam__1___boxed(lean_object* v___f_344_, lean_object* v_x_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Std_Async_ContextAsync_awaitCancellation___lam__1(v___f_344_, v_x_345_);
return v_res_347_;
}
}
lean_object* l_Std_Async_ContextAsync_awaitCancellation(lean_object* v_a_351_){
_start:
{
lean_object* v___f_353_; lean_object* v___x_354_; uint8_t v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___f_353_ = ((lean_object*)(l_Std_Async_ContextAsync_awaitCancellation___closed__1));
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = 0;
lean_inc_ref(v_a_351_);
v___x_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_356_, 0, v_a_351_);
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
v___x_358_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_354_, v___x_355_, v___x_357_, v___f_353_);
return v___x_358_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_awaitCancellation_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_351_ = stack[0].m_obj;
lean_object* v_res_359_;
v_res_359_ = l_Std_Async_ContextAsync_awaitCancellation(v_a_351_);
stack->m_obj
 = v_res_359_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_awaitCancellation___boxed(lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Std_Async_ContextAsync_awaitCancellation(v_a_360_);
lean_dec_ref(v_a_360_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__0(lean_object* v_x_363_){
_start:
{
if (lean_obj_tag(v_x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_365_; 
v_a_364_ = lean_ctor_get(v_x_363_, 0);
lean_inc(v_a_364_);
lean_dec_ref_known(v_x_363_, 1);
v___x_365_ = lean_task_pure(v_a_364_);
return v___x_365_;
}
else
{
lean_object* v_a_366_; 
v_a_366_ = lean_ctor_get(v_x_363_, 0);
lean_inc_ref(v_a_366_);
lean_dec_ref_known(v_x_363_, 1);
return v_a_366_;
}
}
}
lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__4(lean_object* v_x_367_, lean_object* v_x_368_){
_start:
{
if (lean_obj_tag(v_x_368_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_378_; 
lean_dec_ref(v_x_367_);
v_a_370_ = lean_ctor_get(v_x_368_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v_x_368_);
if (v_isSharedCheck_378_ == 0)
{
v___x_372_ = v_x_368_;
v_isShared_373_ = v_isSharedCheck_378_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v_x_368_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_378_;
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
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_370_);
v___x_375_ = v_reuseFailAlloc_377_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; 
v___x_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
return v___x_376_;
}
}
}
else
{
lean_object* v___x_379_; 
lean_dec_ref_known(v_x_368_, 1);
v___x_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_379_, 0, v_x_367_);
return v___x_379_;
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrently___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_367_ = stack[0].m_obj;
lean_object* v_x_368_ = stack[1].m_obj;
lean_object* v_res_380_;
v_res_380_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__4(v_x_367_, v_x_368_);
stack->m_obj
 = v_res_380_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__4___boxed(lean_object* v_x_381_, lean_object* v_x_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__4(v_x_381_, v_x_382_);
return v_res_384_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__1(lean_object* v_a_385_, lean_object* v_x_386_){
_start:
{
if (lean_obj_tag(v_x_386_) == 0)
{
lean_object* v___f_388_; lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___f_388_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_388_, 0, v_x_386_);
v___x_389_ = lean_box(2);
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = 0;
v___x_392_ = l_Std_CancellationContext_cancel(v_a_385_, v___x_389_);
v___x_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
v___x_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
v___x_395_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_390_, v___x_391_, v___x_394_, v___f_388_);
return v___x_395_;
}
else
{
lean_object* v___x_396_; 
lean_dec_ref(v_a_385_);
v___x_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_396_, 0, v_x_386_);
return v___x_396_;
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrently___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_385_ = stack[0].m_obj;
lean_object* v_x_386_ = stack[1].m_obj;
lean_object* v_res_397_;
v_res_397_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__1(v_a_385_, v_x_386_);
stack->m_obj
 = v_res_397_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__1___boxed(lean_object* v_a_398_, lean_object* v_x_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__1(v_a_398_, v_x_399_);
return v_res_401_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__2(lean_object* v_x_402_, lean_object* v_a_403_, lean_object* v___f_404_){
_start:
{
lean_object* v___x_406_; uint8_t v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_406_ = lean_unsigned_to_nat(0u);
v___x_407_ = 0;
v___x_408_ = lean_apply_2(v_x_402_, v_a_403_, lean_box(0));
v___x_409_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_406_, v___x_407_, v___x_408_, v___f_404_);
return v___x_409_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrently___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_402_ = stack[0].m_obj;
lean_object* v_a_403_ = stack[1].m_obj;
lean_object* v___f_404_ = stack[2].m_obj;
lean_object* v_res_410_;
v_res_410_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__2(v_x_402_, v_a_403_, v___f_404_);
stack->m_obj
 = v_res_410_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__2___boxed(lean_object* v_x_411_, lean_object* v_a_412_, lean_object* v___f_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__2(v_x_411_, v_a_412_, v___f_413_);
return v_res_415_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__5(lean_object* v___f_416_, lean_object* v___f_417_, lean_object* v___f_418_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; lean_object* v___x_423_; lean_object* v___y_425_; 
v___x_420_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_420_, 0, lean_box(0));
lean_closure_set(v___x_420_, 1, lean_box(0));
lean_closure_set(v___x_420_, 2, lean_box(0));
lean_closure_set(v___x_420_, 3, v___f_416_);
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = 0;
v___x_423_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_417_, v___f_418_, v___x_421_, v___x_422_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_427_; 
lean_dec_ref(v___x_420_);
v_a_427_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_a_427_);
lean_dec_ref_known(v___x_423_, 1);
if (lean_obj_tag(v_a_427_) == 0)
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
v_a_428_ = lean_ctor_get(v_a_427_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v_a_427_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v_a_427_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v_a_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
v___y_425_ = v___x_433_;
goto v___jp_424_;
}
}
}
else
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_444_; 
v_a_436_ = lean_ctor_get(v_a_427_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v_a_427_);
if (v_isSharedCheck_444_ == 0)
{
v___x_438_ = v_a_427_;
v_isShared_439_ = v_isSharedCheck_444_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v_a_427_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_444_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v_fst_440_; lean_object* v___x_442_; 
v_fst_440_ = lean_ctor_get(v_a_436_, 0);
lean_inc(v_fst_440_);
lean_dec(v_a_436_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v_fst_440_);
v___x_442_ = v___x_438_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_fst_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
v___y_425_ = v___x_442_;
goto v___jp_424_;
}
}
}
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_453_; 
v_a_445_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_453_ == 0)
{
v___x_447_ = v___x_423_;
v_isShared_448_ = v_isSharedCheck_453_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_423_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_453_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_449_ = lean_task_map(v___x_420_, v_a_445_, v___x_421_, v___x_422_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_449_);
v___x_451_ = v___x_447_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
v___jp_424_:
{
lean_object* v___x_426_; 
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___y_425_);
return v___x_426_;
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrently___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_416_ = stack[0].m_obj;
lean_object* v___f_417_ = stack[1].m_obj;
lean_object* v___f_418_ = stack[2].m_obj;
lean_object* v_res_454_;
v_res_454_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__5(v___f_416_, v___f_417_, v___f_418_);
stack->m_obj
 = v_res_454_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed(lean_object* v___f_455_, lean_object* v___f_456_, lean_object* v___f_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__5(v___f_455_, v___f_456_, v___f_457_);
return v_res_459_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__6(lean_object* v_a_460_, lean_object* v___x_461_, lean_object* v_x_462_){
_start:
{
if (lean_obj_tag(v_x_462_) == 0)
{
lean_object* v___f_464_; lean_object* v___x_465_; uint8_t v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___f_464_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_464_, 0, v_x_462_);
v___x_465_ = lean_unsigned_to_nat(0u);
v___x_466_ = 0;
v___x_467_ = l_Std_CancellationContext_cancel(v_a_460_, v___x_461_);
v___x_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
v___x_470_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_465_, v___x_466_, v___x_469_, v___f_464_);
return v___x_470_;
}
else
{
lean_object* v___x_471_; 
lean_dec(v___x_461_);
lean_dec_ref(v_a_460_);
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v_x_462_);
return v___x_471_;
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrently___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_460_ = stack[0].m_obj;
lean_object* v___x_461_ = stack[1].m_obj;
lean_object* v_x_462_ = stack[2].m_obj;
lean_object* v_res_472_;
v_res_472_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__6(v_a_460_, v___x_461_, v_x_462_);
stack->m_obj
 = v_res_472_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__6___boxed(lean_object* v_a_473_, lean_object* v___x_474_, lean_object* v_x_475_, lean_object* v___y_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__6(v_a_473_, v___x_474_, v_x_475_);
return v_res_477_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__3(lean_object* v_y_478_, lean_object* v_a_479_, lean_object* v___f_480_){
_start:
{
lean_object* v___x_482_; uint8_t v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_482_ = lean_unsigned_to_nat(0u);
v___x_483_ = 0;
v___x_484_ = lean_apply_2(v_y_478_, v_a_479_, lean_box(0));
v___x_485_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_482_, v___x_483_, v___x_484_, v___f_480_);
return v___x_485_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrently___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_y_478_ = stack[0].m_obj;
lean_object* v_a_479_ = stack[1].m_obj;
lean_object* v___f_480_ = stack[2].m_obj;
lean_object* v_res_486_;
v_res_486_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__3(v_y_478_, v_a_479_, v___f_480_);
stack->m_obj
 = v_res_486_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__3___boxed(lean_object* v_y_487_, lean_object* v_a_488_, lean_object* v___f_489_, lean_object* v___y_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__3(v_y_487_, v_a_488_, v___f_489_);
return v_res_491_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__9(lean_object* v_a_492_, lean_object* v_x_493_){
_start:
{
if (lean_obj_tag(v_x_493_) == 0)
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_503_; 
lean_dec(v_a_492_);
v_a_495_ = lean_ctor_get(v_x_493_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v_x_493_);
if (v_isSharedCheck_503_ == 0)
{
v___x_497_ = v_x_493_;
v_isShared_498_ = v_isSharedCheck_503_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v_x_493_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_503_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_502_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v___x_501_; 
v___x_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
return v___x_501_;
}
}
}
else
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_513_; 
v_a_504_ = lean_ctor_get(v_x_493_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v_x_493_);
if (v_isSharedCheck_513_ == 0)
{
v___x_506_ = v_x_493_;
v_isShared_507_ = v_isSharedCheck_513_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v_x_493_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_513_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v_a_492_);
lean_ctor_set(v___x_508_, 1, v_a_504_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_508_);
v___x_510_ = v___x_506_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_508_);
v___x_510_ = v_reuseFailAlloc_512_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_511_; 
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrently___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_492_ = stack[0].m_obj;
lean_object* v_x_493_ = stack[1].m_obj;
lean_object* v_res_514_;
v_res_514_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__9(v_a_492_, v_x_493_);
stack->m_obj
 = v_res_514_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__9___boxed(lean_object* v_a_515_, lean_object* v_x_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__9(v_a_515_, v_x_516_);
return v_res_518_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__7(lean_object* v_a_519_, lean_object* v_x_520_){
_start:
{
if (lean_obj_tag(v_x_520_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_530_; 
lean_dec_ref(v_a_519_);
v_a_522_ = lean_ctor_get(v_x_520_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v_x_520_);
if (v_isSharedCheck_530_ == 0)
{
v___x_524_ = v_x_520_;
v_isShared_525_ = v_isSharedCheck_530_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v_x_520_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_530_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_529_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_528_; 
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
return v___x_528_;
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___f_532_; lean_object* v___x_533_; uint8_t v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v_a_531_ = lean_ctor_get(v_x_520_, 0);
lean_inc(v_a_531_);
lean_dec_ref_known(v_x_520_, 1);
v___f_532_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_532_, 0, v_a_531_);
v___x_533_ = lean_unsigned_to_nat(0u);
v___x_534_ = 0;
v___x_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_535_, 0, v_a_519_);
v___x_536_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_533_, v___x_534_, v___x_535_, v___f_532_);
return v___x_536_;
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrently___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_519_ = stack[0].m_obj;
lean_object* v_x_520_ = stack[1].m_obj;
lean_object* v_res_537_;
v_res_537_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__7(v_a_519_, v_x_520_);
stack->m_obj
 = v_res_537_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__7___boxed(lean_object* v_a_538_, lean_object* v_x_539_, lean_object* v___y_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__7(v_a_538_, v_x_539_);
return v_res_541_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__8(lean_object* v_a_542_, lean_object* v_x_543_){
_start:
{
if (lean_obj_tag(v_x_543_) == 0)
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_553_; 
lean_dec_ref(v_a_542_);
v_a_545_ = lean_ctor_get(v_x_543_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v_x_543_);
if (v_isSharedCheck_553_ == 0)
{
v___x_547_ = v_x_543_;
v_isShared_548_ = v_isSharedCheck_553_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v_x_543_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_553_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_552_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_551_; 
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
}
}
else
{
lean_object* v_a_554_; lean_object* v___f_555_; lean_object* v___x_556_; uint8_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v_a_554_ = lean_ctor_get(v_x_543_, 0);
lean_inc(v_a_554_);
lean_dec_ref_known(v_x_543_, 1);
v___f_555_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_555_, 0, v_a_554_);
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = 0;
v___x_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_558_, 0, v_a_542_);
v___x_559_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_556_, v___x_557_, v___x_558_, v___f_555_);
return v___x_559_;
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrently___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_542_ = stack[0].m_obj;
lean_object* v_x_543_ = stack[1].m_obj;
lean_object* v_res_560_;
v_res_560_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__8(v_a_542_, v_x_543_);
stack->m_obj
 = v_res_560_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__8___boxed(lean_object* v_a_561_, lean_object* v_x_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__8(v_a_561_, v_x_562_);
return v_res_564_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__10(lean_object* v___f_565_, lean_object* v_prio_566_, lean_object* v___f_567_, lean_object* v_x_568_){
_start:
{
if (lean_obj_tag(v_x_568_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_578_; 
lean_dec_ref(v___f_567_);
lean_dec(v_prio_566_);
lean_dec_ref(v___f_565_);
v_a_570_ = lean_ctor_get(v_x_568_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v_x_568_);
if (v_isSharedCheck_578_ == 0)
{
v___x_572_ = v_x_568_;
v_isShared_573_ = v_isSharedCheck_578_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v_x_568_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_578_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_577_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_576_; 
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
return v___x_576_;
}
}
}
else
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_595_; 
v_a_579_ = lean_ctor_get(v_x_568_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v_x_568_);
if (v_isSharedCheck_595_ == 0)
{
v___x_581_ = v_x_568_;
v_isShared_582_ = v_isSharedCheck_595_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v_x_568_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_595_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___f_583_; lean_object* v___x_584_; uint8_t v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; lean_object* v___x_589_; lean_object* v___x_591_; 
v___f_583_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__8___boxed), 3, 1);
lean_closure_set(v___f_583_, 0, v_a_579_);
v___x_584_ = lean_unsigned_to_nat(0u);
v___x_585_ = 0;
v___x_586_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_586_, 0, lean_box(0));
lean_closure_set(v___x_586_, 1, v___f_565_);
v___x_587_ = lean_io_as_task(v___x_586_, v_prio_566_);
v___x_588_ = 1;
v___x_589_ = lean_task_bind(v___x_587_, v___f_567_, v___x_584_, v___x_588_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v___x_589_);
v___x_591_ = v___x_581_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_589_);
v___x_591_ = v_reuseFailAlloc_594_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
v___x_593_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_584_, v___x_585_, v___x_592_, v___f_583_);
return v___x_593_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrently___redArg___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_565_ = stack[0].m_obj;
lean_object* v_prio_566_ = stack[1].m_obj;
lean_object* v___f_567_ = stack[2].m_obj;
lean_object* v_x_568_ = stack[3].m_obj;
lean_object* v_res_596_;
v_res_596_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__10(v___f_565_, v_prio_566_, v___f_567_, v_x_568_);
stack->m_obj
 = v_res_596_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__10___boxed(lean_object* v___f_597_, lean_object* v_prio_598_, lean_object* v___f_599_, lean_object* v_x_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__10(v___f_597_, v_prio_598_, v___f_599_, v_x_600_);
return v_res_602_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__11(lean_object* v_x_603_, lean_object* v_x_604_){
_start:
{
if (lean_obj_tag(v_x_604_) == 0)
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_614_; 
lean_dec_ref(v_x_603_);
v_a_606_ = lean_ctor_get(v_x_604_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v_x_604_);
if (v_isSharedCheck_614_ == 0)
{
v___x_608_ = v_x_604_;
v_isShared_609_ = v_isSharedCheck_614_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v_x_604_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_614_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_613_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_612_; 
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
return v___x_612_;
}
}
}
else
{
lean_object* v___x_615_; 
lean_dec_ref_known(v_x_604_, 1);
v___x_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_615_, 0, v_x_603_);
return v___x_615_;
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrently___redArg___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_603_ = stack[0].m_obj;
lean_object* v_x_604_ = stack[1].m_obj;
lean_object* v_res_616_;
v_res_616_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__11(v_x_603_, v_x_604_);
stack->m_obj
 = v_res_616_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__11___boxed(lean_object* v_x_617_, lean_object* v_x_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__11(v_x_617_, v_x_618_);
return v_res_620_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__12(lean_object* v_a_621_, lean_object* v___x_622_, lean_object* v_x_623_){
_start:
{
if (lean_obj_tag(v_x_623_) == 0)
{
lean_object* v___x_625_; 
lean_dec(v___x_622_);
lean_dec_ref(v_a_621_);
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v_x_623_);
return v___x_625_;
}
else
{
lean_object* v___f_626_; lean_object* v___x_627_; uint8_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___f_626_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__11___boxed), 3, 1);
lean_closure_set(v___f_626_, 0, v_x_623_);
v___x_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = 0;
v___x_629_ = l_Std_CancellationContext_cancel(v_a_621_, v___x_622_);
v___x_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
v___x_632_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_627_, v___x_628_, v___x_631_, v___f_626_);
return v___x_632_;
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrently___redArg___lam__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_621_ = stack[0].m_obj;
lean_object* v___x_622_ = stack[1].m_obj;
lean_object* v_x_623_ = stack[2].m_obj;
lean_object* v_res_633_;
v_res_633_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__12(v_a_621_, v___x_622_, v_x_623_);
stack->m_obj
 = v_res_633_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__12___boxed(lean_object* v_a_634_, lean_object* v___x_635_, lean_object* v_x_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__12(v_a_634_, v___x_635_, v_x_636_);
return v_res_638_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__13(lean_object* v_a_639_, lean_object* v___f_640_, lean_object* v___f_641_, lean_object* v_a_642_, lean_object* v_y_643_, lean_object* v___f_644_, lean_object* v_prio_645_, lean_object* v___f_646_, lean_object* v___f_647_, lean_object* v_x_648_){
_start:
{
if (lean_obj_tag(v_x_648_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_658_; 
lean_dec_ref(v___f_647_);
lean_dec_ref(v___f_646_);
lean_dec(v_prio_645_);
lean_dec(v___f_644_);
lean_dec_ref(v_y_643_);
lean_dec_ref(v_a_642_);
lean_dec_ref(v___f_641_);
lean_dec(v___f_640_);
lean_dec_ref(v_a_639_);
v_a_650_ = lean_ctor_get(v_x_648_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v_x_648_);
if (v_isSharedCheck_658_ == 0)
{
v___x_652_ = v_x_648_;
v_isShared_653_ = v_isSharedCheck_658_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v_x_648_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_658_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_657_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_656_; 
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
return v___x_656_;
}
}
}
else
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_684_; 
v_a_659_ = lean_ctor_get(v_x_648_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v_x_648_);
if (v_isSharedCheck_684_ == 0)
{
v___x_661_ = v_x_648_;
v_isShared_662_ = v_isSharedCheck_684_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v_x_648_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_684_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v___f_664_; lean_object* v___f_665_; lean_object* v___f_666_; lean_object* v___f_667_; lean_object* v___f_668_; lean_object* v___f_669_; lean_object* v___f_670_; lean_object* v___f_671_; lean_object* v___x_672_; uint8_t v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_663_ = lean_box(2);
v___f_664_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_run___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_664_, 0, v_a_639_);
lean_closure_set(v___f_664_, 1, v___x_663_);
v___f_665_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_665_, 0, v___f_640_);
lean_closure_set(v___f_665_, 1, v___f_641_);
lean_closure_set(v___f_665_, 2, v___f_664_);
lean_inc_ref(v_a_642_);
v___f_666_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_666_, 0, v_a_642_);
lean_closure_set(v___f_666_, 1, v___x_663_);
lean_inc(v_a_659_);
v___f_667_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_667_, 0, v_y_643_);
lean_closure_set(v___f_667_, 1, v_a_659_);
lean_closure_set(v___f_667_, 2, v___f_666_);
v___f_668_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_run___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_668_, 0, v_a_659_);
lean_closure_set(v___f_668_, 1, v___x_663_);
v___f_669_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_669_, 0, v___f_644_);
lean_closure_set(v___f_669_, 1, v___f_667_);
lean_closure_set(v___f_669_, 2, v___f_668_);
lean_inc(v_prio_645_);
v___f_670_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__10___boxed), 5, 3);
lean_closure_set(v___f_670_, 0, v___f_669_);
lean_closure_set(v___f_670_, 1, v_prio_645_);
lean_closure_set(v___f_670_, 2, v___f_646_);
v___f_671_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__12___boxed), 4, 2);
lean_closure_set(v___f_671_, 0, v_a_642_);
lean_closure_set(v___f_671_, 1, v___x_663_);
v___x_672_ = lean_unsigned_to_nat(0u);
v___x_673_ = 0;
v___x_674_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_674_, 0, lean_box(0));
lean_closure_set(v___x_674_, 1, v___f_665_);
v___x_675_ = lean_io_as_task(v___x_674_, v_prio_645_);
v___x_676_ = 1;
v___x_677_ = lean_task_bind(v___x_675_, v___f_647_, v___x_672_, v___x_676_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_677_);
v___x_679_ = v___x_661_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_677_);
v___x_679_ = v_reuseFailAlloc_683_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
v___x_681_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_672_, v___x_673_, v___x_680_, v___f_670_);
v___x_682_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_672_, v___x_673_, v___x_681_, v___f_671_);
return v___x_682_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrently___redArg___lam__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_639_ = stack[0].m_obj;
lean_object* v___f_640_ = stack[1].m_obj;
lean_object* v___f_641_ = stack[2].m_obj;
lean_object* v_a_642_ = stack[3].m_obj;
lean_object* v_y_643_ = stack[4].m_obj;
lean_object* v___f_644_ = stack[5].m_obj;
lean_object* v_prio_645_ = stack[6].m_obj;
lean_object* v___f_646_ = stack[7].m_obj;
lean_object* v___f_647_ = stack[8].m_obj;
lean_object* v_x_648_ = stack[9].m_obj;
lean_object* v_res_685_;
v_res_685_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__13(v_a_639_, v___f_640_, v___f_641_, v_a_642_, v_y_643_, v___f_644_, v_prio_645_, v___f_646_, v___f_647_, v_x_648_);
stack->m_obj
 = v_res_685_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__13___boxed(lean_object* v_a_686_, lean_object* v___f_687_, lean_object* v___f_688_, lean_object* v_a_689_, lean_object* v_y_690_, lean_object* v___f_691_, lean_object* v_prio_692_, lean_object* v___f_693_, lean_object* v___f_694_, lean_object* v_x_695_, lean_object* v___y_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__13(v_a_686_, v___f_687_, v___f_688_, v_a_689_, v_y_690_, v___f_691_, v_prio_692_, v___f_693_, v___f_694_, v_x_695_);
return v_res_697_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__14(lean_object* v_x_698_, lean_object* v___f_699_, lean_object* v___f_700_, lean_object* v_a_701_, lean_object* v_y_702_, lean_object* v___f_703_, lean_object* v_prio_704_, lean_object* v___f_705_, lean_object* v___f_706_, lean_object* v_x_707_){
_start:
{
if (lean_obj_tag(v_x_707_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_717_; 
lean_dec_ref(v___f_706_);
lean_dec_ref(v___f_705_);
lean_dec(v_prio_704_);
lean_dec(v___f_703_);
lean_dec_ref(v_y_702_);
lean_dec_ref(v_a_701_);
lean_dec(v___f_700_);
lean_dec_ref(v___f_699_);
lean_dec_ref(v_x_698_);
v_a_709_ = lean_ctor_get(v_x_707_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v_x_707_);
if (v_isSharedCheck_717_ == 0)
{
v___x_711_ = v_x_707_;
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v_x_707_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_716_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_715_; 
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
return v___x_715_;
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_732_; 
v_a_718_ = lean_ctor_get(v_x_707_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v_x_707_);
if (v_isSharedCheck_732_ == 0)
{
v___x_720_ = v_x_707_;
v_isShared_721_ = v_isSharedCheck_732_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v_x_707_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_732_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___f_722_; lean_object* v___f_723_; lean_object* v___x_724_; uint8_t v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
lean_inc(v_a_718_);
v___f_722_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_722_, 0, v_x_698_);
lean_closure_set(v___f_722_, 1, v_a_718_);
lean_closure_set(v___f_722_, 2, v___f_699_);
lean_inc_ref(v_a_701_);
v___f_723_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__13___boxed), 11, 9);
lean_closure_set(v___f_723_, 0, v_a_718_);
lean_closure_set(v___f_723_, 1, v___f_700_);
lean_closure_set(v___f_723_, 2, v___f_722_);
lean_closure_set(v___f_723_, 3, v_a_701_);
lean_closure_set(v___f_723_, 4, v_y_702_);
lean_closure_set(v___f_723_, 5, v___f_703_);
lean_closure_set(v___f_723_, 6, v_prio_704_);
lean_closure_set(v___f_723_, 7, v___f_705_);
lean_closure_set(v___f_723_, 8, v___f_706_);
v___x_724_ = lean_unsigned_to_nat(0u);
v___x_725_ = 0;
v___x_726_ = l_Std_CancellationContext_fork(v_a_701_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v___x_726_);
v___x_728_ = v___x_720_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_726_);
v___x_728_ = v_reuseFailAlloc_731_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
v___x_730_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_724_, v___x_725_, v___x_729_, v___f_723_);
return v___x_730_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrently___redArg___lam__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_698_ = stack[0].m_obj;
lean_object* v___f_699_ = stack[1].m_obj;
lean_object* v___f_700_ = stack[2].m_obj;
lean_object* v_a_701_ = stack[3].m_obj;
lean_object* v_y_702_ = stack[4].m_obj;
lean_object* v___f_703_ = stack[5].m_obj;
lean_object* v_prio_704_ = stack[6].m_obj;
lean_object* v___f_705_ = stack[7].m_obj;
lean_object* v___f_706_ = stack[8].m_obj;
lean_object* v_x_707_ = stack[9].m_obj;
lean_object* v_res_733_;
v_res_733_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__14(v_x_698_, v___f_699_, v___f_700_, v_a_701_, v_y_702_, v___f_703_, v_prio_704_, v___f_705_, v___f_706_, v_x_707_);
stack->m_obj
 = v_res_733_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__14___boxed(lean_object* v_x_734_, lean_object* v___f_735_, lean_object* v___f_736_, lean_object* v_a_737_, lean_object* v_y_738_, lean_object* v___f_739_, lean_object* v_prio_740_, lean_object* v___f_741_, lean_object* v___f_742_, lean_object* v_x_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__14(v_x_734_, v___f_735_, v___f_736_, v_a_737_, v_y_738_, v___f_739_, v_prio_740_, v___f_741_, v___f_742_, v_x_743_);
return v_res_745_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__15(lean_object* v_x_746_, lean_object* v___f_747_, lean_object* v_y_748_, lean_object* v___f_749_, lean_object* v_prio_750_, lean_object* v___f_751_, lean_object* v___f_752_, lean_object* v_x_753_){
_start:
{
if (lean_obj_tag(v_x_753_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_763_; 
lean_dec_ref(v___f_752_);
lean_dec_ref(v___f_751_);
lean_dec(v_prio_750_);
lean_dec(v___f_749_);
lean_dec_ref(v_y_748_);
lean_dec(v___f_747_);
lean_dec_ref(v_x_746_);
v_a_755_ = lean_ctor_get(v_x_753_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_763_ == 0)
{
v___x_757_ = v_x_753_;
v_isShared_758_ = v_isSharedCheck_763_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v_x_753_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_763_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_762_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; 
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
return v___x_761_;
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_778_; 
v_a_764_ = lean_ctor_get(v_x_753_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_778_ == 0)
{
v___x_766_ = v_x_753_;
v_isShared_767_ = v_isSharedCheck_778_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v_x_753_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_778_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___f_768_; lean_object* v___f_769_; lean_object* v___x_770_; uint8_t v___x_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
lean_inc_n(v_a_764_, 2);
v___f_768_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_768_, 0, v_a_764_);
v___f_769_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__14___boxed), 11, 9);
lean_closure_set(v___f_769_, 0, v_x_746_);
lean_closure_set(v___f_769_, 1, v___f_768_);
lean_closure_set(v___f_769_, 2, v___f_747_);
lean_closure_set(v___f_769_, 3, v_a_764_);
lean_closure_set(v___f_769_, 4, v_y_748_);
lean_closure_set(v___f_769_, 5, v___f_749_);
lean_closure_set(v___f_769_, 6, v_prio_750_);
lean_closure_set(v___f_769_, 7, v___f_751_);
lean_closure_set(v___f_769_, 8, v___f_752_);
v___x_770_ = lean_unsigned_to_nat(0u);
v___x_771_ = 0;
v___x_772_ = l_Std_CancellationContext_fork(v_a_764_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 0, v___x_772_);
v___x_774_ = v___x_766_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_772_);
v___x_774_ = v_reuseFailAlloc_777_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
v___x_776_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_770_, v___x_771_, v___x_775_, v___f_769_);
return v___x_776_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrently___redArg___lam__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_746_ = stack[0].m_obj;
lean_object* v___f_747_ = stack[1].m_obj;
lean_object* v_y_748_ = stack[2].m_obj;
lean_object* v___f_749_ = stack[3].m_obj;
lean_object* v_prio_750_ = stack[4].m_obj;
lean_object* v___f_751_ = stack[5].m_obj;
lean_object* v___f_752_ = stack[6].m_obj;
lean_object* v_x_753_ = stack[7].m_obj;
lean_object* v_res_779_;
v_res_779_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__15(v_x_746_, v___f_747_, v_y_748_, v___f_749_, v_prio_750_, v___f_751_, v___f_752_, v_x_753_);
stack->m_obj
 = v_res_779_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__15___boxed(lean_object* v_x_780_, lean_object* v___f_781_, lean_object* v_y_782_, lean_object* v___f_783_, lean_object* v_prio_784_, lean_object* v___f_785_, lean_object* v___f_786_, lean_object* v_x_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__15(v_x_780_, v___f_781_, v_y_782_, v___f_783_, v_prio_784_, v___f_785_, v___f_786_, v_x_787_);
return v_res_789_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__16(lean_object* v___f_790_, lean_object* v_x_791_){
_start:
{
if (lean_obj_tag(v_x_791_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_801_; 
lean_dec_ref(v___f_790_);
v_a_793_ = lean_ctor_get(v_x_791_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v_x_791_);
if (v_isSharedCheck_801_ == 0)
{
v___x_795_ = v_x_791_;
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v_x_791_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_793_);
v___x_798_ = v_reuseFailAlloc_800_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
lean_object* v___x_799_; 
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
return v___x_799_;
}
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_814_; 
v_a_802_ = lean_ctor_get(v_x_791_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v_x_791_);
if (v_isSharedCheck_814_ == 0)
{
v___x_804_ = v_x_791_;
v_isShared_805_ = v_isSharedCheck_814_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v_x_791_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_814_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; uint8_t v___x_807_; lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_806_ = lean_unsigned_to_nat(0u);
v___x_807_ = 0;
v___x_808_ = l_Std_CancellationContext_fork(v_a_802_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___x_808_);
v___x_810_ = v___x_804_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_813_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
v___x_812_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_806_, v___x_807_, v___x_811_, v___f_790_);
return v___x_812_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrently___redArg___lam__16_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_790_ = stack[0].m_obj;
lean_object* v_x_791_ = stack[1].m_obj;
lean_object* v_res_815_;
v_res_815_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__16(v___f_790_, v_x_791_);
stack->m_obj
 = v_res_815_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__16___boxed(lean_object* v___f_816_, lean_object* v_x_817_, lean_object* v___y_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__16(v___f_816_, v_x_817_);
return v_res_819_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrently___redArg(lean_object* v_x_821_, lean_object* v_y_822_, lean_object* v_prio_823_, lean_object* v_a_824_){
_start:
{
lean_object* v___f_826_; lean_object* v___f_827_; lean_object* v___f_828_; lean_object* v___f_829_; lean_object* v___x_830_; uint8_t v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___f_826_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_827_ = ((lean_object*)(l_Std_Async_ContextAsync_run___redArg___closed__0));
v___f_828_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__15___boxed), 9, 7);
lean_closure_set(v___f_828_, 0, v_x_821_);
lean_closure_set(v___f_828_, 1, v___f_827_);
lean_closure_set(v___f_828_, 2, v_y_822_);
lean_closure_set(v___f_828_, 3, v___f_827_);
lean_closure_set(v___f_828_, 4, v_prio_823_);
lean_closure_set(v___f_828_, 5, v___f_826_);
lean_closure_set(v___f_828_, 6, v___f_826_);
v___f_829_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__16___boxed), 3, 1);
lean_closure_set(v___f_829_, 0, v___f_828_);
v___x_830_ = lean_unsigned_to_nat(0u);
v___x_831_ = 0;
lean_inc_ref(v_a_824_);
v___x_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_832_, 0, v_a_824_);
v___x_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
v___x_834_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_830_, v___x_831_, v___x_833_, v___f_829_);
return v___x_834_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrently___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_821_ = stack[0].m_obj;
lean_object* v_y_822_ = stack[1].m_obj;
lean_object* v_prio_823_ = stack[2].m_obj;
lean_object* v_a_824_ = stack[3].m_obj;
lean_object* v_res_835_;
v_res_835_ = l_Std_Async_ContextAsync_concurrently___redArg(v_x_821_, v_y_822_, v_prio_823_, v_a_824_);
stack->m_obj
 = v_res_835_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___boxed(lean_object* v_x_836_, lean_object* v_y_837_, lean_object* v_prio_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Std_Async_ContextAsync_concurrently___redArg(v_x_836_, v_y_837_, v_prio_838_, v_a_839_);
lean_dec_ref(v_a_839_);
return v_res_841_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrently(lean_object* v_00_u03b1_842_, lean_object* v_00_u03b2_843_, lean_object* v_x_844_, lean_object* v_y_845_, lean_object* v_prio_846_, lean_object* v_a_847_){
_start:
{
lean_object* v___f_849_; lean_object* v___f_850_; lean_object* v___f_851_; lean_object* v___f_852_; lean_object* v___x_853_; uint8_t v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___f_849_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_850_ = ((lean_object*)(l_Std_Async_ContextAsync_run___redArg___closed__0));
v___f_851_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__15___boxed), 9, 7);
lean_closure_set(v___f_851_, 0, v_x_844_);
lean_closure_set(v___f_851_, 1, v___f_850_);
lean_closure_set(v___f_851_, 2, v_y_845_);
lean_closure_set(v___f_851_, 3, v___f_850_);
lean_closure_set(v___f_851_, 4, v_prio_846_);
lean_closure_set(v___f_851_, 5, v___f_849_);
lean_closure_set(v___f_851_, 6, v___f_849_);
v___f_852_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__16___boxed), 3, 1);
lean_closure_set(v___f_852_, 0, v___f_851_);
v___x_853_ = lean_unsigned_to_nat(0u);
v___x_854_ = 0;
lean_inc_ref(v_a_847_);
v___x_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_855_, 0, v_a_847_);
v___x_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
v___x_857_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_853_, v___x_854_, v___x_856_, v___f_852_);
return v___x_857_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrently_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_844_ = stack[2].m_obj;
lean_object* v_y_845_ = stack[3].m_obj;
lean_object* v_prio_846_ = stack[4].m_obj;
lean_object* v_a_847_ = stack[5].m_obj;
lean_object* v_res_858_;
v_res_858_ = l_Std_Async_ContextAsync_concurrently(lean_box(0), lean_box(0), v_x_844_, v_y_845_, v_prio_846_, v_a_847_);
stack->m_obj
 = v_res_858_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___boxed(lean_object* v_00_u03b1_859_, lean_object* v_00_u03b2_860_, lean_object* v_x_861_, lean_object* v_y_862_, lean_object* v_prio_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Std_Async_ContextAsync_concurrently(v_00_u03b1_859_, v_00_u03b2_860_, v_x_861_, v_y_862_, v_prio_863_, v_a_864_);
lean_dec_ref(v_a_864_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__0(lean_object* v_x_867_){
_start:
{
lean_object* v_fst_868_; 
v_fst_868_ = lean_ctor_get(v_x_867_, 0);
lean_inc(v_fst_868_);
return v_fst_868_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__0___boxed(lean_object* v_x_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__0(v_x_869_);
lean_dec_ref(v_x_869_);
return v_res_870_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1(lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_874_, 0, v___y_871_);
return v___x_874_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_871_ = stack[0].m_obj;
lean_object* v___y_872_ = stack[1].m_obj;
lean_object* v_res_875_;
v_res_875_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1(v___y_871_, v___y_872_);
stack->m_obj
 = v_res_875_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1___boxed(lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1(v___y_876_, v___y_877_);
lean_dec_ref(v___y_877_);
return v_res_879_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6(lean_object* v_ctxAsync_880_, lean_object* v_a_881_, lean_object* v___f_882_){
_start:
{
lean_object* v___x_884_; uint8_t v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_884_ = lean_unsigned_to_nat(0u);
v___x_885_ = 0;
v___x_886_ = lean_apply_2(v_ctxAsync_880_, v_a_881_, lean_box(0));
v___x_887_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_884_, v___x_885_, v___x_886_, v___f_882_);
return v___x_887_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctxAsync_880_ = stack[0].m_obj;
lean_object* v_a_881_ = stack[1].m_obj;
lean_object* v___f_882_ = stack[2].m_obj;
lean_object* v_res_888_;
v_res_888_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6(v_ctxAsync_880_, v_a_881_, v___f_882_);
stack->m_obj
 = v_res_888_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6___boxed(lean_object* v_ctxAsync_889_, lean_object* v_a_890_, lean_object* v___f_891_, lean_object* v___y_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6(v_ctxAsync_889_, v_a_890_, v___f_891_);
return v_res_893_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2(lean_object* v_a_894_, lean_object* v___x_895_, lean_object* v_a_x3f_896_){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_898_ = l_Std_CancellationContext_cancel(v_a_894_, v___x_895_);
v___x_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
v___x_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
return v___x_900_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_894_ = stack[0].m_obj;
lean_object* v___x_895_ = stack[1].m_obj;
lean_object* v_a_x3f_896_ = stack[2].m_obj;
lean_object* v_res_901_;
v_res_901_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2(v_a_894_, v___x_895_, v_a_x3f_896_);
stack->m_obj
 = v_res_901_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2___boxed(lean_object* v_a_902_, lean_object* v___x_903_, lean_object* v_a_x3f_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2(v_a_902_, v___x_903_, v_a_x3f_904_);
lean_dec(v_a_x3f_904_);
return v_res_906_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4(lean_object* v_ctxAsync_907_, lean_object* v___f_908_, lean_object* v___f_909_, lean_object* v_prio_910_, lean_object* v___f_911_, lean_object* v_x_912_){
_start:
{
if (lean_obj_tag(v_x_912_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_922_; 
lean_dec_ref(v___f_911_);
lean_dec(v_prio_910_);
lean_dec(v___f_909_);
lean_dec_ref(v___f_908_);
lean_dec_ref(v_ctxAsync_907_);
v_a_914_ = lean_ctor_get(v_x_912_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v_x_912_);
if (v_isSharedCheck_922_ == 0)
{
v___x_916_ = v_x_912_;
v_isShared_917_ = v_isSharedCheck_922_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v_x_912_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_922_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_921_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_920_; 
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
return v___x_920_;
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_940_; 
v_a_923_ = lean_ctor_get(v_x_912_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v_x_912_);
if (v_isSharedCheck_940_ == 0)
{
v___x_925_ = v_x_912_;
v_isShared_926_ = v_isSharedCheck_940_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v_x_912_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_940_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___f_927_; lean_object* v___x_928_; lean_object* v___f_929_; lean_object* v___f_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; uint8_t v___x_934_; lean_object* v___x_935_; lean_object* v___x_937_; 
lean_inc(v_a_923_);
v___f_927_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6___boxed), 4, 3);
lean_closure_set(v___f_927_, 0, v_ctxAsync_907_);
lean_closure_set(v___f_927_, 1, v_a_923_);
lean_closure_set(v___f_927_, 2, v___f_908_);
v___x_928_ = lean_box(2);
v___f_929_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_929_, 0, v_a_923_);
lean_closure_set(v___f_929_, 1, v___x_928_);
v___f_930_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_930_, 0, v___f_909_);
lean_closure_set(v___f_930_, 1, v___f_927_);
lean_closure_set(v___f_930_, 2, v___f_929_);
v___x_931_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_931_, 0, lean_box(0));
lean_closure_set(v___x_931_, 1, v___f_930_);
v___x_932_ = lean_io_as_task(v___x_931_, v_prio_910_);
v___x_933_ = lean_unsigned_to_nat(0u);
v___x_934_ = 1;
v___x_935_ = lean_task_bind(v___x_932_, v___f_911_, v___x_933_, v___x_934_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v___x_935_);
v___x_937_ = v___x_925_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_935_);
v___x_937_ = v_reuseFailAlloc_939_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_object* v___x_938_; 
v___x_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
return v___x_938_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctxAsync_907_ = stack[0].m_obj;
lean_object* v___f_908_ = stack[1].m_obj;
lean_object* v___f_909_ = stack[2].m_obj;
lean_object* v_prio_910_ = stack[3].m_obj;
lean_object* v___f_911_ = stack[4].m_obj;
lean_object* v_x_912_ = stack[5].m_obj;
lean_object* v_res_941_;
v_res_941_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4(v_ctxAsync_907_, v___f_908_, v___f_909_, v_prio_910_, v___f_911_, v_x_912_);
stack->m_obj
 = v_res_941_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4___boxed(lean_object* v_ctxAsync_942_, lean_object* v___f_943_, lean_object* v___f_944_, lean_object* v_prio_945_, lean_object* v___f_946_, lean_object* v_x_947_, lean_object* v___y_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4(v_ctxAsync_942_, v___f_943_, v___f_944_, v_prio_945_, v___f_946_, v_x_947_);
return v_res_949_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3(lean_object* v___f_950_, lean_object* v___f_951_, lean_object* v_prio_952_, lean_object* v___f_953_, lean_object* v_a_954_, lean_object* v_ctxAsync_955_, lean_object* v___y_956_){
_start:
{
lean_object* v___f_958_; lean_object* v___x_959_; uint8_t v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___f_958_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4___boxed), 7, 5);
lean_closure_set(v___f_958_, 0, v_ctxAsync_955_);
lean_closure_set(v___f_958_, 1, v___f_950_);
lean_closure_set(v___f_958_, 2, v___f_951_);
lean_closure_set(v___f_958_, 3, v_prio_952_);
lean_closure_set(v___f_958_, 4, v___f_953_);
v___x_959_ = lean_unsigned_to_nat(0u);
v___x_960_ = 0;
v___x_961_ = l_Std_CancellationContext_fork(v_a_954_);
v___x_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
v___x_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
v___x_964_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_959_, v___x_960_, v___x_963_, v___f_958_);
return v___x_964_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_950_ = stack[0].m_obj;
lean_object* v___f_951_ = stack[1].m_obj;
lean_object* v_prio_952_ = stack[2].m_obj;
lean_object* v___f_953_ = stack[3].m_obj;
lean_object* v_a_954_ = stack[4].m_obj;
lean_object* v_ctxAsync_955_ = stack[5].m_obj;
lean_object* v___y_956_ = stack[6].m_obj;
lean_object* v_res_965_;
v_res_965_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3(v___f_950_, v___f_951_, v_prio_952_, v___f_953_, v_a_954_, v_ctxAsync_955_, v___y_956_);
stack->m_obj
 = v_res_965_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3___boxed(lean_object* v___f_966_, lean_object* v___f_967_, lean_object* v_prio_968_, lean_object* v___f_969_, lean_object* v_a_970_, lean_object* v_ctxAsync_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3(v___f_966_, v___f_967_, v_prio_968_, v___f_969_, v_a_970_, v_ctxAsync_971_, v___y_972_);
lean_dec_ref(v___y_972_);
return v_res_974_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5(lean_object* v_a_975_, lean_object* v___x_976_, lean_object* v_a_x3f_977_){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_979_ = l_Std_CancellationContext_cancel(v_a_975_, v___x_976_);
v___x_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
v___x_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
return v___x_981_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_975_ = stack[0].m_obj;
lean_object* v___x_976_ = stack[1].m_obj;
lean_object* v_a_x3f_977_ = stack[2].m_obj;
lean_object* v_res_982_;
v_res_982_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5(v_a_975_, v___x_976_, v_a_x3f_977_);
stack->m_obj
 = v_res_982_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5___boxed(lean_object* v_a_983_, lean_object* v___x_984_, lean_object* v_a_x3f_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5(v_a_983_, v___x_984_, v_a_x3f_985_);
lean_dec(v_a_x3f_985_);
return v_res_987_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7(lean_object* v_a_988_, lean_object* v___f_989_, lean_object* v___x_990_, lean_object* v___f_991_, lean_object* v_a_992_, lean_object* v_x_993_){
_start:
{
if (lean_obj_tag(v_x_993_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1003_; 
lean_dec_ref(v___f_991_);
lean_dec_ref(v___x_990_);
lean_dec_ref(v___f_989_);
lean_dec_ref(v_a_988_);
v_a_995_ = lean_ctor_get(v_x_993_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_x_993_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_997_ = v_x_993_;
v_isShared_998_ = v_isSharedCheck_1003_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v_x_993_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1003_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1002_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
return v___x_1001_;
}
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1005_; lean_object* v___f_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; uint8_t v___x_1009_; size_t v_sz_1010_; size_t v___x_1011_; lean_object* v___x_5454__overap_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___y_1016_; 
v_a_1004_ = lean_ctor_get(v_x_993_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v_x_993_, 1);
v___x_1005_ = lean_box(2);
v___f_1006_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_1006_, 0, v_a_988_);
lean_closure_set(v___f_1006_, 1, v___x_1005_);
v___x_1007_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_1007_, 0, lean_box(0));
lean_closure_set(v___x_1007_, 1, lean_box(0));
lean_closure_set(v___x_1007_, 2, lean_box(0));
lean_closure_set(v___x_1007_, 3, v___f_989_);
v___x_1008_ = lean_unsigned_to_nat(0u);
v___x_1009_ = 0;
v_sz_1010_ = lean_array_size(v_a_1004_);
v___x_1011_ = ((size_t)0ULL);
v___x_5454__overap_1012_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_990_, v___f_991_, v_sz_1010_, v___x_1011_, v_a_1004_);
lean_inc_ref(v_a_992_);
v___x_1013_ = lean_apply_1(v___x_5454__overap_1012_, v_a_992_);
v___x_1014_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_1013_, v___f_1006_, v___x_1008_, v___x_1009_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1018_; 
lean_dec_ref(v___x_1007_);
v_a_1018_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1018_);
lean_dec_ref_known(v___x_1014_, 1);
if (lean_obj_tag(v_a_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
v_a_1019_ = lean_ctor_get(v_a_1018_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_a_1018_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v_a_1018_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v_a_1018_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
v___y_1016_ = v___x_1024_;
goto v___jp_1015_;
}
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1035_; 
v_a_1027_ = lean_ctor_get(v_a_1018_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_a_1018_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1029_ = v_a_1018_;
v_isShared_1030_ = v_isSharedCheck_1035_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v_a_1018_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1035_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v_fst_1031_; lean_object* v___x_1033_; 
v_fst_1031_ = lean_ctor_get(v_a_1027_, 0);
lean_inc(v_fst_1031_);
lean_dec(v_a_1027_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v_fst_1031_);
v___x_1033_ = v___x_1029_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_fst_1031_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
v___y_1016_ = v___x_1033_;
goto v___jp_1015_;
}
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1044_; 
v_a_1036_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1038_ = v___x_1014_;
v_isShared_1039_ = v_isSharedCheck_1044_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1014_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1044_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; lean_object* v___x_1042_; 
v___x_1040_ = lean_task_map(v___x_1007_, v_a_1036_, v___x_1008_, v___x_1009_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 0, v___x_1040_);
v___x_1042_ = v___x_1038_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
v___jp_1015_:
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v___y_1016_);
return v___x_1017_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_988_ = stack[0].m_obj;
lean_object* v___f_989_ = stack[1].m_obj;
lean_object* v___x_990_ = stack[2].m_obj;
lean_object* v___f_991_ = stack[3].m_obj;
lean_object* v_a_992_ = stack[4].m_obj;
lean_object* v_x_993_ = stack[5].m_obj;
lean_object* v_res_1045_;
v_res_1045_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7(v_a_988_, v___f_989_, v___x_990_, v___f_991_, v_a_992_, v_x_993_);
stack->m_obj
 = v_res_1045_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7___boxed(lean_object* v_a_1046_, lean_object* v___f_1047_, lean_object* v___x_1048_, lean_object* v___f_1049_, lean_object* v_a_1050_, lean_object* v_x_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7(v_a_1046_, v___f_1047_, v___x_1048_, v___f_1049_, v_a_1050_, v_x_1051_);
lean_dec_ref(v_a_1050_);
return v_res_1053_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__8(lean_object* v___f_1054_, lean_object* v_prio_1055_, lean_object* v___f_1056_, lean_object* v___f_1057_, lean_object* v___x_1058_, lean_object* v___f_1059_, lean_object* v_a_1060_, lean_object* v_xs_1061_, lean_object* v_x_1062_){
_start:
{
if (lean_obj_tag(v_x_1062_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1072_; 
lean_dec_ref(v_xs_1061_);
lean_dec_ref(v___f_1059_);
lean_dec_ref(v___x_1058_);
lean_dec_ref(v___f_1057_);
lean_dec_ref(v___f_1056_);
lean_dec(v_prio_1055_);
lean_dec(v___f_1054_);
v_a_1064_ = lean_ctor_get(v_x_1062_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_x_1062_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1066_ = v_x_1062_;
v_isShared_1067_ = v_isSharedCheck_1072_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v_x_1062_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1072_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
return v___x_1070_;
}
}
}
else
{
lean_object* v_a_1073_; lean_object* v___f_1074_; lean_object* v___f_1075_; lean_object* v___f_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; size_t v_sz_1079_; size_t v___x_1080_; lean_object* v___x_5489__overap_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v_a_1073_ = lean_ctor_get(v_x_1062_, 0);
lean_inc_n(v_a_1073_, 3);
lean_dec_ref_known(v_x_1062_, 1);
v___f_1074_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1074_, 0, v_a_1073_);
v___f_1075_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3___boxed), 8, 5);
lean_closure_set(v___f_1075_, 0, v___f_1074_);
lean_closure_set(v___f_1075_, 1, v___f_1054_);
lean_closure_set(v___f_1075_, 2, v_prio_1055_);
lean_closure_set(v___f_1075_, 3, v___f_1056_);
lean_closure_set(v___f_1075_, 4, v_a_1073_);
lean_inc_ref_n(v_a_1060_, 2);
lean_inc_ref(v___x_1058_);
v___f_1076_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7___boxed), 7, 5);
lean_closure_set(v___f_1076_, 0, v_a_1073_);
lean_closure_set(v___f_1076_, 1, v___f_1057_);
lean_closure_set(v___f_1076_, 2, v___x_1058_);
lean_closure_set(v___f_1076_, 3, v___f_1059_);
lean_closure_set(v___f_1076_, 4, v_a_1060_);
v___x_1077_ = lean_unsigned_to_nat(0u);
v___x_1078_ = 0;
v_sz_1079_ = lean_array_size(v_xs_1061_);
v___x_1080_ = ((size_t)0ULL);
v___x_5489__overap_1081_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1058_, v___f_1075_, v_sz_1079_, v___x_1080_, v_xs_1061_);
v___x_1082_ = lean_apply_2(v___x_5489__overap_1081_, v_a_1060_, lean_box(0));
v___x_1083_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1077_, v___x_1078_, v___x_1082_, v___f_1076_);
return v___x_1083_;
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1054_ = stack[0].m_obj;
lean_object* v_prio_1055_ = stack[1].m_obj;
lean_object* v___f_1056_ = stack[2].m_obj;
lean_object* v___f_1057_ = stack[3].m_obj;
lean_object* v___x_1058_ = stack[4].m_obj;
lean_object* v___f_1059_ = stack[5].m_obj;
lean_object* v_a_1060_ = stack[6].m_obj;
lean_object* v_xs_1061_ = stack[7].m_obj;
lean_object* v_x_1062_ = stack[8].m_obj;
lean_object* v_res_1084_;
v_res_1084_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__8(v___f_1054_, v_prio_1055_, v___f_1056_, v___f_1057_, v___x_1058_, v___f_1059_, v_a_1060_, v_xs_1061_, v_x_1062_);
stack->m_obj
 = v_res_1084_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__8___boxed(lean_object* v___f_1085_, lean_object* v_prio_1086_, lean_object* v___f_1087_, lean_object* v___f_1088_, lean_object* v___x_1089_, lean_object* v___f_1090_, lean_object* v_a_1091_, lean_object* v_xs_1092_, lean_object* v_x_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__8(v___f_1085_, v_prio_1086_, v___f_1087_, v___f_1088_, v___x_1089_, v___f_1090_, v_a_1091_, v_xs_1092_, v_x_1093_);
lean_dec_ref(v_a_1091_);
return v_res_1095_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__9(lean_object* v___f_1096_, lean_object* v_x_1097_){
_start:
{
if (lean_obj_tag(v_x_1097_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1107_; 
lean_dec_ref(v___f_1096_);
v_a_1099_ = lean_ctor_get(v_x_1097_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v_x_1097_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1101_ = v_x_1097_;
v_isShared_1102_ = v_isSharedCheck_1107_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v_x_1097_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1107_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v___x_1105_; 
v___x_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
return v___x_1105_;
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1120_; 
v_a_1108_ = lean_ctor_get(v_x_1097_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_x_1097_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1110_ = v_x_1097_;
v_isShared_1111_ = v_isSharedCheck_1120_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v_x_1097_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1120_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; uint8_t v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1116_; 
v___x_1112_ = lean_unsigned_to_nat(0u);
v___x_1113_ = 0;
v___x_1114_ = l_Std_CancellationContext_fork(v_a_1108_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1114_);
v___x_1116_ = v___x_1110_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
v___x_1118_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1112_, v___x_1113_, v___x_1117_, v___f_1096_);
return v___x_1118_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1096_ = stack[0].m_obj;
lean_object* v_x_1097_ = stack[1].m_obj;
lean_object* v_res_1121_;
v_res_1121_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__9(v___f_1096_, v_x_1097_);
stack->m_obj
 = v_res_1121_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__9___boxed(lean_object* v___f_1122_, lean_object* v_x_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__9(v___f_1122_, v_x_1123_);
return v_res_1125_;
}
}
static lean_object* _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2(void){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_1128_;
}
}
static lean_object* _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__3(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = lean_obj_once(&l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2, &l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2_once, _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2);
v___x_1130_ = l_ReaderT_instMonad___redArg(v___x_1129_);
return v___x_1130_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg(lean_object* v_xs_1131_, lean_object* v_prio_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v___f_1135_; lean_object* v___f_1136_; lean_object* v___f_1137_; lean_object* v___f_1138_; lean_object* v___x_1139_; lean_object* v___f_1140_; lean_object* v___f_1141_; lean_object* v___x_1142_; uint8_t v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___f_1135_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__0));
v___f_1136_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1));
v___f_1137_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_1138_ = ((lean_object*)(l_Std_Async_ContextAsync_run___redArg___closed__0));
v___x_1139_ = lean_obj_once(&l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__3, &l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__3_once, _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__3);
lean_inc_ref_n(v_a_1133_, 2);
v___f_1140_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__8___boxed), 10, 8);
lean_closure_set(v___f_1140_, 0, v___f_1138_);
lean_closure_set(v___f_1140_, 1, v_prio_1132_);
lean_closure_set(v___f_1140_, 2, v___f_1137_);
lean_closure_set(v___f_1140_, 3, v___f_1135_);
lean_closure_set(v___f_1140_, 4, v___x_1139_);
lean_closure_set(v___f_1140_, 5, v___f_1136_);
lean_closure_set(v___f_1140_, 6, v_a_1133_);
lean_closure_set(v___f_1140_, 7, v_xs_1131_);
v___f_1141_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_1141_, 0, v___f_1140_);
v___x_1142_ = lean_unsigned_to_nat(0u);
v___x_1143_ = 0;
v___x_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1144_, 0, v_a_1133_);
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
v___x_1146_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1142_, v___x_1143_, v___x_1145_, v___f_1141_);
return v___x_1146_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrentlyAll___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1131_ = stack[0].m_obj;
lean_object* v_prio_1132_ = stack[1].m_obj;
lean_object* v_a_1133_ = stack[2].m_obj;
lean_object* v_res_1147_;
v_res_1147_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg(v_xs_1131_, v_prio_1132_, v_a_1133_);
stack->m_obj
 = v_res_1147_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___boxed(lean_object* v_xs_1148_, lean_object* v_prio_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg(v_xs_1148_, v_prio_1149_, v_a_1150_);
lean_dec_ref(v_a_1150_);
return v_res_1152_;
}
}
lean_object* l_Std_Async_ContextAsync_concurrentlyAll(lean_object* v_00_u03b1_1153_, lean_object* v_xs_1154_, lean_object* v_prio_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v___f_1158_; lean_object* v___f_1159_; lean_object* v___f_1160_; lean_object* v___f_1161_; lean_object* v___x_1162_; lean_object* v___f_1163_; lean_object* v___f_1164_; lean_object* v___x_1165_; uint8_t v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___f_1158_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__0));
v___f_1159_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1));
v___f_1160_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_1161_ = ((lean_object*)(l_Std_Async_ContextAsync_run___redArg___closed__0));
v___x_1162_ = lean_obj_once(&l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__3, &l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__3_once, _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__3);
lean_inc_ref_n(v_a_1156_, 2);
v___f_1163_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__8___boxed), 10, 8);
lean_closure_set(v___f_1163_, 0, v___f_1161_);
lean_closure_set(v___f_1163_, 1, v_prio_1155_);
lean_closure_set(v___f_1163_, 2, v___f_1160_);
lean_closure_set(v___f_1163_, 3, v___f_1158_);
lean_closure_set(v___f_1163_, 4, v___x_1162_);
lean_closure_set(v___f_1163_, 5, v___f_1159_);
lean_closure_set(v___f_1163_, 6, v_a_1156_);
lean_closure_set(v___f_1163_, 7, v_xs_1154_);
v___f_1164_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_1164_, 0, v___f_1163_);
v___x_1165_ = lean_unsigned_to_nat(0u);
v___x_1166_ = 0;
v___x_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1167_, 0, v_a_1156_);
v___x_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
v___x_1169_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1165_, v___x_1166_, v___x_1168_, v___f_1164_);
return v___x_1169_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_concurrentlyAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1154_ = stack[1].m_obj;
lean_object* v_prio_1155_ = stack[2].m_obj;
lean_object* v_a_1156_ = stack[3].m_obj;
lean_object* v_res_1170_;
v_res_1170_ = l_Std_Async_ContextAsync_concurrentlyAll(lean_box(0), v_xs_1154_, v_prio_1155_, v_a_1156_);
stack->m_obj
 = v_res_1170_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___boxed(lean_object* v_00_u03b1_1171_, lean_object* v_xs_1172_, lean_object* v_prio_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Std_Async_ContextAsync_concurrentlyAll(v_00_u03b1_1171_, v_xs_1172_, v_prio_1173_, v_a_1174_);
lean_dec_ref(v_a_1174_);
return v_res_1176_;
}
}
lean_object* l_Std_Async_ContextAsync_background___redArg___lam__1(lean_object* v_action_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = lean_apply_2(v_action_1177_, v_a_1178_, lean_box(0));
return v___x_1180_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_background___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_action_1177_ = stack[0].m_obj;
lean_object* v_a_1178_ = stack[1].m_obj;
lean_object* v_res_1181_;
v_res_1181_ = l_Std_Async_ContextAsync_background___redArg___lam__1(v_action_1177_, v_a_1178_);
stack->m_obj
 = v_res_1181_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__1___boxed(lean_object* v_action_1182_, lean_object* v_a_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Std_Async_ContextAsync_background___redArg___lam__1(v_action_1182_, v_a_1183_);
return v_res_1185_;
}
}
lean_object* l_Std_Async_ContextAsync_background___redArg___lam__3(lean_object* v_action_1190_, lean_object* v___f_1191_, lean_object* v_prio_1192_, lean_object* v_x_1193_){
_start:
{
if (lean_obj_tag(v_x_1193_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1203_; 
lean_dec(v_prio_1192_);
lean_dec(v___f_1191_);
lean_dec_ref(v_action_1190_);
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
lean_object* v_a_1204_; lean_object* v___f_1205_; lean_object* v___x_1206_; lean_object* v___f_1207_; lean_object* v___f_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v_a_1204_ = lean_ctor_get(v_x_1193_, 0);
lean_inc_n(v_a_1204_, 2);
lean_dec_ref_known(v_x_1193_, 1);
v___f_1205_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_background___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_1205_, 0, v_action_1190_);
lean_closure_set(v___f_1205_, 1, v_a_1204_);
v___x_1206_ = lean_box(2);
v___f_1207_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1207_, 0, v_a_1204_);
lean_closure_set(v___f_1207_, 1, v___x_1206_);
v___f_1208_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_1208_, 0, v___f_1191_);
lean_closure_set(v___f_1208_, 1, v___f_1205_);
lean_closure_set(v___f_1208_, 2, v___f_1207_);
v___x_1209_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1209_, 0, lean_box(0));
lean_closure_set(v___x_1209_, 1, v___f_1208_);
v___x_1210_ = lean_io_as_task(v___x_1209_, v_prio_1192_);
lean_dec_ref(v___x_1210_);
v___x_1211_ = ((lean_object*)(l_Std_Async_ContextAsync_background___redArg___lam__3___closed__1));
return v___x_1211_;
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_background___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_action_1190_ = stack[0].m_obj;
lean_object* v___f_1191_ = stack[1].m_obj;
lean_object* v_prio_1192_ = stack[2].m_obj;
lean_object* v_x_1193_ = stack[3].m_obj;
lean_object* v_res_1212_;
v_res_1212_ = l_Std_Async_ContextAsync_background___redArg___lam__3(v_action_1190_, v___f_1191_, v_prio_1192_, v_x_1193_);
stack->m_obj
 = v_res_1212_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__3___boxed(lean_object* v_action_1213_, lean_object* v___f_1214_, lean_object* v_prio_1215_, lean_object* v_x_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Std_Async_ContextAsync_background___redArg___lam__3(v_action_1213_, v___f_1214_, v_prio_1215_, v_x_1216_);
return v_res_1218_;
}
}
lean_object* l_Std_Async_ContextAsync_background___redArg___lam__0(lean_object* v___f_1219_, lean_object* v_x_1220_){
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
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1243_; 
v_a_1231_ = lean_ctor_get(v_x_1220_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_x_1220_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1233_ = v_x_1220_;
v_isShared_1234_ = v_isSharedCheck_1243_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v_x_1220_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1243_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; uint8_t v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1239_; 
v___x_1235_ = lean_unsigned_to_nat(0u);
v___x_1236_ = 0;
v___x_1237_ = l_Std_CancellationContext_fork(v_a_1231_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v___x_1237_);
v___x_1239_ = v___x_1233_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
v___x_1241_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1235_, v___x_1236_, v___x_1240_, v___f_1219_);
return v___x_1241_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_background___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1219_ = stack[0].m_obj;
lean_object* v_x_1220_ = stack[1].m_obj;
lean_object* v_res_1244_;
v_res_1244_ = l_Std_Async_ContextAsync_background___redArg___lam__0(v___f_1219_, v_x_1220_);
stack->m_obj
 = v_res_1244_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__0___boxed(lean_object* v___f_1245_, lean_object* v_x_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Std_Async_ContextAsync_background___redArg___lam__0(v___f_1245_, v_x_1246_);
return v_res_1248_;
}
}
lean_object* l_Std_Async_ContextAsync_background___redArg(lean_object* v_action_1249_, lean_object* v_prio_1250_, lean_object* v_a_1251_){
_start:
{
lean_object* v___f_1253_; lean_object* v___f_1254_; lean_object* v___f_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___f_1253_ = ((lean_object*)(l_Std_Async_ContextAsync_run___redArg___closed__0));
v___f_1254_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_background___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_1254_, 0, v_action_1249_);
lean_closure_set(v___f_1254_, 1, v___f_1253_);
lean_closure_set(v___f_1254_, 2, v_prio_1250_);
v___f_1255_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_background___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1255_, 0, v___f_1254_);
v___x_1256_ = lean_unsigned_to_nat(0u);
v___x_1257_ = 0;
lean_inc_ref(v_a_1251_);
v___x_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1258_, 0, v_a_1251_);
v___x_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
v___x_1260_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1256_, v___x_1257_, v___x_1259_, v___f_1255_);
return v___x_1260_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_background___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_action_1249_ = stack[0].m_obj;
lean_object* v_prio_1250_ = stack[1].m_obj;
lean_object* v_a_1251_ = stack[2].m_obj;
lean_object* v_res_1261_;
v_res_1261_ = l_Std_Async_ContextAsync_background___redArg(v_action_1249_, v_prio_1250_, v_a_1251_);
stack->m_obj
 = v_res_1261_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___boxed(lean_object* v_action_1262_, lean_object* v_prio_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Std_Async_ContextAsync_background___redArg(v_action_1262_, v_prio_1263_, v_a_1264_);
lean_dec_ref(v_a_1264_);
return v_res_1266_;
}
}
lean_object* l_Std_Async_ContextAsync_background(lean_object* v_00_u03b1_1267_, lean_object* v_action_1268_, lean_object* v_prio_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v___f_1272_; lean_object* v___f_1273_; lean_object* v___f_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___f_1272_ = ((lean_object*)(l_Std_Async_ContextAsync_run___redArg___closed__0));
v___f_1273_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_background___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_1273_, 0, v_action_1268_);
lean_closure_set(v___f_1273_, 1, v___f_1272_);
lean_closure_set(v___f_1273_, 2, v_prio_1269_);
v___f_1274_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_background___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1274_, 0, v___f_1273_);
v___x_1275_ = lean_unsigned_to_nat(0u);
v___x_1276_ = 0;
lean_inc_ref(v_a_1270_);
v___x_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1277_, 0, v_a_1270_);
v___x_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
v___x_1279_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1275_, v___x_1276_, v___x_1278_, v___f_1274_);
return v___x_1279_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_background_0interp(lean_interpreter_value* stack)
{
lean_object* v_action_1268_ = stack[1].m_obj;
lean_object* v_prio_1269_ = stack[2].m_obj;
lean_object* v_a_1270_ = stack[3].m_obj;
lean_object* v_res_1280_;
v_res_1280_ = l_Std_Async_ContextAsync_background(lean_box(0), v_action_1268_, v_prio_1269_, v_a_1270_);
stack->m_obj
 = v_res_1280_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___boxed(lean_object* v_00_u03b1_1281_, lean_object* v_action_1282_, lean_object* v_prio_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Std_Async_ContextAsync_background(v_00_u03b1_1281_, v_action_1282_, v_prio_1283_, v_a_1284_);
lean_dec_ref(v_a_1284_);
return v_res_1286_;
}
}
lean_object* l_Std_Async_ContextAsync_disown___redArg___lam__1(lean_object* v_action_1287_, lean_object* v_prio_1288_, lean_object* v_x_1289_){
_start:
{
if (lean_obj_tag(v_x_1289_) == 0)
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1299_; 
lean_dec(v_prio_1288_);
lean_dec_ref(v_action_1287_);
v_a_1291_ = lean_ctor_get(v_x_1289_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v_x_1289_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1293_ = v_x_1289_;
v_isShared_1294_ = v_isSharedCheck_1299_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v_x_1289_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1299_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
lean_object* v___x_1297_; 
v___x_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
return v___x_1297_;
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___f_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v_a_1300_ = lean_ctor_get(v_x_1289_, 0);
lean_inc(v_a_1300_);
lean_dec_ref_known(v_x_1289_, 1);
v___f_1301_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_background___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_1301_, 0, v_action_1287_);
lean_closure_set(v___f_1301_, 1, v_a_1300_);
v___x_1302_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1302_, 0, lean_box(0));
lean_closure_set(v___x_1302_, 1, v___f_1301_);
v___x_1303_ = lean_io_as_task(v___x_1302_, v_prio_1288_);
lean_dec_ref(v___x_1303_);
v___x_1304_ = ((lean_object*)(l_Std_Async_ContextAsync_background___redArg___lam__3___closed__1));
return v___x_1304_;
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_disown___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_action_1287_ = stack[0].m_obj;
lean_object* v_prio_1288_ = stack[1].m_obj;
lean_object* v_x_1289_ = stack[2].m_obj;
lean_object* v_res_1305_;
v_res_1305_ = l_Std_Async_ContextAsync_disown___redArg___lam__1(v_action_1287_, v_prio_1288_, v_x_1289_);
stack->m_obj
 = v_res_1305_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg___lam__1___boxed(lean_object* v_action_1306_, lean_object* v_prio_1307_, lean_object* v_x_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Std_Async_ContextAsync_disown___redArg___lam__1(v_action_1306_, v_prio_1307_, v_x_1308_);
return v_res_1310_;
}
}
lean_object* l_Std_Async_ContextAsync_disown___redArg(lean_object* v_action_1311_, lean_object* v_prio_1312_){
_start:
{
lean_object* v___f_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___f_1314_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_disown___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1314_, 0, v_action_1311_);
lean_closure_set(v___f_1314_, 1, v_prio_1312_);
v___x_1315_ = lean_unsigned_to_nat(0u);
v___x_1316_ = 0;
v___x_1317_ = l_Std_CancellationContext_new();
v___x_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
v___x_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
v___x_1320_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1315_, v___x_1316_, v___x_1319_, v___f_1314_);
return v___x_1320_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_disown___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_action_1311_ = stack[0].m_obj;
lean_object* v_prio_1312_ = stack[1].m_obj;
lean_object* v_res_1321_;
v_res_1321_ = l_Std_Async_ContextAsync_disown___redArg(v_action_1311_, v_prio_1312_);
stack->m_obj
 = v_res_1321_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg___boxed(lean_object* v_action_1322_, lean_object* v_prio_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Std_Async_ContextAsync_disown___redArg(v_action_1322_, v_prio_1323_);
return v_res_1325_;
}
}
lean_object* l_Std_Async_ContextAsync_disown(lean_object* v_00_u03b1_1326_, lean_object* v_action_1327_, lean_object* v_prio_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v___f_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___f_1331_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_disown___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1331_, 0, v_action_1327_);
lean_closure_set(v___f_1331_, 1, v_prio_1328_);
v___x_1332_ = lean_unsigned_to_nat(0u);
v___x_1333_ = 0;
v___x_1334_ = l_Std_CancellationContext_new();
v___x_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
v___x_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
v___x_1337_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1332_, v___x_1333_, v___x_1336_, v___f_1331_);
return v___x_1337_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_disown_0interp(lean_interpreter_value* stack)
{
lean_object* v_action_1327_ = stack[1].m_obj;
lean_object* v_prio_1328_ = stack[2].m_obj;
lean_object* v_a_1329_ = stack[3].m_obj;
lean_object* v_res_1338_;
v_res_1338_ = l_Std_Async_ContextAsync_disown(lean_box(0), v_action_1327_, v_prio_1328_, v_a_1329_);
stack->m_obj
 = v_res_1338_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___boxed(lean_object* v_00_u03b1_1339_, lean_object* v_action_1340_, lean_object* v_prio_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Std_Async_ContextAsync_disown(v_00_u03b1_1339_, v_action_1340_, v_prio_1341_, v_a_1342_);
lean_dec_ref(v_a_1342_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__1(lean_object* v_a_1345_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1346_, 0, v_a_1345_);
return v___x_1346_;
}
}
lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__0(lean_object* v_a_1347_, lean_object* v_x_1348_){
_start:
{
if (lean_obj_tag(v_x_1348_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1358_; 
lean_dec_ref(v_a_1347_);
v_a_1350_ = lean_ctor_get(v_x_1348_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_x_1348_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1352_ = v_x_1348_;
v_isShared_1353_ = v_isSharedCheck_1358_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v_x_1348_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1358_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1356_; 
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
return v___x_1356_;
}
}
}
else
{
lean_object* v___x_1359_; 
lean_dec_ref_known(v_x_1348_, 1);
v___x_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1359_, 0, v_a_1347_);
return v___x_1359_;
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_raceAll___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1347_ = stack[0].m_obj;
lean_object* v_x_1348_ = stack[1].m_obj;
lean_object* v_res_1360_;
v_res_1360_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__0(v_a_1347_, v_x_1348_);
stack->m_obj
 = v_res_1360_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__0___boxed(lean_object* v_a_1361_, lean_object* v_x_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__0(v_a_1361_, v_x_1362_);
return v_res_1364_;
}
}
lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__2(lean_object* v_a_1365_, lean_object* v_x_1366_){
_start:
{
if (lean_obj_tag(v_x_1366_) == 0)
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1376_; 
lean_dec_ref(v_a_1365_);
v_a_1368_ = lean_ctor_get(v_x_1366_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_x_1366_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1370_ = v_x_1366_;
v_isShared_1371_ = v_isSharedCheck_1376_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v_x_1366_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1376_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
return v___x_1374_;
}
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1391_; 
v_a_1377_ = lean_ctor_get(v_x_1366_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v_x_1366_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1379_ = v_x_1366_;
v_isShared_1380_ = v_isSharedCheck_1391_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v_x_1366_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1391_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___f_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; uint8_t v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1387_; 
v___f_1381_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1381_, 0, v_a_1377_);
v___x_1382_ = lean_box(2);
v___x_1383_ = lean_unsigned_to_nat(0u);
v___x_1384_ = 0;
v___x_1385_ = l_Std_CancellationContext_cancel(v_a_1365_, v___x_1382_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v___x_1385_);
v___x_1387_ = v___x_1379_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1387_);
v___x_1389_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1383_, v___x_1384_, v___x_1388_, v___f_1381_);
return v___x_1389_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_raceAll___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1365_ = stack[0].m_obj;
lean_object* v_x_1366_ = stack[1].m_obj;
lean_object* v_res_1392_;
v_res_1392_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__2(v_a_1365_, v_x_1366_);
stack->m_obj
 = v_res_1392_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__2___boxed(lean_object* v_a_1393_, lean_object* v_x_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__2(v_a_1393_, v_x_1394_);
return v_res_1396_;
}
}
lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__3(lean_object* v_a_1397_, lean_object* v_x_1398_){
_start:
{
if (lean_obj_tag(v_x_1398_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1408_; 
v_a_1400_ = lean_ctor_get(v_x_1398_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_x_1398_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1402_ = v_x_1398_;
v_isShared_1403_ = v_isSharedCheck_1408_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v_x_1398_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1408_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
lean_object* v___x_1406_; 
v___x_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
return v___x_1406_;
}
}
}
else
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1409_ = lean_io_promise_resolve(v_x_1398_, v_a_1397_);
v___x_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
v___x_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
return v___x_1411_;
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_raceAll___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1397_ = stack[0].m_obj;
lean_object* v_x_1398_ = stack[1].m_obj;
lean_object* v_res_1412_;
v_res_1412_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__3(v_a_1397_, v_x_1398_);
stack->m_obj
 = v_res_1412_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__3___boxed(lean_object* v_a_1413_, lean_object* v_x_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__3(v_a_1413_, v_x_1414_);
lean_dec(v_a_1413_);
return v_res_1416_;
}
}
lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__4(lean_object* v_a_1417_, lean_object* v_x_1418_){
_start:
{
if (lean_obj_tag(v_x_1418_) == 0)
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1429_; 
v_a_1420_ = lean_ctor_get(v_x_1418_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_x_1418_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1422_ = v_x_1418_;
v_isShared_1423_ = v_isSharedCheck_1429_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v_x_1418_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1429_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = lean_io_promise_resolve(v___x_1425_, v_a_1417_);
v___x_1427_ = ((lean_object*)(l_Std_Async_ContextAsync_background___redArg___lam__3___closed__1));
return v___x_1427_;
}
}
}
else
{
lean_object* v___x_1430_; 
v___x_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1430_, 0, v_x_1418_);
return v___x_1430_;
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_raceAll___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1417_ = stack[0].m_obj;
lean_object* v_x_1418_ = stack[1].m_obj;
lean_object* v_res_1431_;
v_res_1431_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__4(v_a_1417_, v_x_1418_);
stack->m_obj
 = v_res_1431_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__4___boxed(lean_object* v_a_1432_, lean_object* v_x_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__4(v_a_1432_, v_x_1433_);
lean_dec(v_a_1432_);
return v_res_1435_;
}
}
lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__5(lean_object* v_a_1436_, lean_object* v___f_1437_, lean_object* v___f_1438_){
_start:
{
lean_object* v___x_1440_; uint8_t v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1440_ = lean_unsigned_to_nat(0u);
v___x_1441_ = 0;
v___x_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1442_, 0, v_a_1436_);
v___x_1443_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1440_, v___x_1441_, v___x_1442_, v___f_1437_);
v___x_1444_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1440_, v___x_1441_, v___x_1443_, v___f_1438_);
return v___x_1444_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_raceAll___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1436_ = stack[0].m_obj;
lean_object* v___f_1437_ = stack[1].m_obj;
lean_object* v___f_1438_ = stack[2].m_obj;
lean_object* v_res_1445_;
v_res_1445_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__5(v_a_1436_, v___f_1437_, v___f_1438_);
stack->m_obj
 = v_res_1445_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__5___boxed(lean_object* v_a_1446_, lean_object* v___f_1447_, lean_object* v___f_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__5(v_a_1446_, v___f_1447_, v___f_1448_);
return v_res_1450_;
}
}
lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__6(lean_object* v___f_1451_, lean_object* v___f_1452_, lean_object* v_prio_1453_, lean_object* v_x_1454_){
_start:
{
if (lean_obj_tag(v_x_1454_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1464_; 
lean_dec(v_prio_1453_);
lean_dec_ref(v___f_1452_);
lean_dec_ref(v___f_1451_);
v_a_1456_ = lean_ctor_get(v_x_1454_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v_x_1454_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1458_ = v_x_1454_;
v_isShared_1459_ = v_isSharedCheck_1464_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v_x_1454_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1464_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_object* v___x_1462_; 
v___x_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
return v___x_1462_;
}
}
}
else
{
lean_object* v_a_1465_; lean_object* v___f_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v_a_1465_ = lean_ctor_get(v_x_1454_, 0);
lean_inc(v_a_1465_);
lean_dec_ref_known(v_x_1454_, 1);
v___f_1466_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_1466_, 0, v_a_1465_);
lean_closure_set(v___f_1466_, 1, v___f_1451_);
lean_closure_set(v___f_1466_, 2, v___f_1452_);
v___x_1467_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1467_, 0, lean_box(0));
lean_closure_set(v___x_1467_, 1, v___f_1466_);
v___x_1468_ = lean_io_as_task(v___x_1467_, v_prio_1453_);
lean_dec_ref(v___x_1468_);
v___x_1469_ = ((lean_object*)(l_Std_Async_ContextAsync_background___redArg___lam__3___closed__1));
return v___x_1469_;
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_raceAll___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1451_ = stack[0].m_obj;
lean_object* v___f_1452_ = stack[1].m_obj;
lean_object* v_prio_1453_ = stack[2].m_obj;
lean_object* v_x_1454_ = stack[3].m_obj;
lean_object* v_res_1470_;
v_res_1470_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__6(v___f_1451_, v___f_1452_, v_prio_1453_, v_x_1454_);
stack->m_obj
 = v_res_1470_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__6___boxed(lean_object* v___f_1471_, lean_object* v___f_1472_, lean_object* v_prio_1473_, lean_object* v_x_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__6(v___f_1471_, v___f_1472_, v_prio_1473_, v_x_1474_);
return v_res_1476_;
}
}
lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__7(lean_object* v_x_1477_, lean_object* v_a_1478_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_apply_2(v_x_1477_, v_a_1478_, lean_box(0));
return v___x_1480_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_raceAll___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1477_ = stack[0].m_obj;
lean_object* v_a_1478_ = stack[1].m_obj;
lean_object* v_res_1481_;
v_res_1481_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__7(v_x_1477_, v_a_1478_);
stack->m_obj
 = v_res_1481_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__7___boxed(lean_object* v_x_1482_, lean_object* v_a_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__7(v_x_1482_, v_a_1483_);
return v_res_1485_;
}
}
lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__8(lean_object* v_x_1486_, lean_object* v_prio_1487_, lean_object* v___f_1488_, lean_object* v___f_1489_, lean_object* v_x_1490_){
_start:
{
if (lean_obj_tag(v_x_1490_) == 0)
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1500_; 
lean_dec_ref(v___f_1489_);
lean_dec_ref(v___f_1488_);
lean_dec(v_prio_1487_);
lean_dec_ref(v_x_1486_);
v_a_1492_ = lean_ctor_get(v_x_1490_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_x_1490_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1494_ = v_x_1490_;
v_isShared_1495_ = v_isSharedCheck_1500_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v_x_1490_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1500_;
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
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
lean_object* v___x_1498_; 
v___x_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1497_);
return v___x_1498_;
}
}
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1517_; 
v_a_1501_ = lean_ctor_get(v_x_1490_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_x_1490_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1503_ = v_x_1490_;
v_isShared_1504_ = v_isSharedCheck_1517_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v_x_1490_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1517_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___f_1505_; lean_object* v___x_1506_; uint8_t v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1513_; 
v___f_1505_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_1505_, 0, v_x_1486_);
lean_closure_set(v___f_1505_, 1, v_a_1501_);
v___x_1506_ = lean_unsigned_to_nat(0u);
v___x_1507_ = 0;
v___x_1508_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1508_, 0, lean_box(0));
lean_closure_set(v___x_1508_, 1, v___f_1505_);
v___x_1509_ = lean_io_as_task(v___x_1508_, v_prio_1487_);
v___x_1510_ = 1;
v___x_1511_ = lean_task_bind(v___x_1509_, v___f_1488_, v___x_1506_, v___x_1510_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 0, v___x_1511_);
v___x_1513_ = v___x_1503_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
v___x_1515_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1506_, v___x_1507_, v___x_1514_, v___f_1489_);
return v___x_1515_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_raceAll___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1486_ = stack[0].m_obj;
lean_object* v_prio_1487_ = stack[1].m_obj;
lean_object* v___f_1488_ = stack[2].m_obj;
lean_object* v___f_1489_ = stack[3].m_obj;
lean_object* v_x_1490_ = stack[4].m_obj;
lean_object* v_res_1518_;
v_res_1518_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__8(v_x_1486_, v_prio_1487_, v___f_1488_, v___f_1489_, v_x_1490_);
stack->m_obj
 = v_res_1518_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__8___boxed(lean_object* v_x_1519_, lean_object* v_prio_1520_, lean_object* v___f_1521_, lean_object* v___f_1522_, lean_object* v_x_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__8(v_x_1519_, v_prio_1520_, v___f_1521_, v___f_1522_, v_x_1523_);
return v_res_1525_;
}
}
lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__9(lean_object* v_prio_1526_, lean_object* v___f_1527_, lean_object* v___f_1528_, lean_object* v_a_1529_, lean_object* v_x_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v___f_1533_; lean_object* v___x_1534_; uint8_t v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___f_1533_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_1533_, 0, v_x_1530_);
lean_closure_set(v___f_1533_, 1, v_prio_1526_);
lean_closure_set(v___f_1533_, 2, v___f_1527_);
lean_closure_set(v___f_1533_, 3, v___f_1528_);
v___x_1534_ = lean_unsigned_to_nat(0u);
v___x_1535_ = 0;
v___x_1536_ = l_Std_CancellationContext_fork(v_a_1529_);
v___x_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
v___x_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
v___x_1539_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1534_, v___x_1535_, v___x_1538_, v___f_1533_);
return v___x_1539_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_raceAll___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_prio_1526_ = stack[0].m_obj;
lean_object* v___f_1527_ = stack[1].m_obj;
lean_object* v___f_1528_ = stack[2].m_obj;
lean_object* v_a_1529_ = stack[3].m_obj;
lean_object* v_x_1530_ = stack[4].m_obj;
lean_object* v___y_1531_ = stack[5].m_obj;
lean_object* v_res_1540_;
v_res_1540_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__9(v_prio_1526_, v___f_1527_, v___f_1528_, v_a_1529_, v_x_1530_, v___y_1531_);
stack->m_obj
 = v_res_1540_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__9___boxed(lean_object* v_prio_1541_, lean_object* v___f_1542_, lean_object* v___f_1543_, lean_object* v_a_1544_, lean_object* v_x_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__9(v_prio_1541_, v___f_1542_, v___f_1543_, v_a_1544_, v_x_1545_, v___y_1546_);
lean_dec_ref(v___y_1546_);
return v_res_1548_;
}
}
lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__10(lean_object* v_a_1549_, lean_object* v___f_1550_, lean_object* v___f_1551_, lean_object* v_x_1552_){
_start:
{
if (lean_obj_tag(v_x_1552_) == 0)
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1562_; 
lean_dec_ref(v___f_1551_);
lean_dec_ref(v___f_1550_);
v_a_1554_ = lean_ctor_get(v_x_1552_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v_x_1552_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1556_ = v_x_1552_;
v_isShared_1557_ = v_isSharedCheck_1562_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v_x_1552_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1562_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
lean_object* v___x_1560_; 
v___x_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
return v___x_1560_;
}
}
}
else
{
lean_object* v___x_1563_; uint8_t v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
lean_dec_ref_known(v_x_1552_, 1);
v___x_1563_ = lean_unsigned_to_nat(0u);
v___x_1564_ = 0;
v___x_1565_ = l_IO_Promise_result_x21___redArg(v_a_1549_);
v___x_1566_ = lean_task_map(v___f_1550_, v___x_1565_, v___x_1563_, v___x_1564_);
v___x_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1566_);
v___x_1568_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1563_, v___x_1564_, v___x_1567_, v___f_1551_);
return v___x_1568_;
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_raceAll___redArg___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1549_ = stack[0].m_obj;
lean_object* v___f_1550_ = stack[1].m_obj;
lean_object* v___f_1551_ = stack[2].m_obj;
lean_object* v_x_1552_ = stack[3].m_obj;
lean_object* v_res_1569_;
v_res_1569_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__10(v_a_1549_, v___f_1550_, v___f_1551_, v_x_1552_);
stack->m_obj
 = v_res_1569_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__10___boxed(lean_object* v_a_1570_, lean_object* v___f_1571_, lean_object* v___f_1572_, lean_object* v_x_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__10(v_a_1570_, v___f_1571_, v___f_1572_, v_x_1573_);
lean_dec(v_a_1570_);
return v_res_1575_;
}
}
lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__11(lean_object* v_prio_1576_, lean_object* v___f_1577_, lean_object* v_a_1578_, lean_object* v___f_1579_, lean_object* v___f_1580_, lean_object* v_inst_1581_, lean_object* v_xs_1582_, lean_object* v_a_1583_, lean_object* v_x_1584_){
_start:
{
if (lean_obj_tag(v_x_1584_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1594_; 
lean_dec(v_xs_1582_);
lean_dec_ref(v_inst_1581_);
lean_dec_ref(v___f_1580_);
lean_dec_ref(v___f_1579_);
lean_dec_ref(v_a_1578_);
lean_dec_ref(v___f_1577_);
lean_dec(v_prio_1576_);
v_a_1586_ = lean_ctor_get(v_x_1584_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_x_1584_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1588_ = v_x_1584_;
v_isShared_1589_ = v_isSharedCheck_1594_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v_x_1584_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1594_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1592_; 
v___x_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
return v___x_1592_;
}
}
}
else
{
lean_object* v_a_1595_; lean_object* v___f_1596_; lean_object* v___f_1597_; lean_object* v___f_1598_; lean_object* v___f_1599_; lean_object* v___f_1600_; lean_object* v___x_1601_; uint8_t v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v_a_1595_ = lean_ctor_get(v_x_1584_, 0);
lean_inc_n(v_a_1595_, 3);
lean_dec_ref_known(v_x_1584_, 1);
v___f_1596_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1596_, 0, v_a_1595_);
v___f_1597_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1597_, 0, v_a_1595_);
lean_inc(v_prio_1576_);
v___f_1598_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__6___boxed), 5, 3);
lean_closure_set(v___f_1598_, 0, v___f_1596_);
lean_closure_set(v___f_1598_, 1, v___f_1597_);
lean_closure_set(v___f_1598_, 2, v_prio_1576_);
v___f_1599_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__9___boxed), 7, 4);
lean_closure_set(v___f_1599_, 0, v_prio_1576_);
lean_closure_set(v___f_1599_, 1, v___f_1577_);
lean_closure_set(v___f_1599_, 2, v___f_1598_);
lean_closure_set(v___f_1599_, 3, v_a_1578_);
v___f_1600_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__10___boxed), 5, 3);
lean_closure_set(v___f_1600_, 0, v_a_1595_);
lean_closure_set(v___f_1600_, 1, v___f_1579_);
lean_closure_set(v___f_1600_, 2, v___f_1580_);
v___x_1601_ = lean_unsigned_to_nat(0u);
v___x_1602_ = 0;
lean_inc_ref(v_a_1583_);
v___x_1603_ = lean_apply_4(v_inst_1581_, v_xs_1582_, v___f_1599_, v_a_1583_, lean_box(0));
v___x_1604_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1601_, v___x_1602_, v___x_1603_, v___f_1600_);
return v___x_1604_;
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_raceAll___redArg___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_prio_1576_ = stack[0].m_obj;
lean_object* v___f_1577_ = stack[1].m_obj;
lean_object* v_a_1578_ = stack[2].m_obj;
lean_object* v___f_1579_ = stack[3].m_obj;
lean_object* v___f_1580_ = stack[4].m_obj;
lean_object* v_inst_1581_ = stack[5].m_obj;
lean_object* v_xs_1582_ = stack[6].m_obj;
lean_object* v_a_1583_ = stack[7].m_obj;
lean_object* v_x_1584_ = stack[8].m_obj;
lean_object* v_res_1605_;
v_res_1605_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__11(v_prio_1576_, v___f_1577_, v_a_1578_, v___f_1579_, v___f_1580_, v_inst_1581_, v_xs_1582_, v_a_1583_, v_x_1584_);
stack->m_obj
 = v_res_1605_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__11___boxed(lean_object* v_prio_1606_, lean_object* v___f_1607_, lean_object* v_a_1608_, lean_object* v___f_1609_, lean_object* v___f_1610_, lean_object* v_inst_1611_, lean_object* v_xs_1612_, lean_object* v_a_1613_, lean_object* v_x_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__11(v_prio_1606_, v___f_1607_, v_a_1608_, v___f_1609_, v___f_1610_, v_inst_1611_, v_xs_1612_, v_a_1613_, v_x_1614_);
lean_dec_ref(v_a_1613_);
return v_res_1616_;
}
}
lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__12(lean_object* v_prio_1617_, lean_object* v___f_1618_, lean_object* v___f_1619_, lean_object* v_inst_1620_, lean_object* v_xs_1621_, lean_object* v_a_1622_, lean_object* v_x_1623_){
_start:
{
if (lean_obj_tag(v_x_1623_) == 0)
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1633_; 
lean_dec(v_xs_1621_);
lean_dec_ref(v_inst_1620_);
lean_dec_ref(v___f_1619_);
lean_dec_ref(v___f_1618_);
lean_dec(v_prio_1617_);
v_a_1625_ = lean_ctor_get(v_x_1623_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v_x_1623_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1627_ = v_x_1623_;
v_isShared_1628_ = v_isSharedCheck_1633_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v_x_1623_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1633_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1631_; 
v___x_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
return v___x_1631_;
}
}
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1648_; 
v_a_1634_ = lean_ctor_get(v_x_1623_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_x_1623_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1636_ = v_x_1623_;
v_isShared_1637_ = v_isSharedCheck_1648_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v_x_1623_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1648_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___f_1638_; lean_object* v___f_1639_; lean_object* v___x_1640_; uint8_t v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1644_; 
lean_inc(v_a_1634_);
v___f_1638_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1638_, 0, v_a_1634_);
lean_inc_ref(v_a_1622_);
v___f_1639_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__11___boxed), 10, 8);
lean_closure_set(v___f_1639_, 0, v_prio_1617_);
lean_closure_set(v___f_1639_, 1, v___f_1618_);
lean_closure_set(v___f_1639_, 2, v_a_1634_);
lean_closure_set(v___f_1639_, 3, v___f_1619_);
lean_closure_set(v___f_1639_, 4, v___f_1638_);
lean_closure_set(v___f_1639_, 5, v_inst_1620_);
lean_closure_set(v___f_1639_, 6, v_xs_1621_);
lean_closure_set(v___f_1639_, 7, v_a_1622_);
v___x_1640_ = lean_unsigned_to_nat(0u);
v___x_1641_ = 0;
v___x_1642_ = lean_io_promise_new();
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v___x_1642_);
v___x_1644_ = v___x_1636_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
v___x_1646_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1640_, v___x_1641_, v___x_1645_, v___f_1639_);
return v___x_1646_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_raceAll___redArg___lam__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_prio_1617_ = stack[0].m_obj;
lean_object* v___f_1618_ = stack[1].m_obj;
lean_object* v___f_1619_ = stack[2].m_obj;
lean_object* v_inst_1620_ = stack[3].m_obj;
lean_object* v_xs_1621_ = stack[4].m_obj;
lean_object* v_a_1622_ = stack[5].m_obj;
lean_object* v_x_1623_ = stack[6].m_obj;
lean_object* v_res_1649_;
v_res_1649_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__12(v_prio_1617_, v___f_1618_, v___f_1619_, v_inst_1620_, v_xs_1621_, v_a_1622_, v_x_1623_);
stack->m_obj
 = v_res_1649_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__12___boxed(lean_object* v_prio_1650_, lean_object* v___f_1651_, lean_object* v___f_1652_, lean_object* v_inst_1653_, lean_object* v_xs_1654_, lean_object* v_a_1655_, lean_object* v_x_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__12(v_prio_1650_, v___f_1651_, v___f_1652_, v_inst_1653_, v_xs_1654_, v_a_1655_, v_x_1656_);
lean_dec_ref(v_a_1655_);
return v_res_1658_;
}
}
lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__13(lean_object* v___f_1659_, lean_object* v_x_1660_){
_start:
{
if (lean_obj_tag(v_x_1660_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1670_; 
lean_dec_ref(v___f_1659_);
v_a_1662_ = lean_ctor_get(v_x_1660_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_x_1660_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1664_ = v_x_1660_;
v_isShared_1665_ = v_isSharedCheck_1670_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v_x_1660_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1670_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
lean_object* v___x_1668_; 
v___x_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
return v___x_1668_;
}
}
}
else
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1683_; 
v_a_1671_ = lean_ctor_get(v_x_1660_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v_x_1660_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1673_ = v_x_1660_;
v_isShared_1674_ = v_isSharedCheck_1683_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v_x_1660_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1683_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; uint8_t v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1675_ = lean_unsigned_to_nat(0u);
v___x_1676_ = 0;
v___x_1677_ = l_Std_CancellationContext_fork(v_a_1671_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1677_);
v___x_1679_ = v___x_1673_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
v___x_1681_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1675_, v___x_1676_, v___x_1680_, v___f_1659_);
return v___x_1681_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_raceAll___redArg___lam__13_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1659_ = stack[0].m_obj;
lean_object* v_x_1660_ = stack[1].m_obj;
lean_object* v_res_1684_;
v_res_1684_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__13(v___f_1659_, v_x_1660_);
stack->m_obj
 = v_res_1684_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__13___boxed(lean_object* v___f_1685_, lean_object* v_x_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__13(v___f_1685_, v_x_1686_);
return v_res_1688_;
}
}
lean_object* l_Std_Async_ContextAsync_raceAll___redArg(lean_object* v_inst_1690_, lean_object* v_xs_1691_, lean_object* v_prio_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v___f_1695_; lean_object* v___f_1696_; lean_object* v___f_1697_; lean_object* v___f_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___f_1695_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_1696_ = ((lean_object*)(l_Std_Async_ContextAsync_raceAll___redArg___closed__0));
lean_inc_ref_n(v_a_1693_, 2);
v___f_1697_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__12___boxed), 8, 6);
lean_closure_set(v___f_1697_, 0, v_prio_1692_);
lean_closure_set(v___f_1697_, 1, v___f_1695_);
lean_closure_set(v___f_1697_, 2, v___f_1696_);
lean_closure_set(v___f_1697_, 3, v_inst_1690_);
lean_closure_set(v___f_1697_, 4, v_xs_1691_);
lean_closure_set(v___f_1697_, 5, v_a_1693_);
v___f_1698_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__13___boxed), 3, 1);
lean_closure_set(v___f_1698_, 0, v___f_1697_);
v___x_1699_ = lean_unsigned_to_nat(0u);
v___x_1700_ = 0;
v___x_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1701_, 0, v_a_1693_);
v___x_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1701_);
v___x_1703_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1699_, v___x_1700_, v___x_1702_, v___f_1698_);
return v___x_1703_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_raceAll___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1690_ = stack[0].m_obj;
lean_object* v_xs_1691_ = stack[1].m_obj;
lean_object* v_prio_1692_ = stack[2].m_obj;
lean_object* v_a_1693_ = stack[3].m_obj;
lean_object* v_res_1704_;
v_res_1704_ = l_Std_Async_ContextAsync_raceAll___redArg(v_inst_1690_, v_xs_1691_, v_prio_1692_, v_a_1693_);
stack->m_obj
 = v_res_1704_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___boxed(lean_object* v_inst_1705_, lean_object* v_xs_1706_, lean_object* v_prio_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Std_Async_ContextAsync_raceAll___redArg(v_inst_1705_, v_xs_1706_, v_prio_1707_, v_a_1708_);
lean_dec_ref(v_a_1708_);
return v_res_1710_;
}
}
lean_object* l_Std_Async_ContextAsync_raceAll(lean_object* v_c_1711_, lean_object* v_00_u03b1_1712_, lean_object* v_inst_1713_, lean_object* v_xs_1714_, lean_object* v_prio_1715_, lean_object* v_a_1716_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Std_Async_ContextAsync_raceAll___redArg(v_inst_1713_, v_xs_1714_, v_prio_1715_, v_a_1716_);
return v___x_1718_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_raceAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1713_ = stack[2].m_obj;
lean_object* v_xs_1714_ = stack[3].m_obj;
lean_object* v_prio_1715_ = stack[4].m_obj;
lean_object* v_a_1716_ = stack[5].m_obj;
lean_object* v_res_1719_;
v_res_1719_ = l_Std_Async_ContextAsync_raceAll(lean_box(0), lean_box(0), v_inst_1713_, v_xs_1714_, v_prio_1715_, v_a_1716_);
stack->m_obj
 = v_res_1719_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___boxed(lean_object* v_c_1720_, lean_object* v_00_u03b1_1721_, lean_object* v_inst_1722_, lean_object* v_xs_1723_, lean_object* v_prio_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Std_Async_ContextAsync_raceAll(v_c_1720_, v_00_u03b1_1721_, v_inst_1722_, v_xs_1723_, v_prio_1724_, v_a_1725_);
lean_dec_ref(v_a_1725_);
return v_res_1727_;
}
}
lean_object* l_Std_Async_ContextAsync_async___redArg___lam__3(lean_object* v___f_1728_, lean_object* v___x_1729_, lean_object* v___f_1730_){
_start:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; uint8_t v___x_1734_; lean_object* v___x_1735_; lean_object* v___y_1737_; 
v___x_1732_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_1732_, 0, lean_box(0));
lean_closure_set(v___x_1732_, 1, lean_box(0));
lean_closure_set(v___x_1732_, 2, lean_box(0));
lean_closure_set(v___x_1732_, 3, v___f_1728_);
v___x_1733_ = lean_unsigned_to_nat(0u);
v___x_1734_ = 0;
v___x_1735_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_1729_, v___f_1730_, v___x_1733_, v___x_1734_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1739_; 
lean_dec_ref(v___x_1732_);
v_a_1739_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1739_);
lean_dec_ref_known(v___x_1735_, 1);
if (lean_obj_tag(v_a_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
v_a_1740_ = lean_ctor_get(v_a_1739_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v_a_1739_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v_a_1739_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v_a_1739_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
v___y_1737_ = v___x_1745_;
goto v___jp_1736_;
}
}
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1756_; 
v_a_1748_ = lean_ctor_get(v_a_1739_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v_a_1739_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1750_ = v_a_1739_;
v_isShared_1751_ = v_isSharedCheck_1756_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v_a_1739_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1756_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v_fst_1752_; lean_object* v___x_1754_; 
v_fst_1752_ = lean_ctor_get(v_a_1748_, 0);
lean_inc(v_fst_1752_);
lean_dec(v_a_1748_);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 0, v_fst_1752_);
v___x_1754_ = v___x_1750_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_fst_1752_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
v___y_1737_ = v___x_1754_;
goto v___jp_1736_;
}
}
}
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1765_; 
v_a_1757_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1759_ = v___x_1735_;
v_isShared_1760_ = v_isSharedCheck_1765_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1735_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1765_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1761_; lean_object* v___x_1763_; 
v___x_1761_ = lean_task_map(v___x_1732_, v_a_1757_, v___x_1733_, v___x_1734_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v___x_1761_);
v___x_1763_ = v___x_1759_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1761_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
v___jp_1736_:
{
lean_object* v___x_1738_; 
v___x_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1738_, 0, v___y_1737_);
return v___x_1738_;
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_async___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1728_ = stack[0].m_obj;
lean_object* v___x_1729_ = stack[1].m_obj;
lean_object* v___f_1730_ = stack[2].m_obj;
lean_object* v_res_1766_;
v_res_1766_ = l_Std_Async_ContextAsync_async___redArg___lam__3(v___f_1728_, v___x_1729_, v___f_1730_);
stack->m_obj
 = v_res_1766_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg___lam__3___boxed(lean_object* v___f_1767_, lean_object* v___x_1768_, lean_object* v___f_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Std_Async_ContextAsync_async___redArg___lam__3(v___f_1767_, v___x_1768_, v___f_1769_);
return v_res_1771_;
}
}
lean_object* l_Std_Async_ContextAsync_async___redArg___lam__0(lean_object* v_x_1772_, lean_object* v___f_1773_, lean_object* v_prio_1774_, lean_object* v___f_1775_, lean_object* v_x_1776_){
_start:
{
if (lean_obj_tag(v_x_1776_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1786_; 
lean_dec_ref(v___f_1775_);
lean_dec(v_prio_1774_);
lean_dec(v___f_1773_);
lean_dec_ref(v_x_1772_);
v_a_1778_ = lean_ctor_get(v_x_1776_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_x_1776_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1780_ = v_x_1776_;
v_isShared_1781_ = v_isSharedCheck_1786_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v_x_1776_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1786_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
lean_object* v___x_1784_; 
v___x_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
return v___x_1784_;
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1804_; 
v_a_1787_ = lean_ctor_get(v_x_1776_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v_x_1776_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1789_ = v_x_1776_;
v_isShared_1790_ = v_isSharedCheck_1804_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v_x_1776_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1804_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___f_1793_; lean_object* v___f_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; uint8_t v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1801_; 
lean_inc(v_a_1787_);
v___x_1791_ = lean_apply_1(v_x_1772_, v_a_1787_);
v___x_1792_ = lean_box(2);
v___f_1793_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_run___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1793_, 0, v_a_1787_);
lean_closure_set(v___f_1793_, 1, v___x_1792_);
v___f_1794_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_async___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_1794_, 0, v___f_1773_);
lean_closure_set(v___f_1794_, 1, v___x_1791_);
lean_closure_set(v___f_1794_, 2, v___f_1793_);
v___x_1795_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1795_, 0, lean_box(0));
lean_closure_set(v___x_1795_, 1, v___f_1794_);
v___x_1796_ = lean_io_as_task(v___x_1795_, v_prio_1774_);
v___x_1797_ = lean_unsigned_to_nat(0u);
v___x_1798_ = 1;
v___x_1799_ = lean_task_bind(v___x_1796_, v___f_1775_, v___x_1797_, v___x_1798_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1799_);
v___x_1801_ = v___x_1789_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1799_);
v___x_1801_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
lean_object* v___x_1802_; 
v___x_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1801_);
return v___x_1802_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_async___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1772_ = stack[0].m_obj;
lean_object* v___f_1773_ = stack[1].m_obj;
lean_object* v_prio_1774_ = stack[2].m_obj;
lean_object* v___f_1775_ = stack[3].m_obj;
lean_object* v_x_1776_ = stack[4].m_obj;
lean_object* v_res_1805_;
v_res_1805_ = l_Std_Async_ContextAsync_async___redArg___lam__0(v_x_1772_, v___f_1773_, v_prio_1774_, v___f_1775_, v_x_1776_);
stack->m_obj
 = v_res_1805_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg___lam__0___boxed(lean_object* v_x_1806_, lean_object* v___f_1807_, lean_object* v_prio_1808_, lean_object* v___f_1809_, lean_object* v_x_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Std_Async_ContextAsync_async___redArg___lam__0(v_x_1806_, v___f_1807_, v_prio_1808_, v___f_1809_, v_x_1810_);
return v_res_1812_;
}
}
lean_object* l_Std_Async_ContextAsync_async___redArg(lean_object* v_x_1813_, lean_object* v_prio_1814_, lean_object* v_ctx_1815_){
_start:
{
lean_object* v___f_1817_; lean_object* v___f_1818_; lean_object* v___f_1819_; lean_object* v___x_1820_; uint8_t v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___f_1817_ = ((lean_object*)(l_Std_Async_ContextAsync_run___redArg___closed__0));
v___f_1818_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_1819_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_async___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1819_, 0, v_x_1813_);
lean_closure_set(v___f_1819_, 1, v___f_1817_);
lean_closure_set(v___f_1819_, 2, v_prio_1814_);
lean_closure_set(v___f_1819_, 3, v___f_1818_);
v___x_1820_ = lean_unsigned_to_nat(0u);
v___x_1821_ = 0;
lean_inc_ref(v_ctx_1815_);
v___x_1822_ = l_Std_CancellationContext_fork(v_ctx_1815_);
v___x_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
v___x_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
v___x_1825_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1820_, v___x_1821_, v___x_1824_, v___f_1819_);
return v___x_1825_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_async___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1813_ = stack[0].m_obj;
lean_object* v_prio_1814_ = stack[1].m_obj;
lean_object* v_ctx_1815_ = stack[2].m_obj;
lean_object* v_res_1826_;
v_res_1826_ = l_Std_Async_ContextAsync_async___redArg(v_x_1813_, v_prio_1814_, v_ctx_1815_);
stack->m_obj
 = v_res_1826_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg___boxed(lean_object* v_x_1827_, lean_object* v_prio_1828_, lean_object* v_ctx_1829_, lean_object* v_a_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Std_Async_ContextAsync_async___redArg(v_x_1827_, v_prio_1828_, v_ctx_1829_);
lean_dec_ref(v_ctx_1829_);
return v_res_1831_;
}
}
lean_object* l_Std_Async_ContextAsync_async(lean_object* v_00_u03b1_1832_, lean_object* v_x_1833_, lean_object* v_prio_1834_, lean_object* v_ctx_1835_){
_start:
{
lean_object* v___f_1837_; lean_object* v___f_1838_; lean_object* v___f_1839_; lean_object* v___x_1840_; uint8_t v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___f_1837_ = ((lean_object*)(l_Std_Async_ContextAsync_run___redArg___closed__0));
v___f_1838_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_1839_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_async___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1839_, 0, v_x_1833_);
lean_closure_set(v___f_1839_, 1, v___f_1837_);
lean_closure_set(v___f_1839_, 2, v_prio_1834_);
lean_closure_set(v___f_1839_, 3, v___f_1838_);
v___x_1840_ = lean_unsigned_to_nat(0u);
v___x_1841_ = 0;
lean_inc_ref(v_ctx_1835_);
v___x_1842_ = l_Std_CancellationContext_fork(v_ctx_1835_);
v___x_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
v___x_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
v___x_1845_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1840_, v___x_1841_, v___x_1844_, v___f_1839_);
return v___x_1845_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_async_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1833_ = stack[1].m_obj;
lean_object* v_prio_1834_ = stack[2].m_obj;
lean_object* v_ctx_1835_ = stack[3].m_obj;
lean_object* v_res_1846_;
v_res_1846_ = l_Std_Async_ContextAsync_async(lean_box(0), v_x_1833_, v_prio_1834_, v_ctx_1835_);
stack->m_obj
 = v_res_1846_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___boxed(lean_object* v_00_u03b1_1847_, lean_object* v_x_1848_, lean_object* v_prio_1849_, lean_object* v_ctx_1850_, lean_object* v_a_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Std_Async_ContextAsync_async(v_00_u03b1_1847_, v_x_1848_, v_prio_1849_, v_ctx_1850_);
lean_dec_ref(v_ctx_1850_);
return v_res_1852_;
}
}
lean_object* l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5(lean_object* v___f_1853_, lean_object* v___f_1854_, lean_object* v_00_u03b1_1855_, lean_object* v_x_1856_, lean_object* v_prio_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v___f_1860_; lean_object* v___x_1861_; uint8_t v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___f_1860_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_async___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1860_, 0, v_x_1856_);
lean_closure_set(v___f_1860_, 1, v___f_1853_);
lean_closure_set(v___f_1860_, 2, v_prio_1857_);
lean_closure_set(v___f_1860_, 3, v___f_1854_);
v___x_1861_ = lean_unsigned_to_nat(0u);
v___x_1862_ = 0;
lean_inc_ref(v___y_1858_);
v___x_1863_ = l_Std_CancellationContext_fork(v___y_1858_);
v___x_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
v___x_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1864_);
v___x_1866_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1861_, v___x_1862_, v___x_1865_, v___f_1860_);
return v___x_1866_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1853_ = stack[0].m_obj;
lean_object* v___f_1854_ = stack[1].m_obj;
lean_object* v_x_1856_ = stack[3].m_obj;
lean_object* v_prio_1857_ = stack[4].m_obj;
lean_object* v___y_1858_ = stack[5].m_obj;
lean_object* v_res_1867_;
v_res_1867_ = l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5(v___f_1853_, v___f_1854_, lean_box(0), v_x_1856_, v_prio_1857_, v___y_1858_);
stack->m_obj
 = v_res_1867_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5___boxed(lean_object* v___f_1868_, lean_object* v___f_1869_, lean_object* v_00_u03b1_1870_, lean_object* v_x_1871_, lean_object* v_prio_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5(v___f_1868_, v___f_1869_, v_00_u03b1_1870_, v_x_1871_, v_prio_1872_, v___y_1873_);
lean_dec_ref(v___y_1873_);
return v_res_1875_;
}
}
lean_object* l_Std_Async_ContextAsync_instFunctor___lam__0(lean_object* v_00_u03b1_1880_, lean_object* v_00_u03b2_1881_, lean_object* v_f_1882_, lean_object* v_x_1883_, lean_object* v_ctx_1884_){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; uint8_t v___x_1888_; lean_object* v___x_1889_; lean_object* v___y_1891_; 
lean_inc(v_f_1882_);
v___x_1886_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_1886_, 0, lean_box(0));
lean_closure_set(v___x_1886_, 1, lean_box(0));
lean_closure_set(v___x_1886_, 2, lean_box(0));
lean_closure_set(v___x_1886_, 3, v_f_1882_);
v___x_1887_ = lean_unsigned_to_nat(0u);
v___x_1888_ = 0;
v___x_1889_ = lean_apply_2(v_x_1883_, v_ctx_1884_, lean_box(0));
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1893_; 
lean_dec_ref(v___x_1886_);
v_a_1893_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_a_1893_);
lean_dec_ref_known(v___x_1889_, 1);
if (lean_obj_tag(v_a_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_dec(v_f_1882_);
v_a_1894_ = lean_ctor_get(v_a_1893_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_a_1893_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v_a_1893_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v_a_1893_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
v___y_1891_ = v___x_1899_;
goto v___jp_1890_;
}
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1910_; 
v_a_1902_ = lean_ctor_get(v_a_1893_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v_a_1893_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1904_ = v_a_1893_;
v_isShared_1905_ = v_isSharedCheck_1910_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v_a_1893_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1910_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1906_; lean_object* v___x_1908_; 
v___x_1906_ = lean_apply_1(v_f_1882_, v_a_1902_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v___x_1906_);
v___x_1908_ = v___x_1904_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1906_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
v___y_1891_ = v___x_1908_;
goto v___jp_1890_;
}
}
}
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1919_; 
lean_dec(v_f_1882_);
v_a_1911_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1913_ = v___x_1889_;
v_isShared_1914_ = v_isSharedCheck_1919_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1889_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1919_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1915_; lean_object* v___x_1917_; 
v___x_1915_ = lean_task_map(v___x_1886_, v_a_1911_, v___x_1887_, v___x_1888_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 0, v___x_1915_);
v___x_1917_ = v___x_1913_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1915_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
v___jp_1890_:
{
lean_object* v___x_1892_; 
v___x_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1892_, 0, v___y_1891_);
return v___x_1892_;
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_instFunctor___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1882_ = stack[2].m_obj;
lean_object* v_x_1883_ = stack[3].m_obj;
lean_object* v_ctx_1884_ = stack[4].m_obj;
lean_object* v_res_1920_;
v_res_1920_ = l_Std_Async_ContextAsync_instFunctor___lam__0(lean_box(0), lean_box(0), v_f_1882_, v_x_1883_, v_ctx_1884_);
stack->m_obj
 = v_res_1920_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instFunctor___lam__0___boxed(lean_object* v_00_u03b1_1921_, lean_object* v_00_u03b2_1922_, lean_object* v_f_1923_, lean_object* v_x_1924_, lean_object* v_ctx_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Std_Async_ContextAsync_instFunctor___lam__0(v_00_u03b1_1921_, v_00_u03b2_1922_, v_f_1923_, v_x_1924_, v_ctx_1925_);
return v_res_1927_;
}
}
lean_object* l_Std_Async_ContextAsync_instFunctor___lam__1(lean_object* v___f_1928_, lean_object* v_00_u03b1_1929_, lean_object* v_00_u03b2_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_1935_, 0, lean_box(0));
lean_closure_set(v___x_1935_, 1, lean_box(0));
lean_closure_set(v___x_1935_, 2, v___y_1931_);
lean_inc_ref(v___y_1933_);
v___x_1936_ = lean_apply_6(v___f_1928_, lean_box(0), lean_box(0), v___x_1935_, v___y_1932_, v___y_1933_, lean_box(0));
return v___x_1936_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_instFunctor___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1928_ = stack[0].m_obj;
lean_object* v___y_1931_ = stack[3].m_obj;
lean_object* v___y_1932_ = stack[4].m_obj;
lean_object* v___y_1933_ = stack[5].m_obj;
lean_object* v_res_1937_;
v_res_1937_ = l_Std_Async_ContextAsync_instFunctor___lam__1(v___f_1928_, lean_box(0), lean_box(0), v___y_1931_, v___y_1932_, v___y_1933_);
stack->m_obj
 = v_res_1937_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instFunctor___lam__1___boxed(lean_object* v___f_1938_, lean_object* v_00_u03b1_1939_, lean_object* v_00_u03b2_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Std_Async_ContextAsync_instFunctor___lam__1(v___f_1938_, v_00_u03b1_1939_, v_00_u03b2_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
lean_dec_ref(v___y_1943_);
return v_res_1945_;
}
}
lean_object* l_Std_Async_ContextAsync_instMonad___lam__0(lean_object* v_00_u03b1_1953_, lean_object* v_a_1954_, lean_object* v_x_1955_){
_start:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1957_, 0, v_a_1954_);
v___x_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_instMonad___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1954_ = stack[1].m_obj;
lean_object* v_x_1955_ = stack[2].m_obj;
lean_object* v_res_1959_;
v_res_1959_ = l_Std_Async_ContextAsync_instMonad___lam__0(lean_box(0), v_a_1954_, v_x_1955_);
stack->m_obj
 = v_res_1959_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__0___boxed(lean_object* v_00_u03b1_1960_, lean_object* v_a_1961_, lean_object* v_x_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Std_Async_ContextAsync_instMonad___lam__0(v_00_u03b1_1960_, v_a_1961_, v_x_1962_);
lean_dec_ref(v_x_1962_);
return v_res_1964_;
}
}
lean_object* l_Std_Async_ContextAsync_instMonad___lam__1(lean_object* v_f_1965_, lean_object* v_ctx_1966_, lean_object* v_x_1967_){
_start:
{
if (lean_obj_tag(v_x_1967_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1977_; 
lean_dec_ref(v_ctx_1966_);
lean_dec_ref(v_f_1965_);
v_a_1969_ = lean_ctor_get(v_x_1967_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_x_1967_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1971_ = v_x_1967_;
v_isShared_1972_ = v_isSharedCheck_1977_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v_x_1967_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1977_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
lean_object* v___x_1975_; 
v___x_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
return v___x_1975_;
}
}
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1979_; 
v_a_1978_ = lean_ctor_get(v_x_1967_, 0);
lean_inc(v_a_1978_);
lean_dec_ref_known(v_x_1967_, 1);
v___x_1979_ = lean_apply_3(v_f_1965_, v_a_1978_, v_ctx_1966_, lean_box(0));
return v___x_1979_;
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_instMonad___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1965_ = stack[0].m_obj;
lean_object* v_ctx_1966_ = stack[1].m_obj;
lean_object* v_x_1967_ = stack[2].m_obj;
lean_object* v_res_1980_;
v_res_1980_ = l_Std_Async_ContextAsync_instMonad___lam__1(v_f_1965_, v_ctx_1966_, v_x_1967_);
stack->m_obj
 = v_res_1980_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__1___boxed(lean_object* v_f_1981_, lean_object* v_ctx_1982_, lean_object* v_x_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Std_Async_ContextAsync_instMonad___lam__1(v_f_1981_, v_ctx_1982_, v_x_1983_);
return v_res_1985_;
}
}
lean_object* l_Std_Async_ContextAsync_instMonad___lam__2(lean_object* v_00_u03b1_1986_, lean_object* v_00_u03b2_1987_, lean_object* v_x_1988_, lean_object* v_f_1989_, lean_object* v_ctx_1990_){
_start:
{
lean_object* v___f_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
lean_inc_ref(v_ctx_1990_);
v___f_1992_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_instMonad___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1992_, 0, v_f_1989_);
lean_closure_set(v___f_1992_, 1, v_ctx_1990_);
v___x_1993_ = lean_unsigned_to_nat(0u);
v___x_1994_ = 0;
v___x_1995_ = lean_apply_2(v_x_1988_, v_ctx_1990_, lean_box(0));
v___x_1996_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1993_, v___x_1994_, v___x_1995_, v___f_1992_);
return v___x_1996_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_instMonad___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1988_ = stack[2].m_obj;
lean_object* v_f_1989_ = stack[3].m_obj;
lean_object* v_ctx_1990_ = stack[4].m_obj;
lean_object* v_res_1997_;
v_res_1997_ = l_Std_Async_ContextAsync_instMonad___lam__2(lean_box(0), lean_box(0), v_x_1988_, v_f_1989_, v_ctx_1990_);
stack->m_obj
 = v_res_1997_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__2___boxed(lean_object* v_00_u03b1_1998_, lean_object* v_00_u03b2_1999_, lean_object* v_x_2000_, lean_object* v_f_2001_, lean_object* v_ctx_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_Std_Async_ContextAsync_instMonad___lam__2(v_00_u03b1_1998_, v_00_u03b2_1999_, v_x_2000_, v_f_2001_, v_ctx_2002_);
return v_res_2004_;
}
}
static lean_object* _init_l_Std_Async_ContextAsync_instMonad(void){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v_toApplicative_2009_; lean_object* v_toSeq_2010_; lean_object* v_toSeqLeft_2011_; lean_object* v_toSeqRight_2012_; lean_object* v___f_2013_; lean_object* v___f_2014_; lean_object* v___f_2015_; lean_object* v___f_2016_; lean_object* v___f_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2007_ = ((lean_object*)(l_Std_Async_ContextAsync_instFunctor));
v___x_2008_ = lean_obj_once(&l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2, &l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2_once, _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2);
v_toApplicative_2009_ = lean_ctor_get(v___x_2008_, 0);
v_toSeq_2010_ = lean_ctor_get(v_toApplicative_2009_, 2);
v_toSeqLeft_2011_ = lean_ctor_get(v_toApplicative_2009_, 3);
v_toSeqRight_2012_ = lean_ctor_get(v_toApplicative_2009_, 4);
v___f_2013_ = ((lean_object*)(l_Std_Async_ContextAsync_instMonad___closed__0));
v___f_2014_ = ((lean_object*)(l_Std_Async_ContextAsync_instMonad___closed__1));
lean_inc(v_toSeqRight_2012_);
v___f_2015_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2015_, 0, v_toSeqRight_2012_);
lean_inc(v_toSeqLeft_2011_);
v___f_2016_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2016_, 0, v_toSeqLeft_2011_);
lean_inc(v_toSeq_2010_);
v___f_2017_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2017_, 0, v_toSeq_2010_);
v___x_2018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2007_);
lean_ctor_set(v___x_2018_, 1, v___f_2013_);
lean_ctor_set(v___x_2018_, 2, v___f_2017_);
lean_ctor_set(v___x_2018_, 3, v___f_2016_);
lean_ctor_set(v___x_2018_, 4, v___f_2015_);
v___x_2019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
lean_ctor_set(v___x_2019_, 1, v___f_2014_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___lam__0(lean_object* v_a_2020_){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2021_, 0, v_a_2020_);
return v___x_2021_;
}
}
lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___lam__1(lean_object* v___f_2022_, lean_object* v_x_2023_){
_start:
{
if (lean_obj_tag(v_x_2023_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2033_; 
lean_dec_ref(v___f_2022_);
v_a_2025_ = lean_ctor_get(v_x_2023_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v_x_2023_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2027_ = v_x_2023_;
v_isShared_2028_ = v_isSharedCheck_2033_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v_x_2023_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2033_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
lean_object* v___x_2031_; 
v___x_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2030_);
return v___x_2031_;
}
}
}
else
{
lean_object* v_a_2034_; 
v_a_2034_ = lean_ctor_get(v_x_2023_, 0);
lean_inc(v_a_2034_);
lean_dec_ref_known(v_x_2023_, 1);
if (lean_obj_tag(v_a_2034_) == 0)
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2043_; 
lean_dec_ref(v___f_2022_);
v_a_2035_ = lean_ctor_get(v_a_2034_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_a_2034_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2037_ = v_a_2034_;
v_isShared_2038_ = v_isSharedCheck_2043_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v_a_2034_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2043_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2041_; 
v___x_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2040_);
return v___x_2041_;
}
}
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v_a_2044_ = lean_ctor_get(v_a_2034_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v_a_2034_, 1);
v___x_2045_ = lean_unsigned_to_nat(0u);
v___x_2046_ = 0;
v___x_2047_ = lean_task_map(v___f_2022_, v_a_2044_, v___x_2045_, v___x_2046_);
v___x_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2047_);
return v___x_2048_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_instMonadLiftIO___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2022_ = stack[0].m_obj;
lean_object* v_x_2023_ = stack[1].m_obj;
lean_object* v_res_2049_;
v_res_2049_ = l_Std_Async_ContextAsync_instMonadLiftIO___lam__1(v___f_2022_, v_x_2023_);
stack->m_obj
 = v_res_2049_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___lam__1___boxed(lean_object* v___f_2050_, lean_object* v_x_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Std_Async_ContextAsync_instMonadLiftIO___lam__1(v___f_2050_, v_x_2051_);
return v_res_2053_;
}
}
lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___lam__2(lean_object* v___f_2054_, lean_object* v_00_u03b1_2055_, lean_object* v_x_2056_, lean_object* v_x_2057_){
_start:
{
lean_object* v___x_2059_; uint8_t v___x_2060_; lean_object* v_val_2062_; lean_object* v___x_2066_; 
v___x_2059_ = lean_unsigned_to_nat(0u);
v___x_2060_ = 0;
v___x_2066_ = lean_apply_1(v_x_2056_, lean_box(0));
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2075_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2069_ = v___x_2066_;
v_isShared_2070_ = v_isSharedCheck_2075_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2075_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2071_; lean_object* v___x_2073_; 
v___x_2071_ = lean_task_pure(v_a_2067_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set_tag(v___x_2069_, 1);
lean_ctor_set(v___x_2069_, 0, v___x_2071_);
v___x_2073_ = v___x_2069_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
v_val_2062_ = v___x_2073_;
goto v___jp_2061_;
}
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
v_a_2076_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2066_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2066_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
lean_ctor_set_tag(v___x_2078_, 0);
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
v_val_2062_ = v___x_2081_;
goto v___jp_2061_;
}
}
}
v___jp_2061_:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2063_, 0, v_val_2062_);
v___x_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
v___x_2065_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2059_, v___x_2060_, v___x_2064_, v___f_2054_);
return v___x_2065_;
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_instMonadLiftIO___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2054_ = stack[0].m_obj;
lean_object* v_x_2056_ = stack[2].m_obj;
lean_object* v_x_2057_ = stack[3].m_obj;
lean_object* v_res_2084_;
v_res_2084_ = l_Std_Async_ContextAsync_instMonadLiftIO___lam__2(v___f_2054_, lean_box(0), v_x_2056_, v_x_2057_);
stack->m_obj
 = v_res_2084_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___lam__2___boxed(lean_object* v___f_2085_, lean_object* v_00_u03b1_2086_, lean_object* v_x_2087_, lean_object* v_x_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Std_Async_ContextAsync_instMonadLiftIO___lam__2(v___f_2085_, v_00_u03b1_2086_, v_x_2087_, v_x_2088_);
lean_dec_ref(v_x_2088_);
return v_res_2090_;
}
}
lean_object* l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0(lean_object* v_00_u03b1_2097_, lean_object* v_x_2098_, lean_object* v_x_2099_){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2101_ = lean_apply_1(v_x_2098_, lean_box(0));
v___x_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
v___x_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
return v___x_2103_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2098_ = stack[1].m_obj;
lean_object* v_x_2099_ = stack[2].m_obj;
lean_object* v_res_2104_;
v_res_2104_ = l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0(lean_box(0), v_x_2098_, v_x_2099_);
stack->m_obj
 = v_res_2104_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0___boxed(lean_object* v_00_u03b1_2105_, lean_object* v_x_2106_, lean_object* v_x_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0(v_00_u03b1_2105_, v_x_2106_, v_x_2107_);
lean_dec_ref(v_x_2107_);
return v_res_2109_;
}
}
lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__0(lean_object* v_00_u03b1_2112_, lean_object* v_e_2113_, lean_object* v_x_2114_){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2116_, 0, v_e_2113_);
v___x_2117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
return v___x_2117_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_instMonadExceptError___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2113_ = stack[1].m_obj;
lean_object* v_x_2114_ = stack[2].m_obj;
lean_object* v_res_2118_;
v_res_2118_ = l_Std_Async_ContextAsync_instMonadExceptError___lam__0(lean_box(0), v_e_2113_, v_x_2114_);
stack->m_obj
 = v_res_2118_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__0___boxed(lean_object* v_00_u03b1_2119_, lean_object* v_e_2120_, lean_object* v_x_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Std_Async_ContextAsync_instMonadExceptError___lam__0(v_00_u03b1_2119_, v_e_2120_, v_x_2121_);
lean_dec_ref(v_x_2121_);
return v_res_2123_;
}
}
lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__1(lean_object* v_h_2124_, lean_object* v_ctx_2125_, lean_object* v_x_2126_){
_start:
{
if (lean_obj_tag(v_x_2126_) == 0)
{
lean_object* v_a_2128_; lean_object* v___x_2129_; 
v_a_2128_ = lean_ctor_get(v_x_2126_, 0);
lean_inc(v_a_2128_);
lean_dec_ref_known(v_x_2126_, 1);
v___x_2129_ = lean_apply_3(v_h_2124_, v_a_2128_, v_ctx_2125_, lean_box(0));
return v___x_2129_;
}
else
{
lean_object* v___x_2130_; 
lean_dec_ref(v_ctx_2125_);
lean_dec_ref(v_h_2124_);
v___x_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2130_, 0, v_x_2126_);
return v___x_2130_;
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_instMonadExceptError___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_2124_ = stack[0].m_obj;
lean_object* v_ctx_2125_ = stack[1].m_obj;
lean_object* v_x_2126_ = stack[2].m_obj;
lean_object* v_res_2131_;
v_res_2131_ = l_Std_Async_ContextAsync_instMonadExceptError___lam__1(v_h_2124_, v_ctx_2125_, v_x_2126_);
stack->m_obj
 = v_res_2131_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__1___boxed(lean_object* v_h_2132_, lean_object* v_ctx_2133_, lean_object* v_x_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Std_Async_ContextAsync_instMonadExceptError___lam__1(v_h_2132_, v_ctx_2133_, v_x_2134_);
return v_res_2136_;
}
}
lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__2(lean_object* v_00_u03b1_2137_, lean_object* v_x_2138_, lean_object* v_h_2139_, lean_object* v_ctx_2140_){
_start:
{
lean_object* v___f_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
lean_inc_ref(v_ctx_2140_);
v___f_2142_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_instMonadExceptError___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2142_, 0, v_h_2139_);
lean_closure_set(v___f_2142_, 1, v_ctx_2140_);
v___x_2143_ = lean_unsigned_to_nat(0u);
v___x_2144_ = 0;
v___x_2145_ = lean_apply_2(v_x_2138_, v_ctx_2140_, lean_box(0));
v___x_2146_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2143_, v___x_2144_, v___x_2145_, v___f_2142_);
return v___x_2146_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_instMonadExceptError___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2138_ = stack[1].m_obj;
lean_object* v_h_2139_ = stack[2].m_obj;
lean_object* v_ctx_2140_ = stack[3].m_obj;
lean_object* v_res_2147_;
v_res_2147_ = l_Std_Async_ContextAsync_instMonadExceptError___lam__2(lean_box(0), v_x_2138_, v_h_2139_, v_ctx_2140_);
stack->m_obj
 = v_res_2147_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__2___boxed(lean_object* v_00_u03b1_2148_, lean_object* v_x_2149_, lean_object* v_h_2150_, lean_object* v_ctx_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Std_Async_ContextAsync_instMonadExceptError___lam__2(v_00_u03b1_2148_, v_x_2149_, v_h_2150_, v_ctx_2151_);
return v_res_2153_;
}
}
lean_object* l_Std_Async_ContextAsync_instMonadFinally___lam__0(lean_object* v_f_2160_, lean_object* v_ctx_2161_, lean_object* v_opt_2162_){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = lean_apply_3(v_f_2160_, v_opt_2162_, v_ctx_2161_, lean_box(0));
return v___x_2164_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_instMonadFinally___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2160_ = stack[0].m_obj;
lean_object* v_ctx_2161_ = stack[1].m_obj;
lean_object* v_opt_2162_ = stack[2].m_obj;
lean_object* v_res_2165_;
v_res_2165_ = l_Std_Async_ContextAsync_instMonadFinally___lam__0(v_f_2160_, v_ctx_2161_, v_opt_2162_);
stack->m_obj
 = v_res_2165_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadFinally___lam__0___boxed(lean_object* v_f_2166_, lean_object* v_ctx_2167_, lean_object* v_opt_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_Std_Async_ContextAsync_instMonadFinally___lam__0(v_f_2166_, v_ctx_2167_, v_opt_2168_);
return v_res_2170_;
}
}
lean_object* l_Std_Async_ContextAsync_instMonadFinally___lam__1(lean_object* v_00_u03b1_2171_, lean_object* v_00_u03b2_2172_, lean_object* v_x_2173_, lean_object* v_f_2174_, lean_object* v_ctx_2175_){
_start:
{
lean_object* v___f_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; lean_object* v___x_2181_; 
lean_inc_ref(v_ctx_2175_);
v___f_2177_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_instMonadFinally___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2177_, 0, v_f_2174_);
lean_closure_set(v___f_2177_, 1, v_ctx_2175_);
v___x_2178_ = lean_apply_1(v_x_2173_, v_ctx_2175_);
v___x_2179_ = lean_unsigned_to_nat(0u);
v___x_2180_ = 0;
v___x_2181_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_2178_, v___f_2177_, v___x_2179_, v___x_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_instMonadFinally___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2173_ = stack[2].m_obj;
lean_object* v_f_2174_ = stack[3].m_obj;
lean_object* v_ctx_2175_ = stack[4].m_obj;
lean_object* v_res_2182_;
v_res_2182_ = l_Std_Async_ContextAsync_instMonadFinally___lam__1(lean_box(0), lean_box(0), v_x_2173_, v_f_2174_, v_ctx_2175_);
stack->m_obj
 = v_res_2182_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadFinally___lam__1___boxed(lean_object* v_00_u03b1_2183_, lean_object* v_00_u03b2_2184_, lean_object* v_x_2185_, lean_object* v_f_2186_, lean_object* v_ctx_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Std_Async_ContextAsync_instMonadFinally___lam__1(v_00_u03b1_2183_, v_00_u03b2_2184_, v_x_2185_, v_f_2186_, v_ctx_2187_);
return v_res_2189_;
}
}
lean_object* l_Std_Async_ContextAsync_instInhabited___redArg___lam__0(lean_object* v_x_2199_){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = ((lean_object*)(l_Std_Async_ContextAsync_instInhabited___redArg___lam__0___closed__3));
return v___x_2201_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_instInhabited___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2199_ = stack[0].m_obj;
lean_object* v_res_2202_;
v_res_2202_ = l_Std_Async_ContextAsync_instInhabited___redArg___lam__0(v_x_2199_);
stack->m_obj
 = v_res_2202_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited___redArg___lam__0___boxed(lean_object* v_x_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l_Std_Async_ContextAsync_instInhabited___redArg___lam__0(v_x_2203_);
lean_dec_ref(v_x_2203_);
return v_res_2205_;
}
}
lean_object* l_Std_Async_ContextAsync_instInhabited___redArg(){
_start:
{
lean_object* v___f_2208_; 
v___f_2208_ = ((lean_object*)(l_Std_Async_ContextAsync_instInhabited___redArg___closed__0));
return v___f_2208_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2209_;
v_res_2209_ = l_Std_Async_ContextAsync_instInhabited___redArg();
stack->m_obj
 = v_res_2209_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited___redArg___boxed(lean_object* v___dummy_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Std_Async_ContextAsync_instInhabited___redArg();
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited(lean_object* v_00_u03b1_2212_, lean_object* v_inst_2213_){
_start:
{
lean_object* v___f_2214_; 
v___f_2214_ = ((lean_object*)(l_Std_Async_ContextAsync_instInhabited___redArg___closed__0));
return v___f_2214_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited___boxed(lean_object* v_00_u03b1_2215_, lean_object* v_inst_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Std_Async_ContextAsync_instInhabited(v_00_u03b1_2215_, v_inst_2216_);
lean_dec(v_inst_2216_);
return v_res_2217_;
}
}
lean_object* l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0(lean_object* v_00_u03b1_2218_, lean_object* v_t_2219_, lean_object* v_x_2220_){
_start:
{
lean_object* v___x_2222_; 
v___x_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2222_, 0, v_t_2219_);
return v___x_2222_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2219_ = stack[1].m_obj;
lean_object* v_x_2220_ = stack[2].m_obj;
lean_object* v_res_2223_;
v_res_2223_ = l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0(lean_box(0), v_t_2219_, v_x_2220_);
stack->m_obj
 = v_res_2223_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0___boxed(lean_object* v_00_u03b1_2224_, lean_object* v_t_2225_, lean_object* v_x_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0(v_00_u03b1_2224_, v_t_2225_, v_x_2226_);
lean_dec_ref(v_x_2226_);
return v_res_2228_;
}
}
lean_object* l_Std_Async_ContextAsync_forIn___redArg___lam__0(lean_object* v_f_2231_, lean_object* v_ctx_2232_, lean_object* v_u_2233_, lean_object* v_b_2234_){
_start:
{
lean_object* v___x_2236_; 
lean_inc_ref(v_ctx_2232_);
v___x_2236_ = lean_apply_4(v_f_2231_, v_u_2233_, v_b_2234_, v_ctx_2232_, lean_box(0));
return v___x_2236_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_forIn___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2231_ = stack[0].m_obj;
lean_object* v_ctx_2232_ = stack[1].m_obj;
lean_object* v_u_2233_ = stack[2].m_obj;
lean_object* v_b_2234_ = stack[3].m_obj;
lean_object* v_res_2237_;
v_res_2237_ = l_Std_Async_ContextAsync_forIn___redArg___lam__0(v_f_2231_, v_ctx_2232_, v_u_2233_, v_b_2234_);
stack->m_obj
 = v_res_2237_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_forIn___redArg___lam__0___boxed(lean_object* v_f_2238_, lean_object* v_ctx_2239_, lean_object* v_u_2240_, lean_object* v_b_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Std_Async_ContextAsync_forIn___redArg___lam__0(v_f_2238_, v_ctx_2239_, v_u_2240_, v_b_2241_);
lean_dec_ref(v_ctx_2239_);
return v_res_2243_;
}
}
lean_object* l_Std_Async_ContextAsync_forIn___redArg___lam__1(lean_object* v_a_2244_, lean_object* v_x_2245_){
_start:
{
if (lean_obj_tag(v_x_2245_) == 0)
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2255_; 
v_a_2247_ = lean_ctor_get(v_x_2245_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v_x_2245_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2249_ = v_x_2245_;
v_isShared_2250_ = v_isSharedCheck_2255_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v_x_2245_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2255_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
lean_object* v___x_2253_; 
v___x_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
return v___x_2253_;
}
}
}
else
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
lean_dec_ref_known(v_x_2245_, 1);
v___x_2256_ = l_IO_Promise_result_x21___redArg(v_a_2244_);
v___x_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
return v___x_2257_;
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_forIn___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2244_ = stack[0].m_obj;
lean_object* v_x_2245_ = stack[1].m_obj;
lean_object* v_res_2258_;
v_res_2258_ = l_Std_Async_ContextAsync_forIn___redArg___lam__1(v_a_2244_, v_x_2245_);
stack->m_obj
 = v_res_2258_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_forIn___redArg___lam__1___boxed(lean_object* v_a_2259_, lean_object* v_x_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Std_Async_ContextAsync_forIn___redArg___lam__1(v_a_2259_, v_x_2260_);
lean_dec(v_a_2259_);
return v_res_2262_;
}
}
lean_object* l_Std_Async_ContextAsync_forIn___redArg___lam__2(lean_object* v___f_2263_, lean_object* v_prio_2264_, lean_object* v_init_2265_, lean_object* v_x_2266_){
_start:
{
if (lean_obj_tag(v_x_2266_) == 0)
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2276_; 
lean_dec(v_init_2265_);
lean_dec(v_prio_2264_);
lean_dec_ref(v___f_2263_);
v_a_2268_ = lean_ctor_get(v_x_2266_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v_x_2266_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2270_ = v_x_2266_;
v_isShared_2271_ = v_isSharedCheck_2276_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v_x_2266_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2276_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
lean_object* v___x_2274_; 
v___x_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
return v___x_2274_;
}
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2290_; 
v_a_2277_ = lean_ctor_get(v_x_2266_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v_x_2266_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2279_ = v_x_2266_;
v_isShared_2280_ = v_isSharedCheck_2290_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v_x_2266_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2290_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___f_2281_; lean_object* v___x_2282_; uint8_t v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2286_; 
lean_inc(v_a_2277_);
v___f_2281_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_forIn___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2281_, 0, v_a_2277_);
v___x_2282_ = lean_unsigned_to_nat(0u);
v___x_2283_ = 0;
v___x_2284_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_2263_, v_prio_2264_, v_a_2277_, v_init_2265_);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v___x_2284_);
v___x_2286_ = v___x_2279_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2284_);
v___x_2286_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
v___x_2288_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2282_, v___x_2283_, v___x_2287_, v___f_2281_);
return v___x_2288_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_forIn___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2263_ = stack[0].m_obj;
lean_object* v_prio_2264_ = stack[1].m_obj;
lean_object* v_init_2265_ = stack[2].m_obj;
lean_object* v_x_2266_ = stack[3].m_obj;
lean_object* v_res_2291_;
v_res_2291_ = l_Std_Async_ContextAsync_forIn___redArg___lam__2(v___f_2263_, v_prio_2264_, v_init_2265_, v_x_2266_);
stack->m_obj
 = v_res_2291_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_forIn___redArg___lam__2___boxed(lean_object* v___f_2292_, lean_object* v_prio_2293_, lean_object* v_init_2294_, lean_object* v_x_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Std_Async_ContextAsync_forIn___redArg___lam__2(v___f_2292_, v_prio_2293_, v_init_2294_, v_x_2295_);
return v_res_2297_;
}
}
lean_object* l_Std_Async_ContextAsync_forIn___redArg(lean_object* v_init_2298_, lean_object* v_f_2299_, lean_object* v_prio_2300_, lean_object* v_ctx_2301_){
_start:
{
lean_object* v___f_2303_; lean_object* v___f_2304_; lean_object* v___x_2305_; uint8_t v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
lean_inc_ref(v_ctx_2301_);
v___f_2303_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_forIn___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_2303_, 0, v_f_2299_);
lean_closure_set(v___f_2303_, 1, v_ctx_2301_);
v___f_2304_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_forIn___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_2304_, 0, v___f_2303_);
lean_closure_set(v___f_2304_, 1, v_prio_2300_);
lean_closure_set(v___f_2304_, 2, v_init_2298_);
v___x_2305_ = lean_unsigned_to_nat(0u);
v___x_2306_ = 0;
v___x_2307_ = lean_io_promise_new();
v___x_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
v___x_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
v___x_2310_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2305_, v___x_2306_, v___x_2309_, v___f_2304_);
return v___x_2310_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_forIn___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_2298_ = stack[0].m_obj;
lean_object* v_f_2299_ = stack[1].m_obj;
lean_object* v_prio_2300_ = stack[2].m_obj;
lean_object* v_ctx_2301_ = stack[3].m_obj;
lean_object* v_res_2311_;
v_res_2311_ = l_Std_Async_ContextAsync_forIn___redArg(v_init_2298_, v_f_2299_, v_prio_2300_, v_ctx_2301_);
stack->m_obj
 = v_res_2311_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_forIn___redArg___boxed(lean_object* v_init_2312_, lean_object* v_f_2313_, lean_object* v_prio_2314_, lean_object* v_ctx_2315_, lean_object* v_a_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Std_Async_ContextAsync_forIn___redArg(v_init_2312_, v_f_2313_, v_prio_2314_, v_ctx_2315_);
lean_dec_ref(v_ctx_2315_);
return v_res_2317_;
}
}
lean_object* l_Std_Async_ContextAsync_forIn(lean_object* v_00_u03b2_2318_, lean_object* v_init_2319_, lean_object* v_f_2320_, lean_object* v_prio_2321_, lean_object* v_ctx_2322_){
_start:
{
lean_object* v___f_2324_; lean_object* v___f_2325_; lean_object* v___x_2326_; uint8_t v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
lean_inc_ref(v_ctx_2322_);
v___f_2324_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_forIn___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_2324_, 0, v_f_2320_);
lean_closure_set(v___f_2324_, 1, v_ctx_2322_);
v___f_2325_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_forIn___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_2325_, 0, v___f_2324_);
lean_closure_set(v___f_2325_, 1, v_prio_2321_);
lean_closure_set(v___f_2325_, 2, v_init_2319_);
v___x_2326_ = lean_unsigned_to_nat(0u);
v___x_2327_ = 0;
v___x_2328_ = lean_io_promise_new();
v___x_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
v___x_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2329_);
v___x_2331_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2326_, v___x_2327_, v___x_2330_, v___f_2325_);
return v___x_2331_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_forIn_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_2319_ = stack[1].m_obj;
lean_object* v_f_2320_ = stack[2].m_obj;
lean_object* v_prio_2321_ = stack[3].m_obj;
lean_object* v_ctx_2322_ = stack[4].m_obj;
lean_object* v_res_2332_;
v_res_2332_ = l_Std_Async_ContextAsync_forIn(lean_box(0), v_init_2319_, v_f_2320_, v_prio_2321_, v_ctx_2322_);
stack->m_obj
 = v_res_2332_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_forIn___boxed(lean_object* v_00_u03b2_2333_, lean_object* v_init_2334_, lean_object* v_f_2335_, lean_object* v_prio_2336_, lean_object* v_ctx_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Std_Async_ContextAsync_forIn(v_00_u03b2_2333_, v_init_2334_, v_f_2335_, v_prio_2336_, v_ctx_2337_);
lean_dec_ref(v_ctx_2337_);
return v_res_2339_;
}
}
lean_object* l_Std_Async_ContextAsync_instForInLoopUnit___lam__0(lean_object* v_f_2340_, lean_object* v___y_2341_, lean_object* v_u_2342_, lean_object* v_b_2343_){
_start:
{
lean_object* v___x_2345_; 
lean_inc_ref(v___y_2341_);
v___x_2345_ = lean_apply_4(v_f_2340_, v_u_2342_, v_b_2343_, v___y_2341_, lean_box(0));
return v___x_2345_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_instForInLoopUnit___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2340_ = stack[0].m_obj;
lean_object* v___y_2341_ = stack[1].m_obj;
lean_object* v_u_2342_ = stack[2].m_obj;
lean_object* v_b_2343_ = stack[3].m_obj;
lean_object* v_res_2346_;
v_res_2346_ = l_Std_Async_ContextAsync_instForInLoopUnit___lam__0(v_f_2340_, v___y_2341_, v_u_2342_, v_b_2343_);
stack->m_obj
 = v_res_2346_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instForInLoopUnit___lam__0___boxed(lean_object* v_f_2347_, lean_object* v___y_2348_, lean_object* v_u_2349_, lean_object* v_b_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Std_Async_ContextAsync_instForInLoopUnit___lam__0(v_f_2347_, v___y_2348_, v_u_2349_, v_b_2350_);
lean_dec_ref(v___y_2348_);
return v_res_2352_;
}
}
lean_object* l_Std_Async_ContextAsync_instForInLoopUnit___lam__2(lean_object* v___f_2353_, lean_object* v___x_2354_, lean_object* v_init_2355_, lean_object* v_x_2356_){
_start:
{
if (lean_obj_tag(v_x_2356_) == 0)
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2366_; 
lean_dec(v_init_2355_);
lean_dec(v___x_2354_);
lean_dec_ref(v___f_2353_);
v_a_2358_ = lean_ctor_get(v_x_2356_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v_x_2356_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2360_ = v_x_2356_;
v_isShared_2361_ = v_isSharedCheck_2366_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v_x_2356_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2366_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2364_; 
v___x_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2363_);
return v___x_2364_;
}
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2379_; 
v_a_2367_ = lean_ctor_get(v_x_2356_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v_x_2356_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2369_ = v_x_2356_;
v_isShared_2370_ = v_isSharedCheck_2379_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v_x_2356_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2379_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___f_2371_; uint8_t v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2375_; 
lean_inc(v_a_2367_);
v___f_2371_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_forIn___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2371_, 0, v_a_2367_);
v___x_2372_ = 0;
lean_inc(v___x_2354_);
v___x_2373_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_2353_, v___x_2354_, v_a_2367_, v_init_2355_);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 0, v___x_2373_);
v___x_2375_ = v___x_2369_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2373_);
v___x_2375_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
v___x_2377_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2354_, v___x_2372_, v___x_2376_, v___f_2371_);
return v___x_2377_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_instForInLoopUnit___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2353_ = stack[0].m_obj;
lean_object* v___x_2354_ = stack[1].m_obj;
lean_object* v_init_2355_ = stack[2].m_obj;
lean_object* v_x_2356_ = stack[3].m_obj;
lean_object* v_res_2380_;
v_res_2380_ = l_Std_Async_ContextAsync_instForInLoopUnit___lam__2(v___f_2353_, v___x_2354_, v_init_2355_, v_x_2356_);
stack->m_obj
 = v_res_2380_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instForInLoopUnit___lam__2___boxed(lean_object* v___f_2381_, lean_object* v___x_2382_, lean_object* v_init_2383_, lean_object* v_x_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Std_Async_ContextAsync_instForInLoopUnit___lam__2(v___f_2381_, v___x_2382_, v_init_2383_, v_x_2384_);
return v_res_2386_;
}
}
lean_object* l_Std_Async_ContextAsync_instForInLoopUnit___lam__1(lean_object* v_00_u03b2_2387_, lean_object* v_x_2388_, lean_object* v_init_2389_, lean_object* v_f_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v___f_2393_; lean_object* v___x_2394_; lean_object* v___f_2395_; uint8_t v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
lean_inc_ref(v___y_2391_);
v___f_2393_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_instForInLoopUnit___lam__0___boxed), 5, 2);
lean_closure_set(v___f_2393_, 0, v_f_2390_);
lean_closure_set(v___f_2393_, 1, v___y_2391_);
v___x_2394_ = lean_unsigned_to_nat(0u);
v___f_2395_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_instForInLoopUnit___lam__2___boxed), 5, 3);
lean_closure_set(v___f_2395_, 0, v___f_2393_);
lean_closure_set(v___f_2395_, 1, v___x_2394_);
lean_closure_set(v___f_2395_, 2, v_init_2389_);
v___x_2396_ = 0;
v___x_2397_ = lean_io_promise_new();
v___x_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2397_);
v___x_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
v___x_2400_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2394_, v___x_2396_, v___x_2399_, v___f_2395_);
return v___x_2400_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_instForInLoopUnit___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2388_ = stack[1].m_obj;
lean_object* v_init_2389_ = stack[2].m_obj;
lean_object* v_f_2390_ = stack[3].m_obj;
lean_object* v___y_2391_ = stack[4].m_obj;
lean_object* v_res_2401_;
v_res_2401_ = l_Std_Async_ContextAsync_instForInLoopUnit___lam__1(lean_box(0), v_x_2388_, v_init_2389_, v_f_2390_, v___y_2391_);
stack->m_obj
 = v_res_2401_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instForInLoopUnit___lam__1___boxed(lean_object* v_00_u03b2_2402_, lean_object* v_x_2403_, lean_object* v_init_2404_, lean_object* v_f_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_Std_Async_ContextAsync_instForInLoopUnit___lam__1(v_00_u03b2_2402_, v_x_2403_, v_init_2404_, v_f_2405_, v___y_2406_);
lean_dec_ref(v___y_2406_);
return v_res_2408_;
}
}
lean_object* l_Std_Async_ContextAsync_race___redArg___lam__4(lean_object* v_a_2411_, lean_object* v___x_2412_, lean_object* v___f_2413_, lean_object* v_x_2414_){
_start:
{
if (lean_obj_tag(v_x_2414_) == 0)
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2424_; 
lean_dec_ref(v___f_2413_);
lean_dec(v___x_2412_);
lean_dec_ref(v_a_2411_);
v_a_2416_ = lean_ctor_get(v_x_2414_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v_x_2414_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2418_ = v_x_2414_;
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v_x_2414_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2416_);
v___x_2421_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
lean_object* v___x_2422_; 
v___x_2422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2421_);
return v___x_2422_;
}
}
}
else
{
lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2436_; 
v_isSharedCheck_2436_ = !lean_is_exclusive(v_x_2414_);
if (v_isSharedCheck_2436_ == 0)
{
lean_object* v_unused_2437_; 
v_unused_2437_ = lean_ctor_get(v_x_2414_, 0);
lean_dec(v_unused_2437_);
v___x_2426_ = v_x_2414_;
v_isShared_2427_ = v_isSharedCheck_2436_;
goto v_resetjp_2425_;
}
else
{
lean_dec(v_x_2414_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2436_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2428_; uint8_t v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2432_; 
v___x_2428_ = lean_unsigned_to_nat(0u);
v___x_2429_ = 0;
v___x_2430_ = l_Std_CancellationContext_cancel(v_a_2411_, v___x_2412_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v___x_2430_);
v___x_2432_ = v___x_2426_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2430_);
v___x_2432_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2432_);
v___x_2434_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2428_, v___x_2429_, v___x_2433_, v___f_2413_);
return v___x_2434_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_race___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2411_ = stack[0].m_obj;
lean_object* v___x_2412_ = stack[1].m_obj;
lean_object* v___f_2413_ = stack[2].m_obj;
lean_object* v_x_2414_ = stack[3].m_obj;
lean_object* v_res_2438_;
v_res_2438_ = l_Std_Async_ContextAsync_race___redArg___lam__4(v_a_2411_, v___x_2412_, v___f_2413_, v_x_2414_);
stack->m_obj
 = v_res_2438_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__4___boxed(lean_object* v_a_2439_, lean_object* v___x_2440_, lean_object* v___f_2441_, lean_object* v_x_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Std_Async_ContextAsync_race___redArg___lam__4(v_a_2439_, v___x_2440_, v___f_2441_, v_x_2442_);
return v_res_2444_;
}
}
lean_object* l_Std_Async_ContextAsync_race___redArg___lam__0(lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_x_2447_){
_start:
{
if (lean_obj_tag(v_x_2447_) == 0)
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2457_; 
lean_dec_ref(v_a_2446_);
lean_dec_ref(v_a_2445_);
v_a_2449_ = lean_ctor_get(v_x_2447_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v_x_2447_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2451_ = v_x_2447_;
v_isShared_2452_ = v_isSharedCheck_2457_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v_x_2447_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2457_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
lean_object* v___x_2455_; 
v___x_2455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2454_);
return v___x_2455_;
}
}
}
else
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2473_; 
v_a_2458_ = lean_ctor_get(v_x_2447_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v_x_2447_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2460_ = v_x_2447_;
v_isShared_2461_ = v_isSharedCheck_2473_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v_x_2447_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2473_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___f_2462_; lean_object* v___x_2463_; lean_object* v___f_2464_; lean_object* v___x_2465_; uint8_t v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2469_; 
v___f_2462_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2462_, 0, v_a_2458_);
v___x_2463_ = lean_box(2);
v___f_2464_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_2464_, 0, v_a_2445_);
lean_closure_set(v___f_2464_, 1, v___x_2463_);
lean_closure_set(v___f_2464_, 2, v___f_2462_);
v___x_2465_ = lean_unsigned_to_nat(0u);
v___x_2466_ = 0;
v___x_2467_ = l_Std_CancellationContext_cancel(v_a_2446_, v___x_2463_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 0, v___x_2467_);
v___x_2469_ = v___x_2460_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2467_);
v___x_2469_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
v___x_2471_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2465_, v___x_2466_, v___x_2470_, v___f_2464_);
return v___x_2471_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_race___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2445_ = stack[0].m_obj;
lean_object* v_a_2446_ = stack[1].m_obj;
lean_object* v_x_2447_ = stack[2].m_obj;
lean_object* v_res_2474_;
v_res_2474_ = l_Std_Async_ContextAsync_race___redArg___lam__0(v_a_2445_, v_a_2446_, v_x_2447_);
stack->m_obj
 = v_res_2474_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__0___boxed(lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_x_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Std_Async_ContextAsync_race___redArg___lam__0(v_a_2475_, v_a_2476_, v_x_2477_);
return v_res_2479_;
}
}
lean_object* l_Std_Async_ContextAsync_race___redArg___lam__1(lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_result_2482_){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2484_ = lean_io_promise_resolve(v_result_2482_, v_a_2480_);
v___x_2485_ = lean_box(2);
v___x_2486_ = l_Std_CancellationContext_cancel(v_a_2481_, v___x_2485_);
return v___x_2486_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_race___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2480_ = stack[0].m_obj;
lean_object* v_a_2481_ = stack[1].m_obj;
lean_object* v_result_2482_ = stack[2].m_obj;
lean_object* v_res_2487_;
v_res_2487_ = l_Std_Async_ContextAsync_race___redArg___lam__1(v_a_2480_, v_a_2481_, v_result_2482_);
stack->m_obj
 = v_res_2487_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__1___boxed(lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_result_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Std_Async_ContextAsync_race___redArg___lam__1(v_a_2488_, v_a_2489_, v_result_2490_);
lean_dec(v_a_2488_);
return v_res_2492_;
}
}
lean_object* l_Std_Async_ContextAsync_race___redArg___lam__5(lean_object* v_a_2493_, lean_object* v___f_2494_, lean_object* v___x_2495_, uint8_t v___x_2496_, lean_object* v___f_2497_, lean_object* v_x_2498_){
_start:
{
if (lean_obj_tag(v_x_2498_) == 0)
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2508_; 
lean_dec_ref(v___f_2497_);
lean_dec(v___x_2495_);
lean_dec_ref(v___f_2494_);
lean_dec_ref(v_a_2493_);
v_a_2500_ = lean_ctor_get(v_x_2498_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v_x_2498_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2502_ = v_x_2498_;
v_isShared_2503_ = v_isSharedCheck_2508_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v_x_2498_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2508_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
lean_object* v___x_2506_; 
v___x_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
return v___x_2506_;
}
}
}
else
{
lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2518_; 
v_isSharedCheck_2518_ = !lean_is_exclusive(v_x_2498_);
if (v_isSharedCheck_2518_ == 0)
{
lean_object* v_unused_2519_; 
v_unused_2519_ = lean_ctor_get(v_x_2498_, 0);
lean_dec(v_unused_2519_);
v___x_2510_ = v_x_2498_;
v_isShared_2511_ = v_isSharedCheck_2518_;
goto v_resetjp_2509_;
}
else
{
lean_dec(v_x_2498_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2518_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2512_; lean_object* v___x_2514_; 
lean_inc(v___x_2495_);
v___x_2512_ = l_BaseIO_chainTask___redArg(v_a_2493_, v___f_2494_, v___x_2495_, v___x_2496_);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 0, v___x_2512_);
v___x_2514_ = v___x_2510_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2512_);
v___x_2514_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2514_);
v___x_2516_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2495_, v___x_2496_, v___x_2515_, v___f_2497_);
return v___x_2516_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_race___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2493_ = stack[0].m_obj;
lean_object* v___f_2494_ = stack[1].m_obj;
lean_object* v___x_2495_ = stack[2].m_obj;
uint8_t v___x_2496_ = stack[3].m_num;
lean_object* v___f_2497_ = stack[4].m_obj;
lean_object* v_x_2498_ = stack[5].m_obj;
lean_object* v_res_2520_;
v_res_2520_ = l_Std_Async_ContextAsync_race___redArg___lam__5(v_a_2493_, v___f_2494_, v___x_2495_, v___x_2496_, v___f_2497_, v_x_2498_);
stack->m_obj
 = v_res_2520_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__5___boxed(lean_object* v_a_2521_, lean_object* v___f_2522_, lean_object* v___x_2523_, lean_object* v___x_2524_, lean_object* v___f_2525_, lean_object* v_x_2526_, lean_object* v___y_2527_){
_start:
{
uint8_t v___x_4116__boxed_2528_; lean_object* v_res_2529_; 
v___x_4116__boxed_2528_ = lean_unbox(v___x_2524_);
v_res_2529_ = l_Std_Async_ContextAsync_race___redArg___lam__5(v_a_2521_, v___f_2522_, v___x_2523_, v___x_4116__boxed_2528_, v___f_2525_, v_x_2526_);
return v_res_2529_;
}
}
lean_object* l_Std_Async_ContextAsync_race___redArg___lam__2(lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v___f_2532_, lean_object* v___f_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_x_2536_){
_start:
{
if (lean_obj_tag(v_x_2536_) == 0)
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2546_; 
lean_dec_ref(v_a_2535_);
lean_dec_ref(v_a_2534_);
lean_dec_ref(v___f_2533_);
lean_dec_ref(v___f_2532_);
lean_dec_ref(v_a_2531_);
lean_dec_ref(v_a_2530_);
v_a_2538_ = lean_ctor_get(v_x_2536_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v_x_2536_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2540_ = v_x_2536_;
v_isShared_2541_ = v_isSharedCheck_2546_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v_x_2536_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2546_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
lean_object* v___x_2544_; 
v___x_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2543_);
return v___x_2544_;
}
}
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2564_; 
v_a_2547_ = lean_ctor_get(v_x_2536_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v_x_2536_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2549_ = v_x_2536_;
v_isShared_2550_ = v_isSharedCheck_2564_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v_x_2536_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2564_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___f_2551_; lean_object* v___f_2552_; lean_object* v___f_2553_; lean_object* v___x_2554_; uint8_t v___x_2555_; lean_object* v___x_2556_; lean_object* v___f_2557_; lean_object* v___x_2558_; lean_object* v___x_2560_; 
lean_inc_n(v_a_2547_, 2);
v___f_2551_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2551_, 0, v_a_2547_);
lean_closure_set(v___f_2551_, 1, v_a_2530_);
v___f_2552_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2552_, 0, v_a_2547_);
lean_closure_set(v___f_2552_, 1, v_a_2531_);
v___f_2553_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__10___boxed), 5, 3);
lean_closure_set(v___f_2553_, 0, v_a_2547_);
lean_closure_set(v___f_2553_, 1, v___f_2532_);
lean_closure_set(v___f_2553_, 2, v___f_2533_);
v___x_2554_ = lean_unsigned_to_nat(0u);
v___x_2555_ = 0;
v___x_2556_ = lean_box(v___x_2555_);
v___f_2557_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__5___boxed), 7, 5);
lean_closure_set(v___f_2557_, 0, v_a_2534_);
lean_closure_set(v___f_2557_, 1, v___f_2552_);
lean_closure_set(v___f_2557_, 2, v___x_2554_);
lean_closure_set(v___f_2557_, 3, v___x_2556_);
lean_closure_set(v___f_2557_, 4, v___f_2553_);
v___x_2558_ = l_BaseIO_chainTask___redArg(v_a_2535_, v___f_2551_, v___x_2554_, v___x_2555_);
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 0, v___x_2558_);
v___x_2560_ = v___x_2549_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2558_);
v___x_2560_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2560_);
v___x_2562_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2554_, v___x_2555_, v___x_2561_, v___f_2557_);
return v___x_2562_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_race___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2530_ = stack[0].m_obj;
lean_object* v_a_2531_ = stack[1].m_obj;
lean_object* v___f_2532_ = stack[2].m_obj;
lean_object* v___f_2533_ = stack[3].m_obj;
lean_object* v_a_2534_ = stack[4].m_obj;
lean_object* v_a_2535_ = stack[5].m_obj;
lean_object* v_x_2536_ = stack[6].m_obj;
lean_object* v_res_2565_;
v_res_2565_ = l_Std_Async_ContextAsync_race___redArg___lam__2(v_a_2530_, v_a_2531_, v___f_2532_, v___f_2533_, v_a_2534_, v_a_2535_, v_x_2536_);
stack->m_obj
 = v_res_2565_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__2___boxed(lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v___f_2568_, lean_object* v___f_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_x_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Std_Async_ContextAsync_race___redArg___lam__2(v_a_2566_, v_a_2567_, v___f_2568_, v___f_2569_, v_a_2570_, v_a_2571_, v_x_2572_);
return v_res_2574_;
}
}
lean_object* l_Std_Async_ContextAsync_race___redArg___lam__3(lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v___f_2577_, lean_object* v___f_2578_, lean_object* v_a_2579_, lean_object* v_x_2580_){
_start:
{
if (lean_obj_tag(v_x_2580_) == 0)
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2590_; 
lean_dec_ref(v_a_2579_);
lean_dec_ref(v___f_2578_);
lean_dec_ref(v___f_2577_);
lean_dec_ref(v_a_2576_);
lean_dec_ref(v_a_2575_);
v_a_2582_ = lean_ctor_get(v_x_2580_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v_x_2580_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2584_ = v_x_2580_;
v_isShared_2585_ = v_isSharedCheck_2590_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v_x_2580_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2590_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
lean_object* v___x_2588_; 
v___x_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
return v___x_2588_;
}
}
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2604_; 
v_a_2591_ = lean_ctor_get(v_x_2580_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v_x_2580_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2593_ = v_x_2580_;
v_isShared_2594_ = v_isSharedCheck_2604_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v_x_2580_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2604_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___f_2595_; lean_object* v___x_2596_; uint8_t v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2600_; 
v___f_2595_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__2___boxed), 8, 6);
lean_closure_set(v___f_2595_, 0, v_a_2575_);
lean_closure_set(v___f_2595_, 1, v_a_2576_);
lean_closure_set(v___f_2595_, 2, v___f_2577_);
lean_closure_set(v___f_2595_, 3, v___f_2578_);
lean_closure_set(v___f_2595_, 4, v_a_2591_);
lean_closure_set(v___f_2595_, 5, v_a_2579_);
v___x_2596_ = lean_unsigned_to_nat(0u);
v___x_2597_ = 0;
v___x_2598_ = lean_io_promise_new();
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v___x_2598_);
v___x_2600_ = v___x_2593_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
v___x_2602_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2596_, v___x_2597_, v___x_2601_, v___f_2595_);
return v___x_2602_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_race___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2575_ = stack[0].m_obj;
lean_object* v_a_2576_ = stack[1].m_obj;
lean_object* v___f_2577_ = stack[2].m_obj;
lean_object* v___f_2578_ = stack[3].m_obj;
lean_object* v_a_2579_ = stack[4].m_obj;
lean_object* v_x_2580_ = stack[5].m_obj;
lean_object* v_res_2605_;
v_res_2605_ = l_Std_Async_ContextAsync_race___redArg___lam__3(v_a_2575_, v_a_2576_, v___f_2577_, v___f_2578_, v_a_2579_, v_x_2580_);
stack->m_obj
 = v_res_2605_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__3___boxed(lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v___f_2608_, lean_object* v___f_2609_, lean_object* v_a_2610_, lean_object* v_x_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Std_Async_ContextAsync_race___redArg___lam__3(v_a_2606_, v_a_2607_, v___f_2608_, v___f_2609_, v_a_2610_, v_x_2611_);
return v_res_2613_;
}
}
lean_object* l_Std_Async_ContextAsync_race___redArg___lam__6(lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v___f_2616_, lean_object* v___f_2617_, lean_object* v_y_2618_, lean_object* v_prio_2619_, lean_object* v___f_2620_, lean_object* v_x_2621_){
_start:
{
if (lean_obj_tag(v_x_2621_) == 0)
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2631_; 
lean_dec_ref(v___f_2620_);
lean_dec(v_prio_2619_);
lean_dec_ref(v_y_2618_);
lean_dec_ref(v___f_2617_);
lean_dec_ref(v___f_2616_);
lean_dec_ref(v_a_2615_);
lean_dec_ref(v_a_2614_);
v_a_2623_ = lean_ctor_get(v_x_2621_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v_x_2621_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2625_ = v_x_2621_;
v_isShared_2626_ = v_isSharedCheck_2631_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v_x_2621_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2631_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
lean_object* v___x_2629_; 
v___x_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2628_);
return v___x_2629_;
}
}
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2649_; 
v_a_2632_ = lean_ctor_get(v_x_2621_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v_x_2621_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2634_ = v_x_2621_;
v_isShared_2635_ = v_isSharedCheck_2649_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v_x_2621_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2649_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___f_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; uint8_t v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2645_; 
lean_inc_ref(v_a_2614_);
v___f_2636_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__3___boxed), 7, 5);
lean_closure_set(v___f_2636_, 0, v_a_2614_);
lean_closure_set(v___f_2636_, 1, v_a_2615_);
lean_closure_set(v___f_2636_, 2, v___f_2616_);
lean_closure_set(v___f_2636_, 3, v___f_2617_);
lean_closure_set(v___f_2636_, 4, v_a_2632_);
v___x_2637_ = lean_apply_1(v_y_2618_, v_a_2614_);
v___x_2638_ = lean_unsigned_to_nat(0u);
v___x_2639_ = 0;
v___x_2640_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2640_, 0, lean_box(0));
lean_closure_set(v___x_2640_, 1, v___x_2637_);
v___x_2641_ = lean_io_as_task(v___x_2640_, v_prio_2619_);
v___x_2642_ = 1;
v___x_2643_ = lean_task_bind(v___x_2641_, v___f_2620_, v___x_2638_, v___x_2642_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 0, v___x_2643_);
v___x_2645_ = v___x_2634_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2645_);
v___x_2647_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2638_, v___x_2639_, v___x_2646_, v___f_2636_);
return v___x_2647_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_race___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2614_ = stack[0].m_obj;
lean_object* v_a_2615_ = stack[1].m_obj;
lean_object* v___f_2616_ = stack[2].m_obj;
lean_object* v___f_2617_ = stack[3].m_obj;
lean_object* v_y_2618_ = stack[4].m_obj;
lean_object* v_prio_2619_ = stack[5].m_obj;
lean_object* v___f_2620_ = stack[6].m_obj;
lean_object* v_x_2621_ = stack[7].m_obj;
lean_object* v_res_2650_;
v_res_2650_ = l_Std_Async_ContextAsync_race___redArg___lam__6(v_a_2614_, v_a_2615_, v___f_2616_, v___f_2617_, v_y_2618_, v_prio_2619_, v___f_2620_, v_x_2621_);
stack->m_obj
 = v_res_2650_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__6___boxed(lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v___f_2653_, lean_object* v___f_2654_, lean_object* v_y_2655_, lean_object* v_prio_2656_, lean_object* v___f_2657_, lean_object* v_x_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_Std_Async_ContextAsync_race___redArg___lam__6(v_a_2651_, v_a_2652_, v___f_2653_, v___f_2654_, v_y_2655_, v_prio_2656_, v___f_2657_, v_x_2658_);
return v_res_2660_;
}
}
lean_object* l_Std_Async_ContextAsync_race___redArg___lam__7(lean_object* v_a_2661_, lean_object* v___f_2662_, lean_object* v_y_2663_, lean_object* v_prio_2664_, lean_object* v___f_2665_, lean_object* v_x_2666_, lean_object* v___f_2667_, lean_object* v_x_2668_){
_start:
{
if (lean_obj_tag(v_x_2668_) == 0)
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2678_; 
lean_dec_ref(v___f_2667_);
lean_dec_ref(v_x_2666_);
lean_dec_ref(v___f_2665_);
lean_dec(v_prio_2664_);
lean_dec_ref(v_y_2663_);
lean_dec_ref(v___f_2662_);
lean_dec_ref(v_a_2661_);
v_a_2670_ = lean_ctor_get(v_x_2668_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v_x_2668_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2672_ = v_x_2668_;
v_isShared_2673_ = v_isSharedCheck_2678_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v_x_2668_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2678_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
lean_object* v___x_2676_; 
v___x_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2675_);
return v___x_2676_;
}
}
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2697_; 
v_a_2679_ = lean_ctor_get(v_x_2668_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v_x_2668_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2681_ = v_x_2668_;
v_isShared_2682_ = v_isSharedCheck_2697_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v_x_2668_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2697_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___f_2683_; lean_object* v___f_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; uint8_t v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; uint8_t v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2693_; 
lean_inc_ref_n(v_a_2661_, 2);
lean_inc(v_a_2679_);
v___f_2683_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2683_, 0, v_a_2679_);
lean_closure_set(v___f_2683_, 1, v_a_2661_);
lean_inc(v_prio_2664_);
v___f_2684_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__6___boxed), 9, 7);
lean_closure_set(v___f_2684_, 0, v_a_2679_);
lean_closure_set(v___f_2684_, 1, v_a_2661_);
lean_closure_set(v___f_2684_, 2, v___f_2662_);
lean_closure_set(v___f_2684_, 3, v___f_2683_);
lean_closure_set(v___f_2684_, 4, v_y_2663_);
lean_closure_set(v___f_2684_, 5, v_prio_2664_);
lean_closure_set(v___f_2684_, 6, v___f_2665_);
v___x_2685_ = lean_apply_1(v_x_2666_, v_a_2661_);
v___x_2686_ = lean_unsigned_to_nat(0u);
v___x_2687_ = 0;
v___x_2688_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2688_, 0, lean_box(0));
lean_closure_set(v___x_2688_, 1, v___x_2685_);
v___x_2689_ = lean_io_as_task(v___x_2688_, v_prio_2664_);
v___x_2690_ = 1;
v___x_2691_ = lean_task_bind(v___x_2689_, v___f_2667_, v___x_2686_, v___x_2690_);
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 0, v___x_2691_);
v___x_2693_ = v___x_2681_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2691_);
v___x_2693_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2693_);
v___x_2695_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2686_, v___x_2687_, v___x_2694_, v___f_2684_);
return v___x_2695_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_race___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2661_ = stack[0].m_obj;
lean_object* v___f_2662_ = stack[1].m_obj;
lean_object* v_y_2663_ = stack[2].m_obj;
lean_object* v_prio_2664_ = stack[3].m_obj;
lean_object* v___f_2665_ = stack[4].m_obj;
lean_object* v_x_2666_ = stack[5].m_obj;
lean_object* v___f_2667_ = stack[6].m_obj;
lean_object* v_x_2668_ = stack[7].m_obj;
lean_object* v_res_2698_;
v_res_2698_ = l_Std_Async_ContextAsync_race___redArg___lam__7(v_a_2661_, v___f_2662_, v_y_2663_, v_prio_2664_, v___f_2665_, v_x_2666_, v___f_2667_, v_x_2668_);
stack->m_obj
 = v_res_2698_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__7___boxed(lean_object* v_a_2699_, lean_object* v___f_2700_, lean_object* v_y_2701_, lean_object* v_prio_2702_, lean_object* v___f_2703_, lean_object* v_x_2704_, lean_object* v___f_2705_, lean_object* v_x_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_Std_Async_ContextAsync_race___redArg___lam__7(v_a_2699_, v___f_2700_, v_y_2701_, v_prio_2702_, v___f_2703_, v_x_2704_, v___f_2705_, v_x_2706_);
return v_res_2708_;
}
}
lean_object* l_Std_Async_ContextAsync_race___redArg___lam__8(lean_object* v___f_2709_, lean_object* v_y_2710_, lean_object* v_prio_2711_, lean_object* v___f_2712_, lean_object* v_x_2713_, lean_object* v___f_2714_, lean_object* v_a_2715_, lean_object* v_x_2716_){
_start:
{
if (lean_obj_tag(v_x_2716_) == 0)
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2726_; 
lean_dec_ref(v_a_2715_);
lean_dec_ref(v___f_2714_);
lean_dec_ref(v_x_2713_);
lean_dec_ref(v___f_2712_);
lean_dec(v_prio_2711_);
lean_dec_ref(v_y_2710_);
lean_dec_ref(v___f_2709_);
v_a_2718_ = lean_ctor_get(v_x_2716_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v_x_2716_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2720_ = v_x_2716_;
v_isShared_2721_ = v_isSharedCheck_2726_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v_x_2716_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2726_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2718_);
v___x_2723_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
lean_object* v___x_2724_; 
v___x_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
return v___x_2724_;
}
}
}
else
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2740_; 
v_a_2727_ = lean_ctor_get(v_x_2716_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v_x_2716_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2729_ = v_x_2716_;
v_isShared_2730_ = v_isSharedCheck_2740_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v_x_2716_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2740_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___f_2731_; lean_object* v___x_2732_; uint8_t v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2736_; 
v___f_2731_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__7___boxed), 9, 7);
lean_closure_set(v___f_2731_, 0, v_a_2727_);
lean_closure_set(v___f_2731_, 1, v___f_2709_);
lean_closure_set(v___f_2731_, 2, v_y_2710_);
lean_closure_set(v___f_2731_, 3, v_prio_2711_);
lean_closure_set(v___f_2731_, 4, v___f_2712_);
lean_closure_set(v___f_2731_, 5, v_x_2713_);
lean_closure_set(v___f_2731_, 6, v___f_2714_);
v___x_2732_ = lean_unsigned_to_nat(0u);
v___x_2733_ = 0;
v___x_2734_ = l_Std_CancellationContext_fork(v_a_2715_);
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 0, v___x_2734_);
v___x_2736_ = v___x_2729_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2734_);
v___x_2736_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2736_);
v___x_2738_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2732_, v___x_2733_, v___x_2737_, v___f_2731_);
return v___x_2738_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_race___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2709_ = stack[0].m_obj;
lean_object* v_y_2710_ = stack[1].m_obj;
lean_object* v_prio_2711_ = stack[2].m_obj;
lean_object* v___f_2712_ = stack[3].m_obj;
lean_object* v_x_2713_ = stack[4].m_obj;
lean_object* v___f_2714_ = stack[5].m_obj;
lean_object* v_a_2715_ = stack[6].m_obj;
lean_object* v_x_2716_ = stack[7].m_obj;
lean_object* v_res_2741_;
v_res_2741_ = l_Std_Async_ContextAsync_race___redArg___lam__8(v___f_2709_, v_y_2710_, v_prio_2711_, v___f_2712_, v_x_2713_, v___f_2714_, v_a_2715_, v_x_2716_);
stack->m_obj
 = v_res_2741_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__8___boxed(lean_object* v___f_2742_, lean_object* v_y_2743_, lean_object* v_prio_2744_, lean_object* v___f_2745_, lean_object* v_x_2746_, lean_object* v___f_2747_, lean_object* v_a_2748_, lean_object* v_x_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Std_Async_ContextAsync_race___redArg___lam__8(v___f_2742_, v_y_2743_, v_prio_2744_, v___f_2745_, v_x_2746_, v___f_2747_, v_a_2748_, v_x_2749_);
return v_res_2751_;
}
}
lean_object* l_Std_Async_ContextAsync_race___redArg___lam__9(lean_object* v___f_2752_, lean_object* v_y_2753_, lean_object* v_prio_2754_, lean_object* v___f_2755_, lean_object* v_x_2756_, lean_object* v___f_2757_, lean_object* v_x_2758_){
_start:
{
if (lean_obj_tag(v_x_2758_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2768_; 
lean_dec_ref(v___f_2757_);
lean_dec_ref(v_x_2756_);
lean_dec_ref(v___f_2755_);
lean_dec(v_prio_2754_);
lean_dec_ref(v_y_2753_);
lean_dec_ref(v___f_2752_);
v_a_2760_ = lean_ctor_get(v_x_2758_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v_x_2758_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2762_ = v_x_2758_;
v_isShared_2763_ = v_isSharedCheck_2768_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v_x_2758_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2768_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
lean_object* v___x_2766_; 
v___x_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2765_);
return v___x_2766_;
}
}
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2782_; 
v_a_2769_ = lean_ctor_get(v_x_2758_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v_x_2758_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2771_ = v_x_2758_;
v_isShared_2772_ = v_isSharedCheck_2782_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v_x_2758_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2782_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___f_2773_; lean_object* v___x_2774_; uint8_t v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2778_; 
lean_inc(v_a_2769_);
v___f_2773_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__8___boxed), 9, 7);
lean_closure_set(v___f_2773_, 0, v___f_2752_);
lean_closure_set(v___f_2773_, 1, v_y_2753_);
lean_closure_set(v___f_2773_, 2, v_prio_2754_);
lean_closure_set(v___f_2773_, 3, v___f_2755_);
lean_closure_set(v___f_2773_, 4, v_x_2756_);
lean_closure_set(v___f_2773_, 5, v___f_2757_);
lean_closure_set(v___f_2773_, 6, v_a_2769_);
v___x_2774_ = lean_unsigned_to_nat(0u);
v___x_2775_ = 0;
v___x_2776_ = l_Std_CancellationContext_fork(v_a_2769_);
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 0, v___x_2776_);
v___x_2778_ = v___x_2771_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v___x_2776_);
v___x_2778_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2778_);
v___x_2780_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2774_, v___x_2775_, v___x_2779_, v___f_2773_);
return v___x_2780_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_race___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2752_ = stack[0].m_obj;
lean_object* v_y_2753_ = stack[1].m_obj;
lean_object* v_prio_2754_ = stack[2].m_obj;
lean_object* v___f_2755_ = stack[3].m_obj;
lean_object* v_x_2756_ = stack[4].m_obj;
lean_object* v___f_2757_ = stack[5].m_obj;
lean_object* v_x_2758_ = stack[6].m_obj;
lean_object* v_res_2783_;
v_res_2783_ = l_Std_Async_ContextAsync_race___redArg___lam__9(v___f_2752_, v_y_2753_, v_prio_2754_, v___f_2755_, v_x_2756_, v___f_2757_, v_x_2758_);
stack->m_obj
 = v_res_2783_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__9___boxed(lean_object* v___f_2784_, lean_object* v_y_2785_, lean_object* v_prio_2786_, lean_object* v___f_2787_, lean_object* v_x_2788_, lean_object* v___f_2789_, lean_object* v_x_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v_res_2792_; 
v_res_2792_ = l_Std_Async_ContextAsync_race___redArg___lam__9(v___f_2784_, v_y_2785_, v_prio_2786_, v___f_2787_, v_x_2788_, v___f_2789_, v_x_2790_);
return v_res_2792_;
}
}
lean_object* l_Std_Async_ContextAsync_race___redArg(lean_object* v_x_2793_, lean_object* v_y_2794_, lean_object* v_prio_2795_, lean_object* v_a_2796_){
_start:
{
lean_object* v___f_2798_; lean_object* v___f_2799_; lean_object* v___f_2800_; lean_object* v___x_2801_; uint8_t v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___f_2798_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_2799_ = ((lean_object*)(l_Std_Async_ContextAsync_raceAll___redArg___closed__0));
v___f_2800_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__9___boxed), 8, 6);
lean_closure_set(v___f_2800_, 0, v___f_2799_);
lean_closure_set(v___f_2800_, 1, v_y_2794_);
lean_closure_set(v___f_2800_, 2, v_prio_2795_);
lean_closure_set(v___f_2800_, 3, v___f_2798_);
lean_closure_set(v___f_2800_, 4, v_x_2793_);
lean_closure_set(v___f_2800_, 5, v___f_2798_);
v___x_2801_ = lean_unsigned_to_nat(0u);
v___x_2802_ = 0;
lean_inc_ref(v_a_2796_);
v___x_2803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2803_, 0, v_a_2796_);
v___x_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2803_);
v___x_2805_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2801_, v___x_2802_, v___x_2804_, v___f_2800_);
return v___x_2805_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_race___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2793_ = stack[0].m_obj;
lean_object* v_y_2794_ = stack[1].m_obj;
lean_object* v_prio_2795_ = stack[2].m_obj;
lean_object* v_a_2796_ = stack[3].m_obj;
lean_object* v_res_2806_;
v_res_2806_ = l_Std_Async_ContextAsync_race___redArg(v_x_2793_, v_y_2794_, v_prio_2795_, v_a_2796_);
stack->m_obj
 = v_res_2806_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___boxed(lean_object* v_x_2807_, lean_object* v_y_2808_, lean_object* v_prio_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l_Std_Async_ContextAsync_race___redArg(v_x_2807_, v_y_2808_, v_prio_2809_, v_a_2810_);
lean_dec_ref(v_a_2810_);
return v_res_2812_;
}
}
lean_object* l_Std_Async_ContextAsync_race(lean_object* v_00_u03b1_2813_, lean_object* v_inst_2814_, lean_object* v_x_2815_, lean_object* v_y_2816_, lean_object* v_prio_2817_, lean_object* v_a_2818_){
_start:
{
lean_object* v___f_2820_; lean_object* v___f_2821_; lean_object* v___f_2822_; lean_object* v___x_2823_; uint8_t v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___f_2820_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_2821_ = ((lean_object*)(l_Std_Async_ContextAsync_raceAll___redArg___closed__0));
v___f_2822_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__9___boxed), 8, 6);
lean_closure_set(v___f_2822_, 0, v___f_2821_);
lean_closure_set(v___f_2822_, 1, v_y_2816_);
lean_closure_set(v___f_2822_, 2, v_prio_2817_);
lean_closure_set(v___f_2822_, 3, v___f_2820_);
lean_closure_set(v___f_2822_, 4, v_x_2815_);
lean_closure_set(v___f_2822_, 5, v___f_2820_);
v___x_2823_ = lean_unsigned_to_nat(0u);
v___x_2824_ = 0;
lean_inc_ref(v_a_2818_);
v___x_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2825_, 0, v_a_2818_);
v___x_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2825_);
v___x_2827_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2823_, v___x_2824_, v___x_2826_, v___f_2822_);
return v___x_2827_;
}
}
LEAN_EXPORT void l_Std_Async_ContextAsync_race_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2814_ = stack[1].m_obj;
lean_object* v_x_2815_ = stack[2].m_obj;
lean_object* v_y_2816_ = stack[3].m_obj;
lean_object* v_prio_2817_ = stack[4].m_obj;
lean_object* v_a_2818_ = stack[5].m_obj;
lean_object* v_res_2828_;
v_res_2828_ = l_Std_Async_ContextAsync_race(lean_box(0), v_inst_2814_, v_x_2815_, v_y_2816_, v_prio_2817_, v_a_2818_);
stack->m_obj
 = v_res_2828_;
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___boxed(lean_object* v_00_u03b1_2829_, lean_object* v_inst_2830_, lean_object* v_x_2831_, lean_object* v_y_2832_, lean_object* v_prio_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l_Std_Async_ContextAsync_race(v_00_u03b1_2829_, v_inst_2830_, v_x_2831_, v_y_2832_, v_prio_2833_, v_a_2834_);
lean_dec_ref(v_a_2834_);
lean_dec(v_inst_2830_);
return v_res_2836_;
}
}
lean_object* l_Std_Async_Selector_cancelled(lean_object* v_a_2837_){
_start:
{
lean_object* v___f_2839_; lean_object* v___x_2840_; uint8_t v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___f_2839_ = ((lean_object*)(l_Std_Async_ContextAsync_doneSelector___closed__0));
v___x_2840_ = lean_unsigned_to_nat(0u);
v___x_2841_ = 0;
lean_inc_ref(v_a_2837_);
v___x_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2842_, 0, v_a_2837_);
v___x_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2842_);
v___x_2844_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2840_, v___x_2841_, v___x_2843_, v___f_2839_);
return v___x_2844_;
}
}
LEAN_EXPORT void l_Std_Async_Selector_cancelled_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2837_ = stack[0].m_obj;
lean_object* v_res_2845_;
v_res_2845_ = l_Std_Async_Selector_cancelled(v_a_2837_);
stack->m_obj
 = v_res_2845_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selector_cancelled___boxed(lean_object* v_a_2846_, lean_object* v_a_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Std_Async_Selector_cancelled(v_a_2846_);
lean_dec_ref(v_a_2846_);
return v_res_2848_;
}
}
lean_object* runtime_initialize_Std_Internal_UV(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_Timer(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_CancellationContext(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Async_ContextAsync(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Internal_UV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_Timer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_CancellationContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Async_ContextAsync_instMonad = _init_l_Std_Async_ContextAsync_instMonad();
lean_mark_persistent(l_Std_Async_ContextAsync_instMonad);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Async_ContextAsync(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_UV(uint8_t builtin);
lean_object* initialize_Std_Async_Timer(uint8_t builtin);
lean_object* initialize_Std_Sync_CancellationContext(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Async_ContextAsync(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_UV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Async_Timer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sync_CancellationContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_ContextAsync(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Async_ContextAsync(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Async_ContextAsync(builtin);
}
#ifdef __cplusplus
}
#endif
