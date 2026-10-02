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
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_runIn___redArg(lean_object* v_ctx_1_, lean_object* v_x_2_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_2(v_x_2_, v_ctx_1_, lean_box(0));
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_runIn___redArg___boxed(lean_object* v_ctx_5_, lean_object* v_x_6_, lean_object* v_a_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Std_Async_ContextAsync_runIn___redArg(v_ctx_5_, v_x_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_runIn(lean_object* v_00_u03b1_9_, lean_object* v_ctx_10_, lean_object* v_x_11_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_apply_2(v_x_11_, v_ctx_10_, lean_box(0));
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_runIn___boxed(lean_object* v_00_u03b1_14_, lean_object* v_ctx_15_, lean_object* v_x_16_, lean_object* v_a_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Std_Async_ContextAsync_runIn(v_00_u03b1_14_, v_ctx_15_, v_x_16_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__0(lean_object* v_x_19_){
_start:
{
lean_object* v_fst_20_; 
v_fst_20_ = lean_ctor_get(v_x_19_, 0);
lean_inc(v_fst_20_);
return v_fst_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__0___boxed(lean_object* v_x_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Std_Async_ContextAsync_run___redArg___lam__0(v_x_21_);
lean_dec_ref(v_x_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__1(lean_object* v_a_23_, lean_object* v___x_24_, lean_object* v_x_25_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = l_Std_CancellationContext_cancel(v_a_23_, v___x_24_);
v___x_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
v___x_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__1___boxed(lean_object* v_a_30_, lean_object* v___x_31_, lean_object* v_x_32_, lean_object* v___y_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Std_Async_ContextAsync_run___redArg___lam__1(v_a_30_, v___x_31_, v_x_32_);
lean_dec(v_x_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__2(lean_object* v_x_35_, lean_object* v___f_36_, lean_object* v_x_37_){
_start:
{
if (lean_obj_tag(v_x_37_) == 0)
{
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_47_; 
lean_dec(v___f_36_);
lean_dec_ref(v_x_35_);
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
lean_object* v_a_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___f_51_; lean_object* v___x_52_; lean_object* v___x_53_; uint8_t v___x_54_; lean_object* v___x_55_; lean_object* v___y_57_; 
v_a_48_ = lean_ctor_get(v_x_37_, 0);
lean_inc_n(v_a_48_, 2);
lean_dec_ref_known(v_x_37_, 1);
v___x_49_ = lean_apply_1(v_x_35_, v_a_48_);
v___x_50_ = lean_box(2);
v___f_51_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_run___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_51_, 0, v_a_48_);
lean_closure_set(v___f_51_, 1, v___x_50_);
v___x_52_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_52_, 0, lean_box(0));
lean_closure_set(v___x_52_, 1, lean_box(0));
lean_closure_set(v___x_52_, 2, lean_box(0));
lean_closure_set(v___x_52_, 3, v___f_36_);
v___x_53_ = lean_unsigned_to_nat(0u);
v___x_54_ = 0;
v___x_55_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_49_, v___f_51_, v___x_53_, v___x_54_);
if (lean_obj_tag(v___x_55_) == 0)
{
lean_object* v_a_59_; 
lean_dec_ref(v___x_52_);
v_a_59_ = lean_ctor_get(v___x_55_, 0);
lean_inc(v_a_59_);
lean_dec_ref_known(v___x_55_, 1);
if (lean_obj_tag(v_a_59_) == 0)
{
lean_object* v_a_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_67_; 
v_a_60_ = lean_ctor_get(v_a_59_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v_a_59_);
if (v_isSharedCheck_67_ == 0)
{
v___x_62_ = v_a_59_;
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_a_60_);
lean_dec(v_a_59_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_65_; 
if (v_isShared_63_ == 0)
{
v___x_65_ = v___x_62_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_a_60_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
v___y_57_ = v___x_65_;
goto v___jp_56_;
}
}
}
else
{
lean_object* v_a_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_76_; 
v_a_68_ = lean_ctor_get(v_a_59_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v_a_59_);
if (v_isSharedCheck_76_ == 0)
{
v___x_70_ = v_a_59_;
v_isShared_71_ = v_isSharedCheck_76_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_a_68_);
lean_dec(v_a_59_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_76_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v_fst_72_; lean_object* v___x_74_; 
v_fst_72_ = lean_ctor_get(v_a_68_, 0);
lean_inc(v_fst_72_);
lean_dec(v_a_68_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v_fst_72_);
v___x_74_ = v___x_70_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_fst_72_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
v___y_57_ = v___x_74_;
goto v___jp_56_;
}
}
}
}
else
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_85_; 
v_a_77_ = lean_ctor_get(v___x_55_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_55_);
if (v_isSharedCheck_85_ == 0)
{
v___x_79_ = v___x_55_;
v_isShared_80_ = v_isSharedCheck_85_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_55_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_85_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_81_; lean_object* v___x_83_; 
v___x_81_ = lean_task_map(v___x_52_, v_a_77_, v___x_53_, v___x_54_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_81_);
v___x_83_ = v___x_79_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_81_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
v___jp_56_:
{
lean_object* v___x_58_; 
v___x_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_58_, 0, v___y_57_);
return v___x_58_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__2___boxed(lean_object* v_x_86_, lean_object* v___f_87_, lean_object* v_x_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Std_Async_ContextAsync_run___redArg___lam__2(v_x_86_, v___f_87_, v_x_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg(lean_object* v_x_92_){
_start:
{
lean_object* v___f_94_; lean_object* v___f_95_; lean_object* v___x_96_; uint8_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___f_94_ = ((lean_object*)(l_Std_Async_ContextAsync_run___redArg___closed__0));
v___f_95_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_run___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_95_, 0, v_x_92_);
lean_closure_set(v___f_95_, 1, v___f_94_);
v___x_96_ = lean_unsigned_to_nat(0u);
v___x_97_ = 0;
v___x_98_ = l_Std_CancellationContext_new();
v___x_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
v___x_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
v___x_101_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_96_, v___x_97_, v___x_100_, v___f_95_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___boxed(lean_object* v_x_102_, lean_object* v_a_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Std_Async_ContextAsync_run___redArg(v_x_102_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run(lean_object* v_00_u03b1_105_, lean_object* v_x_106_){
_start:
{
lean_object* v___f_108_; lean_object* v___f_109_; lean_object* v___x_110_; uint8_t v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___f_108_ = ((lean_object*)(l_Std_Async_ContextAsync_run___redArg___closed__0));
v___f_109_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_run___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_109_, 0, v_x_106_);
lean_closure_set(v___f_109_, 1, v___f_108_);
v___x_110_ = lean_unsigned_to_nat(0u);
v___x_111_ = 0;
v___x_112_ = l_Std_CancellationContext_new();
v___x_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
v___x_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
v___x_115_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_110_, v___x_111_, v___x_114_, v___f_109_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___boxed(lean_object* v_00_u03b1_116_, lean_object* v_x_117_, lean_object* v_a_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Std_Async_ContextAsync_run(v_00_u03b1_116_, v_x_117_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_getContext(lean_object* v_ctx_120_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
lean_inc_ref(v_ctx_120_);
v___x_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_122_, 0, v_ctx_120_);
v___x_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_getContext___boxed(lean_object* v_ctx_124_, lean_object* v_a_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Std_Async_ContextAsync_getContext(v_ctx_124_);
lean_dec_ref(v_ctx_124_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_isCancelled___lam__0(lean_object* v_x_127_){
_start:
{
if (lean_obj_tag(v_x_127_) == 0)
{
lean_object* v_a_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_137_; 
v_a_129_ = lean_ctor_get(v_x_127_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v_x_127_);
if (v_isSharedCheck_137_ == 0)
{
v___x_131_ = v_x_127_;
v_isShared_132_ = v_isSharedCheck_137_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_a_129_);
lean_dec(v_x_127_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_137_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_134_; 
if (v_isShared_132_ == 0)
{
v___x_134_ = v___x_131_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_129_);
v___x_134_ = v_reuseFailAlloc_136_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_135_; 
v___x_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
return v___x_135_;
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_149_; 
v_a_138_ = lean_ctor_get(v_x_127_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v_x_127_);
if (v_isSharedCheck_149_ == 0)
{
v___x_140_ = v_x_127_;
v_isShared_141_ = v_isSharedCheck_149_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v_x_127_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_149_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v_token_142_; uint8_t v___x_143_; lean_object* v___x_144_; lean_object* v___x_146_; 
v_token_142_ = lean_ctor_get(v_a_138_, 1);
lean_inc_ref(v_token_142_);
lean_dec(v_a_138_);
v___x_143_ = l_Std_CancellationToken_isCancelled(v_token_142_);
v___x_144_ = lean_box(v___x_143_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_144_);
v___x_146_ = v___x_140_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_144_);
v___x_146_ = v_reuseFailAlloc_148_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_147_; 
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_isCancelled___lam__0___boxed(lean_object* v_x_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Std_Async_ContextAsync_isCancelled___lam__0(v_x_150_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_isCancelled(lean_object* v_a_154_){
_start:
{
lean_object* v___f_156_; lean_object* v___x_157_; uint8_t v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___f_156_ = ((lean_object*)(l_Std_Async_ContextAsync_isCancelled___closed__0));
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = 0;
lean_inc_ref(v_a_154_);
v___x_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_159_, 0, v_a_154_);
v___x_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
v___x_161_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_157_, v___x_158_, v___x_160_, v___f_156_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_isCancelled___boxed(lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Std_Async_ContextAsync_isCancelled(v_a_162_);
lean_dec_ref(v_a_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_getCancellationReason___lam__0(lean_object* v_x_165_){
_start:
{
if (lean_obj_tag(v_x_165_) == 0)
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_175_; 
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
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_186_; 
v_a_176_ = lean_ctor_get(v_x_165_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v_x_165_);
if (v_isSharedCheck_186_ == 0)
{
v___x_178_ = v_x_165_;
v_isShared_179_ = v_isSharedCheck_186_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v_x_165_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_186_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v_token_180_; lean_object* v___x_181_; lean_object* v___x_183_; 
v_token_180_ = lean_ctor_get(v_a_176_, 1);
lean_inc_ref(v_token_180_);
lean_dec(v_a_176_);
v___x_181_ = l_Std_CancellationToken_getCancellationReason(v_token_180_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_181_);
v___x_183_ = v___x_178_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_181_);
v___x_183_ = v_reuseFailAlloc_185_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
lean_object* v___x_184_; 
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
return v___x_184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_getCancellationReason___lam__0___boxed(lean_object* v_x_187_, lean_object* v___y_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Std_Async_ContextAsync_getCancellationReason___lam__0(v_x_187_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_getCancellationReason(lean_object* v_a_191_){
_start:
{
lean_object* v___f_193_; lean_object* v___x_194_; uint8_t v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___f_193_ = ((lean_object*)(l_Std_Async_ContextAsync_getCancellationReason___closed__0));
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = 0;
lean_inc_ref(v_a_191_);
v___x_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_196_, 0, v_a_191_);
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
v___x_198_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_194_, v___x_195_, v___x_197_, v___f_193_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_getCancellationReason___boxed(lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Std_Async_ContextAsync_getCancellationReason(v_a_199_);
lean_dec_ref(v_a_199_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_cancel___lam__0(lean_object* v_reason_202_, lean_object* v_x_203_){
_start:
{
if (lean_obj_tag(v_x_203_) == 0)
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_213_; 
lean_dec(v_reason_202_);
v_a_205_ = lean_ctor_get(v_x_203_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v_x_203_);
if (v_isSharedCheck_213_ == 0)
{
v___x_207_ = v_x_203_;
v_isShared_208_ = v_isSharedCheck_213_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v_x_203_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_213_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_a_205_);
v___x_210_ = v_reuseFailAlloc_212_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_211_; 
v___x_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
return v___x_211_;
}
}
}
else
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_223_; 
v_a_214_ = lean_ctor_get(v_x_203_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v_x_203_);
if (v_isSharedCheck_223_ == 0)
{
v___x_216_ = v_x_203_;
v_isShared_217_ = v_isSharedCheck_223_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v_x_203_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_223_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_218_ = l_Std_CancellationContext_cancel(v_a_214_, v_reason_202_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_218_);
v___x_220_ = v___x_216_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_218_);
v___x_220_ = v_reuseFailAlloc_222_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
lean_object* v___x_221_; 
v___x_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
return v___x_221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_cancel___lam__0___boxed(lean_object* v_reason_224_, lean_object* v_x_225_, lean_object* v___y_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Std_Async_ContextAsync_cancel___lam__0(v_reason_224_, v_x_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_cancel(lean_object* v_reason_228_, lean_object* v_a_229_){
_start:
{
lean_object* v___f_231_; lean_object* v___x_232_; uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___f_231_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_cancel___lam__0___boxed), 3, 1);
lean_closure_set(v___f_231_, 0, v_reason_228_);
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = 0;
lean_inc_ref(v_a_229_);
v___x_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_234_, 0, v_a_229_);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
v___x_236_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_232_, v___x_233_, v___x_235_, v___f_231_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_cancel___boxed(lean_object* v_reason_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Std_Async_ContextAsync_cancel(v_reason_237_, v_a_238_);
lean_dec_ref(v_a_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_doneSelector___lam__0(lean_object* v_x_241_){
_start:
{
if (lean_obj_tag(v_x_241_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_251_; 
v_a_243_ = lean_ctor_get(v_x_241_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v_x_241_);
if (v_isSharedCheck_251_ == 0)
{
v___x_245_ = v_x_241_;
v_isShared_246_ = v_isSharedCheck_251_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v_x_241_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_251_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_243_);
v___x_248_ = v_reuseFailAlloc_250_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_249_; 
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
return v___x_249_;
}
}
}
else
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_262_; 
v_a_252_ = lean_ctor_get(v_x_241_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v_x_241_);
if (v_isSharedCheck_262_ == 0)
{
v___x_254_ = v_x_241_;
v_isShared_255_ = v_isSharedCheck_262_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v_x_241_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_262_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v_token_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v_token_256_ = lean_ctor_get(v_a_252_, 1);
lean_inc_ref(v_token_256_);
lean_dec(v_a_252_);
v___x_257_ = l_Std_CancellationToken_selector(v_token_256_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 0, v___x_257_);
v___x_259_ = v___x_254_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_257_);
v___x_259_ = v_reuseFailAlloc_261_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; 
v___x_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
return v___x_260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_doneSelector___lam__0___boxed(lean_object* v_x_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Std_Async_ContextAsync_doneSelector___lam__0(v_x_263_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_doneSelector(lean_object* v_a_267_){
_start:
{
lean_object* v___f_269_; lean_object* v___x_270_; uint8_t v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___f_269_ = ((lean_object*)(l_Std_Async_ContextAsync_doneSelector___closed__0));
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = 0;
lean_inc_ref(v_a_267_);
v___x_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_272_, 0, v_a_267_);
v___x_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
v___x_274_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_270_, v___x_271_, v___x_273_, v___f_269_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_doneSelector___boxed(lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Std_Async_ContextAsync_doneSelector(v_a_275_);
lean_dec_ref(v_a_275_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_awaitCancellation___lam__0(lean_object* v_x_278_){
_start:
{
if (lean_obj_tag(v_x_278_) == 0)
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_288_; 
v_a_280_ = lean_ctor_get(v_x_278_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v_x_278_);
if (v_isSharedCheck_288_ == 0)
{
v___x_282_ = v_x_278_;
v_isShared_283_ = v_isSharedCheck_288_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v_x_278_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_288_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_a_280_);
v___x_285_ = v_reuseFailAlloc_287_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_286_; 
v___x_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
return v___x_286_;
}
}
}
else
{
lean_object* v_a_289_; lean_object* v___x_290_; 
v_a_289_ = lean_ctor_get(v_x_278_, 0);
lean_inc(v_a_289_);
lean_dec_ref_known(v_x_278_, 1);
v___x_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_290_, 0, v_a_289_);
return v___x_290_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_awaitCancellation___lam__0___boxed(lean_object* v_x_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Std_Async_ContextAsync_awaitCancellation___lam__0(v_x_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_awaitCancellation___lam__1(lean_object* v___f_294_, lean_object* v_x_295_){
_start:
{
if (lean_obj_tag(v_x_295_) == 0)
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_305_; 
lean_dec_ref(v___f_294_);
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
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_326_; 
v_a_306_ = lean_ctor_get(v_x_295_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v_x_295_);
if (v_isSharedCheck_326_ == 0)
{
v___x_308_ = v_x_295_;
v_isShared_309_ = v_isSharedCheck_326_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v_x_295_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_326_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v_token_310_; lean_object* v___x_311_; uint8_t v___x_312_; lean_object* v_val_314_; lean_object* v___x_317_; 
v_token_310_ = lean_ctor_get(v_a_306_, 1);
lean_inc_ref(v_token_310_);
lean_dec(v_a_306_);
v___x_311_ = lean_unsigned_to_nat(0u);
v___x_312_ = 0;
v___x_317_ = l_Std_CancellationToken_wait(v_token_310_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; lean_object* v___x_320_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_a_318_);
lean_dec_ref_known(v___x_317_, 1);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v_a_318_);
v___x_320_ = v___x_308_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
v_val_314_ = v___x_320_;
goto v___jp_313_;
}
}
else
{
lean_object* v_a_322_; lean_object* v___x_324_; 
v_a_322_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v___x_317_, 1);
if (v_isShared_309_ == 0)
{
lean_ctor_set_tag(v___x_308_, 0);
lean_ctor_set(v___x_308_, 0, v_a_322_);
v___x_324_ = v___x_308_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
v_val_314_ = v___x_324_;
goto v___jp_313_;
}
}
v___jp_313_:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v_val_314_);
v___x_316_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_311_, v___x_312_, v___x_315_, v___f_294_);
return v___x_316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_awaitCancellation___lam__1___boxed(lean_object* v___f_327_, lean_object* v_x_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Std_Async_ContextAsync_awaitCancellation___lam__1(v___f_327_, v_x_328_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_awaitCancellation(lean_object* v_a_334_){
_start:
{
lean_object* v___f_336_; lean_object* v___x_337_; uint8_t v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___f_336_ = ((lean_object*)(l_Std_Async_ContextAsync_awaitCancellation___closed__1));
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = 0;
lean_inc_ref(v_a_334_);
v___x_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_339_, 0, v_a_334_);
v___x_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
v___x_341_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_337_, v___x_338_, v___x_340_, v___f_336_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_awaitCancellation___boxed(lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Std_Async_ContextAsync_awaitCancellation(v_a_342_);
lean_dec_ref(v_a_342_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__0(lean_object* v_x_345_){
_start:
{
if (lean_obj_tag(v_x_345_) == 0)
{
lean_object* v_a_346_; lean_object* v___x_347_; 
v_a_346_ = lean_ctor_get(v_x_345_, 0);
lean_inc(v_a_346_);
lean_dec_ref_known(v_x_345_, 1);
v___x_347_ = lean_task_pure(v_a_346_);
return v___x_347_;
}
else
{
lean_object* v_a_348_; 
v_a_348_ = lean_ctor_get(v_x_345_, 0);
lean_inc_ref(v_a_348_);
lean_dec_ref_known(v_x_345_, 1);
return v_a_348_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__4(lean_object* v_x_349_, lean_object* v_x_350_){
_start:
{
if (lean_obj_tag(v_x_350_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_360_; 
lean_dec_ref(v_x_349_);
v_a_352_ = lean_ctor_get(v_x_350_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v_x_350_);
if (v_isSharedCheck_360_ == 0)
{
v___x_354_ = v_x_350_;
v_isShared_355_ = v_isSharedCheck_360_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v_x_350_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_360_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_359_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_358_; 
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
}
else
{
lean_object* v___x_361_; 
lean_dec_ref_known(v_x_350_, 1);
v___x_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_361_, 0, v_x_349_);
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__4___boxed(lean_object* v_x_362_, lean_object* v_x_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__4(v_x_362_, v_x_363_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__1(lean_object* v_a_366_, lean_object* v_x_367_){
_start:
{
if (lean_obj_tag(v_x_367_) == 0)
{
lean_object* v___f_369_; lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___f_369_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_369_, 0, v_x_367_);
v___x_370_ = lean_box(2);
v___x_371_ = lean_unsigned_to_nat(0u);
v___x_372_ = 0;
v___x_373_ = l_Std_CancellationContext_cancel(v_a_366_, v___x_370_);
v___x_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
v___x_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
v___x_376_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_371_, v___x_372_, v___x_375_, v___f_369_);
return v___x_376_;
}
else
{
lean_object* v___x_377_; 
lean_dec_ref(v_a_366_);
v___x_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_377_, 0, v_x_367_);
return v___x_377_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__1___boxed(lean_object* v_a_378_, lean_object* v_x_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__1(v_a_378_, v_x_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__2(lean_object* v_x_382_, lean_object* v_a_383_, lean_object* v___f_384_){
_start:
{
lean_object* v___x_386_; uint8_t v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_386_ = lean_unsigned_to_nat(0u);
v___x_387_ = 0;
v___x_388_ = lean_apply_2(v_x_382_, v_a_383_, lean_box(0));
v___x_389_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_386_, v___x_387_, v___x_388_, v___f_384_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__2___boxed(lean_object* v_x_390_, lean_object* v_a_391_, lean_object* v___f_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__2(v_x_390_, v_a_391_, v___f_392_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__5(lean_object* v___f_395_, lean_object* v___f_396_, lean_object* v___f_397_){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; lean_object* v___x_402_; lean_object* v___y_404_; 
v___x_399_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_399_, 0, lean_box(0));
lean_closure_set(v___x_399_, 1, lean_box(0));
lean_closure_set(v___x_399_, 2, lean_box(0));
lean_closure_set(v___x_399_, 3, v___f_395_);
v___x_400_ = lean_unsigned_to_nat(0u);
v___x_401_ = 0;
v___x_402_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_396_, v___f_397_, v___x_400_, v___x_401_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_406_; 
lean_dec_ref(v___x_399_);
v_a_406_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_406_);
lean_dec_ref_known(v___x_402_, 1);
if (lean_obj_tag(v_a_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
v_a_407_ = lean_ctor_get(v_a_406_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v_a_406_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v_a_406_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v_a_406_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
v___y_404_ = v___x_412_;
goto v___jp_403_;
}
}
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_423_; 
v_a_415_ = lean_ctor_get(v_a_406_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v_a_406_);
if (v_isSharedCheck_423_ == 0)
{
v___x_417_ = v_a_406_;
v_isShared_418_ = v_isSharedCheck_423_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v_a_406_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_423_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v_fst_419_; lean_object* v___x_421_; 
v_fst_419_ = lean_ctor_get(v_a_415_, 0);
lean_inc(v_fst_419_);
lean_dec(v_a_415_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v_fst_419_);
v___x_421_ = v___x_417_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_fst_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
v___y_404_ = v___x_421_;
goto v___jp_403_;
}
}
}
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_432_; 
v_a_424_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_432_ == 0)
{
v___x_426_ = v___x_402_;
v_isShared_427_ = v_isSharedCheck_432_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_402_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_432_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_428_ = lean_task_map(v___x_399_, v_a_424_, v___x_400_, v___x_401_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_428_);
v___x_430_ = v___x_426_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_428_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
v___jp_403_:
{
lean_object* v___x_405_; 
v___x_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_405_, 0, v___y_404_);
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed(lean_object* v___f_433_, lean_object* v___f_434_, lean_object* v___f_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__5(v___f_433_, v___f_434_, v___f_435_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__6(lean_object* v_a_438_, lean_object* v___x_439_, lean_object* v_x_440_){
_start:
{
if (lean_obj_tag(v_x_440_) == 0)
{
lean_object* v___f_442_; lean_object* v___x_443_; uint8_t v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___f_442_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_442_, 0, v_x_440_);
v___x_443_ = lean_unsigned_to_nat(0u);
v___x_444_ = 0;
v___x_445_ = l_Std_CancellationContext_cancel(v_a_438_, v___x_439_);
v___x_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
v___x_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
v___x_448_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_443_, v___x_444_, v___x_447_, v___f_442_);
return v___x_448_;
}
else
{
lean_object* v___x_449_; 
lean_dec(v___x_439_);
lean_dec_ref(v_a_438_);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v_x_440_);
return v___x_449_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__6___boxed(lean_object* v_a_450_, lean_object* v___x_451_, lean_object* v_x_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__6(v_a_450_, v___x_451_, v_x_452_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__3(lean_object* v_y_455_, lean_object* v_a_456_, lean_object* v___f_457_){
_start:
{
lean_object* v___x_459_; uint8_t v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_459_ = lean_unsigned_to_nat(0u);
v___x_460_ = 0;
v___x_461_ = lean_apply_2(v_y_455_, v_a_456_, lean_box(0));
v___x_462_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_459_, v___x_460_, v___x_461_, v___f_457_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__3___boxed(lean_object* v_y_463_, lean_object* v_a_464_, lean_object* v___f_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__3(v_y_463_, v_a_464_, v___f_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__9(lean_object* v_a_468_, lean_object* v_x_469_){
_start:
{
if (lean_obj_tag(v_x_469_) == 0)
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_479_; 
lean_dec(v_a_468_);
v_a_471_ = lean_ctor_get(v_x_469_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v_x_469_);
if (v_isSharedCheck_479_ == 0)
{
v___x_473_ = v_x_469_;
v_isShared_474_ = v_isSharedCheck_479_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v_x_469_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_479_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_478_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v___x_477_; 
v___x_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
return v___x_477_;
}
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_489_; 
v_a_480_ = lean_ctor_get(v_x_469_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v_x_469_);
if (v_isSharedCheck_489_ == 0)
{
v___x_482_ = v_x_469_;
v_isShared_483_ = v_isSharedCheck_489_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v_x_469_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_489_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_484_, 0, v_a_468_);
lean_ctor_set(v___x_484_, 1, v_a_480_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_484_);
v___x_486_ = v___x_482_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_488_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_487_; 
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
return v___x_487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__9___boxed(lean_object* v_a_490_, lean_object* v_x_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__9(v_a_490_, v_x_491_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__7(lean_object* v_a_494_, lean_object* v_x_495_){
_start:
{
if (lean_obj_tag(v_x_495_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_505_; 
lean_dec_ref(v_a_494_);
v_a_497_ = lean_ctor_get(v_x_495_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v_x_495_);
if (v_isSharedCheck_505_ == 0)
{
v___x_499_ = v_x_495_;
v_isShared_500_ = v_isSharedCheck_505_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v_x_495_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_505_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_504_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_503_; 
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
}
}
else
{
lean_object* v_a_506_; lean_object* v___f_507_; lean_object* v___x_508_; uint8_t v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v_a_506_ = lean_ctor_get(v_x_495_, 0);
lean_inc(v_a_506_);
lean_dec_ref_known(v_x_495_, 1);
v___f_507_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_507_, 0, v_a_506_);
v___x_508_ = lean_unsigned_to_nat(0u);
v___x_509_ = 0;
v___x_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_510_, 0, v_a_494_);
v___x_511_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_508_, v___x_509_, v___x_510_, v___f_507_);
return v___x_511_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__7___boxed(lean_object* v_a_512_, lean_object* v_x_513_, lean_object* v___y_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__7(v_a_512_, v_x_513_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__8(lean_object* v_a_516_, lean_object* v_x_517_){
_start:
{
if (lean_obj_tag(v_x_517_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_527_; 
lean_dec_ref(v_a_516_);
v_a_519_ = lean_ctor_get(v_x_517_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v_x_517_);
if (v_isSharedCheck_527_ == 0)
{
v___x_521_ = v_x_517_;
v_isShared_522_ = v_isSharedCheck_527_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v_x_517_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_527_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_526_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_525_; 
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
return v___x_525_;
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___f_529_; lean_object* v___x_530_; uint8_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v_a_528_ = lean_ctor_get(v_x_517_, 0);
lean_inc(v_a_528_);
lean_dec_ref_known(v_x_517_, 1);
v___f_529_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_529_, 0, v_a_528_);
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = 0;
v___x_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_532_, 0, v_a_516_);
v___x_533_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_530_, v___x_531_, v___x_532_, v___f_529_);
return v___x_533_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__8___boxed(lean_object* v_a_534_, lean_object* v_x_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__8(v_a_534_, v_x_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__10(lean_object* v___f_538_, lean_object* v_prio_539_, lean_object* v___f_540_, lean_object* v_x_541_){
_start:
{
if (lean_obj_tag(v_x_541_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_551_; 
lean_dec_ref(v___f_540_);
lean_dec(v_prio_539_);
lean_dec_ref(v___f_538_);
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
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_568_; 
v_a_552_ = lean_ctor_get(v_x_541_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v_x_541_);
if (v_isSharedCheck_568_ == 0)
{
v___x_554_ = v_x_541_;
v_isShared_555_ = v_isSharedCheck_568_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v_x_541_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_568_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___f_556_; lean_object* v___x_557_; uint8_t v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v___f_556_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__8___boxed), 3, 1);
lean_closure_set(v___f_556_, 0, v_a_552_);
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = 0;
v___x_559_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_559_, 0, lean_box(0));
lean_closure_set(v___x_559_, 1, v___f_538_);
v___x_560_ = lean_io_as_task(v___x_559_, v_prio_539_);
v___x_561_ = 1;
v___x_562_ = lean_task_bind(v___x_560_, v___f_540_, v___x_557_, v___x_561_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_562_);
v___x_564_ = v___x_554_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_562_);
v___x_564_ = v_reuseFailAlloc_567_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
v___x_566_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_557_, v___x_558_, v___x_565_, v___f_556_);
return v___x_566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__10___boxed(lean_object* v___f_569_, lean_object* v_prio_570_, lean_object* v___f_571_, lean_object* v_x_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__10(v___f_569_, v_prio_570_, v___f_571_, v_x_572_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__11(lean_object* v_x_575_, lean_object* v_x_576_){
_start:
{
if (lean_obj_tag(v_x_576_) == 0)
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_586_; 
lean_dec_ref(v_x_575_);
v_a_578_ = lean_ctor_get(v_x_576_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v_x_576_);
if (v_isSharedCheck_586_ == 0)
{
v___x_580_ = v_x_576_;
v_isShared_581_ = v_isSharedCheck_586_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v_x_576_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_586_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_585_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_584_; 
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
return v___x_584_;
}
}
}
else
{
lean_object* v___x_587_; 
lean_dec_ref_known(v_x_576_, 1);
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v_x_575_);
return v___x_587_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__11___boxed(lean_object* v_x_588_, lean_object* v_x_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__11(v_x_588_, v_x_589_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__12(lean_object* v_a_592_, lean_object* v___x_593_, lean_object* v_x_594_){
_start:
{
if (lean_obj_tag(v_x_594_) == 0)
{
lean_object* v___x_596_; 
lean_dec(v___x_593_);
lean_dec_ref(v_a_592_);
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v_x_594_);
return v___x_596_;
}
else
{
lean_object* v___f_597_; lean_object* v___x_598_; uint8_t v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___f_597_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__11___boxed), 3, 1);
lean_closure_set(v___f_597_, 0, v_x_594_);
v___x_598_ = lean_unsigned_to_nat(0u);
v___x_599_ = 0;
v___x_600_ = l_Std_CancellationContext_cancel(v_a_592_, v___x_593_);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
v___x_603_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_598_, v___x_599_, v___x_602_, v___f_597_);
return v___x_603_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__12___boxed(lean_object* v_a_604_, lean_object* v___x_605_, lean_object* v_x_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__12(v_a_604_, v___x_605_, v_x_606_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__13(lean_object* v_a_609_, lean_object* v___f_610_, lean_object* v___f_611_, lean_object* v_a_612_, lean_object* v_y_613_, lean_object* v___f_614_, lean_object* v_prio_615_, lean_object* v___f_616_, lean_object* v___f_617_, lean_object* v_x_618_){
_start:
{
if (lean_obj_tag(v_x_618_) == 0)
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_628_; 
lean_dec_ref(v___f_617_);
lean_dec_ref(v___f_616_);
lean_dec(v_prio_615_);
lean_dec(v___f_614_);
lean_dec_ref(v_y_613_);
lean_dec_ref(v_a_612_);
lean_dec_ref(v___f_611_);
lean_dec(v___f_610_);
lean_dec_ref(v_a_609_);
v_a_620_ = lean_ctor_get(v_x_618_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_628_ == 0)
{
v___x_622_ = v_x_618_;
v_isShared_623_ = v_isSharedCheck_628_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v_x_618_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_628_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_627_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_626_; 
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
return v___x_626_;
}
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_654_; 
v_a_629_ = lean_ctor_get(v_x_618_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_654_ == 0)
{
v___x_631_ = v_x_618_;
v_isShared_632_ = v_isSharedCheck_654_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v_x_618_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_654_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; lean_object* v___f_634_; lean_object* v___f_635_; lean_object* v___f_636_; lean_object* v___f_637_; lean_object* v___f_638_; lean_object* v___f_639_; lean_object* v___f_640_; lean_object* v___f_641_; lean_object* v___x_642_; uint8_t v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_633_ = lean_box(2);
v___f_634_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_run___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_634_, 0, v_a_609_);
lean_closure_set(v___f_634_, 1, v___x_633_);
v___f_635_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_635_, 0, v___f_610_);
lean_closure_set(v___f_635_, 1, v___f_611_);
lean_closure_set(v___f_635_, 2, v___f_634_);
lean_inc_ref(v_a_612_);
v___f_636_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_636_, 0, v_a_612_);
lean_closure_set(v___f_636_, 1, v___x_633_);
lean_inc(v_a_629_);
v___f_637_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_637_, 0, v_y_613_);
lean_closure_set(v___f_637_, 1, v_a_629_);
lean_closure_set(v___f_637_, 2, v___f_636_);
v___f_638_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_run___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_638_, 0, v_a_629_);
lean_closure_set(v___f_638_, 1, v___x_633_);
v___f_639_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_639_, 0, v___f_614_);
lean_closure_set(v___f_639_, 1, v___f_637_);
lean_closure_set(v___f_639_, 2, v___f_638_);
lean_inc(v_prio_615_);
v___f_640_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__10___boxed), 5, 3);
lean_closure_set(v___f_640_, 0, v___f_639_);
lean_closure_set(v___f_640_, 1, v_prio_615_);
lean_closure_set(v___f_640_, 2, v___f_616_);
v___f_641_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__12___boxed), 4, 2);
lean_closure_set(v___f_641_, 0, v_a_612_);
lean_closure_set(v___f_641_, 1, v___x_633_);
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = 0;
v___x_644_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_644_, 0, lean_box(0));
lean_closure_set(v___x_644_, 1, v___f_635_);
v___x_645_ = lean_io_as_task(v___x_644_, v_prio_615_);
v___x_646_ = 1;
v___x_647_ = lean_task_bind(v___x_645_, v___f_617_, v___x_642_, v___x_646_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v___x_647_);
v___x_649_ = v___x_631_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_653_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
v___x_651_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_642_, v___x_643_, v___x_650_, v___f_640_);
v___x_652_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_642_, v___x_643_, v___x_651_, v___f_641_);
return v___x_652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__13___boxed(lean_object* v_a_655_, lean_object* v___f_656_, lean_object* v___f_657_, lean_object* v_a_658_, lean_object* v_y_659_, lean_object* v___f_660_, lean_object* v_prio_661_, lean_object* v___f_662_, lean_object* v___f_663_, lean_object* v_x_664_, lean_object* v___y_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__13(v_a_655_, v___f_656_, v___f_657_, v_a_658_, v_y_659_, v___f_660_, v_prio_661_, v___f_662_, v___f_663_, v_x_664_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__14(lean_object* v_x_667_, lean_object* v___f_668_, lean_object* v___f_669_, lean_object* v_a_670_, lean_object* v_y_671_, lean_object* v___f_672_, lean_object* v_prio_673_, lean_object* v___f_674_, lean_object* v___f_675_, lean_object* v_x_676_){
_start:
{
if (lean_obj_tag(v_x_676_) == 0)
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_686_; 
lean_dec_ref(v___f_675_);
lean_dec_ref(v___f_674_);
lean_dec(v_prio_673_);
lean_dec(v___f_672_);
lean_dec_ref(v_y_671_);
lean_dec_ref(v_a_670_);
lean_dec(v___f_669_);
lean_dec_ref(v___f_668_);
lean_dec_ref(v_x_667_);
v_a_678_ = lean_ctor_get(v_x_676_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v_x_676_);
if (v_isSharedCheck_686_ == 0)
{
v___x_680_ = v_x_676_;
v_isShared_681_ = v_isSharedCheck_686_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v_x_676_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_686_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_678_);
v___x_683_ = v_reuseFailAlloc_685_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
lean_object* v___x_684_; 
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
return v___x_684_;
}
}
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_701_; 
v_a_687_ = lean_ctor_get(v_x_676_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v_x_676_);
if (v_isSharedCheck_701_ == 0)
{
v___x_689_ = v_x_676_;
v_isShared_690_ = v_isSharedCheck_701_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v_x_676_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_701_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___f_691_; lean_object* v___f_692_; lean_object* v___x_693_; uint8_t v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
lean_inc(v_a_687_);
v___f_691_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_691_, 0, v_x_667_);
lean_closure_set(v___f_691_, 1, v_a_687_);
lean_closure_set(v___f_691_, 2, v___f_668_);
lean_inc_ref(v_a_670_);
v___f_692_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__13___boxed), 11, 9);
lean_closure_set(v___f_692_, 0, v_a_687_);
lean_closure_set(v___f_692_, 1, v___f_669_);
lean_closure_set(v___f_692_, 2, v___f_691_);
lean_closure_set(v___f_692_, 3, v_a_670_);
lean_closure_set(v___f_692_, 4, v_y_671_);
lean_closure_set(v___f_692_, 5, v___f_672_);
lean_closure_set(v___f_692_, 6, v_prio_673_);
lean_closure_set(v___f_692_, 7, v___f_674_);
lean_closure_set(v___f_692_, 8, v___f_675_);
v___x_693_ = lean_unsigned_to_nat(0u);
v___x_694_ = 0;
v___x_695_ = l_Std_CancellationContext_fork(v_a_670_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_695_);
v___x_697_ = v___x_689_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_695_);
v___x_697_ = v_reuseFailAlloc_700_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
v___x_699_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_693_, v___x_694_, v___x_698_, v___f_692_);
return v___x_699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__14___boxed(lean_object* v_x_702_, lean_object* v___f_703_, lean_object* v___f_704_, lean_object* v_a_705_, lean_object* v_y_706_, lean_object* v___f_707_, lean_object* v_prio_708_, lean_object* v___f_709_, lean_object* v___f_710_, lean_object* v_x_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__14(v_x_702_, v___f_703_, v___f_704_, v_a_705_, v_y_706_, v___f_707_, v_prio_708_, v___f_709_, v___f_710_, v_x_711_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__15(lean_object* v_x_714_, lean_object* v___f_715_, lean_object* v_y_716_, lean_object* v___f_717_, lean_object* v_prio_718_, lean_object* v___f_719_, lean_object* v___f_720_, lean_object* v_x_721_){
_start:
{
if (lean_obj_tag(v_x_721_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_731_; 
lean_dec_ref(v___f_720_);
lean_dec_ref(v___f_719_);
lean_dec(v_prio_718_);
lean_dec(v___f_717_);
lean_dec_ref(v_y_716_);
lean_dec(v___f_715_);
lean_dec_ref(v_x_714_);
v_a_723_ = lean_ctor_get(v_x_721_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v_x_721_);
if (v_isSharedCheck_731_ == 0)
{
v___x_725_ = v_x_721_;
v_isShared_726_ = v_isSharedCheck_731_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v_x_721_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_731_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_730_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_729_; 
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
return v___x_729_;
}
}
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_746_; 
v_a_732_ = lean_ctor_get(v_x_721_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v_x_721_);
if (v_isSharedCheck_746_ == 0)
{
v___x_734_ = v_x_721_;
v_isShared_735_ = v_isSharedCheck_746_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v_x_721_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_746_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___f_736_; lean_object* v___f_737_; lean_object* v___x_738_; uint8_t v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
lean_inc_n(v_a_732_, 2);
v___f_736_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_736_, 0, v_a_732_);
v___f_737_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__14___boxed), 11, 9);
lean_closure_set(v___f_737_, 0, v_x_714_);
lean_closure_set(v___f_737_, 1, v___f_736_);
lean_closure_set(v___f_737_, 2, v___f_715_);
lean_closure_set(v___f_737_, 3, v_a_732_);
lean_closure_set(v___f_737_, 4, v_y_716_);
lean_closure_set(v___f_737_, 5, v___f_717_);
lean_closure_set(v___f_737_, 6, v_prio_718_);
lean_closure_set(v___f_737_, 7, v___f_719_);
lean_closure_set(v___f_737_, 8, v___f_720_);
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = 0;
v___x_740_ = l_Std_CancellationContext_fork(v_a_732_);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 0, v___x_740_);
v___x_742_ = v___x_734_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_745_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
v___x_744_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_738_, v___x_739_, v___x_743_, v___f_737_);
return v___x_744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__15___boxed(lean_object* v_x_747_, lean_object* v___f_748_, lean_object* v_y_749_, lean_object* v___f_750_, lean_object* v_prio_751_, lean_object* v___f_752_, lean_object* v___f_753_, lean_object* v_x_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__15(v_x_747_, v___f_748_, v_y_749_, v___f_750_, v_prio_751_, v___f_752_, v___f_753_, v_x_754_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__16(lean_object* v___f_757_, lean_object* v_x_758_){
_start:
{
if (lean_obj_tag(v_x_758_) == 0)
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_768_; 
lean_dec_ref(v___f_757_);
v_a_760_ = lean_ctor_get(v_x_758_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v_x_758_);
if (v_isSharedCheck_768_ == 0)
{
v___x_762_ = v_x_758_;
v_isShared_763_ = v_isSharedCheck_768_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v_x_758_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_768_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_767_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_766_; 
v___x_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
return v___x_766_;
}
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_781_; 
v_a_769_ = lean_ctor_get(v_x_758_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v_x_758_);
if (v_isSharedCheck_781_ == 0)
{
v___x_771_ = v_x_758_;
v_isShared_772_ = v_isSharedCheck_781_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v_x_758_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_781_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; uint8_t v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = 0;
v___x_775_ = l_Std_CancellationContext_fork(v_a_769_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_775_);
v___x_777_ = v___x_771_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_775_);
v___x_777_ = v_reuseFailAlloc_780_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
v___x_779_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_773_, v___x_774_, v___x_778_, v___f_757_);
return v___x_779_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__16___boxed(lean_object* v___f_782_, lean_object* v_x_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__16(v___f_782_, v_x_783_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg(lean_object* v_x_787_, lean_object* v_y_788_, lean_object* v_prio_789_, lean_object* v_a_790_){
_start:
{
lean_object* v___f_792_; lean_object* v___f_793_; lean_object* v___f_794_; lean_object* v___f_795_; lean_object* v___x_796_; uint8_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___f_792_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_793_ = ((lean_object*)(l_Std_Async_ContextAsync_run___redArg___closed__0));
v___f_794_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__15___boxed), 9, 7);
lean_closure_set(v___f_794_, 0, v_x_787_);
lean_closure_set(v___f_794_, 1, v___f_793_);
lean_closure_set(v___f_794_, 2, v_y_788_);
lean_closure_set(v___f_794_, 3, v___f_793_);
lean_closure_set(v___f_794_, 4, v_prio_789_);
lean_closure_set(v___f_794_, 5, v___f_792_);
lean_closure_set(v___f_794_, 6, v___f_792_);
v___f_795_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__16___boxed), 3, 1);
lean_closure_set(v___f_795_, 0, v___f_794_);
v___x_796_ = lean_unsigned_to_nat(0u);
v___x_797_ = 0;
lean_inc_ref(v_a_790_);
v___x_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_798_, 0, v_a_790_);
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
v___x_800_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_796_, v___x_797_, v___x_799_, v___f_795_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___boxed(lean_object* v_x_801_, lean_object* v_y_802_, lean_object* v_prio_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Std_Async_ContextAsync_concurrently___redArg(v_x_801_, v_y_802_, v_prio_803_, v_a_804_);
lean_dec_ref(v_a_804_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently(lean_object* v_00_u03b1_807_, lean_object* v_00_u03b2_808_, lean_object* v_x_809_, lean_object* v_y_810_, lean_object* v_prio_811_, lean_object* v_a_812_){
_start:
{
lean_object* v___f_814_; lean_object* v___f_815_; lean_object* v___f_816_; lean_object* v___f_817_; lean_object* v___x_818_; uint8_t v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___f_814_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_815_ = ((lean_object*)(l_Std_Async_ContextAsync_run___redArg___closed__0));
v___f_816_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__15___boxed), 9, 7);
lean_closure_set(v___f_816_, 0, v_x_809_);
lean_closure_set(v___f_816_, 1, v___f_815_);
lean_closure_set(v___f_816_, 2, v_y_810_);
lean_closure_set(v___f_816_, 3, v___f_815_);
lean_closure_set(v___f_816_, 4, v_prio_811_);
lean_closure_set(v___f_816_, 5, v___f_814_);
lean_closure_set(v___f_816_, 6, v___f_814_);
v___f_817_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__16___boxed), 3, 1);
lean_closure_set(v___f_817_, 0, v___f_816_);
v___x_818_ = lean_unsigned_to_nat(0u);
v___x_819_ = 0;
lean_inc_ref(v_a_812_);
v___x_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_820_, 0, v_a_812_);
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
v___x_822_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_818_, v___x_819_, v___x_821_, v___f_817_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___boxed(lean_object* v_00_u03b1_823_, lean_object* v_00_u03b2_824_, lean_object* v_x_825_, lean_object* v_y_826_, lean_object* v_prio_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Std_Async_ContextAsync_concurrently(v_00_u03b1_823_, v_00_u03b2_824_, v_x_825_, v_y_826_, v_prio_827_, v_a_828_);
lean_dec_ref(v_a_828_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__0(lean_object* v_x_831_){
_start:
{
lean_object* v_fst_832_; 
v_fst_832_ = lean_ctor_get(v_x_831_, 0);
lean_inc(v_fst_832_);
return v_fst_832_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__0___boxed(lean_object* v_x_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__0(v_x_833_);
lean_dec_ref(v_x_833_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1(lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_838_, 0, v___y_835_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1___boxed(lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1(v___y_839_, v___y_840_);
lean_dec_ref(v___y_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6(lean_object* v_ctxAsync_843_, lean_object* v_a_844_, lean_object* v___f_845_){
_start:
{
lean_object* v___x_847_; uint8_t v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_847_ = lean_unsigned_to_nat(0u);
v___x_848_ = 0;
v___x_849_ = lean_apply_2(v_ctxAsync_843_, v_a_844_, lean_box(0));
v___x_850_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_847_, v___x_848_, v___x_849_, v___f_845_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6___boxed(lean_object* v_ctxAsync_851_, lean_object* v_a_852_, lean_object* v___f_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6(v_ctxAsync_851_, v_a_852_, v___f_853_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2(lean_object* v_a_856_, lean_object* v___x_857_, lean_object* v_a_x3f_858_){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_860_ = l_Std_CancellationContext_cancel(v_a_856_, v___x_857_);
v___x_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2___boxed(lean_object* v_a_863_, lean_object* v___x_864_, lean_object* v_a_x3f_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2(v_a_863_, v___x_864_, v_a_x3f_865_);
lean_dec(v_a_x3f_865_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4(lean_object* v_ctxAsync_868_, lean_object* v___f_869_, lean_object* v___f_870_, lean_object* v_prio_871_, lean_object* v___f_872_, lean_object* v_x_873_){
_start:
{
if (lean_obj_tag(v_x_873_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_883_; 
lean_dec_ref(v___f_872_);
lean_dec(v_prio_871_);
lean_dec(v___f_870_);
lean_dec_ref(v___f_869_);
lean_dec_ref(v_ctxAsync_868_);
v_a_875_ = lean_ctor_get(v_x_873_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v_x_873_);
if (v_isSharedCheck_883_ == 0)
{
v___x_877_ = v_x_873_;
v_isShared_878_ = v_isSharedCheck_883_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v_x_873_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_883_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_882_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; 
v___x_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
return v___x_881_;
}
}
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_901_; 
v_a_884_ = lean_ctor_get(v_x_873_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v_x_873_);
if (v_isSharedCheck_901_ == 0)
{
v___x_886_ = v_x_873_;
v_isShared_887_ = v_isSharedCheck_901_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v_x_873_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_901_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___f_888_; lean_object* v___x_889_; lean_object* v___f_890_; lean_object* v___f_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_898_; 
lean_inc(v_a_884_);
v___f_888_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6___boxed), 4, 3);
lean_closure_set(v___f_888_, 0, v_ctxAsync_868_);
lean_closure_set(v___f_888_, 1, v_a_884_);
lean_closure_set(v___f_888_, 2, v___f_869_);
v___x_889_ = lean_box(2);
v___f_890_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_890_, 0, v_a_884_);
lean_closure_set(v___f_890_, 1, v___x_889_);
v___f_891_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_891_, 0, v___f_870_);
lean_closure_set(v___f_891_, 1, v___f_888_);
lean_closure_set(v___f_891_, 2, v___f_890_);
v___x_892_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_892_, 0, lean_box(0));
lean_closure_set(v___x_892_, 1, v___f_891_);
v___x_893_ = lean_io_as_task(v___x_892_, v_prio_871_);
v___x_894_ = lean_unsigned_to_nat(0u);
v___x_895_ = 1;
v___x_896_ = lean_task_bind(v___x_893_, v___f_872_, v___x_894_, v___x_895_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v___x_896_);
v___x_898_ = v___x_886_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_896_);
v___x_898_ = v_reuseFailAlloc_900_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_899_; 
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
return v___x_899_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4___boxed(lean_object* v_ctxAsync_902_, lean_object* v___f_903_, lean_object* v___f_904_, lean_object* v_prio_905_, lean_object* v___f_906_, lean_object* v_x_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4(v_ctxAsync_902_, v___f_903_, v___f_904_, v_prio_905_, v___f_906_, v_x_907_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3(lean_object* v___f_910_, lean_object* v___f_911_, lean_object* v_prio_912_, lean_object* v___f_913_, lean_object* v_a_914_, lean_object* v_ctxAsync_915_, lean_object* v___y_916_){
_start:
{
lean_object* v___f_918_; lean_object* v___x_919_; uint8_t v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___f_918_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4___boxed), 7, 5);
lean_closure_set(v___f_918_, 0, v_ctxAsync_915_);
lean_closure_set(v___f_918_, 1, v___f_910_);
lean_closure_set(v___f_918_, 2, v___f_911_);
lean_closure_set(v___f_918_, 3, v_prio_912_);
lean_closure_set(v___f_918_, 4, v___f_913_);
v___x_919_ = lean_unsigned_to_nat(0u);
v___x_920_ = 0;
v___x_921_ = l_Std_CancellationContext_fork(v_a_914_);
v___x_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
v___x_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
v___x_924_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_919_, v___x_920_, v___x_923_, v___f_918_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3___boxed(lean_object* v___f_925_, lean_object* v___f_926_, lean_object* v_prio_927_, lean_object* v___f_928_, lean_object* v_a_929_, lean_object* v_ctxAsync_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3(v___f_925_, v___f_926_, v_prio_927_, v___f_928_, v_a_929_, v_ctxAsync_930_, v___y_931_);
lean_dec_ref(v___y_931_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5(lean_object* v_a_934_, lean_object* v___x_935_, lean_object* v_a_x3f_936_){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_938_ = l_Std_CancellationContext_cancel(v_a_934_, v___x_935_);
v___x_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5___boxed(lean_object* v_a_941_, lean_object* v___x_942_, lean_object* v_a_x3f_943_, lean_object* v___y_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5(v_a_941_, v___x_942_, v_a_x3f_943_);
lean_dec(v_a_x3f_943_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7(lean_object* v_a_946_, lean_object* v___f_947_, lean_object* v___x_948_, lean_object* v___f_949_, lean_object* v_a_950_, lean_object* v_x_951_){
_start:
{
if (lean_obj_tag(v_x_951_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_961_; 
lean_dec_ref(v___f_949_);
lean_dec_ref(v___x_948_);
lean_dec_ref(v___f_947_);
lean_dec_ref(v_a_946_);
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
lean_object* v_a_962_; lean_object* v___x_963_; lean_object* v___f_964_; lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; size_t v_sz_968_; size_t v___x_969_; lean_object* v___x_5454__overap_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___y_974_; 
v_a_962_ = lean_ctor_get(v_x_951_, 0);
lean_inc(v_a_962_);
lean_dec_ref_known(v_x_951_, 1);
v___x_963_ = lean_box(2);
v___f_964_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_964_, 0, v_a_946_);
lean_closure_set(v___f_964_, 1, v___x_963_);
v___x_965_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_965_, 0, lean_box(0));
lean_closure_set(v___x_965_, 1, lean_box(0));
lean_closure_set(v___x_965_, 2, lean_box(0));
lean_closure_set(v___x_965_, 3, v___f_947_);
v___x_966_ = lean_unsigned_to_nat(0u);
v___x_967_ = 0;
v_sz_968_ = lean_array_size(v_a_962_);
v___x_969_ = ((size_t)0ULL);
v___x_5454__overap_970_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_948_, v___f_949_, v_sz_968_, v___x_969_, v_a_962_);
lean_inc_ref(v_a_950_);
v___x_971_ = lean_apply_1(v___x_5454__overap_970_, v_a_950_);
v___x_972_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_971_, v___f_964_, v___x_966_, v___x_967_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_976_; 
lean_dec_ref(v___x_965_);
v_a_976_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_a_976_);
lean_dec_ref_known(v___x_972_, 1);
if (lean_obj_tag(v_a_976_) == 0)
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
v_a_977_ = lean_ctor_get(v_a_976_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v_a_976_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v_a_976_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v_a_976_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
v___y_974_ = v___x_982_;
goto v___jp_973_;
}
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_993_; 
v_a_985_ = lean_ctor_get(v_a_976_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v_a_976_);
if (v_isSharedCheck_993_ == 0)
{
v___x_987_ = v_a_976_;
v_isShared_988_ = v_isSharedCheck_993_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v_a_976_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_993_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v_fst_989_; lean_object* v___x_991_; 
v_fst_989_ = lean_ctor_get(v_a_985_, 0);
lean_inc(v_fst_989_);
lean_dec(v_a_985_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v_fst_989_);
v___x_991_ = v___x_987_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_fst_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
v___y_974_ = v___x_991_;
goto v___jp_973_;
}
}
}
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1002_; 
v_a_994_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_996_ = v___x_972_;
v_isShared_997_ = v_isSharedCheck_1002_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_972_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1002_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_998_ = lean_task_map(v___x_965_, v_a_994_, v___x_966_, v___x_967_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_998_);
v___x_1000_ = v___x_996_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
v___jp_973_:
{
lean_object* v___x_975_; 
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v___y_974_);
return v___x_975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7___boxed(lean_object* v_a_1003_, lean_object* v___f_1004_, lean_object* v___x_1005_, lean_object* v___f_1006_, lean_object* v_a_1007_, lean_object* v_x_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7(v_a_1003_, v___f_1004_, v___x_1005_, v___f_1006_, v_a_1007_, v_x_1008_);
lean_dec_ref(v_a_1007_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__8(lean_object* v___f_1011_, lean_object* v_prio_1012_, lean_object* v___f_1013_, lean_object* v___f_1014_, lean_object* v___x_1015_, lean_object* v___f_1016_, lean_object* v_a_1017_, lean_object* v_xs_1018_, lean_object* v_x_1019_){
_start:
{
if (lean_obj_tag(v_x_1019_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1029_; 
lean_dec_ref(v_xs_1018_);
lean_dec_ref(v___f_1016_);
lean_dec_ref(v___x_1015_);
lean_dec_ref(v___f_1014_);
lean_dec_ref(v___f_1013_);
lean_dec(v_prio_1012_);
lean_dec(v___f_1011_);
v_a_1021_ = lean_ctor_get(v_x_1019_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_x_1019_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1023_ = v_x_1019_;
v_isShared_1024_ = v_isSharedCheck_1029_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v_x_1019_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1029_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; 
v___x_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
return v___x_1027_;
}
}
}
else
{
lean_object* v_a_1030_; lean_object* v___f_1031_; lean_object* v___f_1032_; lean_object* v___f_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; size_t v_sz_1036_; size_t v___x_1037_; lean_object* v___x_5489__overap_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v_a_1030_ = lean_ctor_get(v_x_1019_, 0);
lean_inc_n(v_a_1030_, 3);
lean_dec_ref_known(v_x_1019_, 1);
v___f_1031_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1031_, 0, v_a_1030_);
v___f_1032_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3___boxed), 8, 5);
lean_closure_set(v___f_1032_, 0, v___f_1031_);
lean_closure_set(v___f_1032_, 1, v___f_1011_);
lean_closure_set(v___f_1032_, 2, v_prio_1012_);
lean_closure_set(v___f_1032_, 3, v___f_1013_);
lean_closure_set(v___f_1032_, 4, v_a_1030_);
lean_inc_ref_n(v_a_1017_, 2);
lean_inc_ref(v___x_1015_);
v___f_1033_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7___boxed), 7, 5);
lean_closure_set(v___f_1033_, 0, v_a_1030_);
lean_closure_set(v___f_1033_, 1, v___f_1014_);
lean_closure_set(v___f_1033_, 2, v___x_1015_);
lean_closure_set(v___f_1033_, 3, v___f_1016_);
lean_closure_set(v___f_1033_, 4, v_a_1017_);
v___x_1034_ = lean_unsigned_to_nat(0u);
v___x_1035_ = 0;
v_sz_1036_ = lean_array_size(v_xs_1018_);
v___x_1037_ = ((size_t)0ULL);
v___x_5489__overap_1038_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1015_, v___f_1032_, v_sz_1036_, v___x_1037_, v_xs_1018_);
v___x_1039_ = lean_apply_2(v___x_5489__overap_1038_, v_a_1017_, lean_box(0));
v___x_1040_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1034_, v___x_1035_, v___x_1039_, v___f_1033_);
return v___x_1040_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__8___boxed(lean_object* v___f_1041_, lean_object* v_prio_1042_, lean_object* v___f_1043_, lean_object* v___f_1044_, lean_object* v___x_1045_, lean_object* v___f_1046_, lean_object* v_a_1047_, lean_object* v_xs_1048_, lean_object* v_x_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__8(v___f_1041_, v_prio_1042_, v___f_1043_, v___f_1044_, v___x_1045_, v___f_1046_, v_a_1047_, v_xs_1048_, v_x_1049_);
lean_dec_ref(v_a_1047_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__9(lean_object* v___f_1052_, lean_object* v_x_1053_){
_start:
{
if (lean_obj_tag(v_x_1053_) == 0)
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1063_; 
lean_dec_ref(v___f_1052_);
v_a_1055_ = lean_ctor_get(v_x_1053_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_x_1053_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1057_ = v_x_1053_;
v_isShared_1058_ = v_isSharedCheck_1063_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v_x_1053_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1063_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1061_; 
v___x_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
return v___x_1061_;
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1076_; 
v_a_1064_ = lean_ctor_get(v_x_1053_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_x_1053_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1066_ = v_x_1053_;
v_isShared_1067_ = v_isSharedCheck_1076_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v_x_1053_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1076_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; uint8_t v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1068_ = lean_unsigned_to_nat(0u);
v___x_1069_ = 0;
v___x_1070_ = l_Std_CancellationContext_fork(v_a_1064_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1070_);
v___x_1072_ = v___x_1066_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
v___x_1074_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1068_, v___x_1069_, v___x_1073_, v___f_1052_);
return v___x_1074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__9___boxed(lean_object* v___f_1077_, lean_object* v_x_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__9(v___f_1077_, v_x_1078_);
return v_res_1080_;
}
}
static lean_object* _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2(void){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_1083_;
}
}
static lean_object* _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__3(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = lean_obj_once(&l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2, &l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2_once, _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2);
v___x_1085_ = l_ReaderT_instMonad___redArg(v___x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg(lean_object* v_xs_1086_, lean_object* v_prio_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v___f_1090_; lean_object* v___f_1091_; lean_object* v___f_1092_; lean_object* v___f_1093_; lean_object* v___x_1094_; lean_object* v___f_1095_; lean_object* v___f_1096_; lean_object* v___x_1097_; uint8_t v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___f_1090_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__0));
v___f_1091_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1));
v___f_1092_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_1093_ = ((lean_object*)(l_Std_Async_ContextAsync_run___redArg___closed__0));
v___x_1094_ = lean_obj_once(&l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__3, &l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__3_once, _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__3);
lean_inc_ref_n(v_a_1088_, 2);
v___f_1095_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__8___boxed), 10, 8);
lean_closure_set(v___f_1095_, 0, v___f_1093_);
lean_closure_set(v___f_1095_, 1, v_prio_1087_);
lean_closure_set(v___f_1095_, 2, v___f_1092_);
lean_closure_set(v___f_1095_, 3, v___f_1090_);
lean_closure_set(v___f_1095_, 4, v___x_1094_);
lean_closure_set(v___f_1095_, 5, v___f_1091_);
lean_closure_set(v___f_1095_, 6, v_a_1088_);
lean_closure_set(v___f_1095_, 7, v_xs_1086_);
v___f_1096_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_1096_, 0, v___f_1095_);
v___x_1097_ = lean_unsigned_to_nat(0u);
v___x_1098_ = 0;
v___x_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1099_, 0, v_a_1088_);
v___x_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
v___x_1101_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1097_, v___x_1098_, v___x_1100_, v___f_1096_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___boxed(lean_object* v_xs_1102_, lean_object* v_prio_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg(v_xs_1102_, v_prio_1103_, v_a_1104_);
lean_dec_ref(v_a_1104_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll(lean_object* v_00_u03b1_1107_, lean_object* v_xs_1108_, lean_object* v_prio_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v___f_1112_; lean_object* v___f_1113_; lean_object* v___f_1114_; lean_object* v___f_1115_; lean_object* v___x_1116_; lean_object* v___f_1117_; lean_object* v___f_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___f_1112_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__0));
v___f_1113_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1));
v___f_1114_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_1115_ = ((lean_object*)(l_Std_Async_ContextAsync_run___redArg___closed__0));
v___x_1116_ = lean_obj_once(&l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__3, &l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__3_once, _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__3);
lean_inc_ref_n(v_a_1110_, 2);
v___f_1117_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__8___boxed), 10, 8);
lean_closure_set(v___f_1117_, 0, v___f_1115_);
lean_closure_set(v___f_1117_, 1, v_prio_1109_);
lean_closure_set(v___f_1117_, 2, v___f_1114_);
lean_closure_set(v___f_1117_, 3, v___f_1112_);
lean_closure_set(v___f_1117_, 4, v___x_1116_);
lean_closure_set(v___f_1117_, 5, v___f_1113_);
lean_closure_set(v___f_1117_, 6, v_a_1110_);
lean_closure_set(v___f_1117_, 7, v_xs_1108_);
v___f_1118_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_1118_, 0, v___f_1117_);
v___x_1119_ = lean_unsigned_to_nat(0u);
v___x_1120_ = 0;
v___x_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1121_, 0, v_a_1110_);
v___x_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
v___x_1123_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1119_, v___x_1120_, v___x_1122_, v___f_1118_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___boxed(lean_object* v_00_u03b1_1124_, lean_object* v_xs_1125_, lean_object* v_prio_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Std_Async_ContextAsync_concurrentlyAll(v_00_u03b1_1124_, v_xs_1125_, v_prio_1126_, v_a_1127_);
lean_dec_ref(v_a_1127_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__1(lean_object* v_action_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = lean_apply_2(v_action_1130_, v_a_1131_, lean_box(0));
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__1___boxed(lean_object* v_action_1134_, lean_object* v_a_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Std_Async_ContextAsync_background___redArg___lam__1(v_action_1134_, v_a_1135_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__3(lean_object* v_action_1142_, lean_object* v___f_1143_, lean_object* v_prio_1144_, lean_object* v_x_1145_){
_start:
{
if (lean_obj_tag(v_x_1145_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1155_; 
lean_dec(v_prio_1144_);
lean_dec(v___f_1143_);
lean_dec_ref(v_action_1142_);
v_a_1147_ = lean_ctor_get(v_x_1145_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_x_1145_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1149_ = v_x_1145_;
v_isShared_1150_ = v_isSharedCheck_1155_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v_x_1145_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1155_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
lean_object* v___x_1153_; 
v___x_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
return v___x_1153_;
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v___f_1157_; lean_object* v___x_1158_; lean_object* v___f_1159_; lean_object* v___f_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v_a_1156_ = lean_ctor_get(v_x_1145_, 0);
lean_inc_n(v_a_1156_, 2);
lean_dec_ref_known(v_x_1145_, 1);
v___f_1157_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_background___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_1157_, 0, v_action_1142_);
lean_closure_set(v___f_1157_, 1, v_a_1156_);
v___x_1158_ = lean_box(2);
v___f_1159_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1159_, 0, v_a_1156_);
lean_closure_set(v___f_1159_, 1, v___x_1158_);
v___f_1160_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_1160_, 0, v___f_1143_);
lean_closure_set(v___f_1160_, 1, v___f_1157_);
lean_closure_set(v___f_1160_, 2, v___f_1159_);
v___x_1161_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1161_, 0, lean_box(0));
lean_closure_set(v___x_1161_, 1, v___f_1160_);
v___x_1162_ = lean_io_as_task(v___x_1161_, v_prio_1144_);
lean_dec_ref(v___x_1162_);
v___x_1163_ = ((lean_object*)(l_Std_Async_ContextAsync_background___redArg___lam__3___closed__1));
return v___x_1163_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__3___boxed(lean_object* v_action_1164_, lean_object* v___f_1165_, lean_object* v_prio_1166_, lean_object* v_x_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Std_Async_ContextAsync_background___redArg___lam__3(v_action_1164_, v___f_1165_, v_prio_1166_, v_x_1167_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__0(lean_object* v___f_1170_, lean_object* v_x_1171_){
_start:
{
if (lean_obj_tag(v_x_1171_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1181_; 
lean_dec_ref(v___f_1170_);
v_a_1173_ = lean_ctor_get(v_x_1171_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_x_1171_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1175_ = v_x_1171_;
v_isShared_1176_ = v_isSharedCheck_1181_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v_x_1171_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1181_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
return v___x_1179_;
}
}
}
else
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1194_; 
v_a_1182_ = lean_ctor_get(v_x_1171_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_x_1171_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1184_ = v_x_1171_;
v_isShared_1185_ = v_isSharedCheck_1194_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v_x_1171_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1194_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; uint8_t v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1186_ = lean_unsigned_to_nat(0u);
v___x_1187_ = 0;
v___x_1188_ = l_Std_CancellationContext_fork(v_a_1182_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1188_);
v___x_1190_ = v___x_1184_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1190_);
v___x_1192_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1186_, v___x_1187_, v___x_1191_, v___f_1170_);
return v___x_1192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__0___boxed(lean_object* v___f_1195_, lean_object* v_x_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Std_Async_ContextAsync_background___redArg___lam__0(v___f_1195_, v_x_1196_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg(lean_object* v_action_1199_, lean_object* v_prio_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v___f_1203_; lean_object* v___f_1204_; lean_object* v___f_1205_; lean_object* v___x_1206_; uint8_t v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___f_1203_ = ((lean_object*)(l_Std_Async_ContextAsync_run___redArg___closed__0));
v___f_1204_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_background___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_1204_, 0, v_action_1199_);
lean_closure_set(v___f_1204_, 1, v___f_1203_);
lean_closure_set(v___f_1204_, 2, v_prio_1200_);
v___f_1205_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_background___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1205_, 0, v___f_1204_);
v___x_1206_ = lean_unsigned_to_nat(0u);
v___x_1207_ = 0;
lean_inc_ref(v_a_1201_);
v___x_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1208_, 0, v_a_1201_);
v___x_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
v___x_1210_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1206_, v___x_1207_, v___x_1209_, v___f_1205_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___boxed(lean_object* v_action_1211_, lean_object* v_prio_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Std_Async_ContextAsync_background___redArg(v_action_1211_, v_prio_1212_, v_a_1213_);
lean_dec_ref(v_a_1213_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background(lean_object* v_00_u03b1_1216_, lean_object* v_action_1217_, lean_object* v_prio_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v___f_1221_; lean_object* v___f_1222_; lean_object* v___f_1223_; lean_object* v___x_1224_; uint8_t v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___f_1221_ = ((lean_object*)(l_Std_Async_ContextAsync_run___redArg___closed__0));
v___f_1222_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_background___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_1222_, 0, v_action_1217_);
lean_closure_set(v___f_1222_, 1, v___f_1221_);
lean_closure_set(v___f_1222_, 2, v_prio_1218_);
v___f_1223_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_background___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1223_, 0, v___f_1222_);
v___x_1224_ = lean_unsigned_to_nat(0u);
v___x_1225_ = 0;
lean_inc_ref(v_a_1219_);
v___x_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1226_, 0, v_a_1219_);
v___x_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
v___x_1228_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1224_, v___x_1225_, v___x_1227_, v___f_1223_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___boxed(lean_object* v_00_u03b1_1229_, lean_object* v_action_1230_, lean_object* v_prio_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Std_Async_ContextAsync_background(v_00_u03b1_1229_, v_action_1230_, v_prio_1231_, v_a_1232_);
lean_dec_ref(v_a_1232_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg___lam__1(lean_object* v_action_1235_, lean_object* v_prio_1236_, lean_object* v_x_1237_){
_start:
{
if (lean_obj_tag(v_x_1237_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1247_; 
lean_dec(v_prio_1236_);
lean_dec_ref(v_action_1235_);
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
lean_object* v_a_1248_; lean_object* v___f_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v_a_1248_ = lean_ctor_get(v_x_1237_, 0);
lean_inc(v_a_1248_);
lean_dec_ref_known(v_x_1237_, 1);
v___f_1249_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_background___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_1249_, 0, v_action_1235_);
lean_closure_set(v___f_1249_, 1, v_a_1248_);
v___x_1250_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1250_, 0, lean_box(0));
lean_closure_set(v___x_1250_, 1, v___f_1249_);
v___x_1251_ = lean_io_as_task(v___x_1250_, v_prio_1236_);
lean_dec_ref(v___x_1251_);
v___x_1252_ = ((lean_object*)(l_Std_Async_ContextAsync_background___redArg___lam__3___closed__1));
return v___x_1252_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg___lam__1___boxed(lean_object* v_action_1253_, lean_object* v_prio_1254_, lean_object* v_x_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Std_Async_ContextAsync_disown___redArg___lam__1(v_action_1253_, v_prio_1254_, v_x_1255_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg(lean_object* v_action_1258_, lean_object* v_prio_1259_){
_start:
{
lean_object* v___f_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___f_1261_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_disown___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1261_, 0, v_action_1258_);
lean_closure_set(v___f_1261_, 1, v_prio_1259_);
v___x_1262_ = lean_unsigned_to_nat(0u);
v___x_1263_ = 0;
v___x_1264_ = l_Std_CancellationContext_new();
v___x_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
v___x_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
v___x_1267_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1262_, v___x_1263_, v___x_1266_, v___f_1261_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg___boxed(lean_object* v_action_1268_, lean_object* v_prio_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Std_Async_ContextAsync_disown___redArg(v_action_1268_, v_prio_1269_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown(lean_object* v_00_u03b1_1272_, lean_object* v_action_1273_, lean_object* v_prio_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v___f_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___f_1277_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_disown___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1277_, 0, v_action_1273_);
lean_closure_set(v___f_1277_, 1, v_prio_1274_);
v___x_1278_ = lean_unsigned_to_nat(0u);
v___x_1279_ = 0;
v___x_1280_ = l_Std_CancellationContext_new();
v___x_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
v___x_1283_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1278_, v___x_1279_, v___x_1282_, v___f_1277_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___boxed(lean_object* v_00_u03b1_1284_, lean_object* v_action_1285_, lean_object* v_prio_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Std_Async_ContextAsync_disown(v_00_u03b1_1284_, v_action_1285_, v_prio_1286_, v_a_1287_);
lean_dec_ref(v_a_1287_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__1(lean_object* v_a_1290_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1291_, 0, v_a_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__0(lean_object* v_a_1292_, lean_object* v_x_1293_){
_start:
{
if (lean_obj_tag(v_x_1293_) == 0)
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1303_; 
lean_dec_ref(v_a_1292_);
v_a_1295_ = lean_ctor_get(v_x_1293_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v_x_1293_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1297_ = v_x_1293_;
v_isShared_1298_ = v_isSharedCheck_1303_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v_x_1293_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1303_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___x_1301_; 
v___x_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
return v___x_1301_;
}
}
}
else
{
lean_object* v___x_1304_; 
lean_dec_ref_known(v_x_1293_, 1);
v___x_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1304_, 0, v_a_1292_);
return v___x_1304_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__0___boxed(lean_object* v_a_1305_, lean_object* v_x_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__0(v_a_1305_, v_x_1306_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__2(lean_object* v_a_1309_, lean_object* v_x_1310_){
_start:
{
if (lean_obj_tag(v_x_1310_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1320_; 
lean_dec_ref(v_a_1309_);
v_a_1312_ = lean_ctor_get(v_x_1310_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_x_1310_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1314_ = v_x_1310_;
v_isShared_1315_ = v_isSharedCheck_1320_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v_x_1310_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1320_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1318_; 
v___x_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
return v___x_1318_;
}
}
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1335_; 
v_a_1321_ = lean_ctor_get(v_x_1310_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_x_1310_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1323_ = v_x_1310_;
v_isShared_1324_ = v_isSharedCheck_1335_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v_x_1310_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1335_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___f_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___f_1325_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1325_, 0, v_a_1321_);
v___x_1326_ = lean_box(2);
v___x_1327_ = lean_unsigned_to_nat(0u);
v___x_1328_ = 0;
v___x_1329_ = l_Std_CancellationContext_cancel(v_a_1309_, v___x_1326_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1329_);
v___x_1331_ = v___x_1323_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
v___x_1333_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1327_, v___x_1328_, v___x_1332_, v___f_1325_);
return v___x_1333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__2___boxed(lean_object* v_a_1336_, lean_object* v_x_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__2(v_a_1336_, v_x_1337_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__3(lean_object* v_a_1340_, lean_object* v_x_1341_){
_start:
{
if (lean_obj_tag(v_x_1341_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1351_; 
v_a_1343_ = lean_ctor_get(v_x_1341_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_x_1341_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1345_ = v_x_1341_;
v_isShared_1346_ = v_isSharedCheck_1351_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v_x_1341_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1351_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1349_; 
v___x_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
return v___x_1349_;
}
}
}
else
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1352_ = lean_io_promise_resolve(v_x_1341_, v_a_1340_);
v___x_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
v___x_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
return v___x_1354_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__3___boxed(lean_object* v_a_1355_, lean_object* v_x_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__3(v_a_1355_, v_x_1356_);
lean_dec(v_a_1355_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__4(lean_object* v_a_1359_, lean_object* v_x_1360_){
_start:
{
if (lean_obj_tag(v_x_1360_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1371_; 
v_a_1362_ = lean_ctor_get(v_x_1360_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_x_1360_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1364_ = v_x_1360_;
v_isShared_1365_ = v_isSharedCheck_1371_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v_x_1360_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1371_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_io_promise_resolve(v___x_1367_, v_a_1359_);
v___x_1369_ = ((lean_object*)(l_Std_Async_ContextAsync_background___redArg___lam__3___closed__1));
return v___x_1369_;
}
}
}
else
{
lean_object* v___x_1372_; 
v___x_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1372_, 0, v_x_1360_);
return v___x_1372_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__4___boxed(lean_object* v_a_1373_, lean_object* v_x_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__4(v_a_1373_, v_x_1374_);
lean_dec(v_a_1373_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__5(lean_object* v_a_1377_, lean_object* v___f_1378_, lean_object* v___f_1379_){
_start:
{
lean_object* v___x_1381_; uint8_t v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1381_ = lean_unsigned_to_nat(0u);
v___x_1382_ = 0;
v___x_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1383_, 0, v_a_1377_);
v___x_1384_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1381_, v___x_1382_, v___x_1383_, v___f_1378_);
v___x_1385_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1381_, v___x_1382_, v___x_1384_, v___f_1379_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__5___boxed(lean_object* v_a_1386_, lean_object* v___f_1387_, lean_object* v___f_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__5(v_a_1386_, v___f_1387_, v___f_1388_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__6(lean_object* v___f_1391_, lean_object* v___f_1392_, lean_object* v_prio_1393_, lean_object* v_x_1394_){
_start:
{
if (lean_obj_tag(v_x_1394_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1404_; 
lean_dec(v_prio_1393_);
lean_dec_ref(v___f_1392_);
lean_dec_ref(v___f_1391_);
v_a_1396_ = lean_ctor_get(v_x_1394_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_x_1394_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1398_ = v_x_1394_;
v_isShared_1399_ = v_isSharedCheck_1404_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v_x_1394_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1404_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
lean_object* v___x_1402_; 
v___x_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
return v___x_1402_;
}
}
}
else
{
lean_object* v_a_1405_; lean_object* v___f_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v_a_1405_ = lean_ctor_get(v_x_1394_, 0);
lean_inc(v_a_1405_);
lean_dec_ref_known(v_x_1394_, 1);
v___f_1406_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_1406_, 0, v_a_1405_);
lean_closure_set(v___f_1406_, 1, v___f_1391_);
lean_closure_set(v___f_1406_, 2, v___f_1392_);
v___x_1407_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1407_, 0, lean_box(0));
lean_closure_set(v___x_1407_, 1, v___f_1406_);
v___x_1408_ = lean_io_as_task(v___x_1407_, v_prio_1393_);
lean_dec_ref(v___x_1408_);
v___x_1409_ = ((lean_object*)(l_Std_Async_ContextAsync_background___redArg___lam__3___closed__1));
return v___x_1409_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__6___boxed(lean_object* v___f_1410_, lean_object* v___f_1411_, lean_object* v_prio_1412_, lean_object* v_x_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__6(v___f_1410_, v___f_1411_, v_prio_1412_, v_x_1413_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__7(lean_object* v_x_1416_, lean_object* v_a_1417_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_apply_2(v_x_1416_, v_a_1417_, lean_box(0));
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__7___boxed(lean_object* v_x_1420_, lean_object* v_a_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__7(v_x_1420_, v_a_1421_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__8(lean_object* v_x_1424_, lean_object* v_prio_1425_, lean_object* v___f_1426_, lean_object* v___f_1427_, lean_object* v_x_1428_){
_start:
{
if (lean_obj_tag(v_x_1428_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1438_; 
lean_dec_ref(v___f_1427_);
lean_dec_ref(v___f_1426_);
lean_dec(v_prio_1425_);
lean_dec_ref(v_x_1424_);
v_a_1430_ = lean_ctor_get(v_x_1428_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_x_1428_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1432_ = v_x_1428_;
v_isShared_1433_ = v_isSharedCheck_1438_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v_x_1428_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1438_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
return v___x_1436_;
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1455_; 
v_a_1439_ = lean_ctor_get(v_x_1428_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_x_1428_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1441_ = v_x_1428_;
v_isShared_1442_ = v_isSharedCheck_1455_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v_x_1428_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1455_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___f_1443_; lean_object* v___x_1444_; uint8_t v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___f_1443_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_1443_, 0, v_x_1424_);
lean_closure_set(v___f_1443_, 1, v_a_1439_);
v___x_1444_ = lean_unsigned_to_nat(0u);
v___x_1445_ = 0;
v___x_1446_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1446_, 0, lean_box(0));
lean_closure_set(v___x_1446_, 1, v___f_1443_);
v___x_1447_ = lean_io_as_task(v___x_1446_, v_prio_1425_);
v___x_1448_ = 1;
v___x_1449_ = lean_task_bind(v___x_1447_, v___f_1426_, v___x_1444_, v___x_1448_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v___x_1449_);
v___x_1451_ = v___x_1441_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
v___x_1453_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1444_, v___x_1445_, v___x_1452_, v___f_1427_);
return v___x_1453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__8___boxed(lean_object* v_x_1456_, lean_object* v_prio_1457_, lean_object* v___f_1458_, lean_object* v___f_1459_, lean_object* v_x_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__8(v_x_1456_, v_prio_1457_, v___f_1458_, v___f_1459_, v_x_1460_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__9(lean_object* v_prio_1463_, lean_object* v___f_1464_, lean_object* v___f_1465_, lean_object* v_a_1466_, lean_object* v_x_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v___f_1470_; lean_object* v___x_1471_; uint8_t v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___f_1470_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_1470_, 0, v_x_1467_);
lean_closure_set(v___f_1470_, 1, v_prio_1463_);
lean_closure_set(v___f_1470_, 2, v___f_1464_);
lean_closure_set(v___f_1470_, 3, v___f_1465_);
v___x_1471_ = lean_unsigned_to_nat(0u);
v___x_1472_ = 0;
v___x_1473_ = l_Std_CancellationContext_fork(v_a_1466_);
v___x_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
v___x_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1474_);
v___x_1476_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1471_, v___x_1472_, v___x_1475_, v___f_1470_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__9___boxed(lean_object* v_prio_1477_, lean_object* v___f_1478_, lean_object* v___f_1479_, lean_object* v_a_1480_, lean_object* v_x_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__9(v_prio_1477_, v___f_1478_, v___f_1479_, v_a_1480_, v_x_1481_, v___y_1482_);
lean_dec_ref(v___y_1482_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__10(lean_object* v_a_1485_, lean_object* v___f_1486_, lean_object* v___f_1487_, lean_object* v_x_1488_){
_start:
{
if (lean_obj_tag(v_x_1488_) == 0)
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1498_; 
lean_dec_ref(v___f_1487_);
lean_dec_ref(v___f_1486_);
v_a_1490_ = lean_ctor_get(v_x_1488_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v_x_1488_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1492_ = v_x_1488_;
v_isShared_1493_ = v_isSharedCheck_1498_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v_x_1488_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1498_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
return v___x_1496_;
}
}
}
else
{
lean_object* v___x_1499_; uint8_t v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
lean_dec_ref_known(v_x_1488_, 1);
v___x_1499_ = lean_unsigned_to_nat(0u);
v___x_1500_ = 0;
v___x_1501_ = l_IO_Promise_result_x21___redArg(v_a_1485_);
v___x_1502_ = lean_task_map(v___f_1486_, v___x_1501_, v___x_1499_, v___x_1500_);
v___x_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1502_);
v___x_1504_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1499_, v___x_1500_, v___x_1503_, v___f_1487_);
return v___x_1504_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__10___boxed(lean_object* v_a_1505_, lean_object* v___f_1506_, lean_object* v___f_1507_, lean_object* v_x_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__10(v_a_1505_, v___f_1506_, v___f_1507_, v_x_1508_);
lean_dec(v_a_1505_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__11(lean_object* v_prio_1511_, lean_object* v___f_1512_, lean_object* v_a_1513_, lean_object* v___f_1514_, lean_object* v___f_1515_, lean_object* v_inst_1516_, lean_object* v_xs_1517_, lean_object* v_a_1518_, lean_object* v_x_1519_){
_start:
{
if (lean_obj_tag(v_x_1519_) == 0)
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1529_; 
lean_dec(v_xs_1517_);
lean_dec_ref(v_inst_1516_);
lean_dec_ref(v___f_1515_);
lean_dec_ref(v___f_1514_);
lean_dec_ref(v_a_1513_);
lean_dec_ref(v___f_1512_);
lean_dec(v_prio_1511_);
v_a_1521_ = lean_ctor_get(v_x_1519_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v_x_1519_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1523_ = v_x_1519_;
v_isShared_1524_ = v_isSharedCheck_1529_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v_x_1519_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1529_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1527_; 
v___x_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
return v___x_1527_;
}
}
}
else
{
lean_object* v_a_1530_; lean_object* v___f_1531_; lean_object* v___f_1532_; lean_object* v___f_1533_; lean_object* v___f_1534_; lean_object* v___f_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v_a_1530_ = lean_ctor_get(v_x_1519_, 0);
lean_inc_n(v_a_1530_, 3);
lean_dec_ref_known(v_x_1519_, 1);
v___f_1531_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1531_, 0, v_a_1530_);
v___f_1532_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1532_, 0, v_a_1530_);
lean_inc(v_prio_1511_);
v___f_1533_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__6___boxed), 5, 3);
lean_closure_set(v___f_1533_, 0, v___f_1531_);
lean_closure_set(v___f_1533_, 1, v___f_1532_);
lean_closure_set(v___f_1533_, 2, v_prio_1511_);
v___f_1534_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__9___boxed), 7, 4);
lean_closure_set(v___f_1534_, 0, v_prio_1511_);
lean_closure_set(v___f_1534_, 1, v___f_1512_);
lean_closure_set(v___f_1534_, 2, v___f_1533_);
lean_closure_set(v___f_1534_, 3, v_a_1513_);
v___f_1535_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__10___boxed), 5, 3);
lean_closure_set(v___f_1535_, 0, v_a_1530_);
lean_closure_set(v___f_1535_, 1, v___f_1514_);
lean_closure_set(v___f_1535_, 2, v___f_1515_);
v___x_1536_ = lean_unsigned_to_nat(0u);
v___x_1537_ = 0;
lean_inc_ref(v_a_1518_);
v___x_1538_ = lean_apply_4(v_inst_1516_, v_xs_1517_, v___f_1534_, v_a_1518_, lean_box(0));
v___x_1539_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1536_, v___x_1537_, v___x_1538_, v___f_1535_);
return v___x_1539_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__11___boxed(lean_object* v_prio_1540_, lean_object* v___f_1541_, lean_object* v_a_1542_, lean_object* v___f_1543_, lean_object* v___f_1544_, lean_object* v_inst_1545_, lean_object* v_xs_1546_, lean_object* v_a_1547_, lean_object* v_x_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__11(v_prio_1540_, v___f_1541_, v_a_1542_, v___f_1543_, v___f_1544_, v_inst_1545_, v_xs_1546_, v_a_1547_, v_x_1548_);
lean_dec_ref(v_a_1547_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__12(lean_object* v_prio_1551_, lean_object* v___f_1552_, lean_object* v___f_1553_, lean_object* v_inst_1554_, lean_object* v_xs_1555_, lean_object* v_a_1556_, lean_object* v_x_1557_){
_start:
{
if (lean_obj_tag(v_x_1557_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1567_; 
lean_dec(v_xs_1555_);
lean_dec_ref(v_inst_1554_);
lean_dec_ref(v___f_1553_);
lean_dec_ref(v___f_1552_);
lean_dec(v_prio_1551_);
v_a_1559_ = lean_ctor_get(v_x_1557_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v_x_1557_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1561_ = v_x_1557_;
v_isShared_1562_ = v_isSharedCheck_1567_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v_x_1557_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1567_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
return v___x_1565_;
}
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1582_; 
v_a_1568_ = lean_ctor_get(v_x_1557_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_x_1557_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1570_ = v_x_1557_;
v_isShared_1571_ = v_isSharedCheck_1582_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v_x_1557_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1582_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___f_1572_; lean_object* v___f_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1578_; 
lean_inc(v_a_1568_);
v___f_1572_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1572_, 0, v_a_1568_);
lean_inc_ref(v_a_1556_);
v___f_1573_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__11___boxed), 10, 8);
lean_closure_set(v___f_1573_, 0, v_prio_1551_);
lean_closure_set(v___f_1573_, 1, v___f_1552_);
lean_closure_set(v___f_1573_, 2, v_a_1568_);
lean_closure_set(v___f_1573_, 3, v___f_1553_);
lean_closure_set(v___f_1573_, 4, v___f_1572_);
lean_closure_set(v___f_1573_, 5, v_inst_1554_);
lean_closure_set(v___f_1573_, 6, v_xs_1555_);
lean_closure_set(v___f_1573_, 7, v_a_1556_);
v___x_1574_ = lean_unsigned_to_nat(0u);
v___x_1575_ = 0;
v___x_1576_ = lean_io_promise_new();
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v___x_1576_);
v___x_1578_ = v___x_1570_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
v___x_1580_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1574_, v___x_1575_, v___x_1579_, v___f_1573_);
return v___x_1580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__12___boxed(lean_object* v_prio_1583_, lean_object* v___f_1584_, lean_object* v___f_1585_, lean_object* v_inst_1586_, lean_object* v_xs_1587_, lean_object* v_a_1588_, lean_object* v_x_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__12(v_prio_1583_, v___f_1584_, v___f_1585_, v_inst_1586_, v_xs_1587_, v_a_1588_, v_x_1589_);
lean_dec_ref(v_a_1588_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__13(lean_object* v___f_1592_, lean_object* v_x_1593_){
_start:
{
if (lean_obj_tag(v_x_1593_) == 0)
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1603_; 
lean_dec_ref(v___f_1592_);
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
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1616_; 
v_a_1604_ = lean_ctor_get(v_x_1593_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_x_1593_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1606_ = v_x_1593_;
v_isShared_1607_ = v_isSharedCheck_1616_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v_x_1593_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1616_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1608_; uint8_t v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1612_; 
v___x_1608_ = lean_unsigned_to_nat(0u);
v___x_1609_ = 0;
v___x_1610_ = l_Std_CancellationContext_fork(v_a_1604_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v___x_1610_);
v___x_1612_ = v___x_1606_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1610_);
v___x_1612_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
v___x_1614_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1608_, v___x_1609_, v___x_1613_, v___f_1592_);
return v___x_1614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__13___boxed(lean_object* v___f_1617_, lean_object* v_x_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__13(v___f_1617_, v_x_1618_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg(lean_object* v_inst_1622_, lean_object* v_xs_1623_, lean_object* v_prio_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v___f_1627_; lean_object* v___f_1628_; lean_object* v___f_1629_; lean_object* v___f_1630_; lean_object* v___x_1631_; uint8_t v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___f_1627_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_1628_ = ((lean_object*)(l_Std_Async_ContextAsync_raceAll___redArg___closed__0));
lean_inc_ref_n(v_a_1625_, 2);
v___f_1629_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__12___boxed), 8, 6);
lean_closure_set(v___f_1629_, 0, v_prio_1624_);
lean_closure_set(v___f_1629_, 1, v___f_1627_);
lean_closure_set(v___f_1629_, 2, v___f_1628_);
lean_closure_set(v___f_1629_, 3, v_inst_1622_);
lean_closure_set(v___f_1629_, 4, v_xs_1623_);
lean_closure_set(v___f_1629_, 5, v_a_1625_);
v___f_1630_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__13___boxed), 3, 1);
lean_closure_set(v___f_1630_, 0, v___f_1629_);
v___x_1631_ = lean_unsigned_to_nat(0u);
v___x_1632_ = 0;
v___x_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1633_, 0, v_a_1625_);
v___x_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
v___x_1635_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1631_, v___x_1632_, v___x_1634_, v___f_1630_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___boxed(lean_object* v_inst_1636_, lean_object* v_xs_1637_, lean_object* v_prio_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Std_Async_ContextAsync_raceAll___redArg(v_inst_1636_, v_xs_1637_, v_prio_1638_, v_a_1639_);
lean_dec_ref(v_a_1639_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll(lean_object* v_c_1642_, lean_object* v_00_u03b1_1643_, lean_object* v_inst_1644_, lean_object* v_xs_1645_, lean_object* v_prio_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Std_Async_ContextAsync_raceAll___redArg(v_inst_1644_, v_xs_1645_, v_prio_1646_, v_a_1647_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___boxed(lean_object* v_c_1650_, lean_object* v_00_u03b1_1651_, lean_object* v_inst_1652_, lean_object* v_xs_1653_, lean_object* v_prio_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Std_Async_ContextAsync_raceAll(v_c_1650_, v_00_u03b1_1651_, v_inst_1652_, v_xs_1653_, v_prio_1654_, v_a_1655_);
lean_dec_ref(v_a_1655_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg___lam__3(lean_object* v___f_1658_, lean_object* v___x_1659_, lean_object* v___f_1660_){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; uint8_t v___x_1664_; lean_object* v___x_1665_; lean_object* v___y_1667_; 
v___x_1662_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_1662_, 0, lean_box(0));
lean_closure_set(v___x_1662_, 1, lean_box(0));
lean_closure_set(v___x_1662_, 2, lean_box(0));
lean_closure_set(v___x_1662_, 3, v___f_1658_);
v___x_1663_ = lean_unsigned_to_nat(0u);
v___x_1664_ = 0;
v___x_1665_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_1659_, v___f_1660_, v___x_1663_, v___x_1664_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1669_; 
lean_dec_ref(v___x_1662_);
v_a_1669_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_a_1669_);
lean_dec_ref_known(v___x_1665_, 1);
if (lean_obj_tag(v_a_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
v_a_1670_ = lean_ctor_get(v_a_1669_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_a_1669_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v_a_1669_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v_a_1669_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
v___y_1667_ = v___x_1675_;
goto v___jp_1666_;
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1686_; 
v_a_1678_ = lean_ctor_get(v_a_1669_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_a_1669_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1680_ = v_a_1669_;
v_isShared_1681_ = v_isSharedCheck_1686_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v_a_1669_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1686_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v_fst_1682_; lean_object* v___x_1684_; 
v_fst_1682_ = lean_ctor_get(v_a_1678_, 0);
lean_inc(v_fst_1682_);
lean_dec(v_a_1678_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v_fst_1682_);
v___x_1684_ = v___x_1680_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_fst_1682_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
v___y_1667_ = v___x_1684_;
goto v___jp_1666_;
}
}
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1695_; 
v_a_1687_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1689_ = v___x_1665_;
v_isShared_1690_ = v_isSharedCheck_1695_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1665_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1695_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1691_; lean_object* v___x_1693_; 
v___x_1691_ = lean_task_map(v___x_1662_, v_a_1687_, v___x_1663_, v___x_1664_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 0, v___x_1691_);
v___x_1693_ = v___x_1689_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1691_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
v___jp_1666_:
{
lean_object* v___x_1668_; 
v___x_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1668_, 0, v___y_1667_);
return v___x_1668_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg___lam__3___boxed(lean_object* v___f_1696_, lean_object* v___x_1697_, lean_object* v___f_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Std_Async_ContextAsync_async___redArg___lam__3(v___f_1696_, v___x_1697_, v___f_1698_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg___lam__0(lean_object* v_x_1701_, lean_object* v___f_1702_, lean_object* v_prio_1703_, lean_object* v___f_1704_, lean_object* v_x_1705_){
_start:
{
if (lean_obj_tag(v_x_1705_) == 0)
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1715_; 
lean_dec_ref(v___f_1704_);
lean_dec(v_prio_1703_);
lean_dec(v___f_1702_);
lean_dec_ref(v_x_1701_);
v_a_1707_ = lean_ctor_get(v_x_1705_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v_x_1705_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1709_ = v_x_1705_;
v_isShared_1710_ = v_isSharedCheck_1715_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v_x_1705_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1715_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
lean_object* v___x_1713_; 
v___x_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
return v___x_1713_;
}
}
}
else
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1733_; 
v_a_1716_ = lean_ctor_get(v_x_1705_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_x_1705_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1718_ = v_x_1705_;
v_isShared_1719_ = v_isSharedCheck_1733_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v_x_1705_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1733_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___f_1722_; lean_object* v___f_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; uint8_t v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1730_; 
lean_inc(v_a_1716_);
v___x_1720_ = lean_apply_1(v_x_1701_, v_a_1716_);
v___x_1721_ = lean_box(2);
v___f_1722_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_run___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1722_, 0, v_a_1716_);
lean_closure_set(v___f_1722_, 1, v___x_1721_);
v___f_1723_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_async___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_1723_, 0, v___f_1702_);
lean_closure_set(v___f_1723_, 1, v___x_1720_);
lean_closure_set(v___f_1723_, 2, v___f_1722_);
v___x_1724_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1724_, 0, lean_box(0));
lean_closure_set(v___x_1724_, 1, v___f_1723_);
v___x_1725_ = lean_io_as_task(v___x_1724_, v_prio_1703_);
v___x_1726_ = lean_unsigned_to_nat(0u);
v___x_1727_ = 1;
v___x_1728_ = lean_task_bind(v___x_1725_, v___f_1704_, v___x_1726_, v___x_1727_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1728_);
v___x_1730_ = v___x_1718_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1728_);
v___x_1730_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
return v___x_1731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg___lam__0___boxed(lean_object* v_x_1734_, lean_object* v___f_1735_, lean_object* v_prio_1736_, lean_object* v___f_1737_, lean_object* v_x_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Std_Async_ContextAsync_async___redArg___lam__0(v_x_1734_, v___f_1735_, v_prio_1736_, v___f_1737_, v_x_1738_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg(lean_object* v_x_1741_, lean_object* v_prio_1742_, lean_object* v_ctx_1743_){
_start:
{
lean_object* v___f_1745_; lean_object* v___f_1746_; lean_object* v___f_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___f_1745_ = ((lean_object*)(l_Std_Async_ContextAsync_run___redArg___closed__0));
v___f_1746_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_1747_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_async___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1747_, 0, v_x_1741_);
lean_closure_set(v___f_1747_, 1, v___f_1745_);
lean_closure_set(v___f_1747_, 2, v_prio_1742_);
lean_closure_set(v___f_1747_, 3, v___f_1746_);
v___x_1748_ = lean_unsigned_to_nat(0u);
v___x_1749_ = 0;
lean_inc_ref(v_ctx_1743_);
v___x_1750_ = l_Std_CancellationContext_fork(v_ctx_1743_);
v___x_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
v___x_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1751_);
v___x_1753_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1748_, v___x_1749_, v___x_1752_, v___f_1747_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg___boxed(lean_object* v_x_1754_, lean_object* v_prio_1755_, lean_object* v_ctx_1756_, lean_object* v_a_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Std_Async_ContextAsync_async___redArg(v_x_1754_, v_prio_1755_, v_ctx_1756_);
lean_dec_ref(v_ctx_1756_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async(lean_object* v_00_u03b1_1759_, lean_object* v_x_1760_, lean_object* v_prio_1761_, lean_object* v_ctx_1762_){
_start:
{
lean_object* v___f_1764_; lean_object* v___f_1765_; lean_object* v___f_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___f_1764_ = ((lean_object*)(l_Std_Async_ContextAsync_run___redArg___closed__0));
v___f_1765_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_1766_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_async___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1766_, 0, v_x_1760_);
lean_closure_set(v___f_1766_, 1, v___f_1764_);
lean_closure_set(v___f_1766_, 2, v_prio_1761_);
lean_closure_set(v___f_1766_, 3, v___f_1765_);
v___x_1767_ = lean_unsigned_to_nat(0u);
v___x_1768_ = 0;
lean_inc_ref(v_ctx_1762_);
v___x_1769_ = l_Std_CancellationContext_fork(v_ctx_1762_);
v___x_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
v___x_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
v___x_1772_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1767_, v___x_1768_, v___x_1771_, v___f_1766_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___boxed(lean_object* v_00_u03b1_1773_, lean_object* v_x_1774_, lean_object* v_prio_1775_, lean_object* v_ctx_1776_, lean_object* v_a_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Std_Async_ContextAsync_async(v_00_u03b1_1773_, v_x_1774_, v_prio_1775_, v_ctx_1776_);
lean_dec_ref(v_ctx_1776_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5(lean_object* v___f_1779_, lean_object* v___f_1780_, lean_object* v_00_u03b1_1781_, lean_object* v_x_1782_, lean_object* v_prio_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v___f_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___f_1786_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_async___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1786_, 0, v_x_1782_);
lean_closure_set(v___f_1786_, 1, v___f_1779_);
lean_closure_set(v___f_1786_, 2, v_prio_1783_);
lean_closure_set(v___f_1786_, 3, v___f_1780_);
v___x_1787_ = lean_unsigned_to_nat(0u);
v___x_1788_ = 0;
lean_inc_ref(v___y_1784_);
v___x_1789_ = l_Std_CancellationContext_fork(v___y_1784_);
v___x_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
v___x_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
v___x_1792_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1787_, v___x_1788_, v___x_1791_, v___f_1786_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5___boxed(lean_object* v___f_1793_, lean_object* v___f_1794_, lean_object* v_00_u03b1_1795_, lean_object* v_x_1796_, lean_object* v_prio_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5(v___f_1793_, v___f_1794_, v_00_u03b1_1795_, v_x_1796_, v_prio_1797_, v___y_1798_);
lean_dec_ref(v___y_1798_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instFunctor___lam__0(lean_object* v_00_u03b1_1805_, lean_object* v_00_u03b2_1806_, lean_object* v_f_1807_, lean_object* v_x_1808_, lean_object* v_ctx_1809_){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; uint8_t v___x_1813_; lean_object* v___x_1814_; lean_object* v___y_1816_; 
lean_inc(v_f_1807_);
v___x_1811_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_1811_, 0, lean_box(0));
lean_closure_set(v___x_1811_, 1, lean_box(0));
lean_closure_set(v___x_1811_, 2, lean_box(0));
lean_closure_set(v___x_1811_, 3, v_f_1807_);
v___x_1812_ = lean_unsigned_to_nat(0u);
v___x_1813_ = 0;
v___x_1814_ = lean_apply_2(v_x_1808_, v_ctx_1809_, lean_box(0));
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1818_; 
lean_dec_ref(v___x_1811_);
v_a_1818_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1818_);
lean_dec_ref_known(v___x_1814_, 1);
if (lean_obj_tag(v_a_1818_) == 0)
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
lean_dec(v_f_1807_);
v_a_1819_ = lean_ctor_get(v_a_1818_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v_a_1818_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v_a_1818_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v_a_1818_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
v___y_1816_ = v___x_1824_;
goto v___jp_1815_;
}
}
}
else
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1835_; 
v_a_1827_ = lean_ctor_get(v_a_1818_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_a_1818_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1829_ = v_a_1818_;
v_isShared_1830_ = v_isSharedCheck_1835_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v_a_1818_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1835_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1831_; lean_object* v___x_1833_; 
v___x_1831_ = lean_apply_1(v_f_1807_, v_a_1827_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1831_);
v___x_1833_ = v___x_1829_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
v___y_1816_ = v___x_1833_;
goto v___jp_1815_;
}
}
}
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1844_; 
lean_dec(v_f_1807_);
v_a_1836_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1838_ = v___x_1814_;
v_isShared_1839_ = v_isSharedCheck_1844_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1814_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1844_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; lean_object* v___x_1842_; 
v___x_1840_ = lean_task_map(v___x_1811_, v_a_1836_, v___x_1812_, v___x_1813_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1840_);
v___x_1842_ = v___x_1838_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
v___jp_1815_:
{
lean_object* v___x_1817_; 
v___x_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1817_, 0, v___y_1816_);
return v___x_1817_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instFunctor___lam__0___boxed(lean_object* v_00_u03b1_1845_, lean_object* v_00_u03b2_1846_, lean_object* v_f_1847_, lean_object* v_x_1848_, lean_object* v_ctx_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Std_Async_ContextAsync_instFunctor___lam__0(v_00_u03b1_1845_, v_00_u03b2_1846_, v_f_1847_, v_x_1848_, v_ctx_1849_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instFunctor___lam__1(lean_object* v___f_1852_, lean_object* v_00_u03b1_1853_, lean_object* v_00_u03b2_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_1859_, 0, lean_box(0));
lean_closure_set(v___x_1859_, 1, lean_box(0));
lean_closure_set(v___x_1859_, 2, v___y_1855_);
lean_inc_ref(v___y_1857_);
v___x_1860_ = lean_apply_6(v___f_1852_, lean_box(0), lean_box(0), v___x_1859_, v___y_1856_, v___y_1857_, lean_box(0));
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instFunctor___lam__1___boxed(lean_object* v___f_1861_, lean_object* v_00_u03b1_1862_, lean_object* v_00_u03b2_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Std_Async_ContextAsync_instFunctor___lam__1(v___f_1861_, v_00_u03b1_1862_, v_00_u03b2_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
lean_dec_ref(v___y_1866_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__0(lean_object* v_00_u03b1_1876_, lean_object* v_a_1877_, lean_object* v_x_1878_){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1880_, 0, v_a_1877_);
v___x_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__0___boxed(lean_object* v_00_u03b1_1882_, lean_object* v_a_1883_, lean_object* v_x_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Std_Async_ContextAsync_instMonad___lam__0(v_00_u03b1_1882_, v_a_1883_, v_x_1884_);
lean_dec_ref(v_x_1884_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__1(lean_object* v_f_1887_, lean_object* v_ctx_1888_, lean_object* v_x_1889_){
_start:
{
if (lean_obj_tag(v_x_1889_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1899_; 
lean_dec_ref(v_ctx_1888_);
lean_dec_ref(v_f_1887_);
v_a_1891_ = lean_ctor_get(v_x_1889_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_x_1889_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1893_ = v_x_1889_;
v_isShared_1894_ = v_isSharedCheck_1899_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v_x_1889_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1899_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
lean_object* v___x_1897_; 
v___x_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
return v___x_1897_;
}
}
}
else
{
lean_object* v_a_1900_; lean_object* v___x_1901_; 
v_a_1900_ = lean_ctor_get(v_x_1889_, 0);
lean_inc(v_a_1900_);
lean_dec_ref_known(v_x_1889_, 1);
v___x_1901_ = lean_apply_3(v_f_1887_, v_a_1900_, v_ctx_1888_, lean_box(0));
return v___x_1901_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__1___boxed(lean_object* v_f_1902_, lean_object* v_ctx_1903_, lean_object* v_x_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Std_Async_ContextAsync_instMonad___lam__1(v_f_1902_, v_ctx_1903_, v_x_1904_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__2(lean_object* v_00_u03b1_1907_, lean_object* v_00_u03b2_1908_, lean_object* v_x_1909_, lean_object* v_f_1910_, lean_object* v_ctx_1911_){
_start:
{
lean_object* v___f_1913_; lean_object* v___x_1914_; uint8_t v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
lean_inc_ref(v_ctx_1911_);
v___f_1913_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_instMonad___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1913_, 0, v_f_1910_);
lean_closure_set(v___f_1913_, 1, v_ctx_1911_);
v___x_1914_ = lean_unsigned_to_nat(0u);
v___x_1915_ = 0;
v___x_1916_ = lean_apply_2(v_x_1909_, v_ctx_1911_, lean_box(0));
v___x_1917_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1914_, v___x_1915_, v___x_1916_, v___f_1913_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__2___boxed(lean_object* v_00_u03b1_1918_, lean_object* v_00_u03b2_1919_, lean_object* v_x_1920_, lean_object* v_f_1921_, lean_object* v_ctx_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Std_Async_ContextAsync_instMonad___lam__2(v_00_u03b1_1918_, v_00_u03b2_1919_, v_x_1920_, v_f_1921_, v_ctx_1922_);
return v_res_1924_;
}
}
static lean_object* _init_l_Std_Async_ContextAsync_instMonad(void){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v_toApplicative_1929_; lean_object* v_toSeq_1930_; lean_object* v_toSeqLeft_1931_; lean_object* v_toSeqRight_1932_; lean_object* v___f_1933_; lean_object* v___f_1934_; lean_object* v___f_1935_; lean_object* v___f_1936_; lean_object* v___f_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1927_ = ((lean_object*)(l_Std_Async_ContextAsync_instFunctor));
v___x_1928_ = lean_obj_once(&l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2, &l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2_once, _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2);
v_toApplicative_1929_ = lean_ctor_get(v___x_1928_, 0);
v_toSeq_1930_ = lean_ctor_get(v_toApplicative_1929_, 2);
v_toSeqLeft_1931_ = lean_ctor_get(v_toApplicative_1929_, 3);
v_toSeqRight_1932_ = lean_ctor_get(v_toApplicative_1929_, 4);
v___f_1933_ = ((lean_object*)(l_Std_Async_ContextAsync_instMonad___closed__0));
v___f_1934_ = ((lean_object*)(l_Std_Async_ContextAsync_instMonad___closed__1));
lean_inc(v_toSeqRight_1932_);
v___f_1935_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1935_, 0, v_toSeqRight_1932_);
lean_inc(v_toSeqLeft_1931_);
v___f_1936_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1936_, 0, v_toSeqLeft_1931_);
lean_inc(v_toSeq_1930_);
v___f_1937_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1937_, 0, v_toSeq_1930_);
v___x_1938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1927_);
lean_ctor_set(v___x_1938_, 1, v___f_1933_);
lean_ctor_set(v___x_1938_, 2, v___f_1937_);
lean_ctor_set(v___x_1938_, 3, v___f_1936_);
lean_ctor_set(v___x_1938_, 4, v___f_1935_);
v___x_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
lean_ctor_set(v___x_1939_, 1, v___f_1934_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___lam__0(lean_object* v_a_1940_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1941_, 0, v_a_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___lam__1(lean_object* v___f_1942_, lean_object* v_x_1943_){
_start:
{
if (lean_obj_tag(v_x_1943_) == 0)
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1953_; 
lean_dec_ref(v___f_1942_);
v_a_1945_ = lean_ctor_get(v_x_1943_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v_x_1943_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1947_ = v_x_1943_;
v_isShared_1948_ = v_isSharedCheck_1953_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v_x_1943_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1953_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
lean_object* v___x_1951_; 
v___x_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
return v___x_1951_;
}
}
}
else
{
lean_object* v_a_1954_; 
v_a_1954_ = lean_ctor_get(v_x_1943_, 0);
lean_inc(v_a_1954_);
lean_dec_ref_known(v_x_1943_, 1);
if (lean_obj_tag(v_a_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1963_; 
lean_dec_ref(v___f_1942_);
v_a_1955_ = lean_ctor_get(v_a_1954_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v_a_1954_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1957_ = v_a_1954_;
v_isShared_1958_ = v_isSharedCheck_1963_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v_a_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1963_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1961_; 
v___x_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
return v___x_1961_;
}
}
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1965_; uint8_t v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v_a_1964_ = lean_ctor_get(v_a_1954_, 0);
lean_inc(v_a_1964_);
lean_dec_ref_known(v_a_1954_, 1);
v___x_1965_ = lean_unsigned_to_nat(0u);
v___x_1966_ = 0;
v___x_1967_ = lean_task_map(v___f_1942_, v_a_1964_, v___x_1965_, v___x_1966_);
v___x_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
return v___x_1968_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___lam__1___boxed(lean_object* v___f_1969_, lean_object* v_x_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Std_Async_ContextAsync_instMonadLiftIO___lam__1(v___f_1969_, v_x_1970_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___lam__2(lean_object* v___f_1973_, lean_object* v_00_u03b1_1974_, lean_object* v_x_1975_, lean_object* v_x_1976_){
_start:
{
lean_object* v___x_1978_; uint8_t v___x_1979_; lean_object* v_val_1981_; lean_object* v___x_1985_; 
v___x_1978_ = lean_unsigned_to_nat(0u);
v___x_1979_ = 0;
v___x_1985_ = lean_apply_1(v_x_1975_, lean_box(0));
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1994_; 
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1988_ = v___x_1985_;
v_isShared_1989_ = v_isSharedCheck_1994_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1985_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1994_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1990_; lean_object* v___x_1992_; 
v___x_1990_ = lean_task_pure(v_a_1986_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set_tag(v___x_1988_, 1);
lean_ctor_set(v___x_1988_, 0, v___x_1990_);
v___x_1992_ = v___x_1988_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1990_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
v_val_1981_ = v___x_1992_;
goto v___jp_1980_;
}
}
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
v_a_1995_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1985_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1985_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set_tag(v___x_1997_, 0);
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
v_val_1981_ = v___x_2000_;
goto v___jp_1980_;
}
}
}
v___jp_1980_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1982_, 0, v_val_1981_);
v___x_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
v___x_1984_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1978_, v___x_1979_, v___x_1983_, v___f_1973_);
return v___x_1984_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___lam__2___boxed(lean_object* v___f_2003_, lean_object* v_00_u03b1_2004_, lean_object* v_x_2005_, lean_object* v_x_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Std_Async_ContextAsync_instMonadLiftIO___lam__2(v___f_2003_, v_00_u03b1_2004_, v_x_2005_, v_x_2006_);
lean_dec_ref(v_x_2006_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0(lean_object* v_00_u03b1_2015_, lean_object* v_x_2016_, lean_object* v_x_2017_){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2019_ = lean_apply_1(v_x_2016_, lean_box(0));
v___x_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0___boxed(lean_object* v_00_u03b1_2022_, lean_object* v_x_2023_, lean_object* v_x_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0(v_00_u03b1_2022_, v_x_2023_, v_x_2024_);
lean_dec_ref(v_x_2024_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__0(lean_object* v_00_u03b1_2029_, lean_object* v_e_2030_, lean_object* v_x_2031_){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2033_, 0, v_e_2030_);
v___x_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__0___boxed(lean_object* v_00_u03b1_2035_, lean_object* v_e_2036_, lean_object* v_x_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_Std_Async_ContextAsync_instMonadExceptError___lam__0(v_00_u03b1_2035_, v_e_2036_, v_x_2037_);
lean_dec_ref(v_x_2037_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__1(lean_object* v_h_2040_, lean_object* v_ctx_2041_, lean_object* v_x_2042_){
_start:
{
if (lean_obj_tag(v_x_2042_) == 0)
{
lean_object* v_a_2044_; lean_object* v___x_2045_; 
v_a_2044_ = lean_ctor_get(v_x_2042_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v_x_2042_, 1);
v___x_2045_ = lean_apply_3(v_h_2040_, v_a_2044_, v_ctx_2041_, lean_box(0));
return v___x_2045_;
}
else
{
lean_object* v___x_2046_; 
lean_dec_ref(v_ctx_2041_);
lean_dec_ref(v_h_2040_);
v___x_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2046_, 0, v_x_2042_);
return v___x_2046_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__1___boxed(lean_object* v_h_2047_, lean_object* v_ctx_2048_, lean_object* v_x_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Std_Async_ContextAsync_instMonadExceptError___lam__1(v_h_2047_, v_ctx_2048_, v_x_2049_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__2(lean_object* v_00_u03b1_2052_, lean_object* v_x_2053_, lean_object* v_h_2054_, lean_object* v_ctx_2055_){
_start:
{
lean_object* v___f_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
lean_inc_ref(v_ctx_2055_);
v___f_2057_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_instMonadExceptError___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2057_, 0, v_h_2054_);
lean_closure_set(v___f_2057_, 1, v_ctx_2055_);
v___x_2058_ = lean_unsigned_to_nat(0u);
v___x_2059_ = 0;
v___x_2060_ = lean_apply_2(v_x_2053_, v_ctx_2055_, lean_box(0));
v___x_2061_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2058_, v___x_2059_, v___x_2060_, v___f_2057_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__2___boxed(lean_object* v_00_u03b1_2062_, lean_object* v_x_2063_, lean_object* v_h_2064_, lean_object* v_ctx_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_Std_Async_ContextAsync_instMonadExceptError___lam__2(v_00_u03b1_2062_, v_x_2063_, v_h_2064_, v_ctx_2065_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadFinally___lam__0(lean_object* v_f_2074_, lean_object* v_ctx_2075_, lean_object* v_opt_2076_){
_start:
{
lean_object* v___x_2078_; 
v___x_2078_ = lean_apply_3(v_f_2074_, v_opt_2076_, v_ctx_2075_, lean_box(0));
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadFinally___lam__0___boxed(lean_object* v_f_2079_, lean_object* v_ctx_2080_, lean_object* v_opt_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_Std_Async_ContextAsync_instMonadFinally___lam__0(v_f_2079_, v_ctx_2080_, v_opt_2081_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadFinally___lam__1(lean_object* v_00_u03b1_2084_, lean_object* v_00_u03b2_2085_, lean_object* v_x_2086_, lean_object* v_f_2087_, lean_object* v_ctx_2088_){
_start:
{
lean_object* v___f_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; lean_object* v___x_2094_; 
lean_inc_ref(v_ctx_2088_);
v___f_2090_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_instMonadFinally___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2090_, 0, v_f_2087_);
lean_closure_set(v___f_2090_, 1, v_ctx_2088_);
v___x_2091_ = lean_apply_1(v_x_2086_, v_ctx_2088_);
v___x_2092_ = lean_unsigned_to_nat(0u);
v___x_2093_ = 0;
v___x_2094_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_2091_, v___f_2090_, v___x_2092_, v___x_2093_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadFinally___lam__1___boxed(lean_object* v_00_u03b1_2095_, lean_object* v_00_u03b2_2096_, lean_object* v_x_2097_, lean_object* v_f_2098_, lean_object* v_ctx_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Std_Async_ContextAsync_instMonadFinally___lam__1(v_00_u03b1_2095_, v_00_u03b2_2096_, v_x_2097_, v_f_2098_, v_ctx_2099_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited___redArg___lam__0(lean_object* v_x_2111_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = ((lean_object*)(l_Std_Async_ContextAsync_instInhabited___redArg___lam__0___closed__3));
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited___redArg___lam__0___boxed(lean_object* v_x_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_Std_Async_ContextAsync_instInhabited___redArg___lam__0(v_x_2114_);
lean_dec_ref(v_x_2114_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited___redArg(){
_start:
{
lean_object* v___f_2119_; 
v___f_2119_ = ((lean_object*)(l_Std_Async_ContextAsync_instInhabited___redArg___closed__0));
return v___f_2119_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited___redArg___boxed(lean_object* v___dummy_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l_Std_Async_ContextAsync_instInhabited___redArg();
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited(lean_object* v_00_u03b1_2122_, lean_object* v_inst_2123_){
_start:
{
lean_object* v___f_2124_; 
v___f_2124_ = ((lean_object*)(l_Std_Async_ContextAsync_instInhabited___redArg___closed__0));
return v___f_2124_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited___boxed(lean_object* v_00_u03b1_2125_, lean_object* v_inst_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l_Std_Async_ContextAsync_instInhabited(v_00_u03b1_2125_, v_inst_2126_);
lean_dec(v_inst_2126_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0(lean_object* v_00_u03b1_2128_, lean_object* v_t_2129_, lean_object* v_x_2130_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2132_, 0, v_t_2129_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0___boxed(lean_object* v_00_u03b1_2133_, lean_object* v_t_2134_, lean_object* v_x_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0(v_00_u03b1_2133_, v_t_2134_, v_x_2135_);
lean_dec_ref(v_x_2135_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_forIn___redArg___lam__0(lean_object* v_f_2140_, lean_object* v_ctx_2141_, lean_object* v_u_2142_, lean_object* v_b_2143_){
_start:
{
lean_object* v___x_2145_; 
lean_inc_ref(v_ctx_2141_);
v___x_2145_ = lean_apply_4(v_f_2140_, v_u_2142_, v_b_2143_, v_ctx_2141_, lean_box(0));
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_forIn___redArg___lam__0___boxed(lean_object* v_f_2146_, lean_object* v_ctx_2147_, lean_object* v_u_2148_, lean_object* v_b_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l_Std_Async_ContextAsync_forIn___redArg___lam__0(v_f_2146_, v_ctx_2147_, v_u_2148_, v_b_2149_);
lean_dec_ref(v_ctx_2147_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_forIn___redArg___lam__1(lean_object* v_a_2152_, lean_object* v_x_2153_){
_start:
{
if (lean_obj_tag(v_x_2153_) == 0)
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2163_; 
v_a_2155_ = lean_ctor_get(v_x_2153_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_x_2153_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2157_ = v_x_2153_;
v_isShared_2158_ = v_isSharedCheck_2163_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v_x_2153_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2163_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2155_);
v___x_2160_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
lean_object* v___x_2161_; 
v___x_2161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
return v___x_2161_;
}
}
}
else
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
lean_dec_ref_known(v_x_2153_, 1);
v___x_2164_ = l_IO_Promise_result_x21___redArg(v_a_2152_);
v___x_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
return v___x_2165_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_forIn___redArg___lam__1___boxed(lean_object* v_a_2166_, lean_object* v_x_2167_, lean_object* v___y_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Std_Async_ContextAsync_forIn___redArg___lam__1(v_a_2166_, v_x_2167_);
lean_dec(v_a_2166_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_forIn___redArg___lam__2(lean_object* v___f_2170_, lean_object* v_prio_2171_, lean_object* v_init_2172_, lean_object* v_x_2173_){
_start:
{
if (lean_obj_tag(v_x_2173_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2183_; 
lean_dec(v_init_2172_);
lean_dec(v_prio_2171_);
lean_dec_ref(v___f_2170_);
v_a_2175_ = lean_ctor_get(v_x_2173_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v_x_2173_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2177_ = v_x_2173_;
v_isShared_2178_ = v_isSharedCheck_2183_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v_x_2173_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2183_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2175_);
v___x_2180_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
lean_object* v___x_2181_; 
v___x_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2180_);
return v___x_2181_;
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2197_; 
v_a_2184_ = lean_ctor_get(v_x_2173_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v_x_2173_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2186_ = v_x_2173_;
v_isShared_2187_ = v_isSharedCheck_2197_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v_x_2173_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2197_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___f_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2193_; 
lean_inc(v_a_2184_);
v___f_2188_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_forIn___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2188_, 0, v_a_2184_);
v___x_2189_ = lean_unsigned_to_nat(0u);
v___x_2190_ = 0;
v___x_2191_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_2170_, v_prio_2171_, v_a_2184_, v_init_2172_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 0, v___x_2191_);
v___x_2193_ = v___x_2186_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2191_);
v___x_2193_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
v___x_2195_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2189_, v___x_2190_, v___x_2194_, v___f_2188_);
return v___x_2195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_forIn___redArg___lam__2___boxed(lean_object* v___f_2198_, lean_object* v_prio_2199_, lean_object* v_init_2200_, lean_object* v_x_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Std_Async_ContextAsync_forIn___redArg___lam__2(v___f_2198_, v_prio_2199_, v_init_2200_, v_x_2201_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_forIn___redArg(lean_object* v_init_2204_, lean_object* v_f_2205_, lean_object* v_prio_2206_, lean_object* v_ctx_2207_){
_start:
{
lean_object* v___f_2209_; lean_object* v___f_2210_; lean_object* v___x_2211_; uint8_t v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
lean_inc_ref(v_ctx_2207_);
v___f_2209_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_forIn___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_2209_, 0, v_f_2205_);
lean_closure_set(v___f_2209_, 1, v_ctx_2207_);
v___f_2210_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_forIn___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_2210_, 0, v___f_2209_);
lean_closure_set(v___f_2210_, 1, v_prio_2206_);
lean_closure_set(v___f_2210_, 2, v_init_2204_);
v___x_2211_ = lean_unsigned_to_nat(0u);
v___x_2212_ = 0;
v___x_2213_ = lean_io_promise_new();
v___x_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
v___x_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
v___x_2216_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2211_, v___x_2212_, v___x_2215_, v___f_2210_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_forIn___redArg___boxed(lean_object* v_init_2217_, lean_object* v_f_2218_, lean_object* v_prio_2219_, lean_object* v_ctx_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Std_Async_ContextAsync_forIn___redArg(v_init_2217_, v_f_2218_, v_prio_2219_, v_ctx_2220_);
lean_dec_ref(v_ctx_2220_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_forIn(lean_object* v_00_u03b2_2223_, lean_object* v_init_2224_, lean_object* v_f_2225_, lean_object* v_prio_2226_, lean_object* v_ctx_2227_){
_start:
{
lean_object* v___f_2229_; lean_object* v___f_2230_; lean_object* v___x_2231_; uint8_t v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
lean_inc_ref(v_ctx_2227_);
v___f_2229_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_forIn___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_2229_, 0, v_f_2225_);
lean_closure_set(v___f_2229_, 1, v_ctx_2227_);
v___f_2230_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_forIn___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_2230_, 0, v___f_2229_);
lean_closure_set(v___f_2230_, 1, v_prio_2226_);
lean_closure_set(v___f_2230_, 2, v_init_2224_);
v___x_2231_ = lean_unsigned_to_nat(0u);
v___x_2232_ = 0;
v___x_2233_ = lean_io_promise_new();
v___x_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
v___x_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
v___x_2236_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2231_, v___x_2232_, v___x_2235_, v___f_2230_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_forIn___boxed(lean_object* v_00_u03b2_2237_, lean_object* v_init_2238_, lean_object* v_f_2239_, lean_object* v_prio_2240_, lean_object* v_ctx_2241_, lean_object* v_a_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Std_Async_ContextAsync_forIn(v_00_u03b2_2237_, v_init_2238_, v_f_2239_, v_prio_2240_, v_ctx_2241_);
lean_dec_ref(v_ctx_2241_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instForInLoopUnit___lam__0(lean_object* v_f_2244_, lean_object* v___y_2245_, lean_object* v_u_2246_, lean_object* v_b_2247_){
_start:
{
lean_object* v___x_2249_; 
lean_inc_ref(v___y_2245_);
v___x_2249_ = lean_apply_4(v_f_2244_, v_u_2246_, v_b_2247_, v___y_2245_, lean_box(0));
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instForInLoopUnit___lam__0___boxed(lean_object* v_f_2250_, lean_object* v___y_2251_, lean_object* v_u_2252_, lean_object* v_b_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Std_Async_ContextAsync_instForInLoopUnit___lam__0(v_f_2250_, v___y_2251_, v_u_2252_, v_b_2253_);
lean_dec_ref(v___y_2251_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instForInLoopUnit___lam__2(lean_object* v___f_2256_, lean_object* v___x_2257_, lean_object* v_init_2258_, lean_object* v_x_2259_){
_start:
{
if (lean_obj_tag(v_x_2259_) == 0)
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2269_; 
lean_dec(v_init_2258_);
lean_dec(v___x_2257_);
lean_dec_ref(v___f_2256_);
v_a_2261_ = lean_ctor_get(v_x_2259_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v_x_2259_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2263_ = v_x_2259_;
v_isShared_2264_ = v_isSharedCheck_2269_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v_x_2259_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2269_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
lean_object* v___x_2267_; 
v___x_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
return v___x_2267_;
}
}
}
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2282_; 
v_a_2270_ = lean_ctor_get(v_x_2259_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v_x_2259_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2272_ = v_x_2259_;
v_isShared_2273_ = v_isSharedCheck_2282_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v_x_2259_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2282_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___f_2274_; uint8_t v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2278_; 
lean_inc(v_a_2270_);
v___f_2274_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_forIn___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2274_, 0, v_a_2270_);
v___x_2275_ = 0;
lean_inc(v___x_2257_);
v___x_2276_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_2256_, v___x_2257_, v_a_2270_, v_init_2258_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 0, v___x_2276_);
v___x_2278_ = v___x_2272_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2276_);
v___x_2278_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
v___x_2280_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2257_, v___x_2275_, v___x_2279_, v___f_2274_);
return v___x_2280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instForInLoopUnit___lam__2___boxed(lean_object* v___f_2283_, lean_object* v___x_2284_, lean_object* v_init_2285_, lean_object* v_x_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Std_Async_ContextAsync_instForInLoopUnit___lam__2(v___f_2283_, v___x_2284_, v_init_2285_, v_x_2286_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instForInLoopUnit___lam__1(lean_object* v_00_u03b2_2289_, lean_object* v_x_2290_, lean_object* v_init_2291_, lean_object* v_f_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v___f_2295_; lean_object* v___x_2296_; lean_object* v___f_2297_; uint8_t v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
lean_inc_ref(v___y_2293_);
v___f_2295_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_instForInLoopUnit___lam__0___boxed), 5, 2);
lean_closure_set(v___f_2295_, 0, v_f_2292_);
lean_closure_set(v___f_2295_, 1, v___y_2293_);
v___x_2296_ = lean_unsigned_to_nat(0u);
v___f_2297_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_instForInLoopUnit___lam__2___boxed), 5, 3);
lean_closure_set(v___f_2297_, 0, v___f_2295_);
lean_closure_set(v___f_2297_, 1, v___x_2296_);
lean_closure_set(v___f_2297_, 2, v_init_2291_);
v___x_2298_ = 0;
v___x_2299_ = lean_io_promise_new();
v___x_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
v___x_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
v___x_2302_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2296_, v___x_2298_, v___x_2301_, v___f_2297_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instForInLoopUnit___lam__1___boxed(lean_object* v_00_u03b2_2303_, lean_object* v_x_2304_, lean_object* v_init_2305_, lean_object* v_f_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Std_Async_ContextAsync_instForInLoopUnit___lam__1(v_00_u03b2_2303_, v_x_2304_, v_init_2305_, v_f_2306_, v___y_2307_);
lean_dec_ref(v___y_2307_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__4(lean_object* v_a_2312_, lean_object* v___x_2313_, lean_object* v___f_2314_, lean_object* v_x_2315_){
_start:
{
if (lean_obj_tag(v_x_2315_) == 0)
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2325_; 
lean_dec_ref(v___f_2314_);
lean_dec(v___x_2313_);
lean_dec_ref(v_a_2312_);
v_a_2317_ = lean_ctor_get(v_x_2315_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v_x_2315_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2319_ = v_x_2315_;
v_isShared_2320_ = v_isSharedCheck_2325_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v_x_2315_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2325_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2322_; 
if (v_isShared_2320_ == 0)
{
v___x_2322_ = v___x_2319_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2317_);
v___x_2322_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
lean_object* v___x_2323_; 
v___x_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
return v___x_2323_;
}
}
}
else
{
lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2337_; 
v_isSharedCheck_2337_ = !lean_is_exclusive(v_x_2315_);
if (v_isSharedCheck_2337_ == 0)
{
lean_object* v_unused_2338_; 
v_unused_2338_ = lean_ctor_get(v_x_2315_, 0);
lean_dec(v_unused_2338_);
v___x_2327_ = v_x_2315_;
v_isShared_2328_ = v_isSharedCheck_2337_;
goto v_resetjp_2326_;
}
else
{
lean_dec(v_x_2315_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2337_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2329_; uint8_t v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2333_; 
v___x_2329_ = lean_unsigned_to_nat(0u);
v___x_2330_ = 0;
v___x_2331_ = l_Std_CancellationContext_cancel(v_a_2312_, v___x_2313_);
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 0, v___x_2331_);
v___x_2333_ = v___x_2327_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2333_);
v___x_2335_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2329_, v___x_2330_, v___x_2334_, v___f_2314_);
return v___x_2335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__4___boxed(lean_object* v_a_2339_, lean_object* v___x_2340_, lean_object* v___f_2341_, lean_object* v_x_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Std_Async_ContextAsync_race___redArg___lam__4(v_a_2339_, v___x_2340_, v___f_2341_, v_x_2342_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__0(lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_x_2347_){
_start:
{
if (lean_obj_tag(v_x_2347_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2357_; 
lean_dec_ref(v_a_2346_);
lean_dec_ref(v_a_2345_);
v_a_2349_ = lean_ctor_get(v_x_2347_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v_x_2347_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2351_ = v_x_2347_;
v_isShared_2352_ = v_isSharedCheck_2357_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v_x_2347_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2357_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2349_);
v___x_2354_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
lean_object* v___x_2355_; 
v___x_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2354_);
return v___x_2355_;
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2373_; 
v_a_2358_ = lean_ctor_get(v_x_2347_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v_x_2347_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2360_ = v_x_2347_;
v_isShared_2361_ = v_isSharedCheck_2373_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v_x_2347_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2373_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___f_2362_; lean_object* v___x_2363_; lean_object* v___f_2364_; lean_object* v___x_2365_; uint8_t v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___f_2362_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2362_, 0, v_a_2358_);
v___x_2363_ = lean_box(2);
v___f_2364_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_2364_, 0, v_a_2345_);
lean_closure_set(v___f_2364_, 1, v___x_2363_);
lean_closure_set(v___f_2364_, 2, v___f_2362_);
v___x_2365_ = lean_unsigned_to_nat(0u);
v___x_2366_ = 0;
v___x_2367_ = l_Std_CancellationContext_cancel(v_a_2346_, v___x_2363_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 0, v___x_2367_);
v___x_2369_ = v___x_2360_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
v___x_2371_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2365_, v___x_2366_, v___x_2370_, v___f_2364_);
return v___x_2371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__0___boxed(lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_x_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Std_Async_ContextAsync_race___redArg___lam__0(v_a_2374_, v_a_2375_, v_x_2376_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__1(lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_result_2381_){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2383_ = lean_io_promise_resolve(v_result_2381_, v_a_2379_);
v___x_2384_ = lean_box(2);
v___x_2385_ = l_Std_CancellationContext_cancel(v_a_2380_, v___x_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__1___boxed(lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_result_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Std_Async_ContextAsync_race___redArg___lam__1(v_a_2386_, v_a_2387_, v_result_2388_);
lean_dec(v_a_2386_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__5(lean_object* v_a_2391_, lean_object* v___f_2392_, lean_object* v___x_2393_, uint8_t v___x_2394_, lean_object* v___f_2395_, lean_object* v_x_2396_){
_start:
{
if (lean_obj_tag(v_x_2396_) == 0)
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2406_; 
lean_dec_ref(v___f_2395_);
lean_dec(v___x_2393_);
lean_dec_ref(v___f_2392_);
lean_dec_ref(v_a_2391_);
v_a_2398_ = lean_ctor_get(v_x_2396_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v_x_2396_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2400_ = v_x_2396_;
v_isShared_2401_ = v_isSharedCheck_2406_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v_x_2396_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2406_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
lean_object* v___x_2404_; 
v___x_2404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2403_);
return v___x_2404_;
}
}
}
else
{
lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2416_; 
v_isSharedCheck_2416_ = !lean_is_exclusive(v_x_2396_);
if (v_isSharedCheck_2416_ == 0)
{
lean_object* v_unused_2417_; 
v_unused_2417_ = lean_ctor_get(v_x_2396_, 0);
lean_dec(v_unused_2417_);
v___x_2408_ = v_x_2396_;
v_isShared_2409_ = v_isSharedCheck_2416_;
goto v_resetjp_2407_;
}
else
{
lean_dec(v_x_2396_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2416_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2410_; lean_object* v___x_2412_; 
lean_inc(v___x_2393_);
v___x_2410_ = l_BaseIO_chainTask___redArg(v_a_2391_, v___f_2392_, v___x_2393_, v___x_2394_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 0, v___x_2410_);
v___x_2412_ = v___x_2408_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2410_);
v___x_2412_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
v___x_2414_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2393_, v___x_2394_, v___x_2413_, v___f_2395_);
return v___x_2414_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__5___boxed(lean_object* v_a_2418_, lean_object* v___f_2419_, lean_object* v___x_2420_, lean_object* v___x_2421_, lean_object* v___f_2422_, lean_object* v_x_2423_, lean_object* v___y_2424_){
_start:
{
uint8_t v___x_4042__boxed_2425_; lean_object* v_res_2426_; 
v___x_4042__boxed_2425_ = lean_unbox(v___x_2421_);
v_res_2426_ = l_Std_Async_ContextAsync_race___redArg___lam__5(v_a_2418_, v___f_2419_, v___x_2420_, v___x_4042__boxed_2425_, v___f_2422_, v_x_2423_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__2(lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v___f_2429_, lean_object* v___f_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_x_2433_){
_start:
{
if (lean_obj_tag(v_x_2433_) == 0)
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2443_; 
lean_dec_ref(v_a_2432_);
lean_dec_ref(v_a_2431_);
lean_dec_ref(v___f_2430_);
lean_dec_ref(v___f_2429_);
lean_dec_ref(v_a_2428_);
lean_dec_ref(v_a_2427_);
v_a_2435_ = lean_ctor_get(v_x_2433_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v_x_2433_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2437_ = v_x_2433_;
v_isShared_2438_ = v_isSharedCheck_2443_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v_x_2433_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2443_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2435_);
v___x_2440_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
lean_object* v___x_2441_; 
v___x_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2440_);
return v___x_2441_;
}
}
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2461_; 
v_a_2444_ = lean_ctor_get(v_x_2433_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v_x_2433_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2446_ = v_x_2433_;
v_isShared_2447_ = v_isSharedCheck_2461_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v_x_2433_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2461_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___f_2448_; lean_object* v___f_2449_; lean_object* v___f_2450_; lean_object* v___x_2451_; uint8_t v___x_2452_; lean_object* v___x_2453_; lean_object* v___f_2454_; lean_object* v___x_2455_; lean_object* v___x_2457_; 
lean_inc_n(v_a_2444_, 2);
v___f_2448_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2448_, 0, v_a_2444_);
lean_closure_set(v___f_2448_, 1, v_a_2427_);
v___f_2449_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2449_, 0, v_a_2444_);
lean_closure_set(v___f_2449_, 1, v_a_2428_);
v___f_2450_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__10___boxed), 5, 3);
lean_closure_set(v___f_2450_, 0, v_a_2444_);
lean_closure_set(v___f_2450_, 1, v___f_2429_);
lean_closure_set(v___f_2450_, 2, v___f_2430_);
v___x_2451_ = lean_unsigned_to_nat(0u);
v___x_2452_ = 0;
v___x_2453_ = lean_box(v___x_2452_);
v___f_2454_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__5___boxed), 7, 5);
lean_closure_set(v___f_2454_, 0, v_a_2431_);
lean_closure_set(v___f_2454_, 1, v___f_2449_);
lean_closure_set(v___f_2454_, 2, v___x_2451_);
lean_closure_set(v___f_2454_, 3, v___x_2453_);
lean_closure_set(v___f_2454_, 4, v___f_2450_);
v___x_2455_ = l_BaseIO_chainTask___redArg(v_a_2432_, v___f_2448_, v___x_2451_, v___x_2452_);
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 0, v___x_2455_);
v___x_2457_ = v___x_2446_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2455_);
v___x_2457_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
v___x_2459_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2451_, v___x_2452_, v___x_2458_, v___f_2454_);
return v___x_2459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__2___boxed(lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v___f_2464_, lean_object* v___f_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_x_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l_Std_Async_ContextAsync_race___redArg___lam__2(v_a_2462_, v_a_2463_, v___f_2464_, v___f_2465_, v_a_2466_, v_a_2467_, v_x_2468_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__3(lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v___f_2473_, lean_object* v___f_2474_, lean_object* v_a_2475_, lean_object* v_x_2476_){
_start:
{
if (lean_obj_tag(v_x_2476_) == 0)
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2486_; 
lean_dec_ref(v_a_2475_);
lean_dec_ref(v___f_2474_);
lean_dec_ref(v___f_2473_);
lean_dec_ref(v_a_2472_);
lean_dec_ref(v_a_2471_);
v_a_2478_ = lean_ctor_get(v_x_2476_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v_x_2476_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2480_ = v_x_2476_;
v_isShared_2481_ = v_isSharedCheck_2486_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v_x_2476_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2486_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2478_);
v___x_2483_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
lean_object* v___x_2484_; 
v___x_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2483_);
return v___x_2484_;
}
}
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2500_; 
v_a_2487_ = lean_ctor_get(v_x_2476_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v_x_2476_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2489_ = v_x_2476_;
v_isShared_2490_ = v_isSharedCheck_2500_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v_x_2476_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2500_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___f_2491_; lean_object* v___x_2492_; uint8_t v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2496_; 
v___f_2491_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__2___boxed), 8, 6);
lean_closure_set(v___f_2491_, 0, v_a_2471_);
lean_closure_set(v___f_2491_, 1, v_a_2472_);
lean_closure_set(v___f_2491_, 2, v___f_2473_);
lean_closure_set(v___f_2491_, 3, v___f_2474_);
lean_closure_set(v___f_2491_, 4, v_a_2487_);
lean_closure_set(v___f_2491_, 5, v_a_2475_);
v___x_2492_ = lean_unsigned_to_nat(0u);
v___x_2493_ = 0;
v___x_2494_ = lean_io_promise_new();
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 0, v___x_2494_);
v___x_2496_ = v___x_2489_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2494_);
v___x_2496_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
v___x_2498_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2492_, v___x_2493_, v___x_2497_, v___f_2491_);
return v___x_2498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__3___boxed(lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v___f_2503_, lean_object* v___f_2504_, lean_object* v_a_2505_, lean_object* v_x_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Std_Async_ContextAsync_race___redArg___lam__3(v_a_2501_, v_a_2502_, v___f_2503_, v___f_2504_, v_a_2505_, v_x_2506_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__6(lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v___f_2511_, lean_object* v___f_2512_, lean_object* v_y_2513_, lean_object* v_prio_2514_, lean_object* v___f_2515_, lean_object* v_x_2516_){
_start:
{
if (lean_obj_tag(v_x_2516_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2526_; 
lean_dec_ref(v___f_2515_);
lean_dec(v_prio_2514_);
lean_dec_ref(v_y_2513_);
lean_dec_ref(v___f_2512_);
lean_dec_ref(v___f_2511_);
lean_dec_ref(v_a_2510_);
lean_dec_ref(v_a_2509_);
v_a_2518_ = lean_ctor_get(v_x_2516_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v_x_2516_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2520_ = v_x_2516_;
v_isShared_2521_ = v_isSharedCheck_2526_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v_x_2516_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2526_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
lean_object* v___x_2524_; 
v___x_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2523_);
return v___x_2524_;
}
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2544_; 
v_a_2527_ = lean_ctor_get(v_x_2516_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v_x_2516_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2529_ = v_x_2516_;
v_isShared_2530_ = v_isSharedCheck_2544_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v_x_2516_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2544_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___f_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; uint8_t v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2540_; 
lean_inc_ref(v_a_2509_);
v___f_2531_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__3___boxed), 7, 5);
lean_closure_set(v___f_2531_, 0, v_a_2509_);
lean_closure_set(v___f_2531_, 1, v_a_2510_);
lean_closure_set(v___f_2531_, 2, v___f_2511_);
lean_closure_set(v___f_2531_, 3, v___f_2512_);
lean_closure_set(v___f_2531_, 4, v_a_2527_);
v___x_2532_ = lean_apply_1(v_y_2513_, v_a_2509_);
v___x_2533_ = lean_unsigned_to_nat(0u);
v___x_2534_ = 0;
v___x_2535_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2535_, 0, lean_box(0));
lean_closure_set(v___x_2535_, 1, v___x_2532_);
v___x_2536_ = lean_io_as_task(v___x_2535_, v_prio_2514_);
v___x_2537_ = 1;
v___x_2538_ = lean_task_bind(v___x_2536_, v___f_2515_, v___x_2533_, v___x_2537_);
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 0, v___x_2538_);
v___x_2540_ = v___x_2529_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2538_);
v___x_2540_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
v___x_2542_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2533_, v___x_2534_, v___x_2541_, v___f_2531_);
return v___x_2542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__6___boxed(lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v___f_2547_, lean_object* v___f_2548_, lean_object* v_y_2549_, lean_object* v_prio_2550_, lean_object* v___f_2551_, lean_object* v_x_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Std_Async_ContextAsync_race___redArg___lam__6(v_a_2545_, v_a_2546_, v___f_2547_, v___f_2548_, v_y_2549_, v_prio_2550_, v___f_2551_, v_x_2552_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__7(lean_object* v_a_2555_, lean_object* v___f_2556_, lean_object* v_y_2557_, lean_object* v_prio_2558_, lean_object* v___f_2559_, lean_object* v_x_2560_, lean_object* v___f_2561_, lean_object* v_x_2562_){
_start:
{
if (lean_obj_tag(v_x_2562_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2572_; 
lean_dec_ref(v___f_2561_);
lean_dec_ref(v_x_2560_);
lean_dec_ref(v___f_2559_);
lean_dec(v_prio_2558_);
lean_dec_ref(v_y_2557_);
lean_dec_ref(v___f_2556_);
lean_dec_ref(v_a_2555_);
v_a_2564_ = lean_ctor_get(v_x_2562_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v_x_2562_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2566_ = v_x_2562_;
v_isShared_2567_ = v_isSharedCheck_2572_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v_x_2562_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2572_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2564_);
v___x_2569_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
lean_object* v___x_2570_; 
v___x_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2569_);
return v___x_2570_;
}
}
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2591_; 
v_a_2573_ = lean_ctor_get(v_x_2562_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v_x_2562_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2575_ = v_x_2562_;
v_isShared_2576_ = v_isSharedCheck_2591_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v_x_2562_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2591_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___f_2577_; lean_object* v___f_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; uint8_t v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; uint8_t v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2587_; 
lean_inc_ref_n(v_a_2555_, 2);
lean_inc(v_a_2573_);
v___f_2577_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2577_, 0, v_a_2573_);
lean_closure_set(v___f_2577_, 1, v_a_2555_);
lean_inc(v_prio_2558_);
v___f_2578_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__6___boxed), 9, 7);
lean_closure_set(v___f_2578_, 0, v_a_2573_);
lean_closure_set(v___f_2578_, 1, v_a_2555_);
lean_closure_set(v___f_2578_, 2, v___f_2556_);
lean_closure_set(v___f_2578_, 3, v___f_2577_);
lean_closure_set(v___f_2578_, 4, v_y_2557_);
lean_closure_set(v___f_2578_, 5, v_prio_2558_);
lean_closure_set(v___f_2578_, 6, v___f_2559_);
v___x_2579_ = lean_apply_1(v_x_2560_, v_a_2555_);
v___x_2580_ = lean_unsigned_to_nat(0u);
v___x_2581_ = 0;
v___x_2582_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2582_, 0, lean_box(0));
lean_closure_set(v___x_2582_, 1, v___x_2579_);
v___x_2583_ = lean_io_as_task(v___x_2582_, v_prio_2558_);
v___x_2584_ = 1;
v___x_2585_ = lean_task_bind(v___x_2583_, v___f_2561_, v___x_2580_, v___x_2584_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 0, v___x_2585_);
v___x_2587_ = v___x_2575_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2585_);
v___x_2587_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
v___x_2589_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2580_, v___x_2581_, v___x_2588_, v___f_2578_);
return v___x_2589_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__7___boxed(lean_object* v_a_2592_, lean_object* v___f_2593_, lean_object* v_y_2594_, lean_object* v_prio_2595_, lean_object* v___f_2596_, lean_object* v_x_2597_, lean_object* v___f_2598_, lean_object* v_x_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Std_Async_ContextAsync_race___redArg___lam__7(v_a_2592_, v___f_2593_, v_y_2594_, v_prio_2595_, v___f_2596_, v_x_2597_, v___f_2598_, v_x_2599_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__8(lean_object* v___f_2602_, lean_object* v_y_2603_, lean_object* v_prio_2604_, lean_object* v___f_2605_, lean_object* v_x_2606_, lean_object* v___f_2607_, lean_object* v_a_2608_, lean_object* v_x_2609_){
_start:
{
if (lean_obj_tag(v_x_2609_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2619_; 
lean_dec_ref(v_a_2608_);
lean_dec_ref(v___f_2607_);
lean_dec_ref(v_x_2606_);
lean_dec_ref(v___f_2605_);
lean_dec(v_prio_2604_);
lean_dec_ref(v_y_2603_);
lean_dec_ref(v___f_2602_);
v_a_2611_ = lean_ctor_get(v_x_2609_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v_x_2609_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2613_ = v_x_2609_;
v_isShared_2614_ = v_isSharedCheck_2619_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v_x_2609_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2619_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
lean_object* v___x_2617_; 
v___x_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2616_);
return v___x_2617_;
}
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2633_; 
v_a_2620_ = lean_ctor_get(v_x_2609_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v_x_2609_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2622_ = v_x_2609_;
v_isShared_2623_ = v_isSharedCheck_2633_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v_x_2609_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2633_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___f_2624_; lean_object* v___x_2625_; uint8_t v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2629_; 
v___f_2624_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__7___boxed), 9, 7);
lean_closure_set(v___f_2624_, 0, v_a_2620_);
lean_closure_set(v___f_2624_, 1, v___f_2602_);
lean_closure_set(v___f_2624_, 2, v_y_2603_);
lean_closure_set(v___f_2624_, 3, v_prio_2604_);
lean_closure_set(v___f_2624_, 4, v___f_2605_);
lean_closure_set(v___f_2624_, 5, v_x_2606_);
lean_closure_set(v___f_2624_, 6, v___f_2607_);
v___x_2625_ = lean_unsigned_to_nat(0u);
v___x_2626_ = 0;
v___x_2627_ = l_Std_CancellationContext_fork(v_a_2608_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 0, v___x_2627_);
v___x_2629_ = v___x_2622_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2627_);
v___x_2629_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2629_);
v___x_2631_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2625_, v___x_2626_, v___x_2630_, v___f_2624_);
return v___x_2631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__8___boxed(lean_object* v___f_2634_, lean_object* v_y_2635_, lean_object* v_prio_2636_, lean_object* v___f_2637_, lean_object* v_x_2638_, lean_object* v___f_2639_, lean_object* v_a_2640_, lean_object* v_x_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l_Std_Async_ContextAsync_race___redArg___lam__8(v___f_2634_, v_y_2635_, v_prio_2636_, v___f_2637_, v_x_2638_, v___f_2639_, v_a_2640_, v_x_2641_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__9(lean_object* v___f_2644_, lean_object* v_y_2645_, lean_object* v_prio_2646_, lean_object* v___f_2647_, lean_object* v_x_2648_, lean_object* v___f_2649_, lean_object* v_x_2650_){
_start:
{
if (lean_obj_tag(v_x_2650_) == 0)
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2660_; 
lean_dec_ref(v___f_2649_);
lean_dec_ref(v_x_2648_);
lean_dec_ref(v___f_2647_);
lean_dec(v_prio_2646_);
lean_dec_ref(v_y_2645_);
lean_dec_ref(v___f_2644_);
v_a_2652_ = lean_ctor_get(v_x_2650_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v_x_2650_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2654_ = v_x_2650_;
v_isShared_2655_ = v_isSharedCheck_2660_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v_x_2650_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2660_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
lean_object* v___x_2658_; 
v___x_2658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2657_);
return v___x_2658_;
}
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2674_; 
v_a_2661_ = lean_ctor_get(v_x_2650_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v_x_2650_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2663_ = v_x_2650_;
v_isShared_2664_ = v_isSharedCheck_2674_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v_x_2650_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2674_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___f_2665_; lean_object* v___x_2666_; uint8_t v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2670_; 
lean_inc(v_a_2661_);
v___f_2665_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__8___boxed), 9, 7);
lean_closure_set(v___f_2665_, 0, v___f_2644_);
lean_closure_set(v___f_2665_, 1, v_y_2645_);
lean_closure_set(v___f_2665_, 2, v_prio_2646_);
lean_closure_set(v___f_2665_, 3, v___f_2647_);
lean_closure_set(v___f_2665_, 4, v_x_2648_);
lean_closure_set(v___f_2665_, 5, v___f_2649_);
lean_closure_set(v___f_2665_, 6, v_a_2661_);
v___x_2666_ = lean_unsigned_to_nat(0u);
v___x_2667_ = 0;
v___x_2668_ = l_Std_CancellationContext_fork(v_a_2661_);
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 0, v___x_2668_);
v___x_2670_ = v___x_2663_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2668_);
v___x_2670_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2670_);
v___x_2672_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2666_, v___x_2667_, v___x_2671_, v___f_2665_);
return v___x_2672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__9___boxed(lean_object* v___f_2675_, lean_object* v_y_2676_, lean_object* v_prio_2677_, lean_object* v___f_2678_, lean_object* v_x_2679_, lean_object* v___f_2680_, lean_object* v_x_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l_Std_Async_ContextAsync_race___redArg___lam__9(v___f_2675_, v_y_2676_, v_prio_2677_, v___f_2678_, v_x_2679_, v___f_2680_, v_x_2681_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg(lean_object* v_x_2684_, lean_object* v_y_2685_, lean_object* v_prio_2686_, lean_object* v_a_2687_){
_start:
{
lean_object* v___f_2689_; lean_object* v___f_2690_; lean_object* v___f_2691_; lean_object* v___x_2692_; uint8_t v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___f_2689_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_2690_ = ((lean_object*)(l_Std_Async_ContextAsync_raceAll___redArg___closed__0));
v___f_2691_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__9___boxed), 8, 6);
lean_closure_set(v___f_2691_, 0, v___f_2690_);
lean_closure_set(v___f_2691_, 1, v_y_2685_);
lean_closure_set(v___f_2691_, 2, v_prio_2686_);
lean_closure_set(v___f_2691_, 3, v___f_2689_);
lean_closure_set(v___f_2691_, 4, v_x_2684_);
lean_closure_set(v___f_2691_, 5, v___f_2689_);
v___x_2692_ = lean_unsigned_to_nat(0u);
v___x_2693_ = 0;
lean_inc_ref(v_a_2687_);
v___x_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2694_, 0, v_a_2687_);
v___x_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2694_);
v___x_2696_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2692_, v___x_2693_, v___x_2695_, v___f_2691_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___boxed(lean_object* v_x_2697_, lean_object* v_y_2698_, lean_object* v_prio_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l_Std_Async_ContextAsync_race___redArg(v_x_2697_, v_y_2698_, v_prio_2699_, v_a_2700_);
lean_dec_ref(v_a_2700_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race(lean_object* v_00_u03b1_2703_, lean_object* v_inst_2704_, lean_object* v_x_2705_, lean_object* v_y_2706_, lean_object* v_prio_2707_, lean_object* v_a_2708_){
_start:
{
lean_object* v___f_2710_; lean_object* v___f_2711_; lean_object* v___f_2712_; lean_object* v___x_2713_; uint8_t v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___f_2710_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_2711_ = ((lean_object*)(l_Std_Async_ContextAsync_raceAll___redArg___closed__0));
v___f_2712_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__9___boxed), 8, 6);
lean_closure_set(v___f_2712_, 0, v___f_2711_);
lean_closure_set(v___f_2712_, 1, v_y_2706_);
lean_closure_set(v___f_2712_, 2, v_prio_2707_);
lean_closure_set(v___f_2712_, 3, v___f_2710_);
lean_closure_set(v___f_2712_, 4, v_x_2705_);
lean_closure_set(v___f_2712_, 5, v___f_2710_);
v___x_2713_ = lean_unsigned_to_nat(0u);
v___x_2714_ = 0;
lean_inc_ref(v_a_2708_);
v___x_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2715_, 0, v_a_2708_);
v___x_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2715_);
v___x_2717_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2713_, v___x_2714_, v___x_2716_, v___f_2712_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___boxed(lean_object* v_00_u03b1_2718_, lean_object* v_inst_2719_, lean_object* v_x_2720_, lean_object* v_y_2721_, lean_object* v_prio_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Std_Async_ContextAsync_race(v_00_u03b1_2718_, v_inst_2719_, v_x_2720_, v_y_2721_, v_prio_2722_, v_a_2723_);
lean_dec_ref(v_a_2723_);
lean_dec(v_inst_2719_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selector_cancelled(lean_object* v_a_2726_){
_start:
{
lean_object* v___f_2728_; lean_object* v___x_2729_; uint8_t v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___f_2728_ = ((lean_object*)(l_Std_Async_ContextAsync_doneSelector___closed__0));
v___x_2729_ = lean_unsigned_to_nat(0u);
v___x_2730_ = 0;
lean_inc_ref(v_a_2726_);
v___x_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2731_, 0, v_a_2726_);
v___x_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2731_);
v___x_2733_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2729_, v___x_2730_, v___x_2732_, v___f_2728_);
return v___x_2733_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selector_cancelled___boxed(lean_object* v_a_2734_, lean_object* v_a_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Std_Async_Selector_cancelled(v_a_2734_);
lean_dec_ref(v_a_2734_);
return v_res_2736_;
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
