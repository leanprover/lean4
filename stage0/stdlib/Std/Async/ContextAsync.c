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
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Std_CancellationContext_cancel(lean_object*, lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Async_BaseAsync_toRawBaseIO___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_CancellationContext_fork(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_CancellationToken_selector(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Std_Async_EAsync_instMonad___redArg();
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Function_const___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_CancellationContext_new();
lean_object* l_Std_CancellationToken_getCancellationReason(lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* lean_io_promise_new();
lean_object* l_Std_CancellationToken_wait(lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_CancellationToken_isCancelled(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_runIn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_runIn___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_runIn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_runIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ContextAsync_concurrently___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_concurrently___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_concurrently___redArg___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_concurrently___redArg___closed__0_value;
static const lean_closure_object l_Std_Async_ContextAsync_concurrently___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_concurrently___redArg___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_concurrently___redArg___closed__1 = (const lean_object*)&l_Std_Async_ContextAsync_concurrently___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__0_value;
static lean_once_cell_t l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1;
static lean_once_cell_t l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_ContextAsync_background___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_ContextAsync_background___redArg___lam__2___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_background___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Std_Async_ContextAsync_background___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_ContextAsync_background___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Std_Async_ContextAsync_background___redArg___lam__2___closed__1 = (const lean_object*)&l_Std_Async_ContextAsync_background___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ContextAsync_raceAll___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_raceAll___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_closure_object l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Async_ContextAsync_concurrently___redArg___closed__1_value),((lean_object*)&l_Std_Async_ContextAsync_concurrently___redArg___closed__0_value)} };
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
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ContextAsync_race___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_race___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_race___redArg___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_race___redArg___closed__0_value;
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
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__0(lean_object* v_x_19_, lean_object* v_x_20_){
_start:
{
if (lean_obj_tag(v_x_20_) == 0)
{
lean_object* v_a_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_30_; 
lean_dec_ref(v_x_19_);
v_a_22_ = lean_ctor_get(v_x_20_, 0);
v_isSharedCheck_30_ = !lean_is_exclusive(v_x_20_);
if (v_isSharedCheck_30_ == 0)
{
v___x_24_ = v_x_20_;
v_isShared_25_ = v_isSharedCheck_30_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_a_22_);
lean_dec(v_x_20_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_30_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_a_22_);
v___x_27_ = v_reuseFailAlloc_29_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
lean_object* v___x_28_; 
v___x_28_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
return v___x_28_;
}
}
}
else
{
lean_object* v___x_31_; 
lean_dec_ref_known(v_x_20_, 1);
v___x_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_31_, 0, v_x_19_);
return v___x_31_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__0___boxed(lean_object* v_x_32_, lean_object* v_x_33_, lean_object* v___y_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Std_Async_ContextAsync_run___redArg___lam__0(v_x_32_, v_x_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__1(lean_object* v_a_36_, lean_object* v_x_37_){
_start:
{
if (lean_obj_tag(v_x_37_) == 0)
{
lean_object* v___x_39_; 
lean_dec_ref(v_a_36_);
v___x_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_39_, 0, v_x_37_);
return v___x_39_;
}
else
{
lean_object* v___f_40_; lean_object* v___x_41_; uint8_t v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___f_40_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_run___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_40_, 0, v_x_37_);
v___x_41_ = lean_unsigned_to_nat(0u);
v___x_42_ = 0;
v___x_43_ = lean_box(2);
v___x_44_ = l_Std_CancellationContext_cancel(v_a_36_, v___x_43_);
v___x_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
v___x_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
v___x_47_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_41_, v___x_42_, v___x_46_, v___f_40_);
return v___x_47_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__1___boxed(lean_object* v_a_48_, lean_object* v_x_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Std_Async_ContextAsync_run___redArg___lam__1(v_a_48_, v_x_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__2(lean_object* v_x_52_, lean_object* v_x_53_){
_start:
{
if (lean_obj_tag(v_x_53_) == 0)
{
lean_object* v_a_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_63_; 
lean_dec_ref(v_x_52_);
v_a_55_ = lean_ctor_get(v_x_53_, 0);
v_isSharedCheck_63_ = !lean_is_exclusive(v_x_53_);
if (v_isSharedCheck_63_ == 0)
{
v___x_57_ = v_x_53_;
v_isShared_58_ = v_isSharedCheck_63_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_a_55_);
lean_dec(v_x_53_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_63_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_60_; 
if (v_isShared_58_ == 0)
{
v___x_60_ = v___x_57_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_a_55_);
v___x_60_ = v_reuseFailAlloc_62_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
lean_object* v___x_61_; 
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
return v___x_61_;
}
}
}
else
{
lean_object* v_a_64_; lean_object* v___f_65_; lean_object* v___x_66_; uint8_t v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v_a_64_ = lean_ctor_get(v_x_53_, 0);
lean_inc_n(v_a_64_, 2);
lean_dec_ref_known(v_x_53_, 1);
v___f_65_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_run___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_65_, 0, v_a_64_);
v___x_66_ = lean_unsigned_to_nat(0u);
v___x_67_ = 0;
v___x_68_ = lean_apply_2(v_x_52_, v_a_64_, lean_box(0));
v___x_69_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_66_, v___x_67_, v___x_68_, v___f_65_);
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___lam__2___boxed(lean_object* v_x_70_, lean_object* v_x_71_, lean_object* v___y_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Std_Async_ContextAsync_run___redArg___lam__2(v_x_70_, v_x_71_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg(lean_object* v_x_74_){
_start:
{
lean_object* v___f_76_; lean_object* v___x_77_; uint8_t v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___f_76_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_run___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_76_, 0, v_x_74_);
v___x_77_ = lean_unsigned_to_nat(0u);
v___x_78_ = 0;
v___x_79_ = l_Std_CancellationContext_new();
v___x_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
v___x_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
v___x_82_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_77_, v___x_78_, v___x_81_, v___f_76_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___redArg___boxed(lean_object* v_x_83_, lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Std_Async_ContextAsync_run___redArg(v_x_83_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run(lean_object* v_00_u03b1_86_, lean_object* v_x_87_){
_start:
{
lean_object* v___f_89_; lean_object* v___x_90_; uint8_t v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___f_89_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_run___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_89_, 0, v_x_87_);
v___x_90_ = lean_unsigned_to_nat(0u);
v___x_91_ = 0;
v___x_92_ = l_Std_CancellationContext_new();
v___x_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
v___x_95_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_90_, v___x_91_, v___x_94_, v___f_89_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_run___boxed(lean_object* v_00_u03b1_96_, lean_object* v_x_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Std_Async_ContextAsync_run(v_00_u03b1_96_, v_x_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_getContext(lean_object* v_ctx_100_){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
lean_inc_ref(v_ctx_100_);
v___x_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_102_, 0, v_ctx_100_);
v___x_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_getContext___boxed(lean_object* v_ctx_104_, lean_object* v_a_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Std_Async_ContextAsync_getContext(v_ctx_104_);
lean_dec_ref(v_ctx_104_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_isCancelled___lam__0(lean_object* v_x_107_){
_start:
{
if (lean_obj_tag(v_x_107_) == 0)
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_117_; 
v_a_109_ = lean_ctor_get(v_x_107_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v_x_107_);
if (v_isSharedCheck_117_ == 0)
{
v___x_111_ = v_x_107_;
v_isShared_112_ = v_isSharedCheck_117_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v_x_107_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_117_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_112_ == 0)
{
v___x_114_ = v___x_111_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_109_);
v___x_114_ = v_reuseFailAlloc_116_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
lean_object* v___x_115_; 
v___x_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
return v___x_115_;
}
}
}
else
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_129_; 
v_a_118_ = lean_ctor_get(v_x_107_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v_x_107_);
if (v_isSharedCheck_129_ == 0)
{
v___x_120_ = v_x_107_;
v_isShared_121_ = v_isSharedCheck_129_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v_x_107_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_129_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v_token_122_; uint8_t v___x_123_; lean_object* v___x_124_; lean_object* v___x_126_; 
v_token_122_ = lean_ctor_get(v_a_118_, 1);
lean_inc_ref(v_token_122_);
lean_dec(v_a_118_);
v___x_123_ = l_Std_CancellationToken_isCancelled(v_token_122_);
v___x_124_ = lean_box(v___x_123_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v___x_124_);
v___x_126_ = v___x_120_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_124_);
v___x_126_ = v_reuseFailAlloc_128_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
lean_object* v___x_127_; 
v___x_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
return v___x_127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_isCancelled___lam__0___boxed(lean_object* v_x_130_, lean_object* v___y_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Std_Async_ContextAsync_isCancelled___lam__0(v_x_130_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_isCancelled(lean_object* v_a_134_){
_start:
{
lean_object* v___f_136_; lean_object* v___x_137_; uint8_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___f_136_ = ((lean_object*)(l_Std_Async_ContextAsync_isCancelled___closed__0));
v___x_137_ = lean_unsigned_to_nat(0u);
v___x_138_ = 0;
lean_inc_ref(v_a_134_);
v___x_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_139_, 0, v_a_134_);
v___x_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
v___x_141_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_137_, v___x_138_, v___x_140_, v___f_136_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_isCancelled___boxed(lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Std_Async_ContextAsync_isCancelled(v_a_142_);
lean_dec_ref(v_a_142_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_getCancellationReason___lam__0(lean_object* v_x_145_){
_start:
{
if (lean_obj_tag(v_x_145_) == 0)
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_155_; 
v_a_147_ = lean_ctor_get(v_x_145_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v_x_145_);
if (v_isSharedCheck_155_ == 0)
{
v___x_149_ = v_x_145_;
v_isShared_150_ = v_isSharedCheck_155_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v_x_145_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_155_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_154_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_153_; 
v___x_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
return v___x_153_;
}
}
}
else
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_166_; 
v_a_156_ = lean_ctor_get(v_x_145_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v_x_145_);
if (v_isSharedCheck_166_ == 0)
{
v___x_158_ = v_x_145_;
v_isShared_159_ = v_isSharedCheck_166_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v_x_145_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_166_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v_token_160_; lean_object* v___x_161_; lean_object* v___x_163_; 
v_token_160_ = lean_ctor_get(v_a_156_, 1);
lean_inc_ref(v_token_160_);
lean_dec(v_a_156_);
v___x_161_ = l_Std_CancellationToken_getCancellationReason(v_token_160_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_161_);
v___x_163_ = v___x_158_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_161_);
v___x_163_ = v_reuseFailAlloc_165_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
lean_object* v___x_164_; 
v___x_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_getCancellationReason___lam__0___boxed(lean_object* v_x_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Std_Async_ContextAsync_getCancellationReason___lam__0(v_x_167_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_getCancellationReason(lean_object* v_a_171_){
_start:
{
lean_object* v___f_173_; lean_object* v___x_174_; uint8_t v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___f_173_ = ((lean_object*)(l_Std_Async_ContextAsync_getCancellationReason___closed__0));
v___x_174_ = lean_unsigned_to_nat(0u);
v___x_175_ = 0;
lean_inc_ref(v_a_171_);
v___x_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_176_, 0, v_a_171_);
v___x_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
v___x_178_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_174_, v___x_175_, v___x_177_, v___f_173_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_getCancellationReason___boxed(lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Std_Async_ContextAsync_getCancellationReason(v_a_179_);
lean_dec_ref(v_a_179_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_cancel___lam__0(lean_object* v_reason_182_, lean_object* v_x_183_){
_start:
{
if (lean_obj_tag(v_x_183_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_193_; 
lean_dec(v_reason_182_);
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
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_203_; 
v_a_194_ = lean_ctor_get(v_x_183_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v_x_183_);
if (v_isSharedCheck_203_ == 0)
{
v___x_196_ = v_x_183_;
v_isShared_197_ = v_isSharedCheck_203_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v_x_183_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_203_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v___x_200_; 
v___x_198_ = l_Std_CancellationContext_cancel(v_a_194_, v_reason_182_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_198_);
v___x_200_ = v___x_196_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_198_);
v___x_200_ = v_reuseFailAlloc_202_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_201_; 
v___x_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
return v___x_201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_cancel___lam__0___boxed(lean_object* v_reason_204_, lean_object* v_x_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Std_Async_ContextAsync_cancel___lam__0(v_reason_204_, v_x_205_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_cancel(lean_object* v_reason_208_, lean_object* v_a_209_){
_start:
{
lean_object* v___f_211_; lean_object* v___x_212_; uint8_t v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___f_211_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_cancel___lam__0___boxed), 3, 1);
lean_closure_set(v___f_211_, 0, v_reason_208_);
v___x_212_ = lean_unsigned_to_nat(0u);
v___x_213_ = 0;
lean_inc_ref(v_a_209_);
v___x_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_214_, 0, v_a_209_);
v___x_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
v___x_216_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_212_, v___x_213_, v___x_215_, v___f_211_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_cancel___boxed(lean_object* v_reason_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Std_Async_ContextAsync_cancel(v_reason_217_, v_a_218_);
lean_dec_ref(v_a_218_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_doneSelector___lam__0(lean_object* v_x_221_){
_start:
{
if (lean_obj_tag(v_x_221_) == 0)
{
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_231_; 
v_a_223_ = lean_ctor_get(v_x_221_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v_x_221_);
if (v_isSharedCheck_231_ == 0)
{
v___x_225_ = v_x_221_;
v_isShared_226_ = v_isSharedCheck_231_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v_x_221_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_231_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_228_; 
if (v_isShared_226_ == 0)
{
v___x_228_ = v___x_225_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_223_);
v___x_228_ = v_reuseFailAlloc_230_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; 
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
return v___x_229_;
}
}
}
else
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_242_; 
v_a_232_ = lean_ctor_get(v_x_221_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v_x_221_);
if (v_isSharedCheck_242_ == 0)
{
v___x_234_ = v_x_221_;
v_isShared_235_ = v_isSharedCheck_242_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v_x_221_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_242_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v_token_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v_token_236_ = lean_ctor_get(v_a_232_, 1);
lean_inc_ref(v_token_236_);
lean_dec(v_a_232_);
v___x_237_ = l_Std_CancellationToken_selector(v_token_236_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v___x_237_);
v___x_239_ = v___x_234_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_241_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_240_; 
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_doneSelector___lam__0___boxed(lean_object* v_x_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Std_Async_ContextAsync_doneSelector___lam__0(v_x_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_doneSelector(lean_object* v_a_247_){
_start:
{
lean_object* v___f_249_; lean_object* v___x_250_; uint8_t v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___f_249_ = ((lean_object*)(l_Std_Async_ContextAsync_doneSelector___closed__0));
v___x_250_ = lean_unsigned_to_nat(0u);
v___x_251_ = 0;
lean_inc_ref(v_a_247_);
v___x_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_252_, 0, v_a_247_);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
v___x_254_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_250_, v___x_251_, v___x_253_, v___f_249_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_doneSelector___boxed(lean_object* v_a_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Std_Async_ContextAsync_doneSelector(v_a_255_);
lean_dec_ref(v_a_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_awaitCancellation___lam__0(lean_object* v_x_258_){
_start:
{
if (lean_obj_tag(v_x_258_) == 0)
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_268_; 
v_a_260_ = lean_ctor_get(v_x_258_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v_x_258_);
if (v_isSharedCheck_268_ == 0)
{
v___x_262_ = v_x_258_;
v_isShared_263_ = v_isSharedCheck_268_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v_x_258_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_268_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_260_);
v___x_265_ = v_reuseFailAlloc_267_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v___x_266_; 
v___x_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
return v___x_266_;
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_270_; 
v_a_269_ = lean_ctor_get(v_x_258_, 0);
lean_inc(v_a_269_);
lean_dec_ref_known(v_x_258_, 1);
v___x_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_270_, 0, v_a_269_);
return v___x_270_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_awaitCancellation___lam__0___boxed(lean_object* v_x_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Std_Async_ContextAsync_awaitCancellation___lam__0(v_x_271_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_awaitCancellation___lam__1(lean_object* v___f_274_, lean_object* v_x_275_){
_start:
{
if (lean_obj_tag(v_x_275_) == 0)
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_285_; 
lean_dec_ref(v___f_274_);
v_a_277_ = lean_ctor_get(v_x_275_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v_x_275_);
if (v_isSharedCheck_285_ == 0)
{
v___x_279_ = v_x_275_;
v_isShared_280_ = v_isSharedCheck_285_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v_x_275_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_285_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_277_);
v___x_282_ = v_reuseFailAlloc_284_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_283_; 
v___x_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
return v___x_283_;
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_306_; 
v_a_286_ = lean_ctor_get(v_x_275_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v_x_275_);
if (v_isSharedCheck_306_ == 0)
{
v___x_288_ = v_x_275_;
v_isShared_289_ = v_isSharedCheck_306_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v_x_275_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_306_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v_token_290_; lean_object* v___x_291_; uint8_t v___x_292_; lean_object* v_val_294_; lean_object* v___x_297_; 
v_token_290_ = lean_ctor_get(v_a_286_, 1);
lean_inc_ref(v_token_290_);
lean_dec(v_a_286_);
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_292_ = 0;
v___x_297_ = l_Std_CancellationToken_wait(v_token_290_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v_a_298_; lean_object* v___x_300_; 
v_a_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_a_298_);
lean_dec_ref_known(v___x_297_, 1);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v_a_298_);
v___x_300_ = v___x_288_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
v_val_294_ = v___x_300_;
goto v___jp_293_;
}
}
else
{
lean_object* v_a_302_; lean_object* v___x_304_; 
v_a_302_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_a_302_);
lean_dec_ref_known(v___x_297_, 1);
if (v_isShared_289_ == 0)
{
lean_ctor_set_tag(v___x_288_, 0);
lean_ctor_set(v___x_288_, 0, v_a_302_);
v___x_304_ = v___x_288_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
v_val_294_ = v___x_304_;
goto v___jp_293_;
}
}
v___jp_293_:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v_val_294_);
v___x_296_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_291_, v___x_292_, v___x_295_, v___f_274_);
return v___x_296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_awaitCancellation___lam__1___boxed(lean_object* v___f_307_, lean_object* v_x_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Std_Async_ContextAsync_awaitCancellation___lam__1(v___f_307_, v_x_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_awaitCancellation(lean_object* v_a_314_){
_start:
{
lean_object* v___f_316_; lean_object* v___x_317_; uint8_t v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___f_316_ = ((lean_object*)(l_Std_Async_ContextAsync_awaitCancellation___closed__1));
v___x_317_ = lean_unsigned_to_nat(0u);
v___x_318_ = 0;
lean_inc_ref(v_a_314_);
v___x_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_319_, 0, v_a_314_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
v___x_321_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_317_, v___x_318_, v___x_320_, v___f_316_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_awaitCancellation___boxed(lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Std_Async_ContextAsync_awaitCancellation(v_a_322_);
lean_dec_ref(v_a_322_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__0(lean_object* v_x_325_){
_start:
{
if (lean_obj_tag(v_x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_327_; 
v_a_326_ = lean_ctor_get(v_x_325_, 0);
lean_inc(v_a_326_);
lean_dec_ref_known(v_x_325_, 1);
v___x_327_ = lean_task_pure(v_a_326_);
return v___x_327_;
}
else
{
lean_object* v_a_328_; 
v_a_328_ = lean_ctor_get(v_x_325_, 0);
lean_inc_ref(v_a_328_);
lean_dec_ref_known(v_x_325_, 1);
return v_a_328_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__2(lean_object* v_x_329_){
_start:
{
lean_object* v_fst_330_; 
v_fst_330_ = lean_ctor_get(v_x_329_, 0);
lean_inc(v_fst_330_);
return v_fst_330_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__2___boxed(lean_object* v_x_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__2(v_x_331_);
lean_dec_ref(v_x_331_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__4(lean_object* v_a_333_, lean_object* v_x_334_){
_start:
{
if (lean_obj_tag(v_x_334_) == 0)
{
lean_object* v___f_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___f_336_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_run___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_336_, 0, v_x_334_);
v___x_337_ = lean_box(2);
v___x_338_ = lean_unsigned_to_nat(0u);
v___x_339_ = 0;
v___x_340_ = l_Std_CancellationContext_cancel(v_a_333_, v___x_337_);
v___x_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
v___x_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
v___x_343_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_338_, v___x_339_, v___x_342_, v___f_336_);
return v___x_343_;
}
else
{
lean_object* v___x_344_; 
lean_dec_ref(v_a_333_);
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v_x_334_);
return v___x_344_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__4___boxed(lean_object* v_a_345_, lean_object* v_x_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__4(v_a_345_, v_x_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__1(lean_object* v_x_349_, lean_object* v_a_350_, lean_object* v___f_351_){
_start:
{
lean_object* v___x_353_; uint8_t v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = 0;
v___x_355_ = lean_apply_2(v_x_349_, v_a_350_, lean_box(0));
v___x_356_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_353_, v___x_354_, v___x_355_, v___f_351_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__1___boxed(lean_object* v_x_357_, lean_object* v_a_358_, lean_object* v___f_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__1(v_x_357_, v_a_358_, v___f_359_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__3(lean_object* v_a_362_, lean_object* v___x_363_, lean_object* v_x_364_){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_366_ = l_Std_CancellationContext_cancel(v_a_362_, v___x_363_);
v___x_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__3___boxed(lean_object* v_a_369_, lean_object* v___x_370_, lean_object* v_x_371_, lean_object* v___y_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__3(v_a_369_, v___x_370_, v_x_371_);
lean_dec(v_x_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__5(lean_object* v___f_374_, lean_object* v___f_375_, lean_object* v___f_376_){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; lean_object* v___x_381_; lean_object* v___y_383_; 
v___x_378_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_378_, 0, lean_box(0));
lean_closure_set(v___x_378_, 1, lean_box(0));
lean_closure_set(v___x_378_, 2, lean_box(0));
lean_closure_set(v___x_378_, 3, v___f_374_);
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_380_ = 0;
v___x_381_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_375_, v___f_376_, v___x_379_, v___x_380_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_385_; 
lean_dec_ref(v___x_378_);
v_a_385_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_a_385_);
lean_dec_ref_known(v___x_381_, 1);
if (lean_obj_tag(v_a_385_) == 0)
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
v_a_386_ = lean_ctor_get(v_a_385_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v_a_385_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v_a_385_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v_a_385_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
v___y_383_ = v___x_391_;
goto v___jp_382_;
}
}
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_402_; 
v_a_394_ = lean_ctor_get(v_a_385_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v_a_385_);
if (v_isSharedCheck_402_ == 0)
{
v___x_396_ = v_a_385_;
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v_a_385_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v_fst_398_; lean_object* v___x_400_; 
v_fst_398_ = lean_ctor_get(v_a_394_, 0);
lean_inc(v_fst_398_);
lean_dec(v_a_394_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v_fst_398_);
v___x_400_ = v___x_396_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_fst_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
v___y_383_ = v___x_400_;
goto v___jp_382_;
}
}
}
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_411_; 
v_a_403_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_411_ == 0)
{
v___x_405_ = v___x_381_;
v_isShared_406_ = v_isSharedCheck_411_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_381_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_411_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_407_ = lean_task_map(v___x_378_, v_a_403_, v___x_379_, v___x_380_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v___x_407_);
v___x_409_ = v___x_405_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
v___jp_382_:
{
lean_object* v___x_384_; 
v___x_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_384_, 0, v___y_383_);
return v___x_384_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed(lean_object* v___f_412_, lean_object* v___f_413_, lean_object* v___f_414_, lean_object* v___y_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__5(v___f_412_, v___f_413_, v___f_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__7(lean_object* v_a_417_, lean_object* v___x_418_, lean_object* v_x_419_){
_start:
{
if (lean_obj_tag(v_x_419_) == 0)
{
lean_object* v___f_421_; lean_object* v___x_422_; uint8_t v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___f_421_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_run___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_421_, 0, v_x_419_);
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = 0;
v___x_424_ = l_Std_CancellationContext_cancel(v_a_417_, v___x_418_);
v___x_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
v___x_427_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_422_, v___x_423_, v___x_426_, v___f_421_);
return v___x_427_;
}
else
{
lean_object* v___x_428_; 
lean_dec(v___x_418_);
lean_dec_ref(v_a_417_);
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v_x_419_);
return v___x_428_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__7___boxed(lean_object* v_a_429_, lean_object* v___x_430_, lean_object* v_x_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__7(v_a_429_, v___x_430_, v_x_431_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__6(lean_object* v_y_434_, lean_object* v_a_435_, lean_object* v___f_436_){
_start:
{
lean_object* v___x_438_; uint8_t v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = 0;
v___x_440_ = lean_apply_2(v_y_434_, v_a_435_, lean_box(0));
v___x_441_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_438_, v___x_439_, v___x_440_, v___f_436_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__6___boxed(lean_object* v_y_442_, lean_object* v_a_443_, lean_object* v___f_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__6(v_y_442_, v_a_443_, v___f_444_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__10(lean_object* v_a_447_, lean_object* v_x_448_){
_start:
{
if (lean_obj_tag(v_x_448_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_458_; 
lean_dec(v_a_447_);
v_a_450_ = lean_ctor_get(v_x_448_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v_x_448_);
if (v_isSharedCheck_458_ == 0)
{
v___x_452_ = v_x_448_;
v_isShared_453_ = v_isSharedCheck_458_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v_x_448_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_458_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_457_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_456_; 
v___x_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
return v___x_456_;
}
}
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_468_; 
v_a_459_ = lean_ctor_get(v_x_448_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v_x_448_);
if (v_isSharedCheck_468_ == 0)
{
v___x_461_ = v_x_448_;
v_isShared_462_ = v_isSharedCheck_468_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v_x_448_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_468_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v_a_447_);
lean_ctor_set(v___x_463_, 1, v_a_459_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_463_);
v___x_465_ = v___x_461_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_463_);
v___x_465_ = v_reuseFailAlloc_467_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_466_; 
v___x_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
return v___x_466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__10___boxed(lean_object* v_a_469_, lean_object* v_x_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__10(v_a_469_, v_x_470_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__8(lean_object* v_a_473_, lean_object* v_x_474_){
_start:
{
if (lean_obj_tag(v_x_474_) == 0)
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_484_; 
lean_dec_ref(v_a_473_);
v_a_476_ = lean_ctor_get(v_x_474_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v_x_474_);
if (v_isSharedCheck_484_ == 0)
{
v___x_478_ = v_x_474_;
v_isShared_479_ = v_isSharedCheck_484_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v_x_474_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_484_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_483_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
lean_object* v___x_482_; 
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
return v___x_482_;
}
}
}
else
{
lean_object* v_a_485_; lean_object* v___f_486_; lean_object* v___x_487_; uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_a_485_ = lean_ctor_get(v_x_474_, 0);
lean_inc(v_a_485_);
lean_dec_ref_known(v_x_474_, 1);
v___f_486_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__10___boxed), 3, 1);
lean_closure_set(v___f_486_, 0, v_a_485_);
v___x_487_ = lean_unsigned_to_nat(0u);
v___x_488_ = 0;
v___x_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_489_, 0, v_a_473_);
v___x_490_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_487_, v___x_488_, v___x_489_, v___f_486_);
return v___x_490_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__8___boxed(lean_object* v_a_491_, lean_object* v_x_492_, lean_object* v___y_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__8(v_a_491_, v_x_492_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__9(lean_object* v_a_495_, lean_object* v_x_496_){
_start:
{
if (lean_obj_tag(v_x_496_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_506_; 
lean_dec_ref(v_a_495_);
v_a_498_ = lean_ctor_get(v_x_496_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v_x_496_);
if (v_isSharedCheck_506_ == 0)
{
v___x_500_ = v_x_496_;
v_isShared_501_ = v_isSharedCheck_506_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v_x_496_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_506_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_505_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; 
v___x_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
return v___x_504_;
}
}
}
else
{
lean_object* v_a_507_; lean_object* v___f_508_; lean_object* v___x_509_; uint8_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v_a_507_ = lean_ctor_get(v_x_496_, 0);
lean_inc(v_a_507_);
lean_dec_ref_known(v_x_496_, 1);
v___f_508_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__8___boxed), 3, 1);
lean_closure_set(v___f_508_, 0, v_a_507_);
v___x_509_ = lean_unsigned_to_nat(0u);
v___x_510_ = 0;
v___x_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_511_, 0, v_a_495_);
v___x_512_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_509_, v___x_510_, v___x_511_, v___f_508_);
return v___x_512_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__9___boxed(lean_object* v_a_513_, lean_object* v_x_514_, lean_object* v___y_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__9(v_a_513_, v_x_514_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__11(lean_object* v___f_517_, lean_object* v_prio_518_, lean_object* v___f_519_, lean_object* v_x_520_){
_start:
{
if (lean_obj_tag(v_x_520_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_530_; 
lean_dec_ref(v___f_519_);
lean_dec(v_prio_518_);
lean_dec_ref(v___f_517_);
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
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_547_; 
v_a_531_ = lean_ctor_get(v_x_520_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v_x_520_);
if (v_isSharedCheck_547_ == 0)
{
v___x_533_ = v_x_520_;
v_isShared_534_ = v_isSharedCheck_547_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v_x_520_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_547_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___f_535_; lean_object* v___x_536_; uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
v___f_535_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_535_, 0, v_a_531_);
v___x_536_ = lean_unsigned_to_nat(0u);
v___x_537_ = 0;
v___x_538_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_538_, 0, lean_box(0));
lean_closure_set(v___x_538_, 1, v___f_517_);
v___x_539_ = lean_io_as_task(v___x_538_, v_prio_518_);
v___x_540_ = 1;
v___x_541_ = lean_task_bind(v___x_539_, v___f_519_, v___x_536_, v___x_540_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_541_);
v___x_543_ = v___x_533_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_546_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
v___x_545_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_536_, v___x_537_, v___x_544_, v___f_535_);
return v___x_545_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__11___boxed(lean_object* v___f_548_, lean_object* v_prio_549_, lean_object* v___f_550_, lean_object* v_x_551_, lean_object* v___y_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__11(v___f_548_, v_prio_549_, v___f_550_, v_x_551_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__12(lean_object* v_x_554_, lean_object* v_x_555_){
_start:
{
if (lean_obj_tag(v_x_555_) == 0)
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_565_; 
lean_dec_ref(v_x_554_);
v_a_557_ = lean_ctor_get(v_x_555_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v_x_555_);
if (v_isSharedCheck_565_ == 0)
{
v___x_559_ = v_x_555_;
v_isShared_560_ = v_isSharedCheck_565_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v_x_555_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_565_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_564_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_563_; 
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
return v___x_563_;
}
}
}
else
{
lean_object* v___x_566_; 
lean_dec_ref_known(v_x_555_, 1);
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v_x_554_);
return v___x_566_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__12___boxed(lean_object* v_x_567_, lean_object* v_x_568_, lean_object* v___y_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__12(v_x_567_, v_x_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__13(lean_object* v_a_571_, lean_object* v___x_572_, lean_object* v_x_573_){
_start:
{
if (lean_obj_tag(v_x_573_) == 0)
{
lean_object* v___x_575_; 
lean_dec(v___x_572_);
lean_dec_ref(v_a_571_);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v_x_573_);
return v___x_575_;
}
else
{
lean_object* v___f_576_; lean_object* v___x_577_; uint8_t v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___f_576_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__12___boxed), 3, 1);
lean_closure_set(v___f_576_, 0, v_x_573_);
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_578_ = 0;
v___x_579_ = l_Std_CancellationContext_cancel(v_a_571_, v___x_572_);
v___x_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
v___x_582_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_577_, v___x_578_, v___x_581_, v___f_576_);
return v___x_582_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__13___boxed(lean_object* v_a_583_, lean_object* v___x_584_, lean_object* v_x_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__13(v_a_583_, v___x_584_, v_x_585_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__14(lean_object* v_a_588_, lean_object* v___f_589_, lean_object* v___f_590_, lean_object* v_a_591_, lean_object* v_y_592_, lean_object* v___f_593_, lean_object* v_prio_594_, lean_object* v___f_595_, lean_object* v___f_596_, lean_object* v_x_597_){
_start:
{
if (lean_obj_tag(v_x_597_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_607_; 
lean_dec_ref(v___f_596_);
lean_dec_ref(v___f_595_);
lean_dec(v_prio_594_);
lean_dec(v___f_593_);
lean_dec_ref(v_y_592_);
lean_dec_ref(v_a_591_);
lean_dec_ref(v___f_590_);
lean_dec(v___f_589_);
lean_dec_ref(v_a_588_);
v_a_599_ = lean_ctor_get(v_x_597_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v_x_597_);
if (v_isSharedCheck_607_ == 0)
{
v___x_601_ = v_x_597_;
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v_x_597_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_599_);
v___x_604_ = v_reuseFailAlloc_606_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_605_; 
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
return v___x_605_;
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_633_; 
v_a_608_ = lean_ctor_get(v_x_597_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v_x_597_);
if (v_isSharedCheck_633_ == 0)
{
v___x_610_ = v_x_597_;
v_isShared_611_ = v_isSharedCheck_633_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v_x_597_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_633_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v___f_613_; lean_object* v___f_614_; lean_object* v___f_615_; lean_object* v___f_616_; lean_object* v___f_617_; lean_object* v___f_618_; lean_object* v___f_619_; lean_object* v___f_620_; lean_object* v___x_621_; uint8_t v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; uint8_t v___x_625_; lean_object* v___x_626_; lean_object* v___x_628_; 
v___x_612_ = lean_box(2);
v___f_613_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_613_, 0, v_a_588_);
lean_closure_set(v___f_613_, 1, v___x_612_);
v___f_614_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_614_, 0, v___f_589_);
lean_closure_set(v___f_614_, 1, v___f_590_);
lean_closure_set(v___f_614_, 2, v___f_613_);
lean_inc_ref(v_a_591_);
v___f_615_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_615_, 0, v_a_591_);
lean_closure_set(v___f_615_, 1, v___x_612_);
lean_inc(v_a_608_);
v___f_616_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__6___boxed), 4, 3);
lean_closure_set(v___f_616_, 0, v_y_592_);
lean_closure_set(v___f_616_, 1, v_a_608_);
lean_closure_set(v___f_616_, 2, v___f_615_);
v___f_617_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_617_, 0, v_a_608_);
lean_closure_set(v___f_617_, 1, v___x_612_);
v___f_618_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_618_, 0, v___f_593_);
lean_closure_set(v___f_618_, 1, v___f_616_);
lean_closure_set(v___f_618_, 2, v___f_617_);
lean_inc(v_prio_594_);
v___f_619_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__11___boxed), 5, 3);
lean_closure_set(v___f_619_, 0, v___f_618_);
lean_closure_set(v___f_619_, 1, v_prio_594_);
lean_closure_set(v___f_619_, 2, v___f_595_);
v___f_620_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__13___boxed), 4, 2);
lean_closure_set(v___f_620_, 0, v_a_591_);
lean_closure_set(v___f_620_, 1, v___x_612_);
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = 0;
v___x_623_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_623_, 0, lean_box(0));
lean_closure_set(v___x_623_, 1, v___f_614_);
v___x_624_ = lean_io_as_task(v___x_623_, v_prio_594_);
v___x_625_ = 1;
v___x_626_ = lean_task_bind(v___x_624_, v___f_596_, v___x_621_, v___x_625_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_626_);
v___x_628_ = v___x_610_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_626_);
v___x_628_ = v_reuseFailAlloc_632_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
v___x_630_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_621_, v___x_622_, v___x_629_, v___f_619_);
v___x_631_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_621_, v___x_622_, v___x_630_, v___f_620_);
return v___x_631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__14___boxed(lean_object* v_a_634_, lean_object* v___f_635_, lean_object* v___f_636_, lean_object* v_a_637_, lean_object* v_y_638_, lean_object* v___f_639_, lean_object* v_prio_640_, lean_object* v___f_641_, lean_object* v___f_642_, lean_object* v_x_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__14(v_a_634_, v___f_635_, v___f_636_, v_a_637_, v_y_638_, v___f_639_, v_prio_640_, v___f_641_, v___f_642_, v_x_643_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__15(lean_object* v_x_646_, lean_object* v___f_647_, lean_object* v___f_648_, lean_object* v_a_649_, lean_object* v_y_650_, lean_object* v___f_651_, lean_object* v_prio_652_, lean_object* v___f_653_, lean_object* v___f_654_, lean_object* v_x_655_){
_start:
{
if (lean_obj_tag(v_x_655_) == 0)
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_665_; 
lean_dec_ref(v___f_654_);
lean_dec_ref(v___f_653_);
lean_dec(v_prio_652_);
lean_dec(v___f_651_);
lean_dec_ref(v_y_650_);
lean_dec_ref(v_a_649_);
lean_dec(v___f_648_);
lean_dec_ref(v___f_647_);
lean_dec_ref(v_x_646_);
v_a_657_ = lean_ctor_get(v_x_655_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v_x_655_);
if (v_isSharedCheck_665_ == 0)
{
v___x_659_ = v_x_655_;
v_isShared_660_ = v_isSharedCheck_665_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v_x_655_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_665_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_657_);
v___x_662_ = v_reuseFailAlloc_664_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_663_; 
v___x_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
return v___x_663_;
}
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_680_; 
v_a_666_ = lean_ctor_get(v_x_655_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v_x_655_);
if (v_isSharedCheck_680_ == 0)
{
v___x_668_ = v_x_655_;
v_isShared_669_ = v_isSharedCheck_680_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v_x_655_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_680_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___f_670_; lean_object* v___f_671_; lean_object* v___x_672_; uint8_t v___x_673_; lean_object* v___x_674_; lean_object* v___x_676_; 
lean_inc(v_a_666_);
v___f_670_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_670_, 0, v_x_646_);
lean_closure_set(v___f_670_, 1, v_a_666_);
lean_closure_set(v___f_670_, 2, v___f_647_);
lean_inc_ref(v_a_649_);
v___f_671_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__14___boxed), 11, 9);
lean_closure_set(v___f_671_, 0, v_a_666_);
lean_closure_set(v___f_671_, 1, v___f_648_);
lean_closure_set(v___f_671_, 2, v___f_670_);
lean_closure_set(v___f_671_, 3, v_a_649_);
lean_closure_set(v___f_671_, 4, v_y_650_);
lean_closure_set(v___f_671_, 5, v___f_651_);
lean_closure_set(v___f_671_, 6, v_prio_652_);
lean_closure_set(v___f_671_, 7, v___f_653_);
lean_closure_set(v___f_671_, 8, v___f_654_);
v___x_672_ = lean_unsigned_to_nat(0u);
v___x_673_ = 0;
v___x_674_ = l_Std_CancellationContext_fork(v_a_649_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_674_);
v___x_676_ = v___x_668_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_674_);
v___x_676_ = v_reuseFailAlloc_679_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
v___x_678_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_672_, v___x_673_, v___x_677_, v___f_671_);
return v___x_678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__15___boxed(lean_object* v_x_681_, lean_object* v___f_682_, lean_object* v___f_683_, lean_object* v_a_684_, lean_object* v_y_685_, lean_object* v___f_686_, lean_object* v_prio_687_, lean_object* v___f_688_, lean_object* v___f_689_, lean_object* v_x_690_, lean_object* v___y_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__15(v_x_681_, v___f_682_, v___f_683_, v_a_684_, v_y_685_, v___f_686_, v_prio_687_, v___f_688_, v___f_689_, v_x_690_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__16(lean_object* v_x_693_, lean_object* v___f_694_, lean_object* v_y_695_, lean_object* v___f_696_, lean_object* v_prio_697_, lean_object* v___f_698_, lean_object* v___f_699_, lean_object* v_x_700_){
_start:
{
if (lean_obj_tag(v_x_700_) == 0)
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_710_; 
lean_dec_ref(v___f_699_);
lean_dec_ref(v___f_698_);
lean_dec(v_prio_697_);
lean_dec(v___f_696_);
lean_dec_ref(v_y_695_);
lean_dec(v___f_694_);
lean_dec_ref(v_x_693_);
v_a_702_ = lean_ctor_get(v_x_700_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v_x_700_);
if (v_isSharedCheck_710_ == 0)
{
v___x_704_ = v_x_700_;
v_isShared_705_ = v_isSharedCheck_710_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v_x_700_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_710_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_709_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_708_; 
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
return v___x_708_;
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_725_; 
v_a_711_ = lean_ctor_get(v_x_700_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v_x_700_);
if (v_isSharedCheck_725_ == 0)
{
v___x_713_ = v_x_700_;
v_isShared_714_ = v_isSharedCheck_725_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v_x_700_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_725_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___f_715_; lean_object* v___f_716_; lean_object* v___x_717_; uint8_t v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
lean_inc_n(v_a_711_, 2);
v___f_715_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_715_, 0, v_a_711_);
v___f_716_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__15___boxed), 11, 9);
lean_closure_set(v___f_716_, 0, v_x_693_);
lean_closure_set(v___f_716_, 1, v___f_715_);
lean_closure_set(v___f_716_, 2, v___f_694_);
lean_closure_set(v___f_716_, 3, v_a_711_);
lean_closure_set(v___f_716_, 4, v_y_695_);
lean_closure_set(v___f_716_, 5, v___f_696_);
lean_closure_set(v___f_716_, 6, v_prio_697_);
lean_closure_set(v___f_716_, 7, v___f_698_);
lean_closure_set(v___f_716_, 8, v___f_699_);
v___x_717_ = lean_unsigned_to_nat(0u);
v___x_718_ = 0;
v___x_719_ = l_Std_CancellationContext_fork(v_a_711_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v___x_719_);
v___x_721_ = v___x_713_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_724_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
v___x_723_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_717_, v___x_718_, v___x_722_, v___f_716_);
return v___x_723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__16___boxed(lean_object* v_x_726_, lean_object* v___f_727_, lean_object* v_y_728_, lean_object* v___f_729_, lean_object* v_prio_730_, lean_object* v___f_731_, lean_object* v___f_732_, lean_object* v_x_733_, lean_object* v___y_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__16(v_x_726_, v___f_727_, v_y_728_, v___f_729_, v_prio_730_, v___f_731_, v___f_732_, v_x_733_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__17(lean_object* v___f_736_, lean_object* v_x_737_){
_start:
{
if (lean_obj_tag(v_x_737_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_747_; 
lean_dec_ref(v___f_736_);
v_a_739_ = lean_ctor_get(v_x_737_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v_x_737_);
if (v_isSharedCheck_747_ == 0)
{
v___x_741_ = v_x_737_;
v_isShared_742_ = v_isSharedCheck_747_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v_x_737_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_747_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_746_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v___x_745_; 
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
return v___x_745_;
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_760_; 
v_a_748_ = lean_ctor_get(v_x_737_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v_x_737_);
if (v_isSharedCheck_760_ == 0)
{
v___x_750_ = v_x_737_;
v_isShared_751_ = v_isSharedCheck_760_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v_x_737_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_760_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; uint8_t v___x_753_; lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_752_ = lean_unsigned_to_nat(0u);
v___x_753_ = 0;
v___x_754_ = l_Std_CancellationContext_fork(v_a_748_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v___x_754_);
v___x_756_ = v___x_750_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_754_);
v___x_756_ = v_reuseFailAlloc_759_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
v___x_758_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_752_, v___x_753_, v___x_757_, v___f_736_);
return v___x_758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__17___boxed(lean_object* v___f_761_, lean_object* v_x_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__17(v___f_761_, v_x_762_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg(lean_object* v_x_767_, lean_object* v_y_768_, lean_object* v_prio_769_, lean_object* v_a_770_){
_start:
{
lean_object* v___f_772_; lean_object* v___f_773_; lean_object* v___f_774_; lean_object* v___f_775_; lean_object* v___x_776_; uint8_t v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___f_772_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_773_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__1));
v___f_774_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__16___boxed), 9, 7);
lean_closure_set(v___f_774_, 0, v_x_767_);
lean_closure_set(v___f_774_, 1, v___f_773_);
lean_closure_set(v___f_774_, 2, v_y_768_);
lean_closure_set(v___f_774_, 3, v___f_773_);
lean_closure_set(v___f_774_, 4, v_prio_769_);
lean_closure_set(v___f_774_, 5, v___f_772_);
lean_closure_set(v___f_774_, 6, v___f_772_);
v___f_775_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__17___boxed), 3, 1);
lean_closure_set(v___f_775_, 0, v___f_774_);
v___x_776_ = lean_unsigned_to_nat(0u);
v___x_777_ = 0;
lean_inc_ref(v_a_770_);
v___x_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_778_, 0, v_a_770_);
v___x_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
v___x_780_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_776_, v___x_777_, v___x_779_, v___f_775_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___boxed(lean_object* v_x_781_, lean_object* v_y_782_, lean_object* v_prio_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Std_Async_ContextAsync_concurrently___redArg(v_x_781_, v_y_782_, v_prio_783_, v_a_784_);
lean_dec_ref(v_a_784_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently(lean_object* v_00_u03b1_787_, lean_object* v_00_u03b2_788_, lean_object* v_x_789_, lean_object* v_y_790_, lean_object* v_prio_791_, lean_object* v_a_792_){
_start:
{
lean_object* v___f_794_; lean_object* v___f_795_; lean_object* v___f_796_; lean_object* v___f_797_; lean_object* v___x_798_; uint8_t v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___f_794_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_795_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__1));
v___f_796_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__16___boxed), 9, 7);
lean_closure_set(v___f_796_, 0, v_x_789_);
lean_closure_set(v___f_796_, 1, v___f_795_);
lean_closure_set(v___f_796_, 2, v_y_790_);
lean_closure_set(v___f_796_, 3, v___f_795_);
lean_closure_set(v___f_796_, 4, v_prio_791_);
lean_closure_set(v___f_796_, 5, v___f_794_);
lean_closure_set(v___f_796_, 6, v___f_794_);
v___f_797_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__17___boxed), 3, 1);
lean_closure_set(v___f_797_, 0, v___f_796_);
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = 0;
lean_inc_ref(v_a_792_);
v___x_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_800_, 0, v_a_792_);
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
v___x_802_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_798_, v___x_799_, v___x_801_, v___f_797_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___boxed(lean_object* v_00_u03b1_803_, lean_object* v_00_u03b2_804_, lean_object* v_x_805_, lean_object* v_y_806_, lean_object* v_prio_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Std_Async_ContextAsync_concurrently(v_00_u03b1_803_, v_00_u03b2_804_, v_x_805_, v_y_806_, v_prio_807_, v_a_808_);
lean_dec_ref(v_a_808_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__0(lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_814_, 0, v___y_811_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__0___boxed(lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__0(v___y_815_, v___y_816_);
lean_dec_ref(v___y_816_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3(lean_object* v___x_819_, lean_object* v___f_820_, lean_object* v_a_821_, lean_object* v_x_822_){
_start:
{
if (lean_obj_tag(v_x_822_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_832_; 
lean_dec_ref(v___f_820_);
lean_dec_ref(v___x_819_);
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
lean_object* v_a_833_; size_t v_sz_834_; size_t v___x_835_; lean_object* v___x_4339__overap_836_; lean_object* v___x_837_; 
v_a_833_ = lean_ctor_get(v_x_822_, 0);
lean_inc(v_a_833_);
lean_dec_ref_known(v_x_822_, 1);
v_sz_834_ = lean_array_size(v_a_833_);
v___x_835_ = ((size_t)0ULL);
v___x_4339__overap_836_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_819_, v___f_820_, v_sz_834_, v___x_835_, v_a_833_);
lean_inc_ref(v_a_821_);
v___x_837_ = lean_apply_2(v___x_4339__overap_836_, v_a_821_, lean_box(0));
return v___x_837_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3___boxed(lean_object* v___x_838_, lean_object* v___f_839_, lean_object* v_a_840_, lean_object* v_x_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3(v___x_838_, v___f_839_, v_a_840_, v_x_841_);
lean_dec_ref(v_a_840_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4(lean_object* v_ctxAsync_844_, lean_object* v_a_845_, lean_object* v___f_846_){
_start:
{
lean_object* v___x_848_; uint8_t v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_848_ = lean_unsigned_to_nat(0u);
v___x_849_ = 0;
v___x_850_ = lean_apply_2(v_ctxAsync_844_, v_a_845_, lean_box(0));
v___x_851_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_848_, v___x_849_, v___x_850_, v___f_846_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4___boxed(lean_object* v_ctxAsync_852_, lean_object* v_a_853_, lean_object* v___f_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4(v_ctxAsync_852_, v_a_853_, v___f_854_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1(lean_object* v_a_857_, lean_object* v___x_858_, lean_object* v_a_x3f_859_){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_861_ = l_Std_CancellationContext_cancel(v_a_857_, v___x_858_);
v___x_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1___boxed(lean_object* v_a_864_, lean_object* v___x_865_, lean_object* v_a_x3f_866_, lean_object* v___y_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1(v_a_864_, v___x_865_, v_a_x3f_866_);
lean_dec(v_a_x3f_866_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5(lean_object* v_ctxAsync_869_, lean_object* v___f_870_, lean_object* v___f_871_, lean_object* v_prio_872_, lean_object* v___f_873_, lean_object* v_x_874_){
_start:
{
if (lean_obj_tag(v_x_874_) == 0)
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_884_; 
lean_dec_ref(v___f_873_);
lean_dec(v_prio_872_);
lean_dec(v___f_871_);
lean_dec_ref(v___f_870_);
lean_dec_ref(v_ctxAsync_869_);
v_a_876_ = lean_ctor_get(v_x_874_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v_x_874_);
if (v_isSharedCheck_884_ == 0)
{
v___x_878_ = v_x_874_;
v_isShared_879_ = v_isSharedCheck_884_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v_x_874_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_884_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_883_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_882_; 
v___x_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
return v___x_882_;
}
}
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_902_; 
v_a_885_ = lean_ctor_get(v_x_874_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v_x_874_);
if (v_isSharedCheck_902_ == 0)
{
v___x_887_ = v_x_874_;
v_isShared_888_ = v_isSharedCheck_902_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v_x_874_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_902_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___f_889_; lean_object* v___x_890_; lean_object* v___f_891_; lean_object* v___f_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
lean_inc(v_a_885_);
v___f_889_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_889_, 0, v_ctxAsync_869_);
lean_closure_set(v___f_889_, 1, v_a_885_);
lean_closure_set(v___f_889_, 2, v___f_870_);
v___x_890_ = lean_box(2);
v___f_891_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_891_, 0, v_a_885_);
lean_closure_set(v___f_891_, 1, v___x_890_);
v___f_892_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_892_, 0, v___f_871_);
lean_closure_set(v___f_892_, 1, v___f_889_);
lean_closure_set(v___f_892_, 2, v___f_891_);
v___x_893_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_893_, 0, lean_box(0));
lean_closure_set(v___x_893_, 1, v___f_892_);
v___x_894_ = lean_io_as_task(v___x_893_, v_prio_872_);
v___x_895_ = lean_unsigned_to_nat(0u);
v___x_896_ = 1;
v___x_897_ = lean_task_bind(v___x_894_, v___f_873_, v___x_895_, v___x_896_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_897_);
v___x_899_ = v___x_887_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_901_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_900_; 
v___x_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
return v___x_900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5___boxed(lean_object* v_ctxAsync_903_, lean_object* v___f_904_, lean_object* v___f_905_, lean_object* v_prio_906_, lean_object* v___f_907_, lean_object* v_x_908_, lean_object* v___y_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5(v_ctxAsync_903_, v___f_904_, v___f_905_, v_prio_906_, v___f_907_, v_x_908_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2(lean_object* v___f_911_, lean_object* v___f_912_, lean_object* v_prio_913_, lean_object* v___f_914_, lean_object* v_a_915_, lean_object* v_ctxAsync_916_, lean_object* v___y_917_){
_start:
{
lean_object* v___f_919_; lean_object* v___x_920_; uint8_t v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___f_919_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5___boxed), 7, 5);
lean_closure_set(v___f_919_, 0, v_ctxAsync_916_);
lean_closure_set(v___f_919_, 1, v___f_911_);
lean_closure_set(v___f_919_, 2, v___f_912_);
lean_closure_set(v___f_919_, 3, v_prio_913_);
lean_closure_set(v___f_919_, 4, v___f_914_);
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = 0;
v___x_922_ = l_Std_CancellationContext_fork(v_a_915_);
v___x_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
v___x_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
v___x_925_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_920_, v___x_921_, v___x_924_, v___f_919_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2___boxed(lean_object* v___f_926_, lean_object* v___f_927_, lean_object* v_prio_928_, lean_object* v___f_929_, lean_object* v_a_930_, lean_object* v_ctxAsync_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2(v___f_926_, v___f_927_, v_prio_928_, v___f_929_, v_a_930_, v_ctxAsync_931_, v___y_932_);
lean_dec_ref(v___y_932_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6(lean_object* v___f_935_, lean_object* v_prio_936_, lean_object* v___f_937_, lean_object* v_xs_938_, lean_object* v___x_939_, lean_object* v_a_940_, lean_object* v___f_941_, lean_object* v_x_942_){
_start:
{
if (lean_obj_tag(v_x_942_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_952_; 
lean_dec_ref(v___f_941_);
lean_dec_ref(v___x_939_);
lean_dec_ref(v_xs_938_);
lean_dec_ref(v___f_937_);
lean_dec(v_prio_936_);
lean_dec(v___f_935_);
v_a_944_ = lean_ctor_get(v_x_942_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v_x_942_);
if (v_isSharedCheck_952_ == 0)
{
v___x_946_ = v_x_942_;
v_isShared_947_ = v_isSharedCheck_952_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v_x_942_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_952_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_944_);
v___x_949_ = v_reuseFailAlloc_951_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; 
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
return v___x_950_;
}
}
}
else
{
lean_object* v_a_953_; lean_object* v___f_954_; lean_object* v___f_955_; lean_object* v___x_956_; uint8_t v___x_957_; size_t v_sz_958_; size_t v___x_959_; lean_object* v___x_4463__overap_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v_a_953_ = lean_ctor_get(v_x_942_, 0);
lean_inc_n(v_a_953_, 2);
lean_dec_ref_known(v_x_942_, 1);
v___f_954_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_954_, 0, v_a_953_);
v___f_955_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_955_, 0, v___f_954_);
lean_closure_set(v___f_955_, 1, v___f_935_);
lean_closure_set(v___f_955_, 2, v_prio_936_);
lean_closure_set(v___f_955_, 3, v___f_937_);
lean_closure_set(v___f_955_, 4, v_a_953_);
v___x_956_ = lean_unsigned_to_nat(0u);
v___x_957_ = 0;
v_sz_958_ = lean_array_size(v_xs_938_);
v___x_959_ = ((size_t)0ULL);
v___x_4463__overap_960_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_939_, v___f_955_, v_sz_958_, v___x_959_, v_xs_938_);
lean_inc_ref(v_a_940_);
v___x_961_ = lean_apply_2(v___x_4463__overap_960_, v_a_940_, lean_box(0));
v___x_962_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_956_, v___x_957_, v___x_961_, v___f_941_);
return v___x_962_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6___boxed(lean_object* v___f_963_, lean_object* v_prio_964_, lean_object* v___f_965_, lean_object* v_xs_966_, lean_object* v___x_967_, lean_object* v_a_968_, lean_object* v___f_969_, lean_object* v_x_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6(v___f_963_, v_prio_964_, v___f_965_, v_xs_966_, v___x_967_, v_a_968_, v___f_969_, v_x_970_);
lean_dec_ref(v_a_968_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7(lean_object* v___f_973_, lean_object* v_x_974_){
_start:
{
if (lean_obj_tag(v_x_974_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_984_; 
lean_dec_ref(v___f_973_);
v_a_976_ = lean_ctor_get(v_x_974_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v_x_974_);
if (v_isSharedCheck_984_ == 0)
{
v___x_978_ = v_x_974_;
v_isShared_979_ = v_isSharedCheck_984_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v_x_974_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_984_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_983_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_982_; 
v___x_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
return v___x_982_;
}
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_997_; 
v_a_985_ = lean_ctor_get(v_x_974_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v_x_974_);
if (v_isSharedCheck_997_ == 0)
{
v___x_987_ = v_x_974_;
v_isShared_988_ = v_isSharedCheck_997_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v_x_974_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_997_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; uint8_t v___x_990_; lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_989_ = lean_unsigned_to_nat(0u);
v___x_990_ = 0;
v___x_991_ = l_Std_CancellationContext_fork(v_a_985_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v___x_991_);
v___x_993_ = v___x_987_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_991_);
v___x_993_ = v_reuseFailAlloc_996_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
v___x_995_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_989_, v___x_990_, v___x_994_, v___f_973_);
return v___x_995_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7___boxed(lean_object* v___f_998_, lean_object* v_x_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7(v___f_998_, v_x_999_);
return v_res_1001_;
}
}
static lean_object* _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1(void){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_1003_;
}
}
static lean_object* _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = lean_obj_once(&l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1, &l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1_once, _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1);
v___x_1005_ = l_ReaderT_instMonad___redArg(v___x_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg(lean_object* v_xs_1006_, lean_object* v_prio_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v___f_1010_; lean_object* v___f_1011_; lean_object* v___f_1012_; lean_object* v___x_1013_; lean_object* v___f_1014_; lean_object* v___f_1015_; lean_object* v___f_1016_; lean_object* v___x_1017_; uint8_t v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___f_1010_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__0));
v___f_1011_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_1012_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__1));
v___x_1013_ = lean_obj_once(&l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2, &l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2_once, _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2);
lean_inc_ref_n(v_a_1008_, 3);
v___f_1014_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_1014_, 0, v___x_1013_);
lean_closure_set(v___f_1014_, 1, v___f_1010_);
lean_closure_set(v___f_1014_, 2, v_a_1008_);
v___f_1015_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6___boxed), 9, 7);
lean_closure_set(v___f_1015_, 0, v___f_1012_);
lean_closure_set(v___f_1015_, 1, v_prio_1007_);
lean_closure_set(v___f_1015_, 2, v___f_1011_);
lean_closure_set(v___f_1015_, 3, v_xs_1006_);
lean_closure_set(v___f_1015_, 4, v___x_1013_);
lean_closure_set(v___f_1015_, 5, v_a_1008_);
lean_closure_set(v___f_1015_, 6, v___f_1014_);
v___f_1016_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_1016_, 0, v___f_1015_);
v___x_1017_ = lean_unsigned_to_nat(0u);
v___x_1018_ = 0;
v___x_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1019_, 0, v_a_1008_);
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
v___x_1021_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1017_, v___x_1018_, v___x_1020_, v___f_1016_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___boxed(lean_object* v_xs_1022_, lean_object* v_prio_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg(v_xs_1022_, v_prio_1023_, v_a_1024_);
lean_dec_ref(v_a_1024_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll(lean_object* v_00_u03b1_1027_, lean_object* v_xs_1028_, lean_object* v_prio_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v___f_1032_; lean_object* v___f_1033_; lean_object* v___f_1034_; lean_object* v___x_1035_; lean_object* v___f_1036_; lean_object* v___f_1037_; lean_object* v___f_1038_; lean_object* v___x_1039_; uint8_t v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___f_1032_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__0));
v___f_1033_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_1034_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__1));
v___x_1035_ = lean_obj_once(&l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2, &l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2_once, _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2);
lean_inc_ref_n(v_a_1030_, 3);
v___f_1036_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_1036_, 0, v___x_1035_);
lean_closure_set(v___f_1036_, 1, v___f_1032_);
lean_closure_set(v___f_1036_, 2, v_a_1030_);
v___f_1037_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6___boxed), 9, 7);
lean_closure_set(v___f_1037_, 0, v___f_1034_);
lean_closure_set(v___f_1037_, 1, v_prio_1029_);
lean_closure_set(v___f_1037_, 2, v___f_1033_);
lean_closure_set(v___f_1037_, 3, v_xs_1028_);
lean_closure_set(v___f_1037_, 4, v___x_1035_);
lean_closure_set(v___f_1037_, 5, v_a_1030_);
lean_closure_set(v___f_1037_, 6, v___f_1036_);
v___f_1038_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_1038_, 0, v___f_1037_);
v___x_1039_ = lean_unsigned_to_nat(0u);
v___x_1040_ = 0;
v___x_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1041_, 0, v_a_1030_);
v___x_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
v___x_1043_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1039_, v___x_1040_, v___x_1042_, v___f_1038_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___boxed(lean_object* v_00_u03b1_1044_, lean_object* v_xs_1045_, lean_object* v_prio_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Std_Async_ContextAsync_concurrentlyAll(v_00_u03b1_1044_, v_xs_1045_, v_prio_1046_, v_a_1047_);
lean_dec_ref(v_a_1047_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__0(lean_object* v_a_1050_, lean_object* v_x_1051_){
_start:
{
if (lean_obj_tag(v_x_1051_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1061_; 
lean_dec_ref(v_a_1050_);
v_a_1053_ = lean_ctor_get(v_x_1051_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_x_1051_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1055_ = v_x_1051_;
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v_x_1051_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
return v___x_1059_;
}
}
}
else
{
lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1071_; 
v_isSharedCheck_1071_ = !lean_is_exclusive(v_x_1051_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; 
v_unused_1072_ = lean_ctor_get(v_x_1051_, 0);
lean_dec(v_unused_1072_);
v___x_1063_ = v_x_1051_;
v_isShared_1064_ = v_isSharedCheck_1071_;
goto v_resetjp_1062_;
}
else
{
lean_dec(v_x_1051_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1071_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1065_ = lean_box(2);
v___x_1066_ = l_Std_CancellationContext_cancel(v_a_1050_, v___x_1065_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1066_);
v___x_1068_ = v___x_1063_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
return v___x_1069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__0___boxed(lean_object* v_a_1073_, lean_object* v_x_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Std_Async_ContextAsync_background___redArg___lam__0(v_a_1073_, v_x_1074_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__1(lean_object* v_action_1077_, lean_object* v_a_1078_, lean_object* v___f_1079_){
_start:
{
lean_object* v___x_1081_; uint8_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1081_ = lean_unsigned_to_nat(0u);
v___x_1082_ = 0;
v___x_1083_ = lean_apply_2(v_action_1077_, v_a_1078_, lean_box(0));
v___x_1084_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1081_, v___x_1082_, v___x_1083_, v___f_1079_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__1___boxed(lean_object* v_action_1085_, lean_object* v_a_1086_, lean_object* v___f_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Std_Async_ContextAsync_background___redArg___lam__1(v_action_1085_, v_a_1086_, v___f_1087_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__2(lean_object* v_action_1094_, lean_object* v_prio_1095_, lean_object* v_x_1096_){
_start:
{
if (lean_obj_tag(v_x_1096_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1106_; 
lean_dec(v_prio_1095_);
lean_dec_ref(v_action_1094_);
v_a_1098_ = lean_ctor_get(v_x_1096_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_x_1096_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1100_ = v_x_1096_;
v_isShared_1101_ = v_isSharedCheck_1106_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v_x_1096_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1106_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
return v___x_1104_;
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___f_1108_; lean_object* v___f_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v_a_1107_ = lean_ctor_get(v_x_1096_, 0);
lean_inc_n(v_a_1107_, 2);
lean_dec_ref_known(v_x_1096_, 1);
v___f_1108_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_background___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1108_, 0, v_a_1107_);
v___f_1109_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_background___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1109_, 0, v_action_1094_);
lean_closure_set(v___f_1109_, 1, v_a_1107_);
lean_closure_set(v___f_1109_, 2, v___f_1108_);
v___x_1110_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1110_, 0, lean_box(0));
lean_closure_set(v___x_1110_, 1, v___f_1109_);
v___x_1111_ = lean_io_as_task(v___x_1110_, v_prio_1095_);
lean_dec_ref(v___x_1111_);
v___x_1112_ = ((lean_object*)(l_Std_Async_ContextAsync_background___redArg___lam__2___closed__1));
return v___x_1112_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__2___boxed(lean_object* v_action_1113_, lean_object* v_prio_1114_, lean_object* v_x_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Std_Async_ContextAsync_background___redArg___lam__2(v_action_1113_, v_prio_1114_, v_x_1115_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__3(lean_object* v___f_1118_, lean_object* v_x_1119_){
_start:
{
if (lean_obj_tag(v_x_1119_) == 0)
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1129_; 
lean_dec_ref(v___f_1118_);
v_a_1121_ = lean_ctor_get(v_x_1119_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_x_1119_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1123_ = v_x_1119_;
v_isShared_1124_ = v_isSharedCheck_1129_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v_x_1119_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1129_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
lean_object* v___x_1127_; 
v___x_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
return v___x_1127_;
}
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1142_; 
v_a_1130_ = lean_ctor_get(v_x_1119_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_x_1119_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1132_ = v_x_1119_;
v_isShared_1133_ = v_isSharedCheck_1142_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v_x_1119_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1142_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; uint8_t v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1134_ = lean_unsigned_to_nat(0u);
v___x_1135_ = 0;
v___x_1136_ = l_Std_CancellationContext_fork(v_a_1130_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___x_1136_);
v___x_1138_ = v___x_1132_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
v___x_1140_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1134_, v___x_1135_, v___x_1139_, v___f_1118_);
return v___x_1140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__3___boxed(lean_object* v___f_1143_, lean_object* v_x_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Std_Async_ContextAsync_background___redArg___lam__3(v___f_1143_, v_x_1144_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg(lean_object* v_action_1147_, lean_object* v_prio_1148_, lean_object* v_a_1149_){
_start:
{
lean_object* v___f_1151_; lean_object* v___f_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___f_1151_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_background___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1151_, 0, v_action_1147_);
lean_closure_set(v___f_1151_, 1, v_prio_1148_);
v___f_1152_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_background___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1152_, 0, v___f_1151_);
v___x_1153_ = lean_unsigned_to_nat(0u);
v___x_1154_ = 0;
lean_inc_ref(v_a_1149_);
v___x_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1155_, 0, v_a_1149_);
v___x_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
v___x_1157_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1153_, v___x_1154_, v___x_1156_, v___f_1152_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___boxed(lean_object* v_action_1158_, lean_object* v_prio_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Std_Async_ContextAsync_background___redArg(v_action_1158_, v_prio_1159_, v_a_1160_);
lean_dec_ref(v_a_1160_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background(lean_object* v_00_u03b1_1163_, lean_object* v_action_1164_, lean_object* v_prio_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v___f_1168_; lean_object* v___f_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___f_1168_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_background___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1168_, 0, v_action_1164_);
lean_closure_set(v___f_1168_, 1, v_prio_1165_);
v___f_1169_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_background___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1169_, 0, v___f_1168_);
v___x_1170_ = lean_unsigned_to_nat(0u);
v___x_1171_ = 0;
lean_inc_ref(v_a_1166_);
v___x_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1172_, 0, v_a_1166_);
v___x_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
v___x_1174_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1170_, v___x_1171_, v___x_1173_, v___f_1169_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___boxed(lean_object* v_00_u03b1_1175_, lean_object* v_action_1176_, lean_object* v_prio_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Std_Async_ContextAsync_background(v_00_u03b1_1175_, v_action_1176_, v_prio_1177_, v_a_1178_);
lean_dec_ref(v_a_1178_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg___lam__0(lean_object* v_action_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_apply_2(v_action_1181_, v_a_1182_, lean_box(0));
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg___lam__0___boxed(lean_object* v_action_1185_, lean_object* v_a_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Std_Async_ContextAsync_disown___redArg___lam__0(v_action_1185_, v_a_1186_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg___lam__1(lean_object* v_action_1189_, lean_object* v_prio_1190_, lean_object* v_x_1191_){
_start:
{
if (lean_obj_tag(v_x_1191_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1201_; 
lean_dec(v_prio_1190_);
lean_dec_ref(v_action_1189_);
v_a_1193_ = lean_ctor_get(v_x_1191_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_x_1191_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1195_ = v_x_1191_;
v_isShared_1196_ = v_isSharedCheck_1201_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v_x_1191_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1201_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1199_; 
v___x_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
return v___x_1199_;
}
}
}
else
{
lean_object* v_a_1202_; lean_object* v___f_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v_a_1202_ = lean_ctor_get(v_x_1191_, 0);
lean_inc(v_a_1202_);
lean_dec_ref_known(v_x_1191_, 1);
v___f_1203_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_disown___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1203_, 0, v_action_1189_);
lean_closure_set(v___f_1203_, 1, v_a_1202_);
v___x_1204_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1204_, 0, lean_box(0));
lean_closure_set(v___x_1204_, 1, v___f_1203_);
v___x_1205_ = lean_io_as_task(v___x_1204_, v_prio_1190_);
lean_dec_ref(v___x_1205_);
v___x_1206_ = ((lean_object*)(l_Std_Async_ContextAsync_background___redArg___lam__2___closed__1));
return v___x_1206_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg___lam__1___boxed(lean_object* v_action_1207_, lean_object* v_prio_1208_, lean_object* v_x_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Std_Async_ContextAsync_disown___redArg___lam__1(v_action_1207_, v_prio_1208_, v_x_1209_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg(lean_object* v_action_1212_, lean_object* v_prio_1213_){
_start:
{
lean_object* v___f_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___f_1215_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_disown___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1215_, 0, v_action_1212_);
lean_closure_set(v___f_1215_, 1, v_prio_1213_);
v___x_1216_ = lean_unsigned_to_nat(0u);
v___x_1217_ = 0;
v___x_1218_ = l_Std_CancellationContext_new();
v___x_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
v___x_1221_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1216_, v___x_1217_, v___x_1220_, v___f_1215_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg___boxed(lean_object* v_action_1222_, lean_object* v_prio_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Std_Async_ContextAsync_disown___redArg(v_action_1222_, v_prio_1223_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown(lean_object* v_00_u03b1_1226_, lean_object* v_action_1227_, lean_object* v_prio_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v___f_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___f_1231_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_disown___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1231_, 0, v_action_1227_);
lean_closure_set(v___f_1231_, 1, v_prio_1228_);
v___x_1232_ = lean_unsigned_to_nat(0u);
v___x_1233_ = 0;
v___x_1234_ = l_Std_CancellationContext_new();
v___x_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
v___x_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
v___x_1237_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1232_, v___x_1233_, v___x_1236_, v___f_1231_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___boxed(lean_object* v_00_u03b1_1238_, lean_object* v_action_1239_, lean_object* v_prio_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Std_Async_ContextAsync_disown(v_00_u03b1_1238_, v_action_1239_, v_prio_1240_, v_a_1241_);
lean_dec_ref(v_a_1241_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__0(lean_object* v_a_1244_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1245_, 0, v_a_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__2(lean_object* v_a_1246_, lean_object* v_x_1247_){
_start:
{
if (lean_obj_tag(v_x_1247_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1257_; 
lean_dec_ref(v_a_1246_);
v_a_1249_ = lean_ctor_get(v_x_1247_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v_x_1247_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1251_ = v_x_1247_;
v_isShared_1252_ = v_isSharedCheck_1257_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v_x_1247_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1257_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
lean_object* v___x_1255_; 
v___x_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
return v___x_1255_;
}
}
}
else
{
lean_object* v___x_1258_; 
lean_dec_ref_known(v_x_1247_, 1);
v___x_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1258_, 0, v_a_1246_);
return v___x_1258_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__2___boxed(lean_object* v_a_1259_, lean_object* v_x_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__2(v_a_1259_, v_x_1260_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__1(lean_object* v_a_1263_, lean_object* v_x_1264_){
_start:
{
if (lean_obj_tag(v_x_1264_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1274_; 
lean_dec_ref(v_a_1263_);
v_a_1266_ = lean_ctor_get(v_x_1264_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_x_1264_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1268_ = v_x_1264_;
v_isShared_1269_ = v_isSharedCheck_1274_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v_x_1264_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1274_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1272_; 
v___x_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
return v___x_1272_;
}
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1289_; 
v_a_1275_ = lean_ctor_get(v_x_1264_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_x_1264_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1277_ = v_x_1264_;
v_isShared_1278_ = v_isSharedCheck_1289_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v_x_1264_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1289_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___f_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1285_; 
v___f_1279_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1279_, 0, v_a_1275_);
v___x_1280_ = lean_box(2);
v___x_1281_ = lean_unsigned_to_nat(0u);
v___x_1282_ = 0;
v___x_1283_ = l_Std_CancellationContext_cancel(v_a_1263_, v___x_1280_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v___x_1283_);
v___x_1285_ = v___x_1277_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1283_);
v___x_1285_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
v___x_1287_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1281_, v___x_1282_, v___x_1286_, v___f_1279_);
return v___x_1287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__1___boxed(lean_object* v_a_1290_, lean_object* v_x_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__1(v_a_1290_, v_x_1291_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__3(lean_object* v_a_1294_, lean_object* v_x_1295_){
_start:
{
if (lean_obj_tag(v_x_1295_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1305_; 
v_a_1297_ = lean_ctor_get(v_x_1295_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v_x_1295_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1299_ = v_x_1295_;
v_isShared_1300_ = v_isSharedCheck_1305_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v_x_1295_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1305_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
lean_object* v___x_1303_; 
v___x_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
return v___x_1303_;
}
}
}
else
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = lean_io_promise_resolve(v_x_1295_, v_a_1294_);
v___x_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
v___x_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
return v___x_1308_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__3___boxed(lean_object* v_a_1309_, lean_object* v_x_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__3(v_a_1309_, v_x_1310_);
lean_dec(v_a_1309_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__4(lean_object* v_a_1313_, lean_object* v_x_1314_){
_start:
{
if (lean_obj_tag(v_x_1314_) == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1325_; 
v_a_1316_ = lean_ctor_get(v_x_1314_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_x_1314_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1318_ = v_x_1314_;
v_isShared_1319_ = v_isSharedCheck_1325_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v_x_1314_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1325_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = lean_io_promise_resolve(v___x_1321_, v_a_1313_);
v___x_1323_ = ((lean_object*)(l_Std_Async_ContextAsync_background___redArg___lam__2___closed__1));
return v___x_1323_;
}
}
}
else
{
lean_object* v___x_1326_; 
v___x_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1326_, 0, v_x_1314_);
return v___x_1326_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__4___boxed(lean_object* v_a_1327_, lean_object* v_x_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__4(v_a_1327_, v_x_1328_);
lean_dec(v_a_1327_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__5(lean_object* v_a_1331_, lean_object* v_x_1332_){
_start:
{
if (lean_obj_tag(v_x_1332_) == 0)
{
lean_object* v___x_1334_; 
lean_dec_ref(v_a_1331_);
v___x_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1334_, 0, v_x_1332_);
return v___x_1334_;
}
else
{
lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1344_; 
v_isSharedCheck_1344_ = !lean_is_exclusive(v_x_1332_);
if (v_isSharedCheck_1344_ == 0)
{
lean_object* v_unused_1345_; 
v_unused_1345_ = lean_ctor_get(v_x_1332_, 0);
lean_dec(v_unused_1345_);
v___x_1336_ = v_x_1332_;
v_isShared_1337_ = v_isSharedCheck_1344_;
goto v_resetjp_1335_;
}
else
{
lean_dec(v_x_1332_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1344_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1338_ = lean_box(2);
v___x_1339_ = l_Std_CancellationContext_cancel(v_a_1331_, v___x_1338_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v___x_1339_);
v___x_1341_ = v___x_1336_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
lean_object* v___x_1342_; 
v___x_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
return v___x_1342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__5___boxed(lean_object* v_a_1346_, lean_object* v_x_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__5(v_a_1346_, v_x_1347_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__6(lean_object* v_a_1350_, lean_object* v___x_1351_, lean_object* v___f_1352_, lean_object* v___f_1353_, lean_object* v___f_1354_){
_start:
{
uint8_t v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1356_ = 0;
v___x_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1357_, 0, v_a_1350_);
lean_inc_n(v___x_1351_, 2);
v___x_1358_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1351_, v___x_1356_, v___x_1357_, v___f_1352_);
v___x_1359_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1351_, v___x_1356_, v___x_1358_, v___f_1353_);
v___x_1360_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1351_, v___x_1356_, v___x_1359_, v___f_1354_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__6___boxed(lean_object* v_a_1361_, lean_object* v___x_1362_, lean_object* v___f_1363_, lean_object* v___f_1364_, lean_object* v___f_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__6(v_a_1361_, v___x_1362_, v___f_1363_, v___f_1364_, v___f_1365_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__7(lean_object* v_a_1368_, lean_object* v___x_1369_, lean_object* v___f_1370_, lean_object* v___f_1371_, lean_object* v_x_1372_){
_start:
{
if (lean_obj_tag(v_x_1372_) == 0)
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1382_; 
lean_dec_ref(v___f_1371_);
lean_dec_ref(v___f_1370_);
lean_dec(v___x_1369_);
lean_dec_ref(v_a_1368_);
v_a_1374_ = lean_ctor_get(v_x_1372_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_x_1372_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1376_ = v_x_1372_;
v_isShared_1377_ = v_isSharedCheck_1382_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v_x_1372_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1382_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
lean_object* v___x_1380_; 
v___x_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
return v___x_1380_;
}
}
}
else
{
lean_object* v_a_1383_; lean_object* v___f_1384_; lean_object* v___f_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v_a_1383_ = lean_ctor_get(v_x_1372_, 0);
lean_inc(v_a_1383_);
lean_dec_ref_known(v_x_1372_, 1);
v___f_1384_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_1384_, 0, v_a_1383_);
lean_inc(v___x_1369_);
v___f_1385_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__6___boxed), 6, 5);
lean_closure_set(v___f_1385_, 0, v_a_1368_);
lean_closure_set(v___f_1385_, 1, v___x_1369_);
lean_closure_set(v___f_1385_, 2, v___f_1370_);
lean_closure_set(v___f_1385_, 3, v___f_1371_);
lean_closure_set(v___f_1385_, 4, v___f_1384_);
v___x_1386_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1386_, 0, lean_box(0));
lean_closure_set(v___x_1386_, 1, v___f_1385_);
v___x_1387_ = lean_io_as_task(v___x_1386_, v___x_1369_);
lean_dec_ref(v___x_1387_);
v___x_1388_ = ((lean_object*)(l_Std_Async_ContextAsync_background___redArg___lam__2___closed__1));
return v___x_1388_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__7___boxed(lean_object* v_a_1389_, lean_object* v___x_1390_, lean_object* v___f_1391_, lean_object* v___f_1392_, lean_object* v_x_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__7(v_a_1389_, v___x_1390_, v___f_1391_, v___f_1392_, v_x_1393_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__8(lean_object* v___x_1396_, lean_object* v___f_1397_, lean_object* v_x_1398_){
_start:
{
if (lean_obj_tag(v_x_1398_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1408_; 
lean_dec_ref(v___f_1397_);
lean_dec(v___x_1396_);
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
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1420_; 
v_a_1409_ = lean_ctor_get(v_x_1398_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v_x_1398_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1411_ = v_x_1398_;
v_isShared_1412_ = v_isSharedCheck_1420_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v_x_1398_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1420_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
uint8_t v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1413_ = 0;
v___x_1414_ = l_Std_CancellationContext_fork(v_a_1409_);
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 0, v___x_1414_);
v___x_1416_ = v___x_1411_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
v___x_1418_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1396_, v___x_1413_, v___x_1417_, v___f_1397_);
return v___x_1418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__8___boxed(lean_object* v___x_1421_, lean_object* v___f_1422_, lean_object* v_x_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__8(v___x_1421_, v___f_1422_, v_x_1423_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__9(lean_object* v___f_1426_, lean_object* v___f_1427_, lean_object* v___y_1428_, lean_object* v_x_1429_){
_start:
{
if (lean_obj_tag(v_x_1429_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1439_; 
lean_dec_ref(v___f_1427_);
lean_dec_ref(v___f_1426_);
v_a_1431_ = lean_ctor_get(v_x_1429_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_x_1429_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1433_ = v_x_1429_;
v_isShared_1434_ = v_isSharedCheck_1439_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v_x_1429_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1439_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
lean_object* v___x_1437_; 
v___x_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
return v___x_1437_;
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1453_; 
v_a_1440_ = lean_ctor_get(v_x_1429_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v_x_1429_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1442_ = v_x_1429_;
v_isShared_1443_ = v_isSharedCheck_1453_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v_x_1429_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1453_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v___f_1445_; lean_object* v___f_1446_; uint8_t v___x_1447_; lean_object* v___x_1449_; 
v___x_1444_ = lean_unsigned_to_nat(0u);
v___f_1445_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_1445_, 0, v_a_1440_);
lean_closure_set(v___f_1445_, 1, v___x_1444_);
lean_closure_set(v___f_1445_, 2, v___f_1426_);
lean_closure_set(v___f_1445_, 3, v___f_1427_);
v___f_1446_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__8___boxed), 4, 2);
lean_closure_set(v___f_1446_, 0, v___x_1444_);
lean_closure_set(v___f_1446_, 1, v___f_1445_);
v___x_1447_ = 0;
lean_inc_ref(v___y_1428_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 0, v___y_1428_);
v___x_1449_ = v___x_1442_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___y_1428_);
v___x_1449_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
v___x_1451_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1444_, v___x_1447_, v___x_1450_, v___f_1446_);
return v___x_1451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__9___boxed(lean_object* v___f_1454_, lean_object* v___f_1455_, lean_object* v___y_1456_, lean_object* v_x_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__9(v___f_1454_, v___f_1455_, v___y_1456_, v_x_1457_);
lean_dec_ref(v___y_1456_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__10(lean_object* v_x_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = lean_apply_2(v_x_1460_, v_a_1461_, lean_box(0));
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__10___boxed(lean_object* v_x_1464_, lean_object* v_a_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__10(v_x_1464_, v_a_1465_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__11(lean_object* v_x_1468_, lean_object* v_prio_1469_, lean_object* v___f_1470_, lean_object* v___f_1471_, lean_object* v_x_1472_){
_start:
{
if (lean_obj_tag(v_x_1472_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1482_; 
lean_dec_ref(v___f_1471_);
lean_dec_ref(v___f_1470_);
lean_dec(v_prio_1469_);
lean_dec_ref(v_x_1468_);
v_a_1474_ = lean_ctor_get(v_x_1472_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_x_1472_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1476_ = v_x_1472_;
v_isShared_1477_ = v_isSharedCheck_1482_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v_x_1472_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1482_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1479_);
return v___x_1480_;
}
}
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1499_; 
v_a_1483_ = lean_ctor_get(v_x_1472_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_x_1472_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1485_ = v_x_1472_;
v_isShared_1486_ = v_isSharedCheck_1499_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v_x_1472_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1499_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___f_1487_; lean_object* v___x_1488_; uint8_t v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; uint8_t v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1495_; 
v___f_1487_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__10___boxed), 3, 2);
lean_closure_set(v___f_1487_, 0, v_x_1468_);
lean_closure_set(v___f_1487_, 1, v_a_1483_);
v___x_1488_ = lean_unsigned_to_nat(0u);
v___x_1489_ = 0;
v___x_1490_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1490_, 0, lean_box(0));
lean_closure_set(v___x_1490_, 1, v___f_1487_);
v___x_1491_ = lean_io_as_task(v___x_1490_, v_prio_1469_);
v___x_1492_ = 1;
v___x_1493_ = lean_task_bind(v___x_1491_, v___f_1470_, v___x_1488_, v___x_1492_);
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 0, v___x_1493_);
v___x_1495_ = v___x_1485_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
v___x_1497_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1488_, v___x_1489_, v___x_1496_, v___f_1471_);
return v___x_1497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__11___boxed(lean_object* v_x_1500_, lean_object* v_prio_1501_, lean_object* v___f_1502_, lean_object* v___f_1503_, lean_object* v_x_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__11(v_x_1500_, v_prio_1501_, v___f_1502_, v___f_1503_, v_x_1504_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__12(lean_object* v___f_1507_, lean_object* v___f_1508_, lean_object* v_prio_1509_, lean_object* v___f_1510_, lean_object* v_a_1511_, lean_object* v_x_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v___f_1515_; lean_object* v___f_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_inc_ref(v___y_1513_);
v___f_1515_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__9___boxed), 5, 3);
lean_closure_set(v___f_1515_, 0, v___f_1507_);
lean_closure_set(v___f_1515_, 1, v___f_1508_);
lean_closure_set(v___f_1515_, 2, v___y_1513_);
v___f_1516_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__11___boxed), 6, 4);
lean_closure_set(v___f_1516_, 0, v_x_1512_);
lean_closure_set(v___f_1516_, 1, v_prio_1509_);
lean_closure_set(v___f_1516_, 2, v___f_1510_);
lean_closure_set(v___f_1516_, 3, v___f_1515_);
v___x_1517_ = lean_unsigned_to_nat(0u);
v___x_1518_ = 0;
v___x_1519_ = l_Std_CancellationContext_fork(v_a_1511_);
v___x_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
v___x_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
v___x_1522_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1517_, v___x_1518_, v___x_1521_, v___f_1516_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__12___boxed(lean_object* v___f_1523_, lean_object* v___f_1524_, lean_object* v_prio_1525_, lean_object* v___f_1526_, lean_object* v_a_1527_, lean_object* v_x_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__12(v___f_1523_, v___f_1524_, v_prio_1525_, v___f_1526_, v_a_1527_, v_x_1528_, v___y_1529_);
lean_dec_ref(v___y_1529_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__13(lean_object* v_a_1532_, lean_object* v___f_1533_, lean_object* v___f_1534_, lean_object* v_x_1535_){
_start:
{
if (lean_obj_tag(v_x_1535_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1545_; 
lean_dec_ref(v___f_1534_);
lean_dec_ref(v___f_1533_);
v_a_1537_ = lean_ctor_get(v_x_1535_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v_x_1535_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1539_ = v_x_1535_;
v_isShared_1540_ = v_isSharedCheck_1545_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v_x_1535_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1545_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
return v___x_1543_;
}
}
}
else
{
lean_object* v___x_1546_; uint8_t v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
lean_dec_ref_known(v_x_1535_, 1);
v___x_1546_ = lean_unsigned_to_nat(0u);
v___x_1547_ = 0;
v___x_1548_ = l_IO_Promise_result_x21___redArg(v_a_1532_);
v___x_1549_ = lean_task_map(v___f_1533_, v___x_1548_, v___x_1546_, v___x_1547_);
v___x_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
v___x_1551_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1546_, v___x_1547_, v___x_1550_, v___f_1534_);
return v___x_1551_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__13___boxed(lean_object* v_a_1552_, lean_object* v___f_1553_, lean_object* v___f_1554_, lean_object* v_x_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__13(v_a_1552_, v___f_1553_, v___f_1554_, v_x_1555_);
lean_dec(v_a_1552_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__14(lean_object* v_prio_1558_, lean_object* v___f_1559_, lean_object* v_a_1560_, lean_object* v___f_1561_, lean_object* v___f_1562_, lean_object* v_inst_1563_, lean_object* v_xs_1564_, lean_object* v_a_1565_, lean_object* v_x_1566_){
_start:
{
if (lean_obj_tag(v_x_1566_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1576_; 
lean_dec(v_xs_1564_);
lean_dec_ref(v_inst_1563_);
lean_dec_ref(v___f_1562_);
lean_dec_ref(v___f_1561_);
lean_dec_ref(v_a_1560_);
lean_dec_ref(v___f_1559_);
lean_dec(v_prio_1558_);
v_a_1568_ = lean_ctor_get(v_x_1566_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v_x_1566_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1570_ = v_x_1566_;
v_isShared_1571_ = v_isSharedCheck_1576_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v_x_1566_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1576_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
return v___x_1574_;
}
}
}
else
{
lean_object* v_a_1577_; lean_object* v___f_1578_; lean_object* v___f_1579_; lean_object* v___f_1580_; lean_object* v___f_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v_a_1577_ = lean_ctor_get(v_x_1566_, 0);
lean_inc_n(v_a_1577_, 3);
lean_dec_ref_known(v_x_1566_, 1);
v___f_1578_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1578_, 0, v_a_1577_);
v___f_1579_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1579_, 0, v_a_1577_);
v___f_1580_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__12___boxed), 8, 5);
lean_closure_set(v___f_1580_, 0, v___f_1578_);
lean_closure_set(v___f_1580_, 1, v___f_1579_);
lean_closure_set(v___f_1580_, 2, v_prio_1558_);
lean_closure_set(v___f_1580_, 3, v___f_1559_);
lean_closure_set(v___f_1580_, 4, v_a_1560_);
v___f_1581_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__13___boxed), 5, 3);
lean_closure_set(v___f_1581_, 0, v_a_1577_);
lean_closure_set(v___f_1581_, 1, v___f_1561_);
lean_closure_set(v___f_1581_, 2, v___f_1562_);
v___x_1582_ = lean_unsigned_to_nat(0u);
v___x_1583_ = 0;
lean_inc_ref(v_a_1565_);
v___x_1584_ = lean_apply_4(v_inst_1563_, v_xs_1564_, v___f_1580_, v_a_1565_, lean_box(0));
v___x_1585_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1582_, v___x_1583_, v___x_1584_, v___f_1581_);
return v___x_1585_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__14___boxed(lean_object* v_prio_1586_, lean_object* v___f_1587_, lean_object* v_a_1588_, lean_object* v___f_1589_, lean_object* v___f_1590_, lean_object* v_inst_1591_, lean_object* v_xs_1592_, lean_object* v_a_1593_, lean_object* v_x_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__14(v_prio_1586_, v___f_1587_, v_a_1588_, v___f_1589_, v___f_1590_, v_inst_1591_, v_xs_1592_, v_a_1593_, v_x_1594_);
lean_dec_ref(v_a_1593_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__15(lean_object* v_prio_1597_, lean_object* v___f_1598_, lean_object* v___f_1599_, lean_object* v_inst_1600_, lean_object* v_xs_1601_, lean_object* v_a_1602_, lean_object* v_x_1603_){
_start:
{
if (lean_obj_tag(v_x_1603_) == 0)
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1613_; 
lean_dec(v_xs_1601_);
lean_dec_ref(v_inst_1600_);
lean_dec_ref(v___f_1599_);
lean_dec_ref(v___f_1598_);
lean_dec(v_prio_1597_);
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
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1628_; 
v_a_1614_ = lean_ctor_get(v_x_1603_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_x_1603_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1616_ = v_x_1603_;
v_isShared_1617_ = v_isSharedCheck_1628_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v_x_1603_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1628_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___f_1618_; lean_object* v___f_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1624_; 
lean_inc(v_a_1614_);
v___f_1618_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1618_, 0, v_a_1614_);
lean_inc_ref(v_a_1602_);
v___f_1619_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__14___boxed), 10, 8);
lean_closure_set(v___f_1619_, 0, v_prio_1597_);
lean_closure_set(v___f_1619_, 1, v___f_1598_);
lean_closure_set(v___f_1619_, 2, v_a_1614_);
lean_closure_set(v___f_1619_, 3, v___f_1599_);
lean_closure_set(v___f_1619_, 4, v___f_1618_);
lean_closure_set(v___f_1619_, 5, v_inst_1600_);
lean_closure_set(v___f_1619_, 6, v_xs_1601_);
lean_closure_set(v___f_1619_, 7, v_a_1602_);
v___x_1620_ = lean_unsigned_to_nat(0u);
v___x_1621_ = 0;
v___x_1622_ = lean_io_promise_new();
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 0, v___x_1622_);
v___x_1624_ = v___x_1616_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1622_);
v___x_1624_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
v___x_1626_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1620_, v___x_1621_, v___x_1625_, v___f_1619_);
return v___x_1626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__15___boxed(lean_object* v_prio_1629_, lean_object* v___f_1630_, lean_object* v___f_1631_, lean_object* v_inst_1632_, lean_object* v_xs_1633_, lean_object* v_a_1634_, lean_object* v_x_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__15(v_prio_1629_, v___f_1630_, v___f_1631_, v_inst_1632_, v_xs_1633_, v_a_1634_, v_x_1635_);
lean_dec_ref(v_a_1634_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg(lean_object* v_inst_1639_, lean_object* v_xs_1640_, lean_object* v_prio_1641_, lean_object* v_a_1642_){
_start:
{
lean_object* v___f_1644_; lean_object* v___f_1645_; lean_object* v___f_1646_; lean_object* v___x_1647_; uint8_t v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___f_1644_ = ((lean_object*)(l_Std_Async_ContextAsync_raceAll___redArg___closed__0));
v___f_1645_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
lean_inc_ref_n(v_a_1642_, 2);
v___f_1646_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__15___boxed), 8, 6);
lean_closure_set(v___f_1646_, 0, v_prio_1641_);
lean_closure_set(v___f_1646_, 1, v___f_1645_);
lean_closure_set(v___f_1646_, 2, v___f_1644_);
lean_closure_set(v___f_1646_, 3, v_inst_1639_);
lean_closure_set(v___f_1646_, 4, v_xs_1640_);
lean_closure_set(v___f_1646_, 5, v_a_1642_);
v___x_1647_ = lean_unsigned_to_nat(0u);
v___x_1648_ = 0;
v___x_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1649_, 0, v_a_1642_);
v___x_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
v___x_1651_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1647_, v___x_1648_, v___x_1650_, v___f_1646_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___boxed(lean_object* v_inst_1652_, lean_object* v_xs_1653_, lean_object* v_prio_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Std_Async_ContextAsync_raceAll___redArg(v_inst_1652_, v_xs_1653_, v_prio_1654_, v_a_1655_);
lean_dec_ref(v_a_1655_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll(lean_object* v_c_1658_, lean_object* v_00_u03b1_1659_, lean_object* v_inst_1660_, lean_object* v_xs_1661_, lean_object* v_prio_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Std_Async_ContextAsync_raceAll___redArg(v_inst_1660_, v_xs_1661_, v_prio_1662_, v_a_1663_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___boxed(lean_object* v_c_1666_, lean_object* v_00_u03b1_1667_, lean_object* v_inst_1668_, lean_object* v_xs_1669_, lean_object* v_prio_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Std_Async_ContextAsync_raceAll(v_c_1666_, v_00_u03b1_1667_, v_inst_1668_, v_xs_1669_, v_prio_1670_, v_a_1671_);
lean_dec_ref(v_a_1671_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg___lam__3(lean_object* v___f_1674_, lean_object* v___x_1675_, lean_object* v___f_1676_){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; lean_object* v___x_1681_; lean_object* v___y_1683_; 
v___x_1678_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_1678_, 0, lean_box(0));
lean_closure_set(v___x_1678_, 1, lean_box(0));
lean_closure_set(v___x_1678_, 2, lean_box(0));
lean_closure_set(v___x_1678_, 3, v___f_1674_);
v___x_1679_ = lean_unsigned_to_nat(0u);
v___x_1680_ = 0;
v___x_1681_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_1675_, v___f_1676_, v___x_1679_, v___x_1680_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1685_; 
lean_dec_ref(v___x_1678_);
v_a_1685_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1685_);
lean_dec_ref_known(v___x_1681_, 1);
if (lean_obj_tag(v_a_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
v_a_1686_ = lean_ctor_get(v_a_1685_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_a_1685_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v_a_1685_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v_a_1685_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
v___y_1683_ = v___x_1691_;
goto v___jp_1682_;
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1702_; 
v_a_1694_ = lean_ctor_get(v_a_1685_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v_a_1685_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1696_ = v_a_1685_;
v_isShared_1697_ = v_isSharedCheck_1702_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v_a_1685_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1702_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v_fst_1698_; lean_object* v___x_1700_; 
v_fst_1698_ = lean_ctor_get(v_a_1694_, 0);
lean_inc(v_fst_1698_);
lean_dec(v_a_1694_);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v_fst_1698_);
v___x_1700_ = v___x_1696_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_fst_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
v___y_1683_ = v___x_1700_;
goto v___jp_1682_;
}
}
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1711_; 
v_a_1703_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1705_ = v___x_1681_;
v_isShared_1706_ = v_isSharedCheck_1711_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1681_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1711_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1707_; lean_object* v___x_1709_; 
v___x_1707_ = lean_task_map(v___x_1678_, v_a_1703_, v___x_1679_, v___x_1680_);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v___x_1707_);
v___x_1709_ = v___x_1705_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
v___jp_1682_:
{
lean_object* v___x_1684_; 
v___x_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1684_, 0, v___y_1683_);
return v___x_1684_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg___lam__3___boxed(lean_object* v___f_1712_, lean_object* v___x_1713_, lean_object* v___f_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Std_Async_ContextAsync_async___redArg___lam__3(v___f_1712_, v___x_1713_, v___f_1714_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg___lam__0(lean_object* v_x_1717_, lean_object* v___f_1718_, lean_object* v_prio_1719_, lean_object* v___f_1720_, lean_object* v_x_1721_){
_start:
{
if (lean_obj_tag(v_x_1721_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1731_; 
lean_dec_ref(v___f_1720_);
lean_dec(v_prio_1719_);
lean_dec(v___f_1718_);
lean_dec_ref(v_x_1717_);
v_a_1723_ = lean_ctor_get(v_x_1721_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_x_1721_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1725_ = v_x_1721_;
v_isShared_1726_ = v_isSharedCheck_1731_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v_x_1721_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1731_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1723_);
v___x_1728_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
lean_object* v___x_1729_; 
v___x_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
return v___x_1729_;
}
}
}
else
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1749_; 
v_a_1732_ = lean_ctor_get(v_x_1721_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v_x_1721_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1734_ = v_x_1721_;
v_isShared_1735_ = v_isSharedCheck_1749_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v_x_1721_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1749_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___f_1738_; lean_object* v___f_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; uint8_t v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1746_; 
lean_inc(v_a_1732_);
v___x_1736_ = lean_apply_1(v_x_1717_, v_a_1732_);
v___x_1737_ = lean_box(2);
v___f_1738_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1738_, 0, v_a_1732_);
lean_closure_set(v___f_1738_, 1, v___x_1737_);
v___f_1739_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_async___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_1739_, 0, v___f_1718_);
lean_closure_set(v___f_1739_, 1, v___x_1736_);
lean_closure_set(v___f_1739_, 2, v___f_1738_);
v___x_1740_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1740_, 0, lean_box(0));
lean_closure_set(v___x_1740_, 1, v___f_1739_);
v___x_1741_ = lean_io_as_task(v___x_1740_, v_prio_1719_);
v___x_1742_ = lean_unsigned_to_nat(0u);
v___x_1743_ = 1;
v___x_1744_ = lean_task_bind(v___x_1741_, v___f_1720_, v___x_1742_, v___x_1743_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 0, v___x_1744_);
v___x_1746_ = v___x_1734_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1744_);
v___x_1746_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
lean_object* v___x_1747_; 
v___x_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
return v___x_1747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg___lam__0___boxed(lean_object* v_x_1750_, lean_object* v___f_1751_, lean_object* v_prio_1752_, lean_object* v___f_1753_, lean_object* v_x_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Std_Async_ContextAsync_async___redArg___lam__0(v_x_1750_, v___f_1751_, v_prio_1752_, v___f_1753_, v_x_1754_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg(lean_object* v_x_1757_, lean_object* v_prio_1758_, lean_object* v_ctx_1759_){
_start:
{
lean_object* v___f_1761_; lean_object* v___f_1762_; lean_object* v___f_1763_; lean_object* v___x_1764_; uint8_t v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___f_1761_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__1));
v___f_1762_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_1763_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_async___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1763_, 0, v_x_1757_);
lean_closure_set(v___f_1763_, 1, v___f_1761_);
lean_closure_set(v___f_1763_, 2, v_prio_1758_);
lean_closure_set(v___f_1763_, 3, v___f_1762_);
v___x_1764_ = lean_unsigned_to_nat(0u);
v___x_1765_ = 0;
lean_inc_ref(v_ctx_1759_);
v___x_1766_ = l_Std_CancellationContext_fork(v_ctx_1759_);
v___x_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
v___x_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
v___x_1769_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1764_, v___x_1765_, v___x_1768_, v___f_1763_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg___boxed(lean_object* v_x_1770_, lean_object* v_prio_1771_, lean_object* v_ctx_1772_, lean_object* v_a_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Std_Async_ContextAsync_async___redArg(v_x_1770_, v_prio_1771_, v_ctx_1772_);
lean_dec_ref(v_ctx_1772_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async(lean_object* v_00_u03b1_1775_, lean_object* v_x_1776_, lean_object* v_prio_1777_, lean_object* v_ctx_1778_){
_start:
{
lean_object* v___f_1780_; lean_object* v___f_1781_; lean_object* v___f_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___f_1780_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__1));
v___f_1781_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_1782_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_async___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1782_, 0, v_x_1776_);
lean_closure_set(v___f_1782_, 1, v___f_1780_);
lean_closure_set(v___f_1782_, 2, v_prio_1777_);
lean_closure_set(v___f_1782_, 3, v___f_1781_);
v___x_1783_ = lean_unsigned_to_nat(0u);
v___x_1784_ = 0;
lean_inc_ref(v_ctx_1778_);
v___x_1785_ = l_Std_CancellationContext_fork(v_ctx_1778_);
v___x_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1785_);
v___x_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
v___x_1788_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1783_, v___x_1784_, v___x_1787_, v___f_1782_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___boxed(lean_object* v_00_u03b1_1789_, lean_object* v_x_1790_, lean_object* v_prio_1791_, lean_object* v_ctx_1792_, lean_object* v_a_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Std_Async_ContextAsync_async(v_00_u03b1_1789_, v_x_1790_, v_prio_1791_, v_ctx_1792_);
lean_dec_ref(v_ctx_1792_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5(lean_object* v___f_1795_, lean_object* v___f_1796_, lean_object* v_00_u03b1_1797_, lean_object* v_x_1798_, lean_object* v_prio_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v___f_1802_; lean_object* v___x_1803_; uint8_t v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___f_1802_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_async___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1802_, 0, v_x_1798_);
lean_closure_set(v___f_1802_, 1, v___f_1795_);
lean_closure_set(v___f_1802_, 2, v_prio_1799_);
lean_closure_set(v___f_1802_, 3, v___f_1796_);
v___x_1803_ = lean_unsigned_to_nat(0u);
v___x_1804_ = 0;
lean_inc_ref(v___y_1800_);
v___x_1805_ = l_Std_CancellationContext_fork(v___y_1800_);
v___x_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
v___x_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
v___x_1808_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1803_, v___x_1804_, v___x_1807_, v___f_1802_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5___boxed(lean_object* v___f_1809_, lean_object* v___f_1810_, lean_object* v_00_u03b1_1811_, lean_object* v_x_1812_, lean_object* v_prio_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5(v___f_1809_, v___f_1810_, v_00_u03b1_1811_, v_x_1812_, v_prio_1813_, v___y_1814_);
lean_dec_ref(v___y_1814_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instFunctor___lam__0(lean_object* v_00_u03b1_1821_, lean_object* v_00_u03b2_1822_, lean_object* v_f_1823_, lean_object* v_x_1824_, lean_object* v_ctx_1825_){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; lean_object* v___x_1830_; lean_object* v___y_1832_; 
lean_inc(v_f_1823_);
v___x_1827_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_1827_, 0, lean_box(0));
lean_closure_set(v___x_1827_, 1, lean_box(0));
lean_closure_set(v___x_1827_, 2, lean_box(0));
lean_closure_set(v___x_1827_, 3, v_f_1823_);
v___x_1828_ = lean_unsigned_to_nat(0u);
v___x_1829_ = 0;
v___x_1830_ = lean_apply_2(v_x_1824_, v_ctx_1825_, lean_box(0));
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1834_; 
lean_dec_ref(v___x_1827_);
v_a_1834_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1834_);
lean_dec_ref_known(v___x_1830_, 1);
if (lean_obj_tag(v_a_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
lean_dec(v_f_1823_);
v_a_1835_ = lean_ctor_get(v_a_1834_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v_a_1834_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v_a_1834_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v_a_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1838_ == 0)
{
v___x_1840_ = v___x_1837_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1835_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
v___y_1832_ = v___x_1840_;
goto v___jp_1831_;
}
}
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1851_; 
v_a_1843_ = lean_ctor_get(v_a_1834_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v_a_1834_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1845_ = v_a_1834_;
v_isShared_1846_ = v_isSharedCheck_1851_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v_a_1834_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1851_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1847_; lean_object* v___x_1849_; 
v___x_1847_ = lean_apply_1(v_f_1823_, v_a_1843_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 0, v___x_1847_);
v___x_1849_ = v___x_1845_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
v___y_1832_ = v___x_1849_;
goto v___jp_1831_;
}
}
}
}
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1860_; 
lean_dec(v_f_1823_);
v_a_1852_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1854_ = v___x_1830_;
v_isShared_1855_ = v_isSharedCheck_1860_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1830_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1860_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1856_; lean_object* v___x_1858_; 
v___x_1856_ = lean_task_map(v___x_1827_, v_a_1852_, v___x_1828_, v___x_1829_);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v___x_1856_);
v___x_1858_ = v___x_1854_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1856_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
v___jp_1831_:
{
lean_object* v___x_1833_; 
v___x_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1833_, 0, v___y_1832_);
return v___x_1833_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instFunctor___lam__0___boxed(lean_object* v_00_u03b1_1861_, lean_object* v_00_u03b2_1862_, lean_object* v_f_1863_, lean_object* v_x_1864_, lean_object* v_ctx_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Std_Async_ContextAsync_instFunctor___lam__0(v_00_u03b1_1861_, v_00_u03b2_1862_, v_f_1863_, v_x_1864_, v_ctx_1865_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instFunctor___lam__1(lean_object* v___f_1868_, lean_object* v_00_u03b1_1869_, lean_object* v_00_u03b2_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_1875_, 0, lean_box(0));
lean_closure_set(v___x_1875_, 1, lean_box(0));
lean_closure_set(v___x_1875_, 2, v___y_1871_);
lean_inc_ref(v___y_1873_);
v___x_1876_ = lean_apply_6(v___f_1868_, lean_box(0), lean_box(0), v___x_1875_, v___y_1872_, v___y_1873_, lean_box(0));
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instFunctor___lam__1___boxed(lean_object* v___f_1877_, lean_object* v_00_u03b1_1878_, lean_object* v_00_u03b2_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Std_Async_ContextAsync_instFunctor___lam__1(v___f_1877_, v_00_u03b1_1878_, v_00_u03b2_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
lean_dec_ref(v___y_1882_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__0(lean_object* v_00_u03b1_1892_, lean_object* v_a_1893_, lean_object* v_x_1894_){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1896_, 0, v_a_1893_);
v___x_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__0___boxed(lean_object* v_00_u03b1_1898_, lean_object* v_a_1899_, lean_object* v_x_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Std_Async_ContextAsync_instMonad___lam__0(v_00_u03b1_1898_, v_a_1899_, v_x_1900_);
lean_dec_ref(v_x_1900_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__1(lean_object* v_f_1903_, lean_object* v_ctx_1904_, lean_object* v_x_1905_){
_start:
{
if (lean_obj_tag(v_x_1905_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1915_; 
lean_dec_ref(v_ctx_1904_);
lean_dec_ref(v_f_1903_);
v_a_1907_ = lean_ctor_get(v_x_1905_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v_x_1905_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1909_ = v_x_1905_;
v_isShared_1910_ = v_isSharedCheck_1915_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v_x_1905_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1915_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
lean_object* v___x_1913_; 
v___x_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
return v___x_1913_;
}
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1917_; 
v_a_1916_ = lean_ctor_get(v_x_1905_, 0);
lean_inc(v_a_1916_);
lean_dec_ref_known(v_x_1905_, 1);
v___x_1917_ = lean_apply_3(v_f_1903_, v_a_1916_, v_ctx_1904_, lean_box(0));
return v___x_1917_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__1___boxed(lean_object* v_f_1918_, lean_object* v_ctx_1919_, lean_object* v_x_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Std_Async_ContextAsync_instMonad___lam__1(v_f_1918_, v_ctx_1919_, v_x_1920_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__2(lean_object* v_00_u03b1_1923_, lean_object* v_00_u03b2_1924_, lean_object* v_x_1925_, lean_object* v_f_1926_, lean_object* v_ctx_1927_){
_start:
{
lean_object* v___f_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
lean_inc_ref(v_ctx_1927_);
v___f_1929_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_instMonad___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1929_, 0, v_f_1926_);
lean_closure_set(v___f_1929_, 1, v_ctx_1927_);
v___x_1930_ = lean_unsigned_to_nat(0u);
v___x_1931_ = 0;
v___x_1932_ = lean_apply_2(v_x_1925_, v_ctx_1927_, lean_box(0));
v___x_1933_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1930_, v___x_1931_, v___x_1932_, v___f_1929_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__2___boxed(lean_object* v_00_u03b1_1934_, lean_object* v_00_u03b2_1935_, lean_object* v_x_1936_, lean_object* v_f_1937_, lean_object* v_ctx_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_Std_Async_ContextAsync_instMonad___lam__2(v_00_u03b1_1934_, v_00_u03b2_1935_, v_x_1936_, v_f_1937_, v_ctx_1938_);
return v_res_1940_;
}
}
static lean_object* _init_l_Std_Async_ContextAsync_instMonad(void){
_start:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v_toApplicative_1945_; lean_object* v_toSeq_1946_; lean_object* v_toSeqLeft_1947_; lean_object* v_toSeqRight_1948_; lean_object* v___f_1949_; lean_object* v___f_1950_; lean_object* v___f_1951_; lean_object* v___f_1952_; lean_object* v___f_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1943_ = ((lean_object*)(l_Std_Async_ContextAsync_instFunctor));
v___x_1944_ = lean_obj_once(&l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1, &l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1_once, _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1);
v_toApplicative_1945_ = lean_ctor_get(v___x_1944_, 0);
v_toSeq_1946_ = lean_ctor_get(v_toApplicative_1945_, 2);
v_toSeqLeft_1947_ = lean_ctor_get(v_toApplicative_1945_, 3);
v_toSeqRight_1948_ = lean_ctor_get(v_toApplicative_1945_, 4);
v___f_1949_ = ((lean_object*)(l_Std_Async_ContextAsync_instMonad___closed__0));
v___f_1950_ = ((lean_object*)(l_Std_Async_ContextAsync_instMonad___closed__1));
lean_inc(v_toSeqRight_1948_);
v___f_1951_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1951_, 0, v_toSeqRight_1948_);
lean_inc(v_toSeqLeft_1947_);
v___f_1952_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1952_, 0, v_toSeqLeft_1947_);
lean_inc(v_toSeq_1946_);
v___f_1953_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1953_, 0, v_toSeq_1946_);
v___x_1954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1943_);
lean_ctor_set(v___x_1954_, 1, v___f_1949_);
lean_ctor_set(v___x_1954_, 2, v___f_1953_);
lean_ctor_set(v___x_1954_, 3, v___f_1952_);
lean_ctor_set(v___x_1954_, 4, v___f_1951_);
v___x_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
lean_ctor_set(v___x_1955_, 1, v___f_1950_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___lam__0(lean_object* v_a_1956_){
_start:
{
lean_object* v___x_1957_; 
v___x_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1957_, 0, v_a_1956_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___lam__1(lean_object* v___f_1958_, lean_object* v_x_1959_){
_start:
{
if (lean_obj_tag(v_x_1959_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1969_; 
lean_dec_ref(v___f_1958_);
v_a_1961_ = lean_ctor_get(v_x_1959_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v_x_1959_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1963_ = v_x_1959_;
v_isShared_1964_ = v_isSharedCheck_1969_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v_x_1959_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1969_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
lean_object* v___x_1967_; 
v___x_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1966_);
return v___x_1967_;
}
}
}
else
{
lean_object* v_a_1970_; 
v_a_1970_ = lean_ctor_get(v_x_1959_, 0);
lean_inc(v_a_1970_);
lean_dec_ref_known(v_x_1959_, 1);
if (lean_obj_tag(v_a_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1979_; 
lean_dec_ref(v___f_1958_);
v_a_1971_ = lean_ctor_get(v_a_1970_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v_a_1970_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1973_ = v_a_1970_;
v_isShared_1974_ = v_isSharedCheck_1979_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v_a_1970_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1979_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1971_);
v___x_1976_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1977_; 
v___x_1977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
return v___x_1977_;
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1981_; uint8_t v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v_a_1980_ = lean_ctor_get(v_a_1970_, 0);
lean_inc(v_a_1980_);
lean_dec_ref_known(v_a_1970_, 1);
v___x_1981_ = lean_unsigned_to_nat(0u);
v___x_1982_ = 0;
v___x_1983_ = lean_task_map(v___f_1958_, v_a_1980_, v___x_1981_, v___x_1982_);
v___x_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
return v___x_1984_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___lam__1___boxed(lean_object* v___f_1985_, lean_object* v_x_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_Std_Async_ContextAsync_instMonadLiftIO___lam__1(v___f_1985_, v_x_1986_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___lam__2(lean_object* v___f_1989_, lean_object* v_00_u03b1_1990_, lean_object* v_x_1991_, lean_object* v_x_1992_){
_start:
{
lean_object* v___x_1994_; uint8_t v___x_1995_; lean_object* v_val_1997_; lean_object* v___x_2001_; 
v___x_1994_ = lean_unsigned_to_nat(0u);
v___x_1995_ = 0;
v___x_2001_ = lean_apply_1(v_x_1991_, lean_box(0));
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2010_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2004_ = v___x_2001_;
v_isShared_2005_ = v_isSharedCheck_2010_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_2001_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2010_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2006_; lean_object* v___x_2008_; 
v___x_2006_ = lean_task_pure(v_a_2002_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set_tag(v___x_2004_, 1);
lean_ctor_set(v___x_2004_, 0, v___x_2006_);
v___x_2008_ = v___x_2004_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2006_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
v_val_1997_ = v___x_2008_;
goto v___jp_1996_;
}
}
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
v_a_2011_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_2001_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2001_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
lean_ctor_set_tag(v___x_2013_, 0);
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
v_val_1997_ = v___x_2016_;
goto v___jp_1996_;
}
}
}
v___jp_1996_:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1998_, 0, v_val_1997_);
v___x_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1998_);
v___x_2000_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1994_, v___x_1995_, v___x_1999_, v___f_1989_);
return v___x_2000_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___lam__2___boxed(lean_object* v___f_2019_, lean_object* v_00_u03b1_2020_, lean_object* v_x_2021_, lean_object* v_x_2022_, lean_object* v___y_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l_Std_Async_ContextAsync_instMonadLiftIO___lam__2(v___f_2019_, v_00_u03b1_2020_, v_x_2021_, v_x_2022_);
lean_dec_ref(v_x_2022_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0(lean_object* v_00_u03b1_2031_, lean_object* v_x_2032_, lean_object* v_x_2033_){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2035_ = lean_apply_1(v_x_2032_, lean_box(0));
v___x_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
v___x_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0___boxed(lean_object* v_00_u03b1_2038_, lean_object* v_x_2039_, lean_object* v_x_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0(v_00_u03b1_2038_, v_x_2039_, v_x_2040_);
lean_dec_ref(v_x_2040_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__0(lean_object* v_00_u03b1_2045_, lean_object* v_e_2046_, lean_object* v_x_2047_){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v_e_2046_);
v___x_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2049_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__0___boxed(lean_object* v_00_u03b1_2051_, lean_object* v_e_2052_, lean_object* v_x_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Std_Async_ContextAsync_instMonadExceptError___lam__0(v_00_u03b1_2051_, v_e_2052_, v_x_2053_);
lean_dec_ref(v_x_2053_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__1(lean_object* v_h_2056_, lean_object* v_ctx_2057_, lean_object* v_x_2058_){
_start:
{
if (lean_obj_tag(v_x_2058_) == 0)
{
lean_object* v_a_2060_; lean_object* v___x_2061_; 
v_a_2060_ = lean_ctor_get(v_x_2058_, 0);
lean_inc(v_a_2060_);
lean_dec_ref_known(v_x_2058_, 1);
v___x_2061_ = lean_apply_3(v_h_2056_, v_a_2060_, v_ctx_2057_, lean_box(0));
return v___x_2061_;
}
else
{
lean_object* v___x_2062_; 
lean_dec_ref(v_ctx_2057_);
lean_dec_ref(v_h_2056_);
v___x_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2062_, 0, v_x_2058_);
return v___x_2062_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__1___boxed(lean_object* v_h_2063_, lean_object* v_ctx_2064_, lean_object* v_x_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_Std_Async_ContextAsync_instMonadExceptError___lam__1(v_h_2063_, v_ctx_2064_, v_x_2065_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__2(lean_object* v_00_u03b1_2068_, lean_object* v_x_2069_, lean_object* v_h_2070_, lean_object* v_ctx_2071_){
_start:
{
lean_object* v___f_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
lean_inc_ref(v_ctx_2071_);
v___f_2073_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_instMonadExceptError___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2073_, 0, v_h_2070_);
lean_closure_set(v___f_2073_, 1, v_ctx_2071_);
v___x_2074_ = lean_unsigned_to_nat(0u);
v___x_2075_ = 0;
v___x_2076_ = lean_apply_2(v_x_2069_, v_ctx_2071_, lean_box(0));
v___x_2077_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2074_, v___x_2075_, v___x_2076_, v___f_2073_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__2___boxed(lean_object* v_00_u03b1_2078_, lean_object* v_x_2079_, lean_object* v_h_2080_, lean_object* v_ctx_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_Std_Async_ContextAsync_instMonadExceptError___lam__2(v_00_u03b1_2078_, v_x_2079_, v_h_2080_, v_ctx_2081_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadFinally___lam__0(lean_object* v_f_2090_, lean_object* v_ctx_2091_, lean_object* v_opt_2092_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = lean_apply_3(v_f_2090_, v_opt_2092_, v_ctx_2091_, lean_box(0));
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadFinally___lam__0___boxed(lean_object* v_f_2095_, lean_object* v_ctx_2096_, lean_object* v_opt_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_Std_Async_ContextAsync_instMonadFinally___lam__0(v_f_2095_, v_ctx_2096_, v_opt_2097_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadFinally___lam__1(lean_object* v_00_u03b1_2100_, lean_object* v_00_u03b2_2101_, lean_object* v_x_2102_, lean_object* v_f_2103_, lean_object* v_ctx_2104_){
_start:
{
lean_object* v___f_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; uint8_t v___x_2109_; lean_object* v___x_2110_; 
lean_inc_ref(v_ctx_2104_);
v___f_2106_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_instMonadFinally___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2106_, 0, v_f_2103_);
lean_closure_set(v___f_2106_, 1, v_ctx_2104_);
v___x_2107_ = lean_apply_1(v_x_2102_, v_ctx_2104_);
v___x_2108_ = lean_unsigned_to_nat(0u);
v___x_2109_ = 0;
v___x_2110_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_2107_, v___f_2106_, v___x_2108_, v___x_2109_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadFinally___lam__1___boxed(lean_object* v_00_u03b1_2111_, lean_object* v_00_u03b2_2112_, lean_object* v_x_2113_, lean_object* v_f_2114_, lean_object* v_ctx_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Std_Async_ContextAsync_instMonadFinally___lam__1(v_00_u03b1_2111_, v_00_u03b2_2112_, v_x_2113_, v_f_2114_, v_ctx_2115_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited___redArg___lam__0(lean_object* v_x_2127_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = ((lean_object*)(l_Std_Async_ContextAsync_instInhabited___redArg___lam__0___closed__3));
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited___redArg___lam__0___boxed(lean_object* v_x_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_Std_Async_ContextAsync_instInhabited___redArg___lam__0(v_x_2130_);
lean_dec_ref(v_x_2130_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited___redArg(){
_start:
{
lean_object* v___f_2135_; 
v___f_2135_ = ((lean_object*)(l_Std_Async_ContextAsync_instInhabited___redArg___closed__0));
return v___f_2135_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited___redArg___boxed(lean_object* v___dummy_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Std_Async_ContextAsync_instInhabited___redArg();
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited(lean_object* v_00_u03b1_2138_, lean_object* v_inst_2139_){
_start:
{
lean_object* v___f_2140_; 
v___f_2140_ = ((lean_object*)(l_Std_Async_ContextAsync_instInhabited___redArg___closed__0));
return v___f_2140_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited___boxed(lean_object* v_00_u03b1_2141_, lean_object* v_inst_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_Std_Async_ContextAsync_instInhabited(v_00_u03b1_2141_, v_inst_2142_);
lean_dec(v_inst_2142_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0(lean_object* v_00_u03b1_2144_, lean_object* v_t_2145_, lean_object* v_x_2146_){
_start:
{
lean_object* v___x_2148_; 
v___x_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2148_, 0, v_t_2145_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0___boxed(lean_object* v_00_u03b1_2149_, lean_object* v_t_2150_, lean_object* v_x_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0(v_00_u03b1_2149_, v_t_2150_, v_x_2151_);
lean_dec_ref(v_x_2151_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__3(lean_object* v_x_2156_){
_start:
{
if (lean_obj_tag(v_x_2156_) == 0)
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2166_; 
v_a_2158_ = lean_ctor_get(v_x_2156_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_x_2156_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2160_ = v_x_2156_;
v_isShared_2161_ = v_isSharedCheck_2166_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v_x_2156_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2166_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2158_);
v___x_2163_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
lean_object* v___x_2164_; 
v___x_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2163_);
return v___x_2164_;
}
}
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2168_; 
v_a_2167_ = lean_ctor_get(v_x_2156_, 0);
lean_inc(v_a_2167_);
lean_dec_ref_known(v_x_2156_, 1);
v___x_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2168_, 0, v_a_2167_);
return v___x_2168_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__3___boxed(lean_object* v_x_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Std_Async_ContextAsync_race___redArg___lam__3(v_x_2169_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__6(lean_object* v___f_2172_, lean_object* v___f_2173_, lean_object* v_prio_2174_, lean_object* v___f_2175_, lean_object* v_x_2176_){
_start:
{
if (lean_obj_tag(v_x_2176_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2186_; 
lean_dec_ref(v___f_2175_);
lean_dec(v_prio_2174_);
lean_dec_ref(v___f_2173_);
lean_dec(v___f_2172_);
v_a_2178_ = lean_ctor_get(v_x_2176_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v_x_2176_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2180_ = v_x_2176_;
v_isShared_2181_ = v_isSharedCheck_2186_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v_x_2176_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2186_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2178_);
v___x_2183_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
lean_object* v___x_2184_; 
v___x_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2183_);
return v___x_2184_;
}
}
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2203_; 
v_a_2187_ = lean_ctor_get(v_x_2176_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v_x_2176_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2189_ = v_x_2176_;
v_isShared_2190_ = v_isSharedCheck_2203_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v_x_2176_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2203_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2191_; lean_object* v___f_2192_; lean_object* v___f_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2191_ = lean_box(2);
v___f_2192_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_2192_, 0, v_a_2187_);
lean_closure_set(v___f_2192_, 1, v___x_2191_);
v___f_2193_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_2193_, 0, v___f_2172_);
lean_closure_set(v___f_2193_, 1, v___f_2173_);
lean_closure_set(v___f_2193_, 2, v___f_2192_);
v___x_2194_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2194_, 0, lean_box(0));
lean_closure_set(v___x_2194_, 1, v___f_2193_);
v___x_2195_ = lean_io_as_task(v___x_2194_, v_prio_2174_);
v___x_2196_ = lean_unsigned_to_nat(0u);
v___x_2197_ = 1;
v___x_2198_ = lean_task_bind(v___x_2195_, v___f_2175_, v___x_2196_, v___x_2197_);
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 0, v___x_2198_);
v___x_2200_ = v___x_2189_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
lean_object* v___x_2201_; 
v___x_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
return v___x_2201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__6___boxed(lean_object* v___f_2204_, lean_object* v___f_2205_, lean_object* v_prio_2206_, lean_object* v___f_2207_, lean_object* v_x_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Std_Async_ContextAsync_race___redArg___lam__6(v___f_2204_, v___f_2205_, v_prio_2206_, v___f_2207_, v_x_2208_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__0(lean_object* v_y_2211_, lean_object* v_a_2212_){
_start:
{
lean_object* v___x_2214_; 
v___x_2214_ = lean_apply_2(v_y_2211_, v_a_2212_, lean_box(0));
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__0___boxed(lean_object* v_y_2215_, lean_object* v_a_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_Std_Async_ContextAsync_race___redArg___lam__0(v_y_2215_, v_a_2216_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__5(lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_result_2221_){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2223_ = lean_io_promise_resolve(v_result_2221_, v_a_2219_);
v___x_2224_ = lean_box(2);
v___x_2225_ = l_Std_CancellationContext_cancel(v_a_2220_, v___x_2224_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__5___boxed(lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_result_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Std_Async_ContextAsync_race___redArg___lam__5(v_a_2226_, v_a_2227_, v_result_2228_);
lean_dec(v_a_2226_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__4(lean_object* v_a_2231_, lean_object* v___f_2232_, lean_object* v___x_2233_, uint8_t v___x_2234_, lean_object* v___f_2235_, lean_object* v_x_2236_){
_start:
{
if (lean_obj_tag(v_x_2236_) == 0)
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2246_; 
lean_dec_ref(v___f_2235_);
lean_dec(v___x_2233_);
lean_dec_ref(v___f_2232_);
lean_dec_ref(v_a_2231_);
v_a_2238_ = lean_ctor_get(v_x_2236_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v_x_2236_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2240_ = v_x_2236_;
v_isShared_2241_ = v_isSharedCheck_2246_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v_x_2236_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2246_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
lean_object* v___x_2244_; 
v___x_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
return v___x_2244_;
}
}
}
else
{
lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2256_; 
v_isSharedCheck_2256_ = !lean_is_exclusive(v_x_2236_);
if (v_isSharedCheck_2256_ == 0)
{
lean_object* v_unused_2257_; 
v_unused_2257_ = lean_ctor_get(v_x_2236_, 0);
lean_dec(v_unused_2257_);
v___x_2248_ = v_x_2236_;
v_isShared_2249_ = v_isSharedCheck_2256_;
goto v_resetjp_2247_;
}
else
{
lean_dec(v_x_2236_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2256_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2250_; lean_object* v___x_2252_; 
lean_inc(v___x_2233_);
v___x_2250_ = l_BaseIO_chainTask___redArg(v_a_2231_, v___f_2232_, v___x_2233_, v___x_2234_);
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 0, v___x_2250_);
v___x_2252_ = v___x_2248_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2250_);
v___x_2252_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
v___x_2254_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2233_, v___x_2234_, v___x_2253_, v___f_2235_);
return v___x_2254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__4___boxed(lean_object* v_a_2258_, lean_object* v___f_2259_, lean_object* v___x_2260_, lean_object* v___x_2261_, lean_object* v___f_2262_, lean_object* v_x_2263_, lean_object* v___y_2264_){
_start:
{
uint8_t v___x_4310__boxed_2265_; lean_object* v_res_2266_; 
v___x_4310__boxed_2265_ = lean_unbox(v___x_2261_);
v_res_2266_ = l_Std_Async_ContextAsync_race___redArg___lam__4(v_a_2258_, v___f_2259_, v___x_2260_, v___x_4310__boxed_2265_, v___f_2262_, v_x_2263_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__1(lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v___f_2269_, lean_object* v___f_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_x_2273_){
_start:
{
if (lean_obj_tag(v_x_2273_) == 0)
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2283_; 
lean_dec_ref(v_a_2272_);
lean_dec_ref(v_a_2271_);
lean_dec_ref(v___f_2270_);
lean_dec_ref(v___f_2269_);
lean_dec_ref(v_a_2268_);
lean_dec_ref(v_a_2267_);
v_a_2275_ = lean_ctor_get(v_x_2273_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v_x_2273_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2277_ = v_x_2273_;
v_isShared_2278_ = v_isSharedCheck_2283_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v_x_2273_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2283_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2275_);
v___x_2280_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
lean_object* v___x_2281_; 
v___x_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2280_);
return v___x_2281_;
}
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2301_; 
v_a_2284_ = lean_ctor_get(v_x_2273_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v_x_2273_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2286_ = v_x_2273_;
v_isShared_2287_ = v_isSharedCheck_2301_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v_x_2273_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2301_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___f_2288_; lean_object* v___f_2289_; lean_object* v___f_2290_; lean_object* v___x_2291_; uint8_t v___x_2292_; lean_object* v___x_2293_; lean_object* v___f_2294_; lean_object* v___x_2295_; lean_object* v___x_2297_; 
lean_inc_n(v_a_2284_, 2);
v___f_2288_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_2288_, 0, v_a_2284_);
lean_closure_set(v___f_2288_, 1, v_a_2267_);
v___f_2289_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_2289_, 0, v_a_2284_);
lean_closure_set(v___f_2289_, 1, v_a_2268_);
v___f_2290_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__13___boxed), 5, 3);
lean_closure_set(v___f_2290_, 0, v_a_2284_);
lean_closure_set(v___f_2290_, 1, v___f_2269_);
lean_closure_set(v___f_2290_, 2, v___f_2270_);
v___x_2291_ = lean_unsigned_to_nat(0u);
v___x_2292_ = 0;
v___x_2293_ = lean_box(v___x_2292_);
v___f_2294_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__4___boxed), 7, 5);
lean_closure_set(v___f_2294_, 0, v_a_2271_);
lean_closure_set(v___f_2294_, 1, v___f_2289_);
lean_closure_set(v___f_2294_, 2, v___x_2291_);
lean_closure_set(v___f_2294_, 3, v___x_2293_);
lean_closure_set(v___f_2294_, 4, v___f_2290_);
v___x_2295_ = l_BaseIO_chainTask___redArg(v_a_2272_, v___f_2288_, v___x_2291_, v___x_2292_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v___x_2295_);
v___x_2297_ = v___x_2286_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2295_);
v___x_2297_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
v___x_2299_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2291_, v___x_2292_, v___x_2298_, v___f_2294_);
return v___x_2299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__1___boxed(lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v___f_2304_, lean_object* v___f_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_x_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Std_Async_ContextAsync_race___redArg___lam__1(v_a_2302_, v_a_2303_, v___f_2304_, v___f_2305_, v_a_2306_, v_a_2307_, v_x_2308_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__2(lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v___f_2313_, lean_object* v___f_2314_, lean_object* v_a_2315_, lean_object* v_x_2316_){
_start:
{
if (lean_obj_tag(v_x_2316_) == 0)
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2326_; 
lean_dec_ref(v_a_2315_);
lean_dec_ref(v___f_2314_);
lean_dec_ref(v___f_2313_);
lean_dec_ref(v_a_2312_);
lean_dec_ref(v_a_2311_);
v_a_2318_ = lean_ctor_get(v_x_2316_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v_x_2316_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2320_ = v_x_2316_;
v_isShared_2321_ = v_isSharedCheck_2326_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v_x_2316_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2326_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
lean_object* v___x_2324_; 
v___x_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2323_);
return v___x_2324_;
}
}
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2340_; 
v_a_2327_ = lean_ctor_get(v_x_2316_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v_x_2316_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2329_ = v_x_2316_;
v_isShared_2330_ = v_isSharedCheck_2340_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v_x_2316_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2340_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___f_2331_; lean_object* v___x_2332_; uint8_t v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2336_; 
v___f_2331_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__1___boxed), 8, 6);
lean_closure_set(v___f_2331_, 0, v_a_2311_);
lean_closure_set(v___f_2331_, 1, v_a_2312_);
lean_closure_set(v___f_2331_, 2, v___f_2313_);
lean_closure_set(v___f_2331_, 3, v___f_2314_);
lean_closure_set(v___f_2331_, 4, v_a_2327_);
lean_closure_set(v___f_2331_, 5, v_a_2315_);
v___x_2332_ = lean_unsigned_to_nat(0u);
v___x_2333_ = 0;
v___x_2334_ = lean_io_promise_new();
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 0, v___x_2334_);
v___x_2336_ = v___x_2329_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2334_);
v___x_2336_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
v___x_2338_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2332_, v___x_2333_, v___x_2337_, v___f_2331_);
return v___x_2338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__2___boxed(lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v___f_2343_, lean_object* v___f_2344_, lean_object* v_a_2345_, lean_object* v_x_2346_, lean_object* v___y_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l_Std_Async_ContextAsync_race___redArg___lam__2(v_a_2341_, v_a_2342_, v___f_2343_, v___f_2344_, v_a_2345_, v_x_2346_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__7(lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v___f_2351_, lean_object* v___f_2352_, lean_object* v_a_2353_, lean_object* v___f_2354_, lean_object* v_x_2355_){
_start:
{
if (lean_obj_tag(v_x_2355_) == 0)
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2365_; 
lean_dec_ref(v___f_2354_);
lean_dec_ref(v___f_2352_);
lean_dec_ref(v___f_2351_);
lean_dec_ref(v_a_2350_);
lean_dec_ref(v_a_2349_);
v_a_2357_ = lean_ctor_get(v_x_2355_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v_x_2355_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2359_ = v_x_2355_;
v_isShared_2360_ = v_isSharedCheck_2365_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v_x_2355_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2365_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
lean_object* v___x_2363_; 
v___x_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2362_);
return v___x_2363_;
}
}
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2380_; 
v_a_2366_ = lean_ctor_get(v_x_2355_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v_x_2355_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2368_ = v_x_2355_;
v_isShared_2369_ = v_isSharedCheck_2380_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v_x_2355_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2380_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___f_2370_; lean_object* v___x_2371_; uint8_t v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2375_; 
v___f_2370_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__2___boxed), 7, 5);
lean_closure_set(v___f_2370_, 0, v_a_2349_);
lean_closure_set(v___f_2370_, 1, v_a_2350_);
lean_closure_set(v___f_2370_, 2, v___f_2351_);
lean_closure_set(v___f_2370_, 3, v___f_2352_);
lean_closure_set(v___f_2370_, 4, v_a_2366_);
v___x_2371_ = lean_unsigned_to_nat(0u);
v___x_2372_ = 0;
lean_inc_ref(v_a_2353_);
v___x_2373_ = l_Std_CancellationContext_fork(v_a_2353_);
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 0, v___x_2373_);
v___x_2375_ = v___x_2368_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2373_);
v___x_2375_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
v___x_2377_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2371_, v___x_2372_, v___x_2376_, v___f_2354_);
v___x_2378_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2371_, v___x_2372_, v___x_2377_, v___f_2370_);
return v___x_2378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__7___boxed(lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v___f_2383_, lean_object* v___f_2384_, lean_object* v_a_2385_, lean_object* v___f_2386_, lean_object* v_x_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_Std_Async_ContextAsync_race___redArg___lam__7(v_a_2381_, v_a_2382_, v___f_2383_, v___f_2384_, v_a_2385_, v___f_2386_, v_x_2387_);
lean_dec_ref(v_a_2385_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__8(lean_object* v_y_2390_, lean_object* v___f_2391_, lean_object* v_prio_2392_, lean_object* v___f_2393_, lean_object* v_a_2394_, lean_object* v___f_2395_, lean_object* v___f_2396_, lean_object* v_a_2397_, lean_object* v___f_2398_, lean_object* v_x_2399_){
_start:
{
if (lean_obj_tag(v_x_2399_) == 0)
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2409_; 
lean_dec_ref(v___f_2398_);
lean_dec_ref(v___f_2396_);
lean_dec_ref(v___f_2395_);
lean_dec_ref(v_a_2394_);
lean_dec_ref(v___f_2393_);
lean_dec(v_prio_2392_);
lean_dec(v___f_2391_);
lean_dec_ref(v_y_2390_);
v_a_2401_ = lean_ctor_get(v_x_2399_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v_x_2399_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2403_ = v_x_2399_;
v_isShared_2404_ = v_isSharedCheck_2409_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v_x_2399_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2409_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2401_);
v___x_2406_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
lean_object* v___x_2407_; 
v___x_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
return v___x_2407_;
}
}
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2426_; 
v_a_2410_ = lean_ctor_get(v_x_2399_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v_x_2399_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2412_ = v_x_2399_;
v_isShared_2413_ = v_isSharedCheck_2426_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v_x_2399_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2426_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___f_2414_; lean_object* v___f_2415_; lean_object* v___f_2416_; lean_object* v___x_2417_; uint8_t v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2421_; 
lean_inc(v_a_2410_);
v___f_2414_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2414_, 0, v_y_2390_);
lean_closure_set(v___f_2414_, 1, v_a_2410_);
v___f_2415_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_2415_, 0, v___f_2391_);
lean_closure_set(v___f_2415_, 1, v___f_2414_);
lean_closure_set(v___f_2415_, 2, v_prio_2392_);
lean_closure_set(v___f_2415_, 3, v___f_2393_);
lean_inc_ref_n(v_a_2397_, 2);
v___f_2416_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__7___boxed), 8, 6);
lean_closure_set(v___f_2416_, 0, v_a_2410_);
lean_closure_set(v___f_2416_, 1, v_a_2394_);
lean_closure_set(v___f_2416_, 2, v___f_2395_);
lean_closure_set(v___f_2416_, 3, v___f_2396_);
lean_closure_set(v___f_2416_, 4, v_a_2397_);
lean_closure_set(v___f_2416_, 5, v___f_2415_);
v___x_2417_ = lean_unsigned_to_nat(0u);
v___x_2418_ = 0;
v___x_2419_ = l_Std_CancellationContext_fork(v_a_2397_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 0, v___x_2419_);
v___x_2421_ = v___x_2412_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2419_);
v___x_2421_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2421_);
v___x_2423_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2417_, v___x_2418_, v___x_2422_, v___f_2398_);
v___x_2424_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2417_, v___x_2418_, v___x_2423_, v___f_2416_);
return v___x_2424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__8___boxed(lean_object* v_y_2427_, lean_object* v___f_2428_, lean_object* v_prio_2429_, lean_object* v___f_2430_, lean_object* v_a_2431_, lean_object* v___f_2432_, lean_object* v___f_2433_, lean_object* v_a_2434_, lean_object* v___f_2435_, lean_object* v_x_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Std_Async_ContextAsync_race___redArg___lam__8(v_y_2427_, v___f_2428_, v_prio_2429_, v___f_2430_, v_a_2431_, v___f_2432_, v___f_2433_, v_a_2434_, v___f_2435_, v_x_2436_);
lean_dec_ref(v_a_2434_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__9(lean_object* v_x_2439_, lean_object* v___f_2440_, lean_object* v_prio_2441_, lean_object* v___f_2442_, lean_object* v_y_2443_, lean_object* v___f_2444_, lean_object* v___f_2445_, lean_object* v___f_2446_, lean_object* v___f_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_x_2450_){
_start:
{
if (lean_obj_tag(v_x_2450_) == 0)
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2460_; 
lean_dec_ref(v_a_2449_);
lean_dec_ref(v___f_2447_);
lean_dec_ref(v___f_2446_);
lean_dec_ref(v___f_2445_);
lean_dec(v___f_2444_);
lean_dec_ref(v_y_2443_);
lean_dec_ref(v___f_2442_);
lean_dec(v_prio_2441_);
lean_dec(v___f_2440_);
lean_dec_ref(v_x_2439_);
v_a_2452_ = lean_ctor_get(v_x_2450_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v_x_2450_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2454_ = v_x_2450_;
v_isShared_2455_ = v_isSharedCheck_2460_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v_x_2450_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2460_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2458_; 
v___x_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
return v___x_2458_;
}
}
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2476_; 
v_a_2461_ = lean_ctor_get(v_x_2450_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v_x_2450_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2463_ = v_x_2450_;
v_isShared_2464_ = v_isSharedCheck_2476_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v_x_2450_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2476_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___f_2465_; lean_object* v___f_2466_; lean_object* v___f_2467_; lean_object* v___x_2468_; uint8_t v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2472_; 
lean_inc(v_a_2461_);
v___f_2465_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__10___boxed), 3, 2);
lean_closure_set(v___f_2465_, 0, v_x_2439_);
lean_closure_set(v___f_2465_, 1, v_a_2461_);
lean_inc(v_prio_2441_);
v___f_2466_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_2466_, 0, v___f_2440_);
lean_closure_set(v___f_2466_, 1, v___f_2465_);
lean_closure_set(v___f_2466_, 2, v_prio_2441_);
lean_closure_set(v___f_2466_, 3, v___f_2442_);
lean_inc_ref(v_a_2448_);
v___f_2467_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__8___boxed), 11, 9);
lean_closure_set(v___f_2467_, 0, v_y_2443_);
lean_closure_set(v___f_2467_, 1, v___f_2444_);
lean_closure_set(v___f_2467_, 2, v_prio_2441_);
lean_closure_set(v___f_2467_, 3, v___f_2445_);
lean_closure_set(v___f_2467_, 4, v_a_2461_);
lean_closure_set(v___f_2467_, 5, v___f_2446_);
lean_closure_set(v___f_2467_, 6, v___f_2447_);
lean_closure_set(v___f_2467_, 7, v_a_2448_);
lean_closure_set(v___f_2467_, 8, v___f_2466_);
v___x_2468_ = lean_unsigned_to_nat(0u);
v___x_2469_ = 0;
v___x_2470_ = l_Std_CancellationContext_fork(v_a_2449_);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 0, v___x_2470_);
v___x_2472_ = v___x_2463_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2470_);
v___x_2472_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2472_);
v___x_2474_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2468_, v___x_2469_, v___x_2473_, v___f_2467_);
return v___x_2474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__9___boxed(lean_object* v_x_2477_, lean_object* v___f_2478_, lean_object* v_prio_2479_, lean_object* v___f_2480_, lean_object* v_y_2481_, lean_object* v___f_2482_, lean_object* v___f_2483_, lean_object* v___f_2484_, lean_object* v___f_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_x_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l_Std_Async_ContextAsync_race___redArg___lam__9(v_x_2477_, v___f_2478_, v_prio_2479_, v___f_2480_, v_y_2481_, v___f_2482_, v___f_2483_, v___f_2484_, v___f_2485_, v_a_2486_, v_a_2487_, v_x_2488_);
lean_dec_ref(v_a_2486_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__10(lean_object* v_x_2491_, lean_object* v___f_2492_, lean_object* v_prio_2493_, lean_object* v___f_2494_, lean_object* v_y_2495_, lean_object* v___f_2496_, lean_object* v___f_2497_, lean_object* v___f_2498_, lean_object* v___f_2499_, lean_object* v_a_2500_, lean_object* v_x_2501_){
_start:
{
if (lean_obj_tag(v_x_2501_) == 0)
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2511_; 
lean_dec_ref(v___f_2499_);
lean_dec_ref(v___f_2498_);
lean_dec_ref(v___f_2497_);
lean_dec(v___f_2496_);
lean_dec_ref(v_y_2495_);
lean_dec_ref(v___f_2494_);
lean_dec(v_prio_2493_);
lean_dec(v___f_2492_);
lean_dec_ref(v_x_2491_);
v_a_2503_ = lean_ctor_get(v_x_2501_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v_x_2501_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2505_ = v_x_2501_;
v_isShared_2506_ = v_isSharedCheck_2511_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v_x_2501_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2511_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2503_);
v___x_2508_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
lean_object* v___x_2509_; 
v___x_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
return v___x_2509_;
}
}
}
else
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2525_; 
v_a_2512_ = lean_ctor_get(v_x_2501_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v_x_2501_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2514_ = v_x_2501_;
v_isShared_2515_ = v_isSharedCheck_2525_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v_x_2501_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2525_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___f_2516_; lean_object* v___x_2517_; uint8_t v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2521_; 
lean_inc(v_a_2512_);
lean_inc_ref(v_a_2500_);
v___f_2516_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__9___boxed), 13, 11);
lean_closure_set(v___f_2516_, 0, v_x_2491_);
lean_closure_set(v___f_2516_, 1, v___f_2492_);
lean_closure_set(v___f_2516_, 2, v_prio_2493_);
lean_closure_set(v___f_2516_, 3, v___f_2494_);
lean_closure_set(v___f_2516_, 4, v_y_2495_);
lean_closure_set(v___f_2516_, 5, v___f_2496_);
lean_closure_set(v___f_2516_, 6, v___f_2497_);
lean_closure_set(v___f_2516_, 7, v___f_2498_);
lean_closure_set(v___f_2516_, 8, v___f_2499_);
lean_closure_set(v___f_2516_, 9, v_a_2500_);
lean_closure_set(v___f_2516_, 10, v_a_2512_);
v___x_2517_ = lean_unsigned_to_nat(0u);
v___x_2518_ = 0;
v___x_2519_ = l_Std_CancellationContext_fork(v_a_2512_);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 0, v___x_2519_);
v___x_2521_ = v___x_2514_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2519_);
v___x_2521_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
v___x_2523_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2517_, v___x_2518_, v___x_2522_, v___f_2516_);
return v___x_2523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__10___boxed(lean_object* v_x_2526_, lean_object* v___f_2527_, lean_object* v_prio_2528_, lean_object* v___f_2529_, lean_object* v_y_2530_, lean_object* v___f_2531_, lean_object* v___f_2532_, lean_object* v___f_2533_, lean_object* v___f_2534_, lean_object* v_a_2535_, lean_object* v_x_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Std_Async_ContextAsync_race___redArg___lam__10(v_x_2526_, v___f_2527_, v_prio_2528_, v___f_2529_, v_y_2530_, v___f_2531_, v___f_2532_, v___f_2533_, v___f_2534_, v_a_2535_, v_x_2536_);
lean_dec_ref(v_a_2535_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg(lean_object* v_x_2540_, lean_object* v_y_2541_, lean_object* v_prio_2542_, lean_object* v_a_2543_){
_start:
{
lean_object* v___f_2545_; lean_object* v___f_2546_; lean_object* v___f_2547_; lean_object* v___f_2548_; lean_object* v___f_2549_; lean_object* v___x_2550_; uint8_t v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___f_2545_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_2546_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__1));
v___f_2547_ = ((lean_object*)(l_Std_Async_ContextAsync_raceAll___redArg___closed__0));
v___f_2548_ = ((lean_object*)(l_Std_Async_ContextAsync_race___redArg___closed__0));
lean_inc_ref_n(v_a_2543_, 2);
v___f_2549_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__10___boxed), 12, 10);
lean_closure_set(v___f_2549_, 0, v_x_2540_);
lean_closure_set(v___f_2549_, 1, v___f_2546_);
lean_closure_set(v___f_2549_, 2, v_prio_2542_);
lean_closure_set(v___f_2549_, 3, v___f_2545_);
lean_closure_set(v___f_2549_, 4, v_y_2541_);
lean_closure_set(v___f_2549_, 5, v___f_2546_);
lean_closure_set(v___f_2549_, 6, v___f_2545_);
lean_closure_set(v___f_2549_, 7, v___f_2547_);
lean_closure_set(v___f_2549_, 8, v___f_2548_);
lean_closure_set(v___f_2549_, 9, v_a_2543_);
v___x_2550_ = lean_unsigned_to_nat(0u);
v___x_2551_ = 0;
v___x_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2552_, 0, v_a_2543_);
v___x_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2552_);
v___x_2554_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2550_, v___x_2551_, v___x_2553_, v___f_2549_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___boxed(lean_object* v_x_2555_, lean_object* v_y_2556_, lean_object* v_prio_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Std_Async_ContextAsync_race___redArg(v_x_2555_, v_y_2556_, v_prio_2557_, v_a_2558_);
lean_dec_ref(v_a_2558_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race(lean_object* v_00_u03b1_2561_, lean_object* v_inst_2562_, lean_object* v_x_2563_, lean_object* v_y_2564_, lean_object* v_prio_2565_, lean_object* v_a_2566_){
_start:
{
lean_object* v___f_2568_; lean_object* v___f_2569_; lean_object* v___f_2570_; lean_object* v___f_2571_; lean_object* v___f_2572_; lean_object* v___x_2573_; uint8_t v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___f_2568_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_2569_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__1));
v___f_2570_ = ((lean_object*)(l_Std_Async_ContextAsync_raceAll___redArg___closed__0));
v___f_2571_ = ((lean_object*)(l_Std_Async_ContextAsync_race___redArg___closed__0));
lean_inc_ref_n(v_a_2566_, 2);
v___f_2572_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__10___boxed), 12, 10);
lean_closure_set(v___f_2572_, 0, v_x_2563_);
lean_closure_set(v___f_2572_, 1, v___f_2569_);
lean_closure_set(v___f_2572_, 2, v_prio_2565_);
lean_closure_set(v___f_2572_, 3, v___f_2568_);
lean_closure_set(v___f_2572_, 4, v_y_2564_);
lean_closure_set(v___f_2572_, 5, v___f_2569_);
lean_closure_set(v___f_2572_, 6, v___f_2568_);
lean_closure_set(v___f_2572_, 7, v___f_2570_);
lean_closure_set(v___f_2572_, 8, v___f_2571_);
lean_closure_set(v___f_2572_, 9, v_a_2566_);
v___x_2573_ = lean_unsigned_to_nat(0u);
v___x_2574_ = 0;
v___x_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2575_, 0, v_a_2566_);
v___x_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
v___x_2577_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2573_, v___x_2574_, v___x_2576_, v___f_2572_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___boxed(lean_object* v_00_u03b1_2578_, lean_object* v_inst_2579_, lean_object* v_x_2580_, lean_object* v_y_2581_, lean_object* v_prio_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Std_Async_ContextAsync_race(v_00_u03b1_2578_, v_inst_2579_, v_x_2580_, v_y_2581_, v_prio_2582_, v_a_2583_);
lean_dec_ref(v_a_2583_);
lean_dec(v_inst_2579_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selector_cancelled(lean_object* v_a_2586_){
_start:
{
lean_object* v___f_2588_; lean_object* v___x_2589_; uint8_t v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___f_2588_ = ((lean_object*)(l_Std_Async_ContextAsync_doneSelector___closed__0));
v___x_2589_ = lean_unsigned_to_nat(0u);
v___x_2590_ = 0;
lean_inc_ref(v_a_2586_);
v___x_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2591_, 0, v_a_2586_);
v___x_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
v___x_2593_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2589_, v___x_2590_, v___x_2592_, v___f_2588_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selector_cancelled___boxed(lean_object* v_a_2594_, lean_object* v_a_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_Std_Async_Selector_cancelled(v_a_2594_);
lean_dec_ref(v_a_2594_);
return v_res_2596_;
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
