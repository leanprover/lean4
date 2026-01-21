// Lean compiler output
// Module: Std.Internal.Async.ContextAsync
// Imports: public import Std.Time public import Std.Internal.UV public import Std.Internal.Async.Basic public import Std.Internal.Async.Timer public import Std.Sync.CancellationContext
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
static lean_object* l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_async(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadFinally___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__1(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___closed__2;
static lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadAsyncAsyncTask___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_isCancelled___boxed(lean_object*, lean_object*);
lean_object* l_Std_Internal_IO_Async_EAsync_instMonad(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadAsyncAsyncTask;
static lean_object* l_Std_Internal_IO_Async_ContextAsync_awaitCancellation___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instFunctor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_run___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_doneSelector___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_io_promise_new();
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_cancel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_getContext(lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadAwaitAsyncTask___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__2;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_isCancelled___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_run(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadLiftBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_getCancellationReason___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_runIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_isCancelled(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_doneSelector___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_awaitCancellation___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_async___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_disown___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_disown___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_doneSelector___closed__0;
static lean_object* l_Std_Internal_IO_Async_ContextAsync_instFunctor___closed__2;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_runIn___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_getCancellationReason(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_doneSelector(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadFinally;
static lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instFunctor___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_wait(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadLiftBaseIO___closed__0;
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Internal_IO_Async_BaseAsync_toRawBaseIO___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_background___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_async___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_run___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___closed__2;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_disown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_liftM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__6(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__12___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonad___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadAwaitAsyncTask;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_run___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___closed__2;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonad___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__4(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__2(lean_object*);
uint8_t l_Std_CancellationToken_isCancelled(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__0(lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_run___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonad;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_awaitCancellation___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_CancellationContext_fork(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadFinally___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_async___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_awaitCancellation(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instFunctor;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_cancel___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_instInhabited___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonad___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_getCancellationReason___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_async___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_async___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_awaitCancellation___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_background(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_instFunctor___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__3(lean_object*, lean_object*);
lean_object* l_Std_CancellationContext_cancel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_async___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__13(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_instFunctor___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_getCancellationReason(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_run___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_awaitCancellation___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_async___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonad___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_background___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_disown___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selector_cancelled(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__3(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_disown___redArg___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_CancellationContext_new();
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_background___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_disown___redArg(lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadFinally___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__1(lean_object*);
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_doneSelector___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_disown___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_run___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_runIn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_run___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instFunctor___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadLiftBaseIO;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonad___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_awaitCancellation___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadFinally___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_runIn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadFinally___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_getContext___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_isCancelled___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Function_const___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_awaitCancellation___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selector_cancelled___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadLiftBaseIO___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_getCancellationReason___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instInhabited___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonad___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Internal_IO_Async_EAsync_tryFinally_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_cancel___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_selector(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_isCancelled___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_run___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_disown(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___closed__2;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_run___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_getCancellationReason___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonad___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_cancel___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_runIn___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_2, x_1, lean_box(0));
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_runIn___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_runIn___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_runIn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_3, x_2, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_runIn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_ContextAsync_runIn(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_run___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_9; 
lean_dec_ref(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_run___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_run___redArg___lam__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_run___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec_ref(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_5 = lean_box(2);
x_6 = l_Std_CancellationContext_cancel(x_1, x_5);
x_7 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_run___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_7, 0, x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = 0;
x_12 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_10, x_11, x_9, x_7);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_run___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_run___redArg___lam__1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_run___redArg___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
lean_inc(x_9);
x_10 = lean_apply_2(x_1, x_9, lean_box(0));
x_11 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_run___redArg___lam__1___boxed), 3, 1);
lean_closure_set(x_11, 0, x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = 0;
x_14 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_12, x_13, x_10, x_11);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_run___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_run___redArg___lam__2(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_run___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_3 = l_Std_CancellationContext_new();
x_4 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_run___redArg___lam__2___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = 0;
x_9 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_7, x_8, x_6, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_run___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_ContextAsync_run___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_run(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = l_Std_CancellationContext_new();
x_5 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_run___redArg___lam__2___boxed), 3, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = 0;
x_10 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_8, x_9, x_7, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_run(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_getContext(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_getContext___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_ContextAsync_getContext(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_isCancelled___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = l_Std_CancellationToken_isCancelled(x_10);
x_12 = lean_box(x_11);
lean_ctor_set(x_1, 0, x_12);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = l_Std_CancellationToken_isCancelled(x_15);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_isCancelled___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_ContextAsync_isCancelled___lam__0(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_isCancelled___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_isCancelled___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_isCancelled(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_3 = l_Std_Internal_IO_Async_ContextAsync_isCancelled___closed__0;
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = 0;
x_8 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_6, x_7, x_5, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_isCancelled___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_ContextAsync_isCancelled(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_getCancellationReason___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = l_Std_CancellationToken_getCancellationReason(x_10);
lean_ctor_set(x_1, 0, x_11);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_14);
lean_dec(x_13);
x_15 = l_Std_CancellationToken_getCancellationReason(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_getCancellationReason___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_ContextAsync_getCancellationReason___lam__0(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_getCancellationReason___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_getCancellationReason___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_getCancellationReason(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_3 = l_Std_Internal_IO_Async_ContextAsync_getCancellationReason___closed__0;
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = 0;
x_8 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_6, x_7, x_5, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_getCancellationReason___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_ContextAsync_getCancellationReason(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_cancel___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = l_Std_CancellationContext_cancel(x_10, x_1);
lean_ctor_set(x_2, 0, x_11);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Std_CancellationContext_cancel(x_13, x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_cancel___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_cancel___lam__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_cancel(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_4 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_cancel___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = 0;
x_9 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_7, x_8, x_6, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_cancel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_cancel(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_doneSelector___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = l_Std_CancellationToken_selector(x_10);
lean_ctor_set(x_1, 0, x_11);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_14);
lean_dec(x_13);
x_15 = l_Std_CancellationToken_selector(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_doneSelector___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_ContextAsync_doneSelector___lam__0(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_doneSelector___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_doneSelector___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_doneSelector(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_3 = l_Std_Internal_IO_Async_ContextAsync_doneSelector___closed__0;
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = 0;
x_8 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_6, x_7, x_5, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_doneSelector___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_ContextAsync_doneSelector(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_awaitCancellation___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_awaitCancellation___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_ContextAsync_awaitCancellation___lam__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_awaitCancellation___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_11; 
lean_dec_ref(x_1);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_18);
lean_dec(x_17);
x_19 = l_Std_CancellationToken_wait(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
lean_ctor_set(x_2, 0, x_20);
x_4 = x_2;
x_5 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec_ref(x_19);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_21);
x_4 = x_2;
x_5 = lean_box(0);
goto block_10;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_23);
lean_dec(x_22);
x_24 = l_Std_CancellationToken_wait(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_4 = x_26;
x_5 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec_ref(x_24);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_4 = x_28;
x_5 = lean_box(0);
goto block_10;
}
}
}
block_10:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = 0;
x_9 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_7, x_8, x_6, x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_awaitCancellation___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_awaitCancellation___lam__1(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_awaitCancellation___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_awaitCancellation___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_awaitCancellation___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_ContextAsync_awaitCancellation___closed__0;
x_2 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_awaitCancellation___lam__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_awaitCancellation(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_3 = l_Std_Internal_IO_Async_ContextAsync_awaitCancellation___closed__1;
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = 0;
x_8 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_6, x_7, x_5, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_awaitCancellation___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_ContextAsync_awaitCancellation(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = lean_task_pure(x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__2(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_4 = lean_box(2);
x_5 = l_Std_CancellationContext_cancel(x_1, x_4);
x_6 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_run___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = 0;
x_11 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_9, x_10, x_8, x_6);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec_ref(x_1);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__4(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_apply_2(x_1, x_2, lean_box(0));
x_6 = lean_unsigned_to_nat(0u);
x_7 = 0;
x_8 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_6, x_7, x_5, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__1(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Std_CancellationContext_cancel(x_1, x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__3(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = 0;
x_7 = l_Std_Internal_IO_Async_EAsync_tryFinally_x27___redArg(x_1, x_2, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_11; 
lean_dec(x_3);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec_ref(x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
x_8 = x_11;
goto block_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_8 = x_14;
goto block_10;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_17);
x_8 = x_11;
goto block_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_8 = x_20;
goto block_10;
}
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(x_23, 0, lean_box(0));
lean_closure_set(x_23, 1, lean_box(0));
lean_closure_set(x_23, 2, lean_box(0));
lean_closure_set(x_23, 3, x_3);
x_24 = lean_task_map(x_23, x_22, x_5, x_6);
lean_ctor_set(x_7, 0, x_24);
return x_7;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
lean_dec(x_7);
x_26 = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(x_26, 0, lean_box(0));
lean_closure_set(x_26, 1, lean_box(0));
lean_closure_set(x_26, 2, lean_box(0));
lean_closure_set(x_26, 3, x_3);
x_27 = lean_task_map(x_26, x_25, x_5, x_6);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
block_10:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__5(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_5 = l_Std_CancellationContext_cancel(x_1, x_2);
x_6 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_run___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_6, 0, x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = 0;
x_11 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_9, x_10, x_8, x_6);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__7(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_apply_2(x_1, x_2, lean_box(0));
x_6 = lean_unsigned_to_nat(0u);
x_7 = 0;
x_8 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_6, x_7, x_5, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__6(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__10(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_2, 0, x_11);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__10(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__8(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__10___boxed), 3, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = 0;
x_14 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_12, x_13, x_11, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__8(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__9(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__8___boxed), 3, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = 0;
x_14 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_12, x_13, x_11, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__9(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_6; 
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(x_13, 0, lean_box(0));
lean_closure_set(x_13, 1, x_1);
x_14 = lean_io_as_task(x_13, x_2);
x_15 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__9___boxed), 3, 1);
lean_closure_set(x_15, 0, x_12);
x_16 = lean_unsigned_to_nat(0u);
x_17 = 1;
x_18 = lean_task_bind(x_14, x_3, x_16, x_17);
lean_ctor_set(x_4, 0, x_18);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_4);
x_20 = 0;
x_21 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_16, x_20, x_19, x_15);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_4, 0);
lean_inc(x_22);
lean_dec(x_4);
x_23 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(x_23, 0, lean_box(0));
lean_closure_set(x_23, 1, x_1);
x_24 = lean_io_as_task(x_23, x_2);
x_25 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__9___boxed), 3, 1);
lean_closure_set(x_25, 0, x_22);
x_26 = lean_unsigned_to_nat(0u);
x_27 = 1;
x_28 = lean_task_bind(x_24, x_3, x_26, x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = 0;
x_32 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_26, x_31, x_30, x_25);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__11(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__12(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_9; 
lean_dec_ref(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__12(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_6 = l_Std_CancellationContext_cancel(x_1, x_2);
x_7 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__12___boxed), 3, 1);
lean_closure_set(x_7, 0, x_3);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = 0;
x_12 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_10, x_11, x_9, x_7);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__13(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_12; 
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_box(2);
x_20 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__3___boxed), 4, 2);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__5___boxed), 4, 3);
lean_closure_set(x_21, 0, x_2);
lean_closure_set(x_21, 1, x_20);
lean_closure_set(x_21, 2, x_3);
x_22 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(x_22, 0, lean_box(0));
lean_closure_set(x_22, 1, x_21);
lean_inc(x_4);
x_23 = lean_io_as_task(x_22, x_4);
lean_inc_ref(x_5);
x_24 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__7___boxed), 4, 2);
lean_closure_set(x_24, 0, x_5);
lean_closure_set(x_24, 1, x_19);
lean_inc(x_18);
x_25 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__6___boxed), 4, 3);
lean_closure_set(x_25, 0, x_6);
lean_closure_set(x_25, 1, x_18);
lean_closure_set(x_25, 2, x_24);
x_26 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__3___boxed), 4, 2);
lean_closure_set(x_26, 0, x_18);
lean_closure_set(x_26, 1, x_19);
x_27 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__5___boxed), 4, 3);
lean_closure_set(x_27, 0, x_25);
lean_closure_set(x_27, 1, x_26);
lean_closure_set(x_27, 2, x_7);
x_28 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__11___boxed), 5, 3);
lean_closure_set(x_28, 0, x_27);
lean_closure_set(x_28, 1, x_4);
lean_closure_set(x_28, 2, x_8);
x_29 = lean_unsigned_to_nat(0u);
x_30 = 1;
x_31 = lean_task_bind(x_23, x_9, x_29, x_30);
lean_ctor_set(x_10, 0, x_31);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_10);
x_33 = 0;
x_34 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_29, x_33, x_32, x_28);
x_35 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__13___boxed), 4, 2);
lean_closure_set(x_35, 0, x_5);
lean_closure_set(x_35, 1, x_19);
x_36 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_29, x_33, x_34, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_37 = lean_ctor_get(x_10, 0);
lean_inc(x_37);
lean_dec(x_10);
x_38 = lean_box(2);
x_39 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__3___boxed), 4, 2);
lean_closure_set(x_39, 0, x_1);
lean_closure_set(x_39, 1, x_38);
x_40 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__5___boxed), 4, 3);
lean_closure_set(x_40, 0, x_2);
lean_closure_set(x_40, 1, x_39);
lean_closure_set(x_40, 2, x_3);
x_41 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(x_41, 0, lean_box(0));
lean_closure_set(x_41, 1, x_40);
lean_inc(x_4);
x_42 = lean_io_as_task(x_41, x_4);
lean_inc_ref(x_5);
x_43 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__7___boxed), 4, 2);
lean_closure_set(x_43, 0, x_5);
lean_closure_set(x_43, 1, x_38);
lean_inc(x_37);
x_44 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__6___boxed), 4, 3);
lean_closure_set(x_44, 0, x_6);
lean_closure_set(x_44, 1, x_37);
lean_closure_set(x_44, 2, x_43);
x_45 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__3___boxed), 4, 2);
lean_closure_set(x_45, 0, x_37);
lean_closure_set(x_45, 1, x_38);
x_46 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__5___boxed), 4, 3);
lean_closure_set(x_46, 0, x_44);
lean_closure_set(x_46, 1, x_45);
lean_closure_set(x_46, 2, x_7);
x_47 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__11___boxed), 5, 3);
lean_closure_set(x_47, 0, x_46);
lean_closure_set(x_47, 1, x_4);
lean_closure_set(x_47, 2, x_8);
x_48 = lean_unsigned_to_nat(0u);
x_49 = 1;
x_50 = lean_task_bind(x_42, x_9, x_48, x_49);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = 0;
x_54 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_48, x_53, x_52, x_47);
x_55 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__13___boxed), 4, 2);
lean_closure_set(x_55, 0, x_5);
lean_closure_set(x_55, 1, x_38);
x_56 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_48, x_53, x_54, x_55);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_12; 
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_1);
x_19 = l_Std_CancellationContext_fork(x_1);
lean_inc(x_18);
x_20 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_18);
lean_closure_set(x_20, 2, x_3);
x_21 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__14___boxed), 11, 9);
lean_closure_set(x_21, 0, x_18);
lean_closure_set(x_21, 1, x_20);
lean_closure_set(x_21, 2, x_4);
lean_closure_set(x_21, 3, x_5);
lean_closure_set(x_21, 4, x_1);
lean_closure_set(x_21, 5, x_6);
lean_closure_set(x_21, 6, x_7);
lean_closure_set(x_21, 7, x_8);
lean_closure_set(x_21, 8, x_9);
lean_ctor_set(x_10, 0, x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_10);
x_23 = lean_unsigned_to_nat(0u);
x_24 = 0;
x_25 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_23, x_24, x_22, x_21);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_10, 0);
lean_inc(x_26);
lean_dec(x_10);
lean_inc_ref(x_1);
x_27 = l_Std_CancellationContext_fork(x_1);
lean_inc(x_26);
x_28 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_28, 0, x_2);
lean_closure_set(x_28, 1, x_26);
lean_closure_set(x_28, 2, x_3);
x_29 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__14___boxed), 11, 9);
lean_closure_set(x_29, 0, x_26);
lean_closure_set(x_29, 1, x_28);
lean_closure_set(x_29, 2, x_4);
lean_closure_set(x_29, 3, x_5);
lean_closure_set(x_29, 4, x_1);
lean_closure_set(x_29, 5, x_6);
lean_closure_set(x_29, 6, x_7);
lean_closure_set(x_29, 7, x_8);
lean_closure_set(x_29, 8, x_9);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_unsigned_to_nat(0u);
x_33 = 0;
x_34 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_32, x_33, x_31, x_29);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_10; 
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = l_Std_CancellationContext_fork(x_16);
lean_inc(x_16);
x_18 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__4___boxed), 3, 1);
lean_closure_set(x_18, 0, x_16);
x_19 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__15___boxed), 11, 9);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_18);
lean_closure_set(x_19, 3, x_2);
lean_closure_set(x_19, 4, x_3);
lean_closure_set(x_19, 5, x_4);
lean_closure_set(x_19, 6, x_5);
lean_closure_set(x_19, 7, x_6);
lean_closure_set(x_19, 8, x_7);
lean_ctor_set(x_8, 0, x_17);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_8);
x_21 = lean_unsigned_to_nat(0u);
x_22 = 0;
x_23 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_21, x_22, x_20, x_19);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_8, 0);
lean_inc(x_24);
lean_dec(x_8);
lean_inc(x_24);
x_25 = l_Std_CancellationContext_fork(x_24);
lean_inc(x_24);
x_26 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__4___boxed), 3, 1);
lean_closure_set(x_26, 0, x_24);
x_27 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__15___boxed), 11, 9);
lean_closure_set(x_27, 0, x_24);
lean_closure_set(x_27, 1, x_1);
lean_closure_set(x_27, 2, x_26);
lean_closure_set(x_27, 3, x_2);
lean_closure_set(x_27, 4, x_3);
lean_closure_set(x_27, 5, x_4);
lean_closure_set(x_27, 6, x_5);
lean_closure_set(x_27, 7, x_6);
lean_closure_set(x_27, 8, x_7);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_unsigned_to_nat(0u);
x_31 = 0;
x_32 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_30, x_31, x_29, x_27);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__17(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = l_Std_CancellationContext_fork(x_10);
lean_ctor_set(x_2, 0, x_11);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = 0;
x_15 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_13, x_14, x_12, x_1);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_Std_CancellationContext_fork(x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = 0;
x_22 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_20, x_21, x_19, x_1);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__17(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__2___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_6 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__0;
x_7 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__1;
x_8 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__16___boxed), 9, 7);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_2);
lean_closure_set(x_8, 4, x_7);
lean_closure_set(x_8, 5, x_6);
lean_closure_set(x_8, 6, x_6);
x_9 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__17___boxed), 3, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = 0;
x_14 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_12, x_13, x_11, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_8 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__0;
x_9 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__1;
x_10 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__16___boxed), 9, 7);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_5);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_9);
lean_closure_set(x_10, 5, x_8);
lean_closure_set(x_10, 6, x_8);
x_11 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__17___boxed), 3, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_6);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = 0;
x_16 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_14, x_15, x_13, x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrently___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Internal_IO_Async_ContextAsync_concurrently(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__2(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__2(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__1(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, lean_box(0));
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__4(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, lean_box(0));
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__6(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = 0;
x_7 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_5, x_6, x_4, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__7(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_6; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_4);
x_11 = l_IO_Promise_result_x21___redArg(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = 0;
x_14 = lean_task_map(x_2, x_11, x_12, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_12, x_13, x_15, x_3);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__5(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_promise_resolve(x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__3(x_1, x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_8; 
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_6, 0);
lean_dec(x_14);
lean_inc(x_3);
x_15 = l_BaseIO_chainTask___redArg(x_1, x_2, x_3, x_4);
lean_ctor_set(x_6, 0, x_15);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_6);
x_17 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_3, x_4, x_16, x_5);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
lean_inc(x_3);
x_18 = l_BaseIO_chainTask___redArg(x_1, x_2, x_3, x_4);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_3, x_4, x_20, x_5);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
x_9 = l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__8(x_1, x_2, x_3, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_7; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(x_14, 0, lean_box(0));
lean_closure_set(x_14, 1, lean_box(0));
lean_closure_set(x_14, 2, x_1);
lean_closure_set(x_14, 3, lean_box(0));
x_15 = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(x_15, 0, lean_box(0));
lean_closure_set(x_15, 1, lean_box(0));
lean_closure_set(x_15, 2, lean_box(0));
lean_closure_set(x_15, 3, x_14);
lean_closure_set(x_15, 4, x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = 0;
lean_inc_ref(x_15);
x_18 = l_BaseIO_chainTask___redArg(x_3, x_15, x_16, x_17);
x_19 = lean_box(x_17);
x_20 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__8___boxed), 7, 5);
lean_closure_set(x_20, 0, x_13);
lean_closure_set(x_20, 1, x_15);
lean_closure_set(x_20, 2, x_16);
lean_closure_set(x_20, 3, x_19);
lean_closure_set(x_20, 4, x_4);
lean_ctor_set(x_5, 0, x_18);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_5);
x_22 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_16, x_17, x_21, x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
lean_dec(x_5);
x_24 = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(x_24, 0, lean_box(0));
lean_closure_set(x_24, 1, lean_box(0));
lean_closure_set(x_24, 2, x_1);
lean_closure_set(x_24, 3, lean_box(0));
x_25 = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(x_25, 0, lean_box(0));
lean_closure_set(x_25, 1, lean_box(0));
lean_closure_set(x_25, 2, lean_box(0));
lean_closure_set(x_25, 3, x_24);
lean_closure_set(x_25, 4, x_2);
x_26 = lean_unsigned_to_nat(0u);
x_27 = 0;
lean_inc_ref(x_25);
x_28 = l_BaseIO_chainTask___redArg(x_3, x_25, x_26, x_27);
x_29 = lean_box(x_27);
x_30 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__8___boxed), 7, 5);
lean_closure_set(x_30, 0, x_23);
lean_closure_set(x_30, 1, x_25);
lean_closure_set(x_30, 2, x_26);
lean_closure_set(x_30, 3, x_29);
lean_closure_set(x_30, 4, x_4);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_26, x_27, x_32, x_30);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__9(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_9; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(x_16, 0, lean_box(0));
lean_closure_set(x_16, 1, x_1);
x_17 = lean_io_as_task(x_16, x_2);
x_18 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__9___boxed), 6, 4);
lean_closure_set(x_18, 0, x_3);
lean_closure_set(x_18, 1, x_4);
lean_closure_set(x_18, 2, x_15);
lean_closure_set(x_18, 3, x_5);
x_19 = lean_unsigned_to_nat(0u);
x_20 = 1;
x_21 = lean_task_bind(x_17, x_6, x_19, x_20);
lean_ctor_set(x_7, 0, x_21);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_7);
x_23 = 0;
x_24 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_19, x_23, x_22, x_18);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
lean_dec(x_7);
x_26 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(x_26, 0, lean_box(0));
lean_closure_set(x_26, 1, x_1);
x_27 = lean_io_as_task(x_26, x_2);
x_28 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__9___boxed), 6, 4);
lean_closure_set(x_28, 0, x_3);
lean_closure_set(x_28, 1, x_4);
lean_closure_set(x_28, 2, x_25);
lean_closure_set(x_28, 3, x_5);
x_29 = lean_unsigned_to_nat(0u);
x_30 = 1;
x_31 = lean_task_bind(x_27, x_6, x_29, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = 0;
x_35 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_29, x_34, x_33, x_28);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(x_18, 0, lean_box(0));
lean_closure_set(x_18, 1, x_1);
lean_inc(x_2);
x_19 = lean_io_as_task(x_18, x_2);
lean_inc(x_17);
x_20 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__5___boxed), 5, 3);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_3);
lean_closure_set(x_20, 2, x_4);
x_21 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__3___boxed), 3, 1);
lean_closure_set(x_21, 0, x_17);
x_22 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__10___boxed), 8, 6);
lean_closure_set(x_22, 0, x_5);
lean_closure_set(x_22, 1, x_2);
lean_closure_set(x_22, 2, x_6);
lean_closure_set(x_22, 3, x_21);
lean_closure_set(x_22, 4, x_20);
lean_closure_set(x_22, 5, x_7);
x_23 = lean_unsigned_to_nat(0u);
x_24 = 1;
x_25 = lean_task_bind(x_19, x_8, x_23, x_24);
lean_ctor_set(x_9, 0, x_25);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_9);
x_27 = 0;
x_28 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_23, x_27, x_26, x_22);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_29 = lean_ctor_get(x_9, 0);
lean_inc(x_29);
lean_dec(x_9);
x_30 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(x_30, 0, lean_box(0));
lean_closure_set(x_30, 1, x_1);
lean_inc(x_2);
x_31 = lean_io_as_task(x_30, x_2);
lean_inc(x_29);
x_32 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__5___boxed), 5, 3);
lean_closure_set(x_32, 0, x_29);
lean_closure_set(x_32, 1, x_3);
lean_closure_set(x_32, 2, x_4);
x_33 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__3___boxed), 3, 1);
lean_closure_set(x_33, 0, x_29);
x_34 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__10___boxed), 8, 6);
lean_closure_set(x_34, 0, x_5);
lean_closure_set(x_34, 1, x_2);
lean_closure_set(x_34, 2, x_6);
lean_closure_set(x_34, 3, x_33);
lean_closure_set(x_34, 4, x_32);
lean_closure_set(x_34, 5, x_7);
x_35 = lean_unsigned_to_nat(0u);
x_36 = 1;
x_37 = lean_task_bind(x_31, x_8, x_35, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = 0;
x_41 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_35, x_40, x_39, x_34);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__12___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadLiftT___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_io_promise_new();
x_19 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__7___boxed), 3, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_1);
x_20 = l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__12___closed__0;
x_21 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__11___boxed), 10, 8);
lean_closure_set(x_21, 0, x_2);
lean_closure_set(x_21, 1, x_3);
lean_closure_set(x_21, 2, x_4);
lean_closure_set(x_21, 3, x_5);
lean_closure_set(x_21, 4, x_19);
lean_closure_set(x_21, 5, x_20);
lean_closure_set(x_21, 6, x_6);
lean_closure_set(x_21, 7, x_7);
lean_ctor_set(x_9, 0, x_18);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
x_23 = lean_unsigned_to_nat(0u);
x_24 = 0;
x_25 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_23, x_24, x_22, x_21);
x_26 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_23, x_24, x_25, x_8);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_9, 0);
lean_inc(x_27);
lean_dec(x_9);
x_28 = lean_io_promise_new();
x_29 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__7___boxed), 3, 2);
lean_closure_set(x_29, 0, x_27);
lean_closure_set(x_29, 1, x_1);
x_30 = l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__12___closed__0;
x_31 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__11___boxed), 10, 8);
lean_closure_set(x_31, 0, x_2);
lean_closure_set(x_31, 1, x_3);
lean_closure_set(x_31, 2, x_4);
lean_closure_set(x_31, 3, x_5);
lean_closure_set(x_31, 4, x_29);
lean_closure_set(x_31, 5, x_30);
lean_closure_set(x_31, 6, x_6);
lean_closure_set(x_31, 7, x_7);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_28);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_unsigned_to_nat(0u);
x_35 = 0;
x_36 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_34, x_35, x_33, x_31);
x_37 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_34, x_35, x_36, x_8);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_13; 
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(x_20, 0, lean_box(0));
lean_closure_set(x_20, 1, x_1);
lean_inc(x_2);
x_21 = lean_io_as_task(x_20, x_2);
x_22 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__7___boxed), 3, 2);
lean_closure_set(x_22, 0, x_19);
lean_closure_set(x_22, 1, x_3);
x_23 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__12___boxed), 10, 8);
lean_closure_set(x_23, 0, x_4);
lean_closure_set(x_23, 1, x_22);
lean_closure_set(x_23, 2, x_2);
lean_closure_set(x_23, 3, x_5);
lean_closure_set(x_23, 4, x_6);
lean_closure_set(x_23, 5, x_7);
lean_closure_set(x_23, 6, x_8);
lean_closure_set(x_23, 7, x_9);
x_24 = lean_unsigned_to_nat(0u);
x_25 = 1;
x_26 = lean_task_bind(x_21, x_10, x_24, x_25);
lean_ctor_set(x_11, 0, x_26);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_11);
x_28 = 0;
x_29 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_24, x_28, x_27, x_23);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_30 = lean_ctor_get(x_11, 0);
lean_inc(x_30);
lean_dec(x_11);
x_31 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(x_31, 0, lean_box(0));
lean_closure_set(x_31, 1, x_1);
lean_inc(x_2);
x_32 = lean_io_as_task(x_31, x_2);
x_33 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__7___boxed), 3, 2);
lean_closure_set(x_33, 0, x_30);
lean_closure_set(x_33, 1, x_3);
x_34 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__12___boxed), 10, 8);
lean_closure_set(x_34, 0, x_4);
lean_closure_set(x_34, 1, x_33);
lean_closure_set(x_34, 2, x_2);
lean_closure_set(x_34, 3, x_5);
lean_closure_set(x_34, 4, x_6);
lean_closure_set(x_34, 5, x_7);
lean_closure_set(x_34, 6, x_8);
lean_closure_set(x_34, 7, x_9);
x_35 = lean_unsigned_to_nat(0u);
x_36 = 1;
x_37 = lean_task_bind(x_32, x_10, x_35, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = 0;
x_41 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_35, x_40, x_39, x_34);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_14; 
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(x_21, 0, lean_box(0));
lean_closure_set(x_21, 1, x_1);
lean_inc(x_2);
x_22 = lean_io_as_task(x_21, x_2);
lean_inc(x_20);
x_23 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__6___boxed), 3, 2);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_20);
x_24 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_run___redArg___lam__1___boxed), 3, 1);
lean_closure_set(x_24, 0, x_20);
x_25 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__13___boxed), 12, 10);
lean_closure_set(x_25, 0, x_23);
lean_closure_set(x_25, 1, x_2);
lean_closure_set(x_25, 2, x_24);
lean_closure_set(x_25, 3, x_4);
lean_closure_set(x_25, 4, x_5);
lean_closure_set(x_25, 5, x_6);
lean_closure_set(x_25, 6, x_7);
lean_closure_set(x_25, 7, x_8);
lean_closure_set(x_25, 8, x_9);
lean_closure_set(x_25, 9, x_10);
x_26 = lean_unsigned_to_nat(0u);
x_27 = 1;
x_28 = lean_task_bind(x_22, x_11, x_26, x_27);
lean_ctor_set(x_12, 0, x_28);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_12);
x_30 = 0;
x_31 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_26, x_30, x_29, x_25);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_32 = lean_ctor_get(x_12, 0);
lean_inc(x_32);
lean_dec(x_12);
x_33 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(x_33, 0, lean_box(0));
lean_closure_set(x_33, 1, x_1);
lean_inc(x_2);
x_34 = lean_io_as_task(x_33, x_2);
lean_inc(x_32);
x_35 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__6___boxed), 3, 2);
lean_closure_set(x_35, 0, x_3);
lean_closure_set(x_35, 1, x_32);
x_36 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_run___redArg___lam__1___boxed), 3, 1);
lean_closure_set(x_36, 0, x_32);
x_37 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__13___boxed), 12, 10);
lean_closure_set(x_37, 0, x_35);
lean_closure_set(x_37, 1, x_2);
lean_closure_set(x_37, 2, x_36);
lean_closure_set(x_37, 3, x_4);
lean_closure_set(x_37, 4, x_5);
lean_closure_set(x_37, 5, x_6);
lean_closure_set(x_37, 6, x_7);
lean_closure_set(x_37, 7, x_8);
lean_closure_set(x_37, 8, x_9);
lean_closure_set(x_37, 9, x_10);
x_38 = lean_unsigned_to_nat(0u);
x_39 = 1;
x_40 = lean_task_bind(x_34, x_11, x_38, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = 0;
x_44 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_38, x_43, x_42, x_37);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_14; 
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = l_Std_CancellationContext_fork(x_1);
lean_inc(x_20);
x_22 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__4___boxed), 3, 2);
lean_closure_set(x_22, 0, x_2);
lean_closure_set(x_22, 1, x_20);
x_23 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_run___redArg___lam__1___boxed), 3, 1);
lean_closure_set(x_23, 0, x_20);
x_24 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__14___boxed), 13, 11);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_3);
lean_closure_set(x_24, 2, x_4);
lean_closure_set(x_24, 3, x_23);
lean_closure_set(x_24, 4, x_5);
lean_closure_set(x_24, 5, x_6);
lean_closure_set(x_24, 6, x_7);
lean_closure_set(x_24, 7, x_8);
lean_closure_set(x_24, 8, x_9);
lean_closure_set(x_24, 9, x_10);
lean_closure_set(x_24, 10, x_11);
lean_ctor_set(x_12, 0, x_21);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_12);
x_26 = lean_unsigned_to_nat(0u);
x_27 = 0;
x_28 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_26, x_27, x_25, x_24);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_12, 0);
lean_inc(x_29);
lean_dec(x_12);
x_30 = l_Std_CancellationContext_fork(x_1);
lean_inc(x_29);
x_31 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__4___boxed), 3, 2);
lean_closure_set(x_31, 0, x_2);
lean_closure_set(x_31, 1, x_29);
x_32 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_run___redArg___lam__1___boxed), 3, 1);
lean_closure_set(x_32, 0, x_29);
x_33 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__14___boxed), 13, 11);
lean_closure_set(x_33, 0, x_31);
lean_closure_set(x_33, 1, x_3);
lean_closure_set(x_33, 2, x_4);
lean_closure_set(x_33, 3, x_32);
lean_closure_set(x_33, 4, x_5);
lean_closure_set(x_33, 5, x_6);
lean_closure_set(x_33, 6, x_7);
lean_closure_set(x_33, 7, x_8);
lean_closure_set(x_33, 8, x_9);
lean_closure_set(x_33, 9, x_10);
lean_closure_set(x_33, 10, x_11);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_30);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_unsigned_to_nat(0u);
x_37 = 0;
x_38 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_36, x_37, x_35, x_33);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_13; 
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
x_20 = l_Std_CancellationContext_fork(x_19);
x_21 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__15___boxed), 13, 11);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_1);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_3);
lean_closure_set(x_21, 4, x_4);
lean_closure_set(x_21, 5, x_5);
lean_closure_set(x_21, 6, x_6);
lean_closure_set(x_21, 7, x_7);
lean_closure_set(x_21, 8, x_8);
lean_closure_set(x_21, 9, x_9);
lean_closure_set(x_21, 10, x_10);
lean_ctor_set(x_11, 0, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_11);
x_23 = lean_unsigned_to_nat(0u);
x_24 = 0;
x_25 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_23, x_24, x_22, x_21);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_11, 0);
lean_inc(x_26);
lean_dec(x_11);
lean_inc(x_26);
x_27 = l_Std_CancellationContext_fork(x_26);
x_28 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__15___boxed), 13, 11);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_1);
lean_closure_set(x_28, 2, x_2);
lean_closure_set(x_28, 3, x_3);
lean_closure_set(x_28, 4, x_4);
lean_closure_set(x_28, 5, x_5);
lean_closure_set(x_28, 6, x_6);
lean_closure_set(x_28, 7, x_7);
lean_closure_set(x_28, 8, x_8);
lean_closure_set(x_28, 9, x_9);
lean_closure_set(x_28, 10, x_10);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_27);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_unsigned_to_nat(0u);
x_32 = 0;
x_33 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_31, x_32, x_30, x_28);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_race___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_race___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_race___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_6 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__0;
x_7 = l_Std_Internal_IO_Async_ContextAsync_race___redArg___closed__0;
x_8 = l_Std_Internal_IO_Async_ContextAsync_race___redArg___closed__1;
x_9 = l_Std_Internal_IO_Async_ContextAsync_race___redArg___closed__2;
x_10 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__16___boxed), 12, 10);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_9);
lean_closure_set(x_10, 4, x_8);
lean_closure_set(x_10, 5, x_6);
lean_closure_set(x_10, 6, x_6);
lean_closure_set(x_10, 7, x_7);
lean_closure_set(x_10, 8, x_6);
lean_closure_set(x_10, 9, x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_4);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = 0;
x_15 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_13, x_14, x_12, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_IO_Async_ContextAsync_race___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_8 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__0;
x_9 = l_Std_Internal_IO_Async_ContextAsync_race___redArg___closed__0;
x_10 = l_Std_Internal_IO_Async_ContextAsync_race___redArg___closed__1;
x_11 = l_Std_Internal_IO_Async_ContextAsync_race___redArg___closed__2;
x_12 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__16___boxed), 12, 10);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_5);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_11);
lean_closure_set(x_12, 4, x_10);
lean_closure_set(x_12, 5, x_8);
lean_closure_set(x_12, 6, x_8);
lean_closure_set(x_12, 7, x_9);
lean_closure_set(x_12, 8, x_8);
lean_closure_set(x_12, 9, x_8);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_6);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = 0;
x_17 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_15, x_16, x_14, x_12);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_race___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Internal_IO_Async_ContextAsync_race(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__1(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_7; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec_ref(x_5);
x_13 = lean_array_size(x_12);
x_14 = 0;
x_15 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_1, x_2, x_13, x_14, x_12);
x_16 = lean_apply_2(x_15, x_3, lean_box(0));
x_17 = lean_unsigned_to_nat(0u);
x_18 = 0;
x_19 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_17, x_18, x_16, x_4);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__4(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_apply_2(x_1, x_2, lean_box(0));
x_6 = lean_unsigned_to_nat(0u);
x_7 = 0;
x_8 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_6, x_7, x_5, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__5(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Std_CancellationContext_cancel(x_1, x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__2(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_8; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__5___boxed), 4, 3);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_14);
lean_closure_set(x_15, 2, x_2);
x_16 = lean_box(2);
x_17 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__2___boxed), 4, 2);
lean_closure_set(x_17, 0, x_14);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__5___boxed), 4, 3);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_3);
x_19 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(x_19, 0, lean_box(0));
lean_closure_set(x_19, 1, x_18);
x_20 = lean_io_as_task(x_19, x_4);
x_21 = lean_unsigned_to_nat(0u);
x_22 = 1;
x_23 = lean_task_bind(x_20, x_5, x_21, x_22);
lean_ctor_set(x_6, 0, x_23);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_6);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_25 = lean_ctor_get(x_6, 0);
lean_inc(x_25);
lean_dec(x_6);
lean_inc(x_25);
x_26 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__5___boxed), 4, 3);
lean_closure_set(x_26, 0, x_1);
lean_closure_set(x_26, 1, x_25);
lean_closure_set(x_26, 2, x_2);
x_27 = lean_box(2);
x_28 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__2___boxed), 4, 2);
lean_closure_set(x_28, 0, x_25);
lean_closure_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__5___boxed), 4, 3);
lean_closure_set(x_29, 0, x_26);
lean_closure_set(x_29, 1, x_28);
lean_closure_set(x_29, 2, x_3);
x_30 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(x_30, 0, lean_box(0));
lean_closure_set(x_30, 1, x_29);
x_31 = lean_io_as_task(x_30, x_4);
x_32 = lean_unsigned_to_nat(0u);
x_33 = 1;
x_34 = lean_task_bind(x_31, x_5, x_32, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__6(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_9 = l_Std_CancellationContext_fork(x_1);
x_10 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__6___boxed), 7, 5);
lean_closure_set(x_10, 0, x_6);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = 0;
x_15 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_13, x_14, x_12, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_10; 
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec_ref(x_8);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__4___boxed), 3, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__3___boxed), 8, 5);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_1);
lean_closure_set(x_17, 3, x_2);
lean_closure_set(x_17, 4, x_3);
x_18 = lean_array_size(x_4);
x_19 = 0;
x_20 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_5, x_17, x_18, x_19, x_4);
x_21 = lean_apply_2(x_20, x_6, lean_box(0));
x_22 = lean_unsigned_to_nat(0u);
x_23 = 0;
x_24 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_22, x_23, x_21, x_7);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__8(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = l_Std_CancellationContext_fork(x_10);
lean_ctor_set(x_2, 0, x_11);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = 0;
x_15 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_13, x_14, x_12, x_1);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_Std_CancellationContext_fork(x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = 0;
x_22 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_20, x_21, x_19, x_1);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__8(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Internal_IO_Async_EAsync_instMonad(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__2;
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_5 = l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__0;
x_6 = l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__1;
x_7 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__0;
x_8 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__1;
x_9 = l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__3;
lean_inc_ref(x_3);
x_10 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__4___boxed), 6, 4);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_6);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_5);
lean_inc_ref(x_3);
x_11 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__7___boxed), 9, 7);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_7);
lean_closure_set(x_11, 3, x_1);
lean_closure_set(x_11, 4, x_9);
lean_closure_set(x_11, 5, x_3);
lean_closure_set(x_11, 6, x_10);
x_12 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__8___boxed), 3, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_3);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = 0;
x_17 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_15, x_16, x_14, x_12);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_6 = l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__0;
x_7 = l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__1;
x_8 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__0;
x_9 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__1;
x_10 = l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__3;
lean_inc_ref(x_4);
x_11 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__4___boxed), 6, 4);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_7);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_6);
lean_inc_ref(x_4);
x_12 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__7___boxed), 9, 7);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_8);
lean_closure_set(x_12, 3, x_2);
lean_closure_set(x_12, 4, x_10);
lean_closure_set(x_12, 5, x_4);
lean_closure_set(x_12, 6, x_11);
x_13 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___lam__8___boxed), 3, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_4);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = 0;
x_18 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_16, x_17, x_15, x_13);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
lean_dec(x_10);
x_11 = lean_box(2);
x_12 = l_Std_CancellationContext_cancel(x_1, x_11);
lean_ctor_set(x_2, 0, x_12);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_14 = lean_box(2);
x_15 = l_Std_CancellationContext_cancel(x_1, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_apply_2(x_1, x_2, lean_box(0));
x_6 = lean_unsigned_to_nat(0u);
x_7 = 0;
x_8 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_6, x_7, x_5, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__1(x_1, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__2___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec_ref(x_3);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_11);
x_13 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(x_13, 0, lean_box(0));
lean_closure_set(x_13, 1, x_12);
x_14 = lean_io_as_task(x_13, x_2);
lean_dec_ref(x_14);
x_15 = l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__2___closed__1;
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__2(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = l_Std_CancellationContext_fork(x_10);
lean_ctor_set(x_2, 0, x_11);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = 0;
x_15 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_13, x_14, x_12, x_1);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_Std_CancellationContext_fork(x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = 0;
x_22 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_20, x_21, x_19, x_1);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__3(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_background___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_5 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__2___boxed), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__3___boxed), 3, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_3);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = 0;
x_11 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_9, x_10, x_8, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_background___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_ContextAsync_background___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_background(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_6 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__2___boxed), 4, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_3);
x_7 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__3___boxed), 3, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_4);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = 0;
x_12 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_10, x_11, x_9, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_background___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_IO_Async_ContextAsync_background(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_disown___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, lean_box(0));
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_disown___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_disown___redArg___lam__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_disown___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec_ref(x_3);
x_11 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_disown___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(x_12, 0, lean_box(0));
lean_closure_set(x_12, 1, x_11);
x_13 = lean_io_as_task(x_12, x_2);
lean_dec_ref(x_13);
x_14 = l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__2___closed__1;
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_disown___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_ContextAsync_disown___redArg___lam__1(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_disown___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = l_Std_CancellationContext_new();
x_5 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_disown___redArg___lam__1___boxed), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = 0;
x_10 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_8, x_9, x_7, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_disown___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_disown___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_disown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_6 = l_Std_CancellationContext_new();
x_7 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_disown___redArg___lam__1___boxed), 4, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_3);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = 0;
x_12 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_10, x_11, x_9, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_disown___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_IO_Async_ContextAsync_disown(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_9; 
lean_dec_ref(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__2(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_box(2);
x_12 = l_Std_CancellationContext_cancel(x_1, x_11);
x_13 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__2___boxed), 3, 1);
lean_closure_set(x_13, 0, x_10);
lean_ctor_set(x_2, 0, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = 0;
x_17 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_15, x_16, x_14, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_box(2);
x_20 = l_Std_CancellationContext_cancel(x_1, x_19);
x_21 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__2___boxed), 3, 1);
lean_closure_set(x_21, 0, x_18);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = 0;
x_26 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_24, x_25, x_23, x_21);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_io_promise_resolve(x_2, x_1);
x_6 = l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__2___closed__1;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_io_promise_resolve(x_8, x_1);
x_10 = l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__2___closed__1;
return x_10;
}
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__1(x_1, x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_io_promise_resolve(x_2, x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__3(x_1, x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec_ref(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_box(2);
x_8 = l_Std_CancellationContext_cancel(x_1, x_7);
lean_ctor_set(x_2, 0, x_8);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_10 = lean_box(2);
x_11 = l_Std_CancellationContext_cancel(x_1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__4(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = 0;
lean_inc(x_2);
x_9 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_2, x_8, x_7, x_3);
lean_inc(x_2);
x_10 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_2, x_8, x_9, x_4);
x_11 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_2, x_8, x_10, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__5(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_7; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec_ref(x_5);
x_13 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__4___boxed), 3, 1);
lean_closure_set(x_13, 0, x_12);
lean_inc(x_2);
x_14 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__5___boxed), 6, 5);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_13);
x_15 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(x_15, 0, lean_box(0));
lean_closure_set(x_15, 1, x_14);
x_16 = lean_io_as_task(x_15, x_2);
lean_dec_ref(x_16);
x_17 = l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__2___closed__1;
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__6(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = l_Std_CancellationContext_fork(x_11);
lean_ctor_set(x_3, 0, x_12);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_3);
x_14 = 0;
x_15 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_1, x_14, x_13, x_2);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = l_Std_CancellationContext_fork(x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = 0;
x_21 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_1, x_20, x_19, x_2);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__7(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_6; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__6___boxed), 6, 4);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_1);
lean_closure_set(x_14, 3, x_2);
x_15 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__7___boxed), 4, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
lean_ctor_set(x_4, 0, x_3);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_4);
x_17 = 0;
x_18 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_13, x_17, x_16, x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__6___boxed), 6, 4);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
lean_closure_set(x_21, 2, x_1);
lean_closure_set(x_21, 3, x_2);
x_22 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__7___boxed), 4, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_3);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = 0;
x_26 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_20, x_25, x_24, x_22);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__8(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_7; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__4___boxed), 3, 2);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_13);
x_15 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(x_15, 0, lean_box(0));
lean_closure_set(x_15, 1, x_14);
x_16 = lean_io_as_task(x_15, x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = 1;
x_19 = lean_task_bind(x_16, x_3, x_17, x_18);
lean_ctor_set(x_5, 0, x_19);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_5);
x_21 = 0;
x_22 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_17, x_21, x_20, x_4);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
lean_dec(x_5);
x_24 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__4___boxed), 3, 2);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(x_25, 0, lean_box(0));
lean_closure_set(x_25, 1, x_24);
x_26 = lean_io_as_task(x_25, x_2);
x_27 = lean_unsigned_to_nat(0u);
x_28 = 1;
x_29 = lean_task_bind(x_26, x_3, x_27, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = 0;
x_33 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_27, x_32, x_31, x_4);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__10(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_9 = l_Std_CancellationContext_fork(x_1);
x_10 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__8___boxed), 5, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_7);
x_11 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__10___boxed), 6, 4);
lean_closure_set(x_11, 0, x_6);
lean_closure_set(x_11, 1, x_4);
lean_closure_set(x_11, 2, x_5);
lean_closure_set(x_11, 3, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_9);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = 0;
x_16 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_14, x_15, x_13, x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec_ref(x_9);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__1___boxed), 3, 1);
lean_closure_set(x_17, 0, x_16);
lean_inc(x_16);
x_18 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__3___boxed), 3, 1);
lean_closure_set(x_18, 0, x_16);
x_19 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__9___boxed), 8, 5);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_18);
lean_closure_set(x_19, 2, x_17);
lean_closure_set(x_19, 3, x_2);
lean_closure_set(x_19, 4, x_3);
x_20 = lean_apply_4(x_4, x_5, x_19, x_6, lean_box(0));
x_21 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__5___boxed), 5, 3);
lean_closure_set(x_21, 0, x_16);
lean_closure_set(x_21, 1, x_7);
lean_closure_set(x_21, 2, x_8);
x_22 = lean_unsigned_to_nat(0u);
x_23 = 0;
x_24 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_22, x_23, x_20, x_21);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_9; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_io_promise_new();
lean_inc(x_15);
x_17 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_17, 0, x_15);
x_18 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__12___boxed), 10, 8);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_3);
lean_closure_set(x_18, 4, x_4);
lean_closure_set(x_18, 5, x_5);
lean_closure_set(x_18, 6, x_6);
lean_closure_set(x_18, 7, x_17);
lean_ctor_set(x_7, 0, x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_7);
x_20 = lean_unsigned_to_nat(0u);
x_21 = 0;
x_22 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_20, x_21, x_19, x_18);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_7, 0);
lean_inc(x_23);
lean_dec(x_7);
x_24 = lean_io_promise_new();
lean_inc(x_23);
x_25 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_25, 0, x_23);
x_26 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__12___boxed), 10, 8);
lean_closure_set(x_26, 0, x_23);
lean_closure_set(x_26, 1, x_1);
lean_closure_set(x_26, 2, x_2);
lean_closure_set(x_26, 3, x_3);
lean_closure_set(x_26, 4, x_4);
lean_closure_set(x_26, 5, x_5);
lean_closure_set(x_26, 6, x_6);
lean_closure_set(x_26, 7, x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_unsigned_to_nat(0u);
x_30 = 0;
x_31 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_29, x_30, x_28, x_26);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_6 = l_Std_Internal_IO_Async_ContextAsync_race___redArg___closed__2;
x_7 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__0;
lean_inc_ref(x_4);
x_8 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___lam__11___boxed), 8, 6);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_1);
lean_closure_set(x_8, 3, x_2);
lean_closure_set(x_8, 4, x_4);
lean_closure_set(x_8, 5, x_6);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = 0;
x_13 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_11, x_12, x_10, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Internal_IO_Async_ContextAsync_raceAll___redArg(x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_raceAll___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Internal_IO_Async_ContextAsync_raceAll(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_async___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = 0;
x_7 = l_Std_Internal_IO_Async_EAsync_tryFinally_x27___redArg(x_1, x_2, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_11; 
lean_dec(x_3);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec_ref(x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
x_8 = x_11;
goto block_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_8 = x_14;
goto block_10;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_17);
x_8 = x_11;
goto block_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_8 = x_20;
goto block_10;
}
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(x_23, 0, lean_box(0));
lean_closure_set(x_23, 1, lean_box(0));
lean_closure_set(x_23, 2, lean_box(0));
lean_closure_set(x_23, 3, x_3);
x_24 = lean_task_map(x_23, x_22, x_5, x_6);
lean_ctor_set(x_7, 0, x_24);
return x_7;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
lean_dec(x_7);
x_26 = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(x_26, 0, lean_box(0));
lean_closure_set(x_26, 1, lean_box(0));
lean_closure_set(x_26, 2, lean_box(0));
lean_closure_set(x_26, 3, x_3);
x_27 = lean_task_map(x_26, x_25, x_5, x_6);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
block_10:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_async___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_ContextAsync_async___redArg___lam__3(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_async___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_7; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
x_14 = lean_apply_1(x_1, x_13);
x_15 = lean_box(2);
x_16 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__3___boxed), 4, 2);
lean_closure_set(x_16, 0, x_13);
lean_closure_set(x_16, 1, x_15);
x_17 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_async___redArg___lam__3___boxed), 4, 3);
lean_closure_set(x_17, 0, x_14);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_2);
x_18 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(x_18, 0, lean_box(0));
lean_closure_set(x_18, 1, x_17);
x_19 = lean_io_as_task(x_18, x_3);
x_20 = lean_unsigned_to_nat(0u);
x_21 = 1;
x_22 = lean_task_bind(x_19, x_4, x_20, x_21);
lean_ctor_set(x_5, 0, x_22);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_5);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
lean_dec(x_5);
lean_inc(x_24);
x_25 = lean_apply_1(x_1, x_24);
x_26 = lean_box(2);
x_27 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___lam__3___boxed), 4, 2);
lean_closure_set(x_27, 0, x_24);
lean_closure_set(x_27, 1, x_26);
x_28 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_async___redArg___lam__3___boxed), 4, 3);
lean_closure_set(x_28, 0, x_25);
lean_closure_set(x_28, 1, x_27);
lean_closure_set(x_28, 2, x_2);
x_29 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(x_29, 0, lean_box(0));
lean_closure_set(x_29, 1, x_28);
x_30 = lean_io_as_task(x_29, x_3);
x_31 = lean_unsigned_to_nat(0u);
x_32 = 1;
x_33 = lean_task_bind(x_30, x_4, x_31, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_async___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Internal_IO_Async_ContextAsync_async___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_async___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_5 = l_Std_CancellationContext_fork(x_3);
x_6 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__1;
x_7 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__0;
x_8 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_async___redArg___lam__0___boxed), 6, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_6);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = 0;
x_13 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_11, x_12, x_10, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_async___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_ContextAsync_async___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_async(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_6 = l_Std_CancellationContext_fork(x_4);
x_7 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__1;
x_8 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__0;
x_9 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_async___redArg___lam__0___boxed), 6, 4);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_7);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = 0;
x_14 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_12, x_13, x_11, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_async___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_IO_Async_ContextAsync_async(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_8 = l_Std_CancellationContext_fork(x_6);
x_9 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_async___redArg___lam__0___boxed), 6, 4);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_5);
lean_closure_set(x_9, 3, x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = 0;
x_14 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_12, x_13, x_11, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Internal_IO_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instMonadAsyncAsyncTask___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__0;
x_2 = l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__1;
x_3 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instMonadAsyncAsyncTask() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Internal_IO_Async_ContextAsync_instMonadAsyncAsyncTask___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instFunctor___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_2(x_4, x_5, lean_box(0));
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec_ref(x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_3);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
x_8 = x_11;
goto block_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_8 = x_14;
goto block_10;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_apply_1(x_3, x_16);
lean_ctor_set(x_11, 0, x_17);
x_8 = x_11;
goto block_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_apply_1(x_3, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_8 = x_20;
goto block_10;
}
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(x_23, 0, lean_box(0));
lean_closure_set(x_23, 1, lean_box(0));
lean_closure_set(x_23, 2, lean_box(0));
lean_closure_set(x_23, 3, x_3);
x_24 = lean_unsigned_to_nat(0u);
x_25 = 0;
x_26 = lean_task_map(x_23, x_22, x_24, x_25);
lean_ctor_set(x_7, 0, x_26);
return x_7;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_7, 0);
lean_inc(x_27);
lean_dec(x_7);
x_28 = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(x_28, 0, lean_box(0));
lean_closure_set(x_28, 1, lean_box(0));
lean_closure_set(x_28, 2, lean_box(0));
lean_closure_set(x_28, 3, x_3);
x_29 = lean_unsigned_to_nat(0u);
x_30 = 0;
x_31 = lean_task_map(x_28, x_27, x_29, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
block_10:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instFunctor___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Internal_IO_Async_ContextAsync_instFunctor___lam__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instFunctor___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_4);
x_9 = lean_apply_6(x_1, lean_box(0), lean_box(0), x_8, x_5, x_6, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instFunctor___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Internal_IO_Async_ContextAsync_instFunctor___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instFunctor___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_instFunctor___lam__0___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instFunctor___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_ContextAsync_instFunctor___closed__0;
x_2 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_instFunctor___lam__1___boxed), 7, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instFunctor___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Internal_IO_Async_ContextAsync_instFunctor___closed__1;
x_2 = l_Std_Internal_IO_Async_ContextAsync_instFunctor___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instFunctor() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Internal_IO_Async_ContextAsync_instFunctor___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonad___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonad___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_ContextAsync_instMonad___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonad___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec_ref(x_3);
x_11 = lean_apply_3(x_1, x_10, x_2, lean_box(0));
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonad___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_ContextAsync_instMonad___lam__1(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonad___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
lean_inc_ref(x_5);
x_7 = lean_apply_2(x_3, x_5, lean_box(0));
x_8 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_instMonad___lam__1___boxed), 4, 2);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = 0;
x_11 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_9, x_10, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonad___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Internal_IO_Async_ContextAsync_instMonad___lam__2(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instMonad___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_instMonad___lam__0___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instMonad___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_instMonad___lam__2___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instMonad() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Std_Internal_IO_Async_ContextAsync_instFunctor;
x_2 = l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__2;
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_dec(x_5);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_10 = lean_ctor_get(x_4, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_4, 0);
lean_dec(x_11);
x_12 = l_Std_Internal_IO_Async_ContextAsync_instMonad___closed__0;
x_13 = l_Std_Internal_IO_Async_ContextAsync_instMonad___closed__1;
x_14 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_14, 0, x_9);
x_15 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_15, 0, x_8);
x_16 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_16, 0, x_7);
lean_ctor_set(x_4, 4, x_14);
lean_ctor_set(x_4, 3, x_15);
lean_ctor_set(x_4, 2, x_16);
lean_ctor_set(x_4, 1, x_12);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_2, 1, x_13);
return x_2;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_4, 2);
x_18 = lean_ctor_get(x_4, 3);
x_19 = lean_ctor_get(x_4, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_20 = l_Std_Internal_IO_Async_ContextAsync_instMonad___closed__0;
x_21 = l_Std_Internal_IO_Async_ContextAsync_instMonad___closed__1;
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_19);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_23, 0, x_18);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_24, 0, x_17);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_25, 2, x_24);
lean_ctor_set(x_25, 3, x_23);
lean_ctor_set(x_25, 4, x_22);
lean_ctor_set(x_2, 1, x_21);
lean_ctor_set(x_2, 0, x_25);
return x_2;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_dec(x_2);
x_27 = lean_ctor_get(x_26, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 3);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 4);
lean_inc(x_29);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 lean_ctor_release(x_26, 3);
 lean_ctor_release(x_26, 4);
 x_30 = x_26;
} else {
 lean_dec_ref(x_26);
 x_30 = lean_box(0);
}
x_31 = l_Std_Internal_IO_Async_ContextAsync_instMonad___closed__0;
x_32 = l_Std_Internal_IO_Async_ContextAsync_instMonad___closed__1;
x_33 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_33, 0, x_29);
x_34 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_34, 0, x_28);
x_35 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_35, 0, x_27);
if (lean_is_scalar(x_30)) {
 x_36 = lean_alloc_ctor(0, 5, 0);
} else {
 x_36 = x_30;
}
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_31);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_36, 3, x_34);
lean_ctor_set(x_36, 4, x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_32);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec_ref(x_1);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec_ref(x_9);
x_16 = lean_unsigned_to_nat(0u);
x_17 = 0;
x_18 = lean_task_map(x_1, x_15, x_16, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___lam__1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_14; 
x_14 = lean_apply_1(x_3, lean_box(0));
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_task_pure(x_16);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_17);
x_6 = x_14;
x_7 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_task_pure(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_6 = x_20;
x_7 = lean_box(0);
goto block_13;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_ctor_set_tag(x_14, 0);
x_6 = x_14;
x_7 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_6 = x_23;
x_7 = lean_box(0);
goto block_13;
}
}
block_13:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = 0;
x_12 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_10, x_11, x_9, x_1);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___lam__2(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
return x_6;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___closed__0;
x_2 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___lam__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___closed__1;
x_2 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___lam__2___boxed), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadLiftBaseIO___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_apply_1(x_2, lean_box(0));
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadLiftBaseIO___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_ContextAsync_instMonadLiftBaseIO___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instMonadLiftBaseIO___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_instMonadLiftBaseIO___lam__0___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instMonadLiftBaseIO() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Internal_IO_Async_ContextAsync_instMonadLiftBaseIO___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_apply_3(x_1, x_5, x_2, lean_box(0));
return x_6;
}
else
{
lean_object* x_7; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___lam__1(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
lean_inc_ref(x_4);
x_6 = lean_apply_2(x_2, x_4, lean_box(0));
x_7 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___lam__1___boxed), 4, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = 0;
x_10 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_8, x_9, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___lam__2(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___lam__0___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___lam__2___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___closed__1;
x_2 = l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadFinally___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, x_3, x_2, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadFinally___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_ContextAsync_instMonadFinally___lam__0(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadFinally___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
lean_inc_ref(x_5);
x_7 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_instMonadFinally___lam__0___boxed), 4, 2);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_apply_1(x_3, x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = 0;
x_11 = l_Std_Internal_IO_Async_EAsync_tryFinally_x27___redArg(x_8, x_7, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadFinally___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Internal_IO_Async_ContextAsync_instMonadFinally___lam__1(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instMonadFinally___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_instMonadFinally___lam__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instMonadFinally() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Internal_IO_Async_ContextAsync_instMonadFinally___closed__0;
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(`Inhabited.default` for `IO.Error`)", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___closed__0;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___closed__3;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instInhabited___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instInhabited(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_ContextAsync_instInhabited___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instInhabited___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_ContextAsync_instInhabited(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instMonadAwaitAsyncTask___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_ContextAsync_instMonadAwaitAsyncTask() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Internal_IO_Async_ContextAsync_instMonadAwaitAsyncTask___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selector_cancelled(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_3 = l_Std_Internal_IO_Async_ContextAsync_doneSelector___closed__0;
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = 0;
x_8 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_6, x_7, x_5, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selector_cancelled___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Selector_cancelled(x_1);
return x_3;
}
}
lean_object* initialize_Std_Time(uint8_t builtin);
lean_object* initialize_Std_Internal_UV(uint8_t builtin);
lean_object* initialize_Std_Internal_Async_Basic(uint8_t builtin);
lean_object* initialize_Std_Internal_Async_Timer(uint8_t builtin);
lean_object* initialize_Std_Sync_CancellationContext(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Async_ContextAsync(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_UV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Async_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Async_Timer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sync_CancellationContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Internal_IO_Async_ContextAsync_isCancelled___closed__0 = _init_l_Std_Internal_IO_Async_ContextAsync_isCancelled___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_isCancelled___closed__0);
l_Std_Internal_IO_Async_ContextAsync_getCancellationReason___closed__0 = _init_l_Std_Internal_IO_Async_ContextAsync_getCancellationReason___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_getCancellationReason___closed__0);
l_Std_Internal_IO_Async_ContextAsync_doneSelector___closed__0 = _init_l_Std_Internal_IO_Async_ContextAsync_doneSelector___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_doneSelector___closed__0);
l_Std_Internal_IO_Async_ContextAsync_awaitCancellation___closed__0 = _init_l_Std_Internal_IO_Async_ContextAsync_awaitCancellation___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_awaitCancellation___closed__0);
l_Std_Internal_IO_Async_ContextAsync_awaitCancellation___closed__1 = _init_l_Std_Internal_IO_Async_ContextAsync_awaitCancellation___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_awaitCancellation___closed__1);
l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__0 = _init_l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__0);
l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__1 = _init_l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_concurrently___redArg___closed__1);
l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__12___closed__0 = _init_l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__12___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_race___redArg___lam__12___closed__0);
l_Std_Internal_IO_Async_ContextAsync_race___redArg___closed__0 = _init_l_Std_Internal_IO_Async_ContextAsync_race___redArg___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_race___redArg___closed__0);
l_Std_Internal_IO_Async_ContextAsync_race___redArg___closed__1 = _init_l_Std_Internal_IO_Async_ContextAsync_race___redArg___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_race___redArg___closed__1);
l_Std_Internal_IO_Async_ContextAsync_race___redArg___closed__2 = _init_l_Std_Internal_IO_Async_ContextAsync_race___redArg___closed__2();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_race___redArg___closed__2);
l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__0 = _init_l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__0);
l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__1 = _init_l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__1);
l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__2 = _init_l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__2();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__2);
l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__3 = _init_l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__3();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_concurrentlyAll___redArg___closed__3);
l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__2___closed__0 = _init_l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__2___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__2___closed__0);
l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__2___closed__1 = _init_l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__2___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_background___redArg___lam__2___closed__1);
l_Std_Internal_IO_Async_ContextAsync_instMonadAsyncAsyncTask___closed__0 = _init_l_Std_Internal_IO_Async_ContextAsync_instMonadAsyncAsyncTask___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instMonadAsyncAsyncTask___closed__0);
l_Std_Internal_IO_Async_ContextAsync_instMonadAsyncAsyncTask = _init_l_Std_Internal_IO_Async_ContextAsync_instMonadAsyncAsyncTask();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instMonadAsyncAsyncTask);
l_Std_Internal_IO_Async_ContextAsync_instFunctor___closed__0 = _init_l_Std_Internal_IO_Async_ContextAsync_instFunctor___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instFunctor___closed__0);
l_Std_Internal_IO_Async_ContextAsync_instFunctor___closed__1 = _init_l_Std_Internal_IO_Async_ContextAsync_instFunctor___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instFunctor___closed__1);
l_Std_Internal_IO_Async_ContextAsync_instFunctor___closed__2 = _init_l_Std_Internal_IO_Async_ContextAsync_instFunctor___closed__2();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instFunctor___closed__2);
l_Std_Internal_IO_Async_ContextAsync_instFunctor = _init_l_Std_Internal_IO_Async_ContextAsync_instFunctor();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instFunctor);
l_Std_Internal_IO_Async_ContextAsync_instMonad___closed__0 = _init_l_Std_Internal_IO_Async_ContextAsync_instMonad___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instMonad___closed__0);
l_Std_Internal_IO_Async_ContextAsync_instMonad___closed__1 = _init_l_Std_Internal_IO_Async_ContextAsync_instMonad___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instMonad___closed__1);
l_Std_Internal_IO_Async_ContextAsync_instMonad = _init_l_Std_Internal_IO_Async_ContextAsync_instMonad();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instMonad);
l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___closed__0 = _init_l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___closed__0);
l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___closed__1 = _init_l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___closed__1);
l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___closed__2 = _init_l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___closed__2();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO___closed__2);
l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO = _init_l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instMonadLiftIO);
l_Std_Internal_IO_Async_ContextAsync_instMonadLiftBaseIO___closed__0 = _init_l_Std_Internal_IO_Async_ContextAsync_instMonadLiftBaseIO___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instMonadLiftBaseIO___closed__0);
l_Std_Internal_IO_Async_ContextAsync_instMonadLiftBaseIO = _init_l_Std_Internal_IO_Async_ContextAsync_instMonadLiftBaseIO();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instMonadLiftBaseIO);
l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___closed__0 = _init_l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___closed__0);
l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___closed__1 = _init_l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___closed__1);
l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___closed__2 = _init_l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___closed__2();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError___closed__2);
l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError = _init_l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instMonadExceptError);
l_Std_Internal_IO_Async_ContextAsync_instMonadFinally___closed__0 = _init_l_Std_Internal_IO_Async_ContextAsync_instMonadFinally___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instMonadFinally___closed__0);
l_Std_Internal_IO_Async_ContextAsync_instMonadFinally = _init_l_Std_Internal_IO_Async_ContextAsync_instMonadFinally();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instMonadFinally);
l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___closed__0 = _init_l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___closed__0);
l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___closed__1 = _init_l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___closed__1);
l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___closed__2 = _init_l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___closed__2();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___closed__2);
l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___closed__3 = _init_l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___closed__3();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instInhabited___lam__0___closed__3);
l_Std_Internal_IO_Async_ContextAsync_instInhabited___closed__0 = _init_l_Std_Internal_IO_Async_ContextAsync_instInhabited___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instInhabited___closed__0);
l_Std_Internal_IO_Async_ContextAsync_instMonadAwaitAsyncTask___closed__0 = _init_l_Std_Internal_IO_Async_ContextAsync_instMonadAwaitAsyncTask___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instMonadAwaitAsyncTask___closed__0);
l_Std_Internal_IO_Async_ContextAsync_instMonadAwaitAsyncTask = _init_l_Std_Internal_IO_Async_ContextAsync_instMonadAwaitAsyncTask();
lean_mark_persistent(l_Std_Internal_IO_Async_ContextAsync_instMonadAwaitAsyncTask);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
