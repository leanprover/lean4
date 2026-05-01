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
lean_object* l_Std_CancellationContext_fork(lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Std_CancellationContext_cancel(lean_object*, lean_object*);
lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_BaseAsync_toRawBaseIO___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_io_promise_new();
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* l_liftM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_CancellationToken_selector(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Std_Async_EAsync_instMonad(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Function_const___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_CancellationContext_new();
lean_object* l_Std_CancellationToken_getCancellationReason(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ContextAsync_race___redArg___lam__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_race___redArg___lam__11___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_race___redArg___lam__11___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ContextAsync_race___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_race___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_race___redArg___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_race___redArg___closed__0_value;
static const lean_closure_object l_Std_Async_ContextAsync_race___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_race___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_race___redArg___closed__1 = (const lean_object*)&l_Std_Async_ContextAsync_race___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Std_Async_ContextAsync_instInhabited___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_Std_Async_ContextAsync_instInhabited___lam__0___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_instInhabited___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Async_ContextAsync_instInhabited___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Std_Async_ContextAsync_instInhabited___lam__0___closed__0_value)}};
static const lean_object* l_Std_Async_ContextAsync_instInhabited___lam__0___closed__1 = (const lean_object*)&l_Std_Async_ContextAsync_instInhabited___lam__0___closed__1_value;
static const lean_ctor_object l_Std_Async_ContextAsync_instInhabited___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_ContextAsync_instInhabited___lam__0___closed__1_value)}};
static const lean_object* l_Std_Async_ContextAsync_instInhabited___lam__0___closed__2 = (const lean_object*)&l_Std_Async_ContextAsync_instInhabited___lam__0___closed__2_value;
static const lean_ctor_object l_Std_Async_ContextAsync_instInhabited___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_ContextAsync_instInhabited___lam__0___closed__2_value)}};
static const lean_object* l_Std_Async_ContextAsync_instInhabited___lam__0___closed__3 = (const lean_object*)&l_Std_Async_ContextAsync_instInhabited___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ContextAsync_instInhabited___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_instInhabited___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_instInhabited___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_instInhabited___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___closed__0 = (const lean_object*)&l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_ContextAsync_instMonadAwaitAsyncTask = (const lean_object*)&l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___closed__0_value;
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
lean_dec_ref(v_x_20_);
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
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___f_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; uint8_t v___x_46_; lean_object* v___x_47_; 
v___x_40_ = lean_box(2);
v___x_41_ = l_Std_CancellationContext_cancel(v_a_36_, v___x_40_);
v___f_42_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_run___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_42_, 0, v_x_37_);
v___x_43_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_43_, 0, v___x_41_);
v___x_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = 0;
v___x_47_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_45_, v___x_46_, v___x_44_, v___f_42_);
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
lean_object* v_a_64_; lean_object* v___x_65_; lean_object* v___f_66_; lean_object* v___x_67_; uint8_t v___x_68_; lean_object* v___x_69_; 
v_a_64_ = lean_ctor_get(v_x_53_, 0);
lean_inc_n(v_a_64_, 2);
lean_dec_ref(v_x_53_);
v___x_65_ = lean_apply_2(v_x_52_, v_a_64_, lean_box(0));
v___f_66_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_run___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_66_, 0, v_a_64_);
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = 0;
v___x_69_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_67_, v___x_68_, v___x_65_, v___f_66_);
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
lean_object* v___x_76_; lean_object* v___f_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; lean_object* v___x_82_; 
v___x_76_ = l_Std_CancellationContext_new();
v___f_77_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_run___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_77_, 0, v_x_74_);
v___x_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_76_);
v___x_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = 0;
v___x_82_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_80_, v___x_81_, v___x_79_, v___f_77_);
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
lean_object* v___x_89_; lean_object* v___f_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; lean_object* v___x_95_; 
v___x_89_ = l_Std_CancellationContext_new();
v___f_90_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_run___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_90_, 0, v_x_87_);
v___x_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_91_, 0, v___x_89_);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = 0;
v___x_95_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_93_, v___x_94_, v___x_92_, v___f_90_);
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
lean_object* v___f_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; lean_object* v___x_141_; 
v___f_136_ = ((lean_object*)(l_Std_Async_ContextAsync_isCancelled___closed__0));
lean_inc_ref(v_a_134_);
v___x_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_137_, 0, v_a_134_);
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
v___x_139_ = lean_unsigned_to_nat(0u);
v___x_140_ = 0;
v___x_141_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_139_, v___x_140_, v___x_138_, v___f_136_);
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
lean_object* v___f_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; lean_object* v___x_178_; 
v___f_173_ = ((lean_object*)(l_Std_Async_ContextAsync_getCancellationReason___closed__0));
lean_inc_ref(v_a_171_);
v___x_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_174_, 0, v_a_171_);
v___x_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_177_ = 0;
v___x_178_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_176_, v___x_177_, v___x_175_, v___f_173_);
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
lean_object* v___f_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; lean_object* v___x_216_; 
v___f_211_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_cancel___lam__0___boxed), 3, 1);
lean_closure_set(v___f_211_, 0, v_reason_208_);
lean_inc_ref(v_a_209_);
v___x_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_212_, 0, v_a_209_);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = 0;
v___x_216_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_214_, v___x_215_, v___x_213_, v___f_211_);
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
lean_object* v___f_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; lean_object* v___x_254_; 
v___f_249_ = ((lean_object*)(l_Std_Async_ContextAsync_doneSelector___closed__0));
lean_inc_ref(v_a_247_);
v___x_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_250_, 0, v_a_247_);
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
v___x_252_ = lean_unsigned_to_nat(0u);
v___x_253_ = 0;
v___x_254_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_252_, v___x_253_, v___x_251_, v___f_249_);
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
lean_dec_ref(v_x_258_);
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
lean_object* v_val_278_; 
if (lean_obj_tag(v_x_275_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_291_; 
lean_dec_ref(v___f_274_);
v_a_283_ = lean_ctor_get(v_x_275_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v_x_275_);
if (v_isSharedCheck_291_ == 0)
{
v___x_285_ = v_x_275_;
v_isShared_286_ = v_isSharedCheck_291_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v_x_275_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_291_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_290_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_289_; 
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
return v___x_289_;
}
}
}
else
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_306_; 
v_a_292_ = lean_ctor_get(v_x_275_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v_x_275_);
if (v_isSharedCheck_306_ == 0)
{
v___x_294_ = v_x_275_;
v_isShared_295_ = v_isSharedCheck_306_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v_x_275_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_306_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v_token_296_; lean_object* v___x_297_; 
v_token_296_ = lean_ctor_get(v_a_292_, 1);
lean_inc_ref(v_token_296_);
lean_dec(v_a_292_);
v___x_297_ = l_Std_CancellationToken_wait(v_token_296_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v_a_298_; lean_object* v___x_300_; 
v_a_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_a_298_);
lean_dec_ref(v___x_297_);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 0, v_a_298_);
v___x_300_ = v___x_294_;
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
v_val_278_ = v___x_300_;
goto v___jp_277_;
}
}
else
{
lean_object* v_a_302_; lean_object* v___x_304_; 
v_a_302_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_a_302_);
lean_dec_ref(v___x_297_);
if (v_isShared_295_ == 0)
{
lean_ctor_set_tag(v___x_294_, 0);
lean_ctor_set(v___x_294_, 0, v_a_302_);
v___x_304_ = v___x_294_;
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
v_val_278_ = v___x_304_;
goto v___jp_277_;
}
}
}
}
v___jp_277_:
{
lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; lean_object* v___x_282_; 
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v_val_278_);
v___x_280_ = lean_unsigned_to_nat(0u);
v___x_281_ = 0;
v___x_282_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_280_, v___x_281_, v___x_279_, v___f_274_);
return v___x_282_;
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
lean_object* v___f_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; lean_object* v___x_321_; 
v___f_316_ = ((lean_object*)(l_Std_Async_ContextAsync_awaitCancellation___closed__1));
lean_inc_ref(v_a_314_);
v___x_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_317_, 0, v_a_314_);
v___x_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = 0;
v___x_321_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_319_, v___x_320_, v___x_318_, v___f_316_);
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
lean_dec_ref(v_x_325_);
v___x_327_ = lean_task_pure(v_a_326_);
return v___x_327_;
}
else
{
lean_object* v_a_328_; 
v_a_328_ = lean_ctor_get(v_x_325_, 0);
lean_inc_ref(v_a_328_);
lean_dec_ref(v_x_325_);
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
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___f_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; lean_object* v___x_343_; 
v___x_336_ = lean_box(2);
v___x_337_ = l_Std_CancellationContext_cancel(v_a_333_, v___x_336_);
v___f_338_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_run___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_338_, 0, v_x_334_);
v___x_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_337_);
v___x_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = 0;
v___x_343_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_341_, v___x_342_, v___x_340_, v___f_338_);
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
lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; lean_object* v___x_356_; 
v___x_353_ = lean_apply_2(v_x_349_, v_a_350_, lean_box(0));
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = 0;
v___x_356_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_354_, v___x_355_, v___x_353_, v___f_351_);
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
lean_object* v___x_378_; uint8_t v___x_379_; lean_object* v___x_380_; lean_object* v___y_382_; 
v___x_378_ = lean_unsigned_to_nat(0u);
v___x_379_ = 0;
v___x_380_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_374_, v___f_375_, v___x_378_, v___x_379_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_384_; 
lean_dec(v___f_376_);
v_a_384_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_384_);
lean_dec_ref(v___x_380_);
if (lean_obj_tag(v_a_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
v_a_385_ = lean_ctor_get(v_a_384_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v_a_384_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v_a_384_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v_a_384_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
v___y_382_ = v___x_390_;
goto v___jp_381_;
}
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_401_; 
v_a_393_ = lean_ctor_get(v_a_384_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v_a_384_);
if (v_isSharedCheck_401_ == 0)
{
v___x_395_ = v_a_384_;
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v_a_384_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v_fst_397_; lean_object* v___x_399_; 
v_fst_397_ = lean_ctor_get(v_a_393_, 0);
lean_inc(v_fst_397_);
lean_dec(v_a_393_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v_fst_397_);
v___x_399_ = v___x_395_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_fst_397_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
v___y_382_ = v___x_399_;
goto v___jp_381_;
}
}
}
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_411_; 
v_a_402_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_411_ == 0)
{
v___x_404_ = v___x_380_;
v_isShared_405_ = v_isSharedCheck_411_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_380_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_411_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_406_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_406_, 0, lean_box(0));
lean_closure_set(v___x_406_, 1, lean_box(0));
lean_closure_set(v___x_406_, 2, lean_box(0));
lean_closure_set(v___x_406_, 3, v___f_376_);
v___x_407_ = lean_task_map(v___x_406_, v_a_402_, v___x_378_, v___x_379_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_407_);
v___x_409_ = v___x_404_;
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
v___jp_381_:
{
lean_object* v___x_383_; 
v___x_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_383_, 0, v___y_382_);
return v___x_383_;
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
lean_object* v___x_421_; lean_object* v___f_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; lean_object* v___x_427_; 
v___x_421_ = l_Std_CancellationContext_cancel(v_a_417_, v___x_418_);
v___f_422_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_run___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_422_, 0, v_x_419_);
v___x_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_421_);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
v___x_425_ = lean_unsigned_to_nat(0u);
v___x_426_ = 0;
v___x_427_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_425_, v___x_426_, v___x_424_, v___f_422_);
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
lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; lean_object* v___x_441_; 
v___x_438_ = lean_apply_2(v_y_434_, v_a_435_, lean_box(0));
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = 0;
v___x_441_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_439_, v___x_440_, v___x_438_, v___f_436_);
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
lean_object* v_a_485_; lean_object* v___f_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; lean_object* v___x_490_; 
v_a_485_ = lean_ctor_get(v_x_474_, 0);
lean_inc(v_a_485_);
lean_dec_ref(v_x_474_);
v___f_486_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__10___boxed), 3, 1);
lean_closure_set(v___f_486_, 0, v_a_485_);
v___x_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_487_, 0, v_a_473_);
v___x_488_ = lean_unsigned_to_nat(0u);
v___x_489_ = 0;
v___x_490_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_488_, v___x_489_, v___x_487_, v___f_486_);
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
lean_object* v_a_507_; lean_object* v___f_508_; lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; lean_object* v___x_512_; 
v_a_507_ = lean_ctor_get(v_x_496_, 0);
lean_inc(v_a_507_);
lean_dec_ref(v_x_496_);
v___f_508_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__8___boxed), 3, 1);
lean_closure_set(v___f_508_, 0, v_a_507_);
v___x_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_509_, 0, v_a_495_);
v___x_510_ = lean_unsigned_to_nat(0u);
v___x_511_ = 0;
v___x_512_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_510_, v___x_511_, v___x_509_, v___f_508_);
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
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___f_537_; lean_object* v___x_538_; uint8_t v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
v___x_535_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_535_, 0, lean_box(0));
lean_closure_set(v___x_535_, 1, v___f_517_);
v___x_536_ = lean_io_as_task(v___x_535_, v_prio_518_);
v___f_537_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_537_, 0, v_a_531_);
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = 1;
v___x_540_ = lean_task_bind(v___x_536_, v___f_519_, v___x_538_, v___x_539_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_540_);
v___x_542_ = v___x_533_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_540_);
v___x_542_ = v_reuseFailAlloc_546_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_object* v___x_543_; uint8_t v___x_544_; lean_object* v___x_545_; 
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
v___x_544_ = 0;
v___x_545_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_538_, v___x_544_, v___x_543_, v___f_537_);
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
lean_dec_ref(v_x_555_);
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
lean_object* v___x_576_; lean_object* v___f_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; lean_object* v___x_582_; 
v___x_576_ = l_Std_CancellationContext_cancel(v_a_571_, v___x_572_);
v___f_577_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__12___boxed), 3, 1);
lean_closure_set(v___f_577_, 0, v_x_573_);
v___x_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_576_);
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
v___x_580_ = lean_unsigned_to_nat(0u);
v___x_581_ = 0;
v___x_582_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_580_, v___x_581_, v___x_579_, v___f_577_);
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
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__14(lean_object* v_a_588_, lean_object* v___f_589_, lean_object* v___f_590_, lean_object* v_prio_591_, lean_object* v_a_592_, lean_object* v_y_593_, lean_object* v___f_594_, lean_object* v___f_595_, lean_object* v___f_596_, lean_object* v_x_597_){
_start:
{
if (lean_obj_tag(v_x_597_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_607_; 
lean_dec_ref(v___f_596_);
lean_dec_ref(v___f_595_);
lean_dec(v___f_594_);
lean_dec_ref(v_y_593_);
lean_dec_ref(v_a_592_);
lean_dec(v_prio_591_);
lean_dec(v___f_590_);
lean_dec_ref(v___f_589_);
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
lean_object* v___x_612_; lean_object* v___f_613_; lean_object* v___f_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___f_617_; lean_object* v___f_618_; lean_object* v___f_619_; lean_object* v___f_620_; lean_object* v___f_621_; lean_object* v___x_622_; uint8_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
v___x_612_ = lean_box(2);
v___f_613_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_613_, 0, v_a_588_);
lean_closure_set(v___f_613_, 1, v___x_612_);
v___f_614_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_614_, 0, v___f_589_);
lean_closure_set(v___f_614_, 1, v___f_613_);
lean_closure_set(v___f_614_, 2, v___f_590_);
v___x_615_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_615_, 0, lean_box(0));
lean_closure_set(v___x_615_, 1, v___f_614_);
lean_inc(v_prio_591_);
v___x_616_ = lean_io_as_task(v___x_615_, v_prio_591_);
lean_inc_ref(v_a_592_);
v___f_617_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_617_, 0, v_a_592_);
lean_closure_set(v___f_617_, 1, v___x_612_);
lean_inc(v_a_608_);
v___f_618_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__6___boxed), 4, 3);
lean_closure_set(v___f_618_, 0, v_y_593_);
lean_closure_set(v___f_618_, 1, v_a_608_);
lean_closure_set(v___f_618_, 2, v___f_617_);
v___f_619_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_619_, 0, v_a_608_);
lean_closure_set(v___f_619_, 1, v___x_612_);
v___f_620_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_620_, 0, v___f_618_);
lean_closure_set(v___f_620_, 1, v___f_619_);
lean_closure_set(v___f_620_, 2, v___f_594_);
v___f_621_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__11___boxed), 5, 3);
lean_closure_set(v___f_621_, 0, v___f_620_);
lean_closure_set(v___f_621_, 1, v_prio_591_);
lean_closure_set(v___f_621_, 2, v___f_595_);
v___x_622_ = lean_unsigned_to_nat(0u);
v___x_623_ = 1;
v___x_624_ = lean_task_bind(v___x_616_, v___f_596_, v___x_622_, v___x_623_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_624_);
v___x_626_ = v___x_610_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_624_);
v___x_626_ = v_reuseFailAlloc_632_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_627_; uint8_t v___x_628_; lean_object* v___x_629_; lean_object* v___f_630_; lean_object* v___x_631_; 
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
v___x_628_ = 0;
v___x_629_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_622_, v___x_628_, v___x_627_, v___f_621_);
v___f_630_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__13___boxed), 4, 2);
lean_closure_set(v___f_630_, 0, v_a_592_);
lean_closure_set(v___f_630_, 1, v___x_612_);
v___x_631_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_622_, v___x_628_, v___x_629_, v___f_630_);
return v___x_631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__14___boxed(lean_object* v_a_634_, lean_object* v___f_635_, lean_object* v___f_636_, lean_object* v_prio_637_, lean_object* v_a_638_, lean_object* v_y_639_, lean_object* v___f_640_, lean_object* v___f_641_, lean_object* v___f_642_, lean_object* v_x_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__14(v_a_634_, v___f_635_, v___f_636_, v_prio_637_, v_a_638_, v_y_639_, v___f_640_, v___f_641_, v___f_642_, v_x_643_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__15(lean_object* v_a_646_, lean_object* v_x_647_, lean_object* v___f_648_, lean_object* v___f_649_, lean_object* v_prio_650_, lean_object* v_y_651_, lean_object* v___f_652_, lean_object* v___f_653_, lean_object* v___f_654_, lean_object* v_x_655_){
_start:
{
if (lean_obj_tag(v_x_655_) == 0)
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_665_; 
lean_dec_ref(v___f_654_);
lean_dec_ref(v___f_653_);
lean_dec(v___f_652_);
lean_dec_ref(v_y_651_);
lean_dec(v_prio_650_);
lean_dec(v___f_649_);
lean_dec_ref(v___f_648_);
lean_dec_ref(v_x_647_);
lean_dec_ref(v_a_646_);
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
lean_object* v___x_670_; lean_object* v___f_671_; lean_object* v___f_672_; lean_object* v___x_674_; 
lean_inc_ref(v_a_646_);
v___x_670_ = l_Std_CancellationContext_fork(v_a_646_);
lean_inc(v_a_666_);
v___f_671_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_671_, 0, v_x_647_);
lean_closure_set(v___f_671_, 1, v_a_666_);
lean_closure_set(v___f_671_, 2, v___f_648_);
v___f_672_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__14___boxed), 11, 9);
lean_closure_set(v___f_672_, 0, v_a_666_);
lean_closure_set(v___f_672_, 1, v___f_671_);
lean_closure_set(v___f_672_, 2, v___f_649_);
lean_closure_set(v___f_672_, 3, v_prio_650_);
lean_closure_set(v___f_672_, 4, v_a_646_);
lean_closure_set(v___f_672_, 5, v_y_651_);
lean_closure_set(v___f_672_, 6, v___f_652_);
lean_closure_set(v___f_672_, 7, v___f_653_);
lean_closure_set(v___f_672_, 8, v___f_654_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_670_);
v___x_674_ = v___x_668_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_670_);
v___x_674_ = v_reuseFailAlloc_679_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; lean_object* v___x_678_; 
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = 0;
v___x_678_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_676_, v___x_677_, v___x_675_, v___f_672_);
return v___x_678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__15___boxed(lean_object* v_a_681_, lean_object* v_x_682_, lean_object* v___f_683_, lean_object* v___f_684_, lean_object* v_prio_685_, lean_object* v_y_686_, lean_object* v___f_687_, lean_object* v___f_688_, lean_object* v___f_689_, lean_object* v_x_690_, lean_object* v___y_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__15(v_a_681_, v_x_682_, v___f_683_, v___f_684_, v_prio_685_, v_y_686_, v___f_687_, v___f_688_, v___f_689_, v_x_690_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__16(lean_object* v_x_693_, lean_object* v___f_694_, lean_object* v_prio_695_, lean_object* v_y_696_, lean_object* v___f_697_, lean_object* v___f_698_, lean_object* v___f_699_, lean_object* v_x_700_){
_start:
{
if (lean_obj_tag(v_x_700_) == 0)
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_710_; 
lean_dec_ref(v___f_699_);
lean_dec_ref(v___f_698_);
lean_dec(v___f_697_);
lean_dec_ref(v_y_696_);
lean_dec(v_prio_695_);
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
lean_object* v___x_715_; lean_object* v___f_716_; lean_object* v___f_717_; lean_object* v___x_719_; 
lean_inc_n(v_a_711_, 2);
v___x_715_ = l_Std_CancellationContext_fork(v_a_711_);
v___f_716_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_716_, 0, v_a_711_);
v___f_717_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__15___boxed), 11, 9);
lean_closure_set(v___f_717_, 0, v_a_711_);
lean_closure_set(v___f_717_, 1, v_x_693_);
lean_closure_set(v___f_717_, 2, v___f_716_);
lean_closure_set(v___f_717_, 3, v___f_694_);
lean_closure_set(v___f_717_, 4, v_prio_695_);
lean_closure_set(v___f_717_, 5, v_y_696_);
lean_closure_set(v___f_717_, 6, v___f_697_);
lean_closure_set(v___f_717_, 7, v___f_698_);
lean_closure_set(v___f_717_, 8, v___f_699_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v___x_715_);
v___x_719_ = v___x_713_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_715_);
v___x_719_ = v_reuseFailAlloc_724_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; lean_object* v___x_723_; 
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
v___x_721_ = lean_unsigned_to_nat(0u);
v___x_722_ = 0;
v___x_723_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_721_, v___x_722_, v___x_720_, v___f_717_);
return v___x_723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrently___redArg___lam__16___boxed(lean_object* v_x_726_, lean_object* v___f_727_, lean_object* v_prio_728_, lean_object* v_y_729_, lean_object* v___f_730_, lean_object* v___f_731_, lean_object* v___f_732_, lean_object* v_x_733_, lean_object* v___y_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__16(v_x_726_, v___f_727_, v_prio_728_, v_y_729_, v___f_730_, v___f_731_, v___f_732_, v_x_733_);
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
lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_752_ = l_Std_CancellationContext_fork(v_a_748_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v___x_752_);
v___x_754_ = v___x_750_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_759_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; lean_object* v___x_758_; 
v___x_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
v___x_756_ = lean_unsigned_to_nat(0u);
v___x_757_ = 0;
v___x_758_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_756_, v___x_757_, v___x_755_, v___f_736_);
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
lean_object* v___f_772_; lean_object* v___f_773_; lean_object* v___f_774_; lean_object* v___f_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; lean_object* v___x_780_; 
v___f_772_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_773_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__1));
v___f_774_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__16___boxed), 9, 7);
lean_closure_set(v___f_774_, 0, v_x_767_);
lean_closure_set(v___f_774_, 1, v___f_773_);
lean_closure_set(v___f_774_, 2, v_prio_769_);
lean_closure_set(v___f_774_, 3, v_y_768_);
lean_closure_set(v___f_774_, 4, v___f_773_);
lean_closure_set(v___f_774_, 5, v___f_772_);
lean_closure_set(v___f_774_, 6, v___f_772_);
v___f_775_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__17___boxed), 3, 1);
lean_closure_set(v___f_775_, 0, v___f_774_);
lean_inc_ref(v_a_770_);
v___x_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_776_, 0, v_a_770_);
v___x_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
v___x_778_ = lean_unsigned_to_nat(0u);
v___x_779_ = 0;
v___x_780_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_778_, v___x_779_, v___x_777_, v___f_775_);
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
lean_object* v___f_794_; lean_object* v___f_795_; lean_object* v___f_796_; lean_object* v___f_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; uint8_t v___x_801_; lean_object* v___x_802_; 
v___f_794_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_795_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__1));
v___f_796_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__16___boxed), 9, 7);
lean_closure_set(v___f_796_, 0, v_x_789_);
lean_closure_set(v___f_796_, 1, v___f_795_);
lean_closure_set(v___f_796_, 2, v_prio_791_);
lean_closure_set(v___f_796_, 3, v_y_790_);
lean_closure_set(v___f_796_, 4, v___f_795_);
lean_closure_set(v___f_796_, 5, v___f_794_);
lean_closure_set(v___f_796_, 6, v___f_794_);
v___f_797_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__17___boxed), 3, 1);
lean_closure_set(v___f_797_, 0, v___f_796_);
lean_inc_ref(v_a_792_);
v___x_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_798_, 0, v_a_792_);
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = 0;
v___x_802_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_800_, v___x_801_, v___x_799_, v___f_797_);
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
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__3(lean_object* v_x_811_){
_start:
{
if (lean_obj_tag(v_x_811_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_821_; 
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
lean_object* v_a_822_; lean_object* v___x_823_; 
v_a_822_ = lean_ctor_get(v_x_811_, 0);
lean_inc(v_a_822_);
lean_dec_ref(v_x_811_);
v___x_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_823_, 0, v_a_822_);
return v___x_823_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__3___boxed(lean_object* v_x_824_, lean_object* v___y_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Std_Async_ContextAsync_race___redArg___lam__3(v_x_824_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__0(lean_object* v_a_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_828_, 0, v_a_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__2(lean_object* v_x_829_, lean_object* v_a_830_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = lean_apply_2(v_x_829_, v_a_830_, lean_box(0));
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__2___boxed(lean_object* v_x_833_, lean_object* v_a_834_, lean_object* v___y_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Std_Async_ContextAsync_race___redArg___lam__2(v_x_833_, v_a_834_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__5(lean_object* v_y_837_, lean_object* v_a_838_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = lean_apply_2(v_y_837_, v_a_838_, lean_box(0));
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__5___boxed(lean_object* v_y_841_, lean_object* v_a_842_, lean_object* v___y_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Std_Async_ContextAsync_race___redArg___lam__5(v_y_841_, v_a_842_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__6(lean_object* v_a_845_, lean_object* v___f_846_){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; lean_object* v___x_851_; 
v___x_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_848_, 0, v_a_845_);
v___x_849_ = lean_unsigned_to_nat(0u);
v___x_850_ = 0;
v___x_851_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_849_, v___x_850_, v___x_848_, v___f_846_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__6___boxed(lean_object* v_a_852_, lean_object* v___f_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Std_Async_ContextAsync_race___redArg___lam__6(v_a_852_, v___f_853_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__4(lean_object* v_a_856_, lean_object* v___f_857_, lean_object* v___f_858_, lean_object* v_x_859_){
_start:
{
if (lean_obj_tag(v_x_859_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_869_; 
lean_dec_ref(v___f_858_);
lean_dec_ref(v___f_857_);
v_a_861_ = lean_ctor_get(v_x_859_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v_x_859_);
if (v_isSharedCheck_869_ == 0)
{
v___x_863_ = v_x_859_;
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v_x_859_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_868_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_867_; 
v___x_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
return v___x_867_;
}
}
}
else
{
lean_object* v___x_870_; lean_object* v___x_871_; uint8_t v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
lean_dec_ref(v_x_859_);
v___x_870_ = l_IO_Promise_result_x21___redArg(v_a_856_);
v___x_871_ = lean_unsigned_to_nat(0u);
v___x_872_ = 0;
v___x_873_ = lean_task_map(v___f_857_, v___x_870_, v___x_871_, v___x_872_);
v___x_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
v___x_875_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_871_, v___x_872_, v___x_874_, v___f_858_);
return v___x_875_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__4___boxed(lean_object* v_a_876_, lean_object* v___f_877_, lean_object* v___f_878_, lean_object* v_x_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Std_Async_ContextAsync_race___redArg___lam__4(v_a_876_, v___f_877_, v___f_878_, v_x_879_);
lean_dec(v_a_876_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__1(lean_object* v_a_882_, lean_object* v_value_883_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = lean_io_promise_resolve(v_value_883_, v_a_882_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__1___boxed(lean_object* v_a_886_, lean_object* v_value_887_, lean_object* v___y_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Std_Async_ContextAsync_race___redArg___lam__1(v_a_886_, v_value_887_);
lean_dec(v_a_886_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__7(lean_object* v_a_890_, lean_object* v___x_891_, lean_object* v___x_892_, uint8_t v___x_893_, lean_object* v___f_894_, lean_object* v_x_895_){
_start:
{
if (lean_obj_tag(v_x_895_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_905_; 
lean_dec_ref(v___f_894_);
lean_dec(v___x_892_);
lean_dec_ref(v___x_891_);
lean_dec_ref(v_a_890_);
v_a_897_ = lean_ctor_get(v_x_895_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v_x_895_);
if (v_isSharedCheck_905_ == 0)
{
v___x_899_ = v_x_895_;
v_isShared_900_ = v_isSharedCheck_905_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v_x_895_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_905_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_904_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_903_; 
v___x_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
return v___x_903_;
}
}
}
else
{
lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_915_; 
v_isSharedCheck_915_ = !lean_is_exclusive(v_x_895_);
if (v_isSharedCheck_915_ == 0)
{
lean_object* v_unused_916_; 
v_unused_916_ = lean_ctor_get(v_x_895_, 0);
lean_dec(v_unused_916_);
v___x_907_ = v_x_895_;
v_isShared_908_ = v_isSharedCheck_915_;
goto v_resetjp_906_;
}
else
{
lean_dec(v_x_895_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_915_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_909_; lean_object* v___x_911_; 
lean_inc(v___x_892_);
v___x_909_ = l_BaseIO_chainTask___redArg(v_a_890_, v___x_891_, v___x_892_, v___x_893_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v___x_909_);
v___x_911_ = v___x_907_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_909_);
v___x_911_ = v_reuseFailAlloc_914_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
v___x_913_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_892_, v___x_893_, v___x_912_, v___f_894_);
return v___x_913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__7___boxed(lean_object* v_a_917_, lean_object* v___x_918_, lean_object* v___x_919_, lean_object* v___x_920_, lean_object* v___f_921_, lean_object* v_x_922_, lean_object* v___y_923_){
_start:
{
uint8_t v___x_8529__boxed_924_; lean_object* v_res_925_; 
v___x_8529__boxed_924_ = lean_unbox(v___x_920_);
v_res_925_ = l_Std_Async_ContextAsync_race___redArg___lam__7(v_a_917_, v___x_918_, v___x_919_, v___x_8529__boxed_924_, v___f_921_, v_x_922_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__8(lean_object* v___f_926_, lean_object* v___f_927_, lean_object* v_a_928_, lean_object* v___f_929_, lean_object* v_x_930_){
_start:
{
if (lean_obj_tag(v_x_930_) == 0)
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_940_; 
lean_dec_ref(v___f_929_);
lean_dec_ref(v_a_928_);
lean_dec_ref(v___f_927_);
lean_dec(v___f_926_);
v_a_932_ = lean_ctor_get(v_x_930_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v_x_930_);
if (v_isSharedCheck_940_ == 0)
{
v___x_934_ = v_x_930_;
v_isShared_935_ = v_isSharedCheck_940_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v_x_930_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_940_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_932_);
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
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_957_; 
v_a_941_ = lean_ctor_get(v_x_930_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v_x_930_);
if (v_isSharedCheck_957_ == 0)
{
v___x_943_ = v_x_930_;
v_isShared_944_ = v_isSharedCheck_957_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v_x_930_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_957_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; uint8_t v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___f_951_; lean_object* v___x_953_; 
v___x_945_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_945_, 0, lean_box(0));
lean_closure_set(v___x_945_, 1, lean_box(0));
lean_closure_set(v___x_945_, 2, v___f_926_);
lean_closure_set(v___x_945_, 3, lean_box(0));
v___x_946_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_946_, 0, lean_box(0));
lean_closure_set(v___x_946_, 1, lean_box(0));
lean_closure_set(v___x_946_, 2, lean_box(0));
lean_closure_set(v___x_946_, 3, v___x_945_);
lean_closure_set(v___x_946_, 4, v___f_927_);
v___x_947_ = lean_unsigned_to_nat(0u);
v___x_948_ = 0;
lean_inc_ref(v___x_946_);
v___x_949_ = l_BaseIO_chainTask___redArg(v_a_928_, v___x_946_, v___x_947_, v___x_948_);
v___x_950_ = lean_box(v___x_948_);
v___f_951_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__7___boxed), 7, 5);
lean_closure_set(v___f_951_, 0, v_a_941_);
lean_closure_set(v___f_951_, 1, v___x_946_);
lean_closure_set(v___f_951_, 2, v___x_947_);
lean_closure_set(v___f_951_, 3, v___x_950_);
lean_closure_set(v___f_951_, 4, v___f_929_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v___x_949_);
v___x_953_ = v___x_943_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_949_);
v___x_953_ = v_reuseFailAlloc_956_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
v___x_955_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_947_, v___x_948_, v___x_954_, v___f_951_);
return v___x_955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__8___boxed(lean_object* v___f_958_, lean_object* v___f_959_, lean_object* v_a_960_, lean_object* v___f_961_, lean_object* v_x_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Std_Async_ContextAsync_race___redArg___lam__8(v___f_958_, v___f_959_, v_a_960_, v___f_961_, v_x_962_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__9(lean_object* v___f_965_, lean_object* v_prio_966_, lean_object* v___f_967_, lean_object* v___f_968_, lean_object* v___f_969_, lean_object* v___f_970_, lean_object* v_x_971_){
_start:
{
if (lean_obj_tag(v_x_971_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_981_; 
lean_dec_ref(v___f_970_);
lean_dec_ref(v___f_969_);
lean_dec_ref(v___f_968_);
lean_dec(v___f_967_);
lean_dec(v_prio_966_);
lean_dec_ref(v___f_965_);
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
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_998_; 
v_a_982_ = lean_ctor_get(v_x_971_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v_x_971_);
if (v_isSharedCheck_998_ == 0)
{
v___x_984_ = v_x_971_;
v_isShared_985_ = v_isSharedCheck_998_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v_x_971_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_998_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___f_988_; lean_object* v___x_989_; uint8_t v___x_990_; lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_986_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_986_, 0, lean_box(0));
lean_closure_set(v___x_986_, 1, v___f_965_);
v___x_987_ = lean_io_as_task(v___x_986_, v_prio_966_);
v___f_988_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_988_, 0, v___f_967_);
lean_closure_set(v___f_988_, 1, v___f_968_);
lean_closure_set(v___f_988_, 2, v_a_982_);
lean_closure_set(v___f_988_, 3, v___f_969_);
v___x_989_ = lean_unsigned_to_nat(0u);
v___x_990_ = 1;
v___x_991_ = lean_task_bind(v___x_987_, v___f_970_, v___x_989_, v___x_990_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v___x_991_);
v___x_993_ = v___x_984_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_991_);
v___x_993_ = v_reuseFailAlloc_997_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_994_; uint8_t v___x_995_; lean_object* v___x_996_; 
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
v___x_995_ = 0;
v___x_996_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_989_, v___x_995_, v___x_994_, v___f_988_);
return v___x_996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__9___boxed(lean_object* v___f_999_, lean_object* v_prio_1000_, lean_object* v___f_1001_, lean_object* v___f_1002_, lean_object* v___f_1003_, lean_object* v___f_1004_, lean_object* v_x_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Std_Async_ContextAsync_race___redArg___lam__9(v___f_999_, v_prio_1000_, v___f_1001_, v___f_1002_, v___f_1003_, v___f_1004_, v_x_1005_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__10(lean_object* v___f_1008_, lean_object* v_prio_1009_, lean_object* v___f_1010_, lean_object* v___f_1011_, lean_object* v___f_1012_, lean_object* v___f_1013_, lean_object* v___f_1014_, lean_object* v___f_1015_, lean_object* v_x_1016_){
_start:
{
if (lean_obj_tag(v_x_1016_) == 0)
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1026_; 
lean_dec_ref(v___f_1015_);
lean_dec_ref(v___f_1014_);
lean_dec(v___f_1013_);
lean_dec_ref(v___f_1012_);
lean_dec_ref(v___f_1011_);
lean_dec_ref(v___f_1010_);
lean_dec(v_prio_1009_);
lean_dec_ref(v___f_1008_);
v_a_1018_ = lean_ctor_get(v_x_1016_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_x_1016_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1020_ = v_x_1016_;
v_isShared_1021_ = v_isSharedCheck_1026_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v_x_1016_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1026_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1024_; 
v___x_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
return v___x_1024_;
}
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1045_; 
v_a_1027_ = lean_ctor_get(v_x_1016_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_x_1016_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1029_ = v_x_1016_;
v_isShared_1030_ = v_isSharedCheck_1045_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v_x_1016_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1045_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___f_1033_; lean_object* v___f_1034_; lean_object* v___f_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1040_; 
v___x_1031_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1031_, 0, lean_box(0));
lean_closure_set(v___x_1031_, 1, v___f_1008_);
lean_inc(v_prio_1009_);
v___x_1032_ = lean_io_as_task(v___x_1031_, v_prio_1009_);
lean_inc(v_a_1027_);
v___f_1033_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_1033_, 0, v_a_1027_);
lean_closure_set(v___f_1033_, 1, v___f_1010_);
lean_closure_set(v___f_1033_, 2, v___f_1011_);
v___f_1034_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1034_, 0, v_a_1027_);
v___f_1035_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__9___boxed), 8, 6);
lean_closure_set(v___f_1035_, 0, v___f_1012_);
lean_closure_set(v___f_1035_, 1, v_prio_1009_);
lean_closure_set(v___f_1035_, 2, v___f_1013_);
lean_closure_set(v___f_1035_, 3, v___f_1034_);
lean_closure_set(v___f_1035_, 4, v___f_1033_);
lean_closure_set(v___f_1035_, 5, v___f_1014_);
v___x_1036_ = lean_unsigned_to_nat(0u);
v___x_1037_ = 1;
v___x_1038_ = lean_task_bind(v___x_1032_, v___f_1015_, v___x_1036_, v___x_1037_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1038_);
v___x_1040_ = v___x_1029_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1041_; uint8_t v___x_1042_; lean_object* v___x_1043_; 
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
v___x_1042_ = 0;
v___x_1043_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1036_, v___x_1042_, v___x_1041_, v___f_1035_);
return v___x_1043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__10___boxed(lean_object* v___f_1046_, lean_object* v_prio_1047_, lean_object* v___f_1048_, lean_object* v___f_1049_, lean_object* v___f_1050_, lean_object* v___f_1051_, lean_object* v___f_1052_, lean_object* v___f_1053_, lean_object* v_x_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Std_Async_ContextAsync_race___redArg___lam__10(v___f_1046_, v_prio_1047_, v___f_1048_, v___f_1049_, v___f_1050_, v___f_1051_, v___f_1052_, v___f_1053_, v_x_1054_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__11(lean_object* v___f_1058_, lean_object* v___f_1059_, lean_object* v_prio_1060_, lean_object* v___f_1061_, lean_object* v___f_1062_, lean_object* v___f_1063_, lean_object* v___f_1064_, lean_object* v_x_1065_){
_start:
{
if (lean_obj_tag(v_x_1065_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1075_; 
lean_dec_ref(v___f_1064_);
lean_dec_ref(v___f_1063_);
lean_dec_ref(v___f_1062_);
lean_dec_ref(v___f_1061_);
lean_dec(v_prio_1060_);
lean_dec_ref(v___f_1059_);
lean_dec_ref(v___f_1058_);
v_a_1067_ = lean_ctor_get(v_x_1065_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_x_1065_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1069_ = v_x_1065_;
v_isShared_1070_ = v_isSharedCheck_1075_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v_x_1065_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1075_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1073_; 
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
return v___x_1073_;
}
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1091_; 
v_a_1076_ = lean_ctor_get(v_x_1065_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_x_1065_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1078_ = v_x_1065_;
v_isShared_1079_ = v_isSharedCheck_1091_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v_x_1065_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1091_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; lean_object* v___f_1081_; lean_object* v___f_1082_; lean_object* v___f_1083_; lean_object* v___x_1085_; 
v___x_1080_ = lean_io_promise_new();
v___f_1081_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__6___boxed), 3, 2);
lean_closure_set(v___f_1081_, 0, v_a_1076_);
lean_closure_set(v___f_1081_, 1, v___f_1058_);
v___f_1082_ = ((lean_object*)(l_Std_Async_ContextAsync_race___redArg___lam__11___closed__0));
v___f_1083_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__10___boxed), 10, 8);
lean_closure_set(v___f_1083_, 0, v___f_1059_);
lean_closure_set(v___f_1083_, 1, v_prio_1060_);
lean_closure_set(v___f_1083_, 2, v___f_1061_);
lean_closure_set(v___f_1083_, 3, v___f_1062_);
lean_closure_set(v___f_1083_, 4, v___f_1081_);
lean_closure_set(v___f_1083_, 5, v___f_1082_);
lean_closure_set(v___f_1083_, 6, v___f_1063_);
lean_closure_set(v___f_1083_, 7, v___f_1064_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v___x_1080_);
v___x_1085_ = v___x_1078_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1080_);
v___x_1085_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; lean_object* v___x_1089_; 
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
v___x_1087_ = lean_unsigned_to_nat(0u);
v___x_1088_ = 0;
v___x_1089_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1087_, v___x_1088_, v___x_1086_, v___f_1083_);
return v___x_1089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__11___boxed(lean_object* v___f_1092_, lean_object* v___f_1093_, lean_object* v_prio_1094_, lean_object* v___f_1095_, lean_object* v___f_1096_, lean_object* v___f_1097_, lean_object* v___f_1098_, lean_object* v_x_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Std_Async_ContextAsync_race___redArg___lam__11(v___f_1092_, v___f_1093_, v_prio_1094_, v___f_1095_, v___f_1096_, v___f_1097_, v___f_1098_, v_x_1099_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__12(lean_object* v___f_1102_, lean_object* v_prio_1103_, lean_object* v___f_1104_, lean_object* v___f_1105_, lean_object* v___f_1106_, lean_object* v___f_1107_, lean_object* v___f_1108_, lean_object* v___f_1109_, lean_object* v___f_1110_, lean_object* v_x_1111_){
_start:
{
if (lean_obj_tag(v_x_1111_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1121_; 
lean_dec_ref(v___f_1110_);
lean_dec_ref(v___f_1109_);
lean_dec_ref(v___f_1108_);
lean_dec_ref(v___f_1107_);
lean_dec_ref(v___f_1106_);
lean_dec_ref(v___f_1105_);
lean_dec_ref(v___f_1104_);
lean_dec(v_prio_1103_);
lean_dec_ref(v___f_1102_);
v_a_1113_ = lean_ctor_get(v_x_1111_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_x_1111_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1115_ = v_x_1111_;
v_isShared_1116_ = v_isSharedCheck_1121_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v_x_1111_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1121_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
return v___x_1119_;
}
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1139_; 
v_a_1122_ = lean_ctor_get(v_x_1111_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_x_1111_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1124_ = v_x_1111_;
v_isShared_1125_ = v_isSharedCheck_1139_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v_x_1111_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1139_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___f_1128_; lean_object* v___f_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1126_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1126_, 0, lean_box(0));
lean_closure_set(v___x_1126_, 1, v___f_1102_);
lean_inc(v_prio_1103_);
v___x_1127_ = lean_io_as_task(v___x_1126_, v_prio_1103_);
v___f_1128_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__6___boxed), 3, 2);
lean_closure_set(v___f_1128_, 0, v_a_1122_);
lean_closure_set(v___f_1128_, 1, v___f_1104_);
v___f_1129_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__11___boxed), 9, 7);
lean_closure_set(v___f_1129_, 0, v___f_1105_);
lean_closure_set(v___f_1129_, 1, v___f_1128_);
lean_closure_set(v___f_1129_, 2, v_prio_1103_);
lean_closure_set(v___f_1129_, 3, v___f_1106_);
lean_closure_set(v___f_1129_, 4, v___f_1107_);
lean_closure_set(v___f_1129_, 5, v___f_1108_);
lean_closure_set(v___f_1129_, 6, v___f_1109_);
v___x_1130_ = lean_unsigned_to_nat(0u);
v___x_1131_ = 1;
v___x_1132_ = lean_task_bind(v___x_1127_, v___f_1110_, v___x_1130_, v___x_1131_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v___x_1132_);
v___x_1134_ = v___x_1124_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1135_; uint8_t v___x_1136_; lean_object* v___x_1137_; 
v___x_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
v___x_1136_ = 0;
v___x_1137_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1130_, v___x_1136_, v___x_1135_, v___f_1129_);
return v___x_1137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__12___boxed(lean_object* v___f_1140_, lean_object* v_prio_1141_, lean_object* v___f_1142_, lean_object* v___f_1143_, lean_object* v___f_1144_, lean_object* v___f_1145_, lean_object* v___f_1146_, lean_object* v___f_1147_, lean_object* v___f_1148_, lean_object* v_x_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Std_Async_ContextAsync_race___redArg___lam__12(v___f_1140_, v_prio_1141_, v___f_1142_, v___f_1143_, v___f_1144_, v___f_1145_, v___f_1146_, v___f_1147_, v___f_1148_, v_x_1149_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__13(lean_object* v___f_1152_, lean_object* v_prio_1153_, lean_object* v_y_1154_, lean_object* v___f_1155_, lean_object* v___f_1156_, lean_object* v___f_1157_, lean_object* v___f_1158_, lean_object* v___f_1159_, lean_object* v___f_1160_, lean_object* v___f_1161_, lean_object* v_x_1162_){
_start:
{
if (lean_obj_tag(v_x_1162_) == 0)
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1172_; 
lean_dec_ref(v___f_1161_);
lean_dec_ref(v___f_1160_);
lean_dec_ref(v___f_1159_);
lean_dec_ref(v___f_1158_);
lean_dec_ref(v___f_1157_);
lean_dec_ref(v___f_1156_);
lean_dec_ref(v___f_1155_);
lean_dec_ref(v_y_1154_);
lean_dec(v_prio_1153_);
lean_dec_ref(v___f_1152_);
v_a_1164_ = lean_ctor_get(v_x_1162_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_x_1162_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1166_ = v_x_1162_;
v_isShared_1167_ = v_isSharedCheck_1172_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v_x_1162_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1172_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
return v___x_1170_;
}
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1191_; 
v_a_1173_ = lean_ctor_get(v_x_1162_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_x_1162_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1175_ = v_x_1162_;
v_isShared_1176_ = v_isSharedCheck_1191_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v_x_1162_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1191_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___f_1179_; lean_object* v___f_1180_; lean_object* v___f_1181_; lean_object* v___x_1182_; uint8_t v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1177_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1177_, 0, lean_box(0));
lean_closure_set(v___x_1177_, 1, v___f_1152_);
lean_inc(v_prio_1153_);
v___x_1178_ = lean_io_as_task(v___x_1177_, v_prio_1153_);
lean_inc(v_a_1173_);
v___f_1179_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__5___boxed), 3, 2);
lean_closure_set(v___f_1179_, 0, v_y_1154_);
lean_closure_set(v___f_1179_, 1, v_a_1173_);
v___f_1180_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_run___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1180_, 0, v_a_1173_);
v___f_1181_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__12___boxed), 11, 9);
lean_closure_set(v___f_1181_, 0, v___f_1179_);
lean_closure_set(v___f_1181_, 1, v_prio_1153_);
lean_closure_set(v___f_1181_, 2, v___f_1180_);
lean_closure_set(v___f_1181_, 3, v___f_1155_);
lean_closure_set(v___f_1181_, 4, v___f_1156_);
lean_closure_set(v___f_1181_, 5, v___f_1157_);
lean_closure_set(v___f_1181_, 6, v___f_1158_);
lean_closure_set(v___f_1181_, 7, v___f_1159_);
lean_closure_set(v___f_1181_, 8, v___f_1160_);
v___x_1182_ = lean_unsigned_to_nat(0u);
v___x_1183_ = 1;
v___x_1184_ = lean_task_bind(v___x_1178_, v___f_1161_, v___x_1182_, v___x_1183_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 0, v___x_1184_);
v___x_1186_ = v___x_1175_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
lean_object* v___x_1187_; uint8_t v___x_1188_; lean_object* v___x_1189_; 
v___x_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
v___x_1188_ = 0;
v___x_1189_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1182_, v___x_1188_, v___x_1187_, v___f_1181_);
return v___x_1189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__13___boxed(lean_object* v___f_1192_, lean_object* v_prio_1193_, lean_object* v_y_1194_, lean_object* v___f_1195_, lean_object* v___f_1196_, lean_object* v___f_1197_, lean_object* v___f_1198_, lean_object* v___f_1199_, lean_object* v___f_1200_, lean_object* v___f_1201_, lean_object* v_x_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Std_Async_ContextAsync_race___redArg___lam__13(v___f_1192_, v_prio_1193_, v_y_1194_, v___f_1195_, v___f_1196_, v___f_1197_, v___f_1198_, v___f_1199_, v___f_1200_, v___f_1201_, v_x_1202_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__14(lean_object* v_a_1205_, lean_object* v_x_1206_, lean_object* v_prio_1207_, lean_object* v_y_1208_, lean_object* v___f_1209_, lean_object* v___f_1210_, lean_object* v___f_1211_, lean_object* v___f_1212_, lean_object* v___f_1213_, lean_object* v___f_1214_, lean_object* v_x_1215_){
_start:
{
if (lean_obj_tag(v_x_1215_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1225_; 
lean_dec_ref(v___f_1214_);
lean_dec_ref(v___f_1213_);
lean_dec_ref(v___f_1212_);
lean_dec_ref(v___f_1211_);
lean_dec_ref(v___f_1210_);
lean_dec_ref(v___f_1209_);
lean_dec_ref(v_y_1208_);
lean_dec(v_prio_1207_);
lean_dec_ref(v_x_1206_);
lean_dec_ref(v_a_1205_);
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
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1241_; 
v_a_1226_ = lean_ctor_get(v_x_1215_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_x_1215_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1228_ = v_x_1215_;
v_isShared_1229_ = v_isSharedCheck_1241_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v_x_1215_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1241_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1230_; lean_object* v___f_1231_; lean_object* v___f_1232_; lean_object* v___f_1233_; lean_object* v___x_1235_; 
v___x_1230_ = l_Std_CancellationContext_fork(v_a_1205_);
lean_inc(v_a_1226_);
v___f_1231_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_1231_, 0, v_x_1206_);
lean_closure_set(v___f_1231_, 1, v_a_1226_);
v___f_1232_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_run___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1232_, 0, v_a_1226_);
v___f_1233_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__13___boxed), 12, 10);
lean_closure_set(v___f_1233_, 0, v___f_1231_);
lean_closure_set(v___f_1233_, 1, v_prio_1207_);
lean_closure_set(v___f_1233_, 2, v_y_1208_);
lean_closure_set(v___f_1233_, 3, v___f_1232_);
lean_closure_set(v___f_1233_, 4, v___f_1209_);
lean_closure_set(v___f_1233_, 5, v___f_1210_);
lean_closure_set(v___f_1233_, 6, v___f_1211_);
lean_closure_set(v___f_1233_, 7, v___f_1212_);
lean_closure_set(v___f_1233_, 8, v___f_1213_);
lean_closure_set(v___f_1233_, 9, v___f_1214_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v___x_1230_);
v___x_1235_ = v___x_1228_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1230_);
v___x_1235_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; lean_object* v___x_1239_; 
v___x_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
v___x_1237_ = lean_unsigned_to_nat(0u);
v___x_1238_ = 0;
v___x_1239_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1237_, v___x_1238_, v___x_1236_, v___f_1233_);
return v___x_1239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__14___boxed(lean_object* v_a_1242_, lean_object* v_x_1243_, lean_object* v_prio_1244_, lean_object* v_y_1245_, lean_object* v___f_1246_, lean_object* v___f_1247_, lean_object* v___f_1248_, lean_object* v___f_1249_, lean_object* v___f_1250_, lean_object* v___f_1251_, lean_object* v_x_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Std_Async_ContextAsync_race___redArg___lam__14(v_a_1242_, v_x_1243_, v_prio_1244_, v_y_1245_, v___f_1246_, v___f_1247_, v___f_1248_, v___f_1249_, v___f_1250_, v___f_1251_, v_x_1252_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__15(lean_object* v_x_1255_, lean_object* v_prio_1256_, lean_object* v_y_1257_, lean_object* v___f_1258_, lean_object* v___f_1259_, lean_object* v___f_1260_, lean_object* v___f_1261_, lean_object* v___f_1262_, lean_object* v___f_1263_, lean_object* v_x_1264_){
_start:
{
if (lean_obj_tag(v_x_1264_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1274_; 
lean_dec_ref(v___f_1263_);
lean_dec_ref(v___f_1262_);
lean_dec_ref(v___f_1261_);
lean_dec_ref(v___f_1260_);
lean_dec_ref(v___f_1259_);
lean_dec_ref(v___f_1258_);
lean_dec_ref(v_y_1257_);
lean_dec(v_prio_1256_);
lean_dec_ref(v_x_1255_);
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
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1288_; 
v_a_1275_ = lean_ctor_get(v_x_1264_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_x_1264_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1277_ = v_x_1264_;
v_isShared_1278_ = v_isSharedCheck_1288_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v_x_1264_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1288_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1279_; lean_object* v___f_1280_; lean_object* v___x_1282_; 
lean_inc(v_a_1275_);
v___x_1279_ = l_Std_CancellationContext_fork(v_a_1275_);
v___f_1280_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__14___boxed), 12, 10);
lean_closure_set(v___f_1280_, 0, v_a_1275_);
lean_closure_set(v___f_1280_, 1, v_x_1255_);
lean_closure_set(v___f_1280_, 2, v_prio_1256_);
lean_closure_set(v___f_1280_, 3, v_y_1257_);
lean_closure_set(v___f_1280_, 4, v___f_1258_);
lean_closure_set(v___f_1280_, 5, v___f_1259_);
lean_closure_set(v___f_1280_, 6, v___f_1260_);
lean_closure_set(v___f_1280_, 7, v___f_1261_);
lean_closure_set(v___f_1280_, 8, v___f_1262_);
lean_closure_set(v___f_1280_, 9, v___f_1263_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v___x_1279_);
v___x_1282_ = v___x_1277_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1279_);
v___x_1282_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; lean_object* v___x_1286_; 
v___x_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
v___x_1284_ = lean_unsigned_to_nat(0u);
v___x_1285_ = 0;
v___x_1286_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1284_, v___x_1285_, v___x_1283_, v___f_1280_);
return v___x_1286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___lam__15___boxed(lean_object* v_x_1289_, lean_object* v_prio_1290_, lean_object* v_y_1291_, lean_object* v___f_1292_, lean_object* v___f_1293_, lean_object* v___f_1294_, lean_object* v___f_1295_, lean_object* v___f_1296_, lean_object* v___f_1297_, lean_object* v_x_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Std_Async_ContextAsync_race___redArg___lam__15(v_x_1289_, v_prio_1290_, v_y_1291_, v___f_1292_, v___f_1293_, v___f_1294_, v___f_1295_, v___f_1296_, v___f_1297_, v_x_1298_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg(lean_object* v_x_1303_, lean_object* v_y_1304_, lean_object* v_prio_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v___f_1308_; lean_object* v___f_1309_; lean_object* v___f_1310_; lean_object* v___f_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; lean_object* v___x_1316_; 
v___f_1308_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_1309_ = ((lean_object*)(l_Std_Async_ContextAsync_race___redArg___closed__0));
v___f_1310_ = ((lean_object*)(l_Std_Async_ContextAsync_race___redArg___closed__1));
v___f_1311_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__15___boxed), 11, 9);
lean_closure_set(v___f_1311_, 0, v_x_1303_);
lean_closure_set(v___f_1311_, 1, v_prio_1305_);
lean_closure_set(v___f_1311_, 2, v_y_1304_);
lean_closure_set(v___f_1311_, 3, v___f_1310_);
lean_closure_set(v___f_1311_, 4, v___f_1309_);
lean_closure_set(v___f_1311_, 5, v___f_1308_);
lean_closure_set(v___f_1311_, 6, v___f_1308_);
lean_closure_set(v___f_1311_, 7, v___f_1308_);
lean_closure_set(v___f_1311_, 8, v___f_1308_);
lean_inc_ref(v_a_1306_);
v___x_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1312_, 0, v_a_1306_);
v___x_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
v___x_1314_ = lean_unsigned_to_nat(0u);
v___x_1315_ = 0;
v___x_1316_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1314_, v___x_1315_, v___x_1313_, v___f_1311_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___redArg___boxed(lean_object* v_x_1317_, lean_object* v_y_1318_, lean_object* v_prio_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Std_Async_ContextAsync_race___redArg(v_x_1317_, v_y_1318_, v_prio_1319_, v_a_1320_);
lean_dec_ref(v_a_1320_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race(lean_object* v_00_u03b1_1323_, lean_object* v_inst_1324_, lean_object* v_x_1325_, lean_object* v_y_1326_, lean_object* v_prio_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v___f_1330_; lean_object* v___f_1331_; lean_object* v___f_1332_; lean_object* v___f_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; lean_object* v___x_1338_; 
v___f_1330_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_1331_ = ((lean_object*)(l_Std_Async_ContextAsync_race___redArg___closed__0));
v___f_1332_ = ((lean_object*)(l_Std_Async_ContextAsync_race___redArg___closed__1));
v___f_1333_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__15___boxed), 11, 9);
lean_closure_set(v___f_1333_, 0, v_x_1325_);
lean_closure_set(v___f_1333_, 1, v_prio_1327_);
lean_closure_set(v___f_1333_, 2, v_y_1326_);
lean_closure_set(v___f_1333_, 3, v___f_1332_);
lean_closure_set(v___f_1333_, 4, v___f_1331_);
lean_closure_set(v___f_1333_, 5, v___f_1330_);
lean_closure_set(v___f_1333_, 6, v___f_1330_);
lean_closure_set(v___f_1333_, 7, v___f_1330_);
lean_closure_set(v___f_1333_, 8, v___f_1330_);
lean_inc_ref(v_a_1328_);
v___x_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1334_, 0, v_a_1328_);
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
v___x_1336_ = lean_unsigned_to_nat(0u);
v___x_1337_ = 0;
v___x_1338_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1336_, v___x_1337_, v___x_1335_, v___f_1333_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_race___boxed(lean_object* v_00_u03b1_1339_, lean_object* v_inst_1340_, lean_object* v_x_1341_, lean_object* v_y_1342_, lean_object* v_prio_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Std_Async_ContextAsync_race(v_00_u03b1_1339_, v_inst_1340_, v_x_1341_, v_y_1342_, v_prio_1343_, v_a_1344_);
lean_dec_ref(v_a_1344_);
lean_dec(v_inst_1340_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__0(lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1350_, 0, v___y_1347_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__0___boxed(lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__0(v___y_1351_, v___y_1352_);
lean_dec_ref(v___y_1352_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3(lean_object* v___x_1355_, lean_object* v___f_1356_, lean_object* v_a_1357_, lean_object* v_x_1358_){
_start:
{
if (lean_obj_tag(v_x_1358_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1368_; 
lean_dec_ref(v___f_1356_);
lean_dec_ref(v___x_1355_);
v_a_1360_ = lean_ctor_get(v_x_1358_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v_x_1358_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1362_ = v_x_1358_;
v_isShared_1363_ = v_isSharedCheck_1368_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v_x_1358_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1368_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1366_; 
v___x_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
return v___x_1366_;
}
}
}
else
{
lean_object* v_a_1369_; size_t v_sz_1370_; size_t v___x_1371_; lean_object* v___x_4336__overap_1372_; lean_object* v___x_1373_; 
v_a_1369_ = lean_ctor_get(v_x_1358_, 0);
lean_inc(v_a_1369_);
lean_dec_ref(v_x_1358_);
v_sz_1370_ = lean_array_size(v_a_1369_);
v___x_1371_ = ((size_t)0ULL);
v___x_4336__overap_1372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1355_, v___f_1356_, v_sz_1370_, v___x_1371_, v_a_1369_);
lean_inc_ref(v_a_1357_);
v___x_1373_ = lean_apply_2(v___x_4336__overap_1372_, v_a_1357_, lean_box(0));
return v___x_1373_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3___boxed(lean_object* v___x_1374_, lean_object* v___f_1375_, lean_object* v_a_1376_, lean_object* v_x_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3(v___x_1374_, v___f_1375_, v_a_1376_, v_x_1377_);
lean_dec_ref(v_a_1376_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4(lean_object* v_ctxAsync_1380_, lean_object* v_a_1381_, lean_object* v___f_1382_){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; lean_object* v___x_1387_; 
v___x_1384_ = lean_apply_2(v_ctxAsync_1380_, v_a_1381_, lean_box(0));
v___x_1385_ = lean_unsigned_to_nat(0u);
v___x_1386_ = 0;
v___x_1387_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1385_, v___x_1386_, v___x_1384_, v___f_1382_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4___boxed(lean_object* v_ctxAsync_1388_, lean_object* v_a_1389_, lean_object* v___f_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4(v_ctxAsync_1388_, v_a_1389_, v___f_1390_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1(lean_object* v_a_1393_, lean_object* v___x_1394_, lean_object* v_a_x3f_1395_){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1397_ = l_Std_CancellationContext_cancel(v_a_1393_, v___x_1394_);
v___x_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
v___x_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1___boxed(lean_object* v_a_1400_, lean_object* v___x_1401_, lean_object* v_a_x3f_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1(v_a_1400_, v___x_1401_, v_a_x3f_1402_);
lean_dec(v_a_x3f_1402_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5(lean_object* v_ctxAsync_1405_, lean_object* v___f_1406_, lean_object* v___f_1407_, lean_object* v_prio_1408_, lean_object* v___f_1409_, lean_object* v_x_1410_){
_start:
{
if (lean_obj_tag(v_x_1410_) == 0)
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1420_; 
lean_dec_ref(v___f_1409_);
lean_dec(v_prio_1408_);
lean_dec(v___f_1407_);
lean_dec_ref(v___f_1406_);
lean_dec_ref(v_ctxAsync_1405_);
v_a_1412_ = lean_ctor_get(v_x_1410_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v_x_1410_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1414_ = v_x_1410_;
v_isShared_1415_ = v_isSharedCheck_1420_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v_x_1410_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1420_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1418_; 
v___x_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
return v___x_1418_;
}
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1438_; 
v_a_1421_ = lean_ctor_get(v_x_1410_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_x_1410_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1423_ = v_x_1410_;
v_isShared_1424_ = v_isSharedCheck_1438_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v_x_1410_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1438_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___f_1425_; lean_object* v___x_1426_; lean_object* v___f_1427_; lean_object* v___f_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; uint8_t v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1435_; 
lean_inc(v_a_1421_);
v___f_1425_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_1425_, 0, v_ctxAsync_1405_);
lean_closure_set(v___f_1425_, 1, v_a_1421_);
lean_closure_set(v___f_1425_, 2, v___f_1406_);
v___x_1426_ = lean_box(2);
v___f_1427_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1427_, 0, v_a_1421_);
lean_closure_set(v___f_1427_, 1, v___x_1426_);
v___f_1428_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_1428_, 0, v___f_1425_);
lean_closure_set(v___f_1428_, 1, v___f_1427_);
lean_closure_set(v___f_1428_, 2, v___f_1407_);
v___x_1429_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1429_, 0, lean_box(0));
lean_closure_set(v___x_1429_, 1, v___f_1428_);
v___x_1430_ = lean_io_as_task(v___x_1429_, v_prio_1408_);
v___x_1431_ = lean_unsigned_to_nat(0u);
v___x_1432_ = 1;
v___x_1433_ = lean_task_bind(v___x_1430_, v___f_1409_, v___x_1431_, v___x_1432_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v___x_1433_);
v___x_1435_ = v___x_1423_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1433_);
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
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5___boxed(lean_object* v_ctxAsync_1439_, lean_object* v___f_1440_, lean_object* v___f_1441_, lean_object* v_prio_1442_, lean_object* v___f_1443_, lean_object* v_x_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5(v_ctxAsync_1439_, v___f_1440_, v___f_1441_, v_prio_1442_, v___f_1443_, v_x_1444_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2(lean_object* v_a_1447_, lean_object* v___f_1448_, lean_object* v___f_1449_, lean_object* v_prio_1450_, lean_object* v___f_1451_, lean_object* v_ctxAsync_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v___x_1455_; lean_object* v___f_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; lean_object* v___x_1461_; 
v___x_1455_ = l_Std_CancellationContext_fork(v_a_1447_);
v___f_1456_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5___boxed), 7, 5);
lean_closure_set(v___f_1456_, 0, v_ctxAsync_1452_);
lean_closure_set(v___f_1456_, 1, v___f_1448_);
lean_closure_set(v___f_1456_, 2, v___f_1449_);
lean_closure_set(v___f_1456_, 3, v_prio_1450_);
lean_closure_set(v___f_1456_, 4, v___f_1451_);
v___x_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1455_);
v___x_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1457_);
v___x_1459_ = lean_unsigned_to_nat(0u);
v___x_1460_ = 0;
v___x_1461_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1459_, v___x_1460_, v___x_1458_, v___f_1456_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2___boxed(lean_object* v_a_1462_, lean_object* v___f_1463_, lean_object* v___f_1464_, lean_object* v_prio_1465_, lean_object* v___f_1466_, lean_object* v_ctxAsync_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2(v_a_1462_, v___f_1463_, v___f_1464_, v_prio_1465_, v___f_1466_, v_ctxAsync_1467_, v___y_1468_);
lean_dec_ref(v___y_1468_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6(lean_object* v___f_1471_, lean_object* v_prio_1472_, lean_object* v___f_1473_, lean_object* v_xs_1474_, lean_object* v___x_1475_, lean_object* v_a_1476_, lean_object* v___f_1477_, lean_object* v_x_1478_){
_start:
{
if (lean_obj_tag(v_x_1478_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1488_; 
lean_dec_ref(v___f_1477_);
lean_dec_ref(v___x_1475_);
lean_dec_ref(v_xs_1474_);
lean_dec_ref(v___f_1473_);
lean_dec(v_prio_1472_);
lean_dec(v___f_1471_);
v_a_1480_ = lean_ctor_get(v_x_1478_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_x_1478_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1482_ = v_x_1478_;
v_isShared_1483_ = v_isSharedCheck_1488_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v_x_1478_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1488_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
return v___x_1486_;
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v___f_1490_; lean_object* v___f_1491_; size_t v_sz_1492_; size_t v___x_1493_; lean_object* v___x_4458__overap_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; uint8_t v___x_1497_; lean_object* v___x_1498_; 
v_a_1489_ = lean_ctor_get(v_x_1478_, 0);
lean_inc_n(v_a_1489_, 2);
lean_dec_ref(v_x_1478_);
v___f_1490_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1490_, 0, v_a_1489_);
v___f_1491_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_1491_, 0, v_a_1489_);
lean_closure_set(v___f_1491_, 1, v___f_1490_);
lean_closure_set(v___f_1491_, 2, v___f_1471_);
lean_closure_set(v___f_1491_, 3, v_prio_1472_);
lean_closure_set(v___f_1491_, 4, v___f_1473_);
v_sz_1492_ = lean_array_size(v_xs_1474_);
v___x_1493_ = ((size_t)0ULL);
v___x_4458__overap_1494_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1475_, v___f_1491_, v_sz_1492_, v___x_1493_, v_xs_1474_);
lean_inc_ref(v_a_1476_);
v___x_1495_ = lean_apply_2(v___x_4458__overap_1494_, v_a_1476_, lean_box(0));
v___x_1496_ = lean_unsigned_to_nat(0u);
v___x_1497_ = 0;
v___x_1498_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1496_, v___x_1497_, v___x_1495_, v___f_1477_);
return v___x_1498_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6___boxed(lean_object* v___f_1499_, lean_object* v_prio_1500_, lean_object* v___f_1501_, lean_object* v_xs_1502_, lean_object* v___x_1503_, lean_object* v_a_1504_, lean_object* v___f_1505_, lean_object* v_x_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6(v___f_1499_, v_prio_1500_, v___f_1501_, v_xs_1502_, v___x_1503_, v_a_1504_, v___f_1505_, v_x_1506_);
lean_dec_ref(v_a_1504_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7(lean_object* v___f_1509_, lean_object* v_x_1510_){
_start:
{
if (lean_obj_tag(v_x_1510_) == 0)
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1520_; 
lean_dec_ref(v___f_1509_);
v_a_1512_ = lean_ctor_get(v_x_1510_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v_x_1510_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1514_ = v_x_1510_;
v_isShared_1515_ = v_isSharedCheck_1520_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v_x_1510_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1520_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1512_);
v___x_1517_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1517_);
return v___x_1518_;
}
}
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1533_; 
v_a_1521_ = lean_ctor_get(v_x_1510_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v_x_1510_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1523_ = v_x_1510_;
v_isShared_1524_ = v_isSharedCheck_1533_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v_x_1510_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1533_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1525_; lean_object* v___x_1527_; 
v___x_1525_ = l_Std_CancellationContext_fork(v_a_1521_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v___x_1525_);
v___x_1527_ = v___x_1523_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1525_);
v___x_1527_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; lean_object* v___x_1531_; 
v___x_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
v___x_1529_ = lean_unsigned_to_nat(0u);
v___x_1530_ = 0;
v___x_1531_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1529_, v___x_1530_, v___x_1528_, v___f_1509_);
return v___x_1531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7___boxed(lean_object* v___f_1534_, lean_object* v_x_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7(v___f_1534_, v_x_1535_);
return v_res_1537_;
}
}
static lean_object* _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1(void){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = l_Std_Async_EAsync_instMonad(lean_box(0));
return v___x_1539_;
}
}
static lean_object* _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = lean_obj_once(&l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1, &l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1_once, _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1);
v___x_1541_ = l_ReaderT_instMonad___redArg(v___x_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg(lean_object* v_xs_1542_, lean_object* v_prio_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v___f_1546_; lean_object* v___f_1547_; lean_object* v___f_1548_; lean_object* v___x_1549_; lean_object* v___f_1550_; lean_object* v___f_1551_; lean_object* v___f_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; lean_object* v___x_1557_; 
v___f_1546_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__0));
v___f_1547_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_1548_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__1));
v___x_1549_ = lean_obj_once(&l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2, &l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2_once, _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2);
lean_inc_ref_n(v_a_1544_, 3);
v___f_1550_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_1550_, 0, v___x_1549_);
lean_closure_set(v___f_1550_, 1, v___f_1546_);
lean_closure_set(v___f_1550_, 2, v_a_1544_);
v___f_1551_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6___boxed), 9, 7);
lean_closure_set(v___f_1551_, 0, v___f_1548_);
lean_closure_set(v___f_1551_, 1, v_prio_1543_);
lean_closure_set(v___f_1551_, 2, v___f_1547_);
lean_closure_set(v___f_1551_, 3, v_xs_1542_);
lean_closure_set(v___f_1551_, 4, v___x_1549_);
lean_closure_set(v___f_1551_, 5, v_a_1544_);
lean_closure_set(v___f_1551_, 6, v___f_1550_);
v___f_1552_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_1552_, 0, v___f_1551_);
v___x_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1553_, 0, v_a_1544_);
v___x_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
v___x_1555_ = lean_unsigned_to_nat(0u);
v___x_1556_ = 0;
v___x_1557_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1555_, v___x_1556_, v___x_1554_, v___f_1552_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___redArg___boxed(lean_object* v_xs_1558_, lean_object* v_prio_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg(v_xs_1558_, v_prio_1559_, v_a_1560_);
lean_dec_ref(v_a_1560_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll(lean_object* v_00_u03b1_1563_, lean_object* v_xs_1564_, lean_object* v_prio_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v___f_1568_; lean_object* v___f_1569_; lean_object* v___f_1570_; lean_object* v___x_1571_; lean_object* v___f_1572_; lean_object* v___f_1573_; lean_object* v___f_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; uint8_t v___x_1578_; lean_object* v___x_1579_; 
v___f_1568_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__0));
v___f_1569_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_1570_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__1));
v___x_1571_ = lean_obj_once(&l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2, &l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2_once, _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2);
lean_inc_ref_n(v_a_1566_, 3);
v___f_1572_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_1572_, 0, v___x_1571_);
lean_closure_set(v___f_1572_, 1, v___f_1568_);
lean_closure_set(v___f_1572_, 2, v_a_1566_);
v___f_1573_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6___boxed), 9, 7);
lean_closure_set(v___f_1573_, 0, v___f_1570_);
lean_closure_set(v___f_1573_, 1, v_prio_1565_);
lean_closure_set(v___f_1573_, 2, v___f_1569_);
lean_closure_set(v___f_1573_, 3, v_xs_1564_);
lean_closure_set(v___f_1573_, 4, v___x_1571_);
lean_closure_set(v___f_1573_, 5, v_a_1566_);
lean_closure_set(v___f_1573_, 6, v___f_1572_);
v___f_1574_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_1574_, 0, v___f_1573_);
v___x_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1575_, 0, v_a_1566_);
v___x_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
v___x_1577_ = lean_unsigned_to_nat(0u);
v___x_1578_ = 0;
v___x_1579_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1577_, v___x_1578_, v___x_1576_, v___f_1574_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_concurrentlyAll___boxed(lean_object* v_00_u03b1_1580_, lean_object* v_xs_1581_, lean_object* v_prio_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Std_Async_ContextAsync_concurrentlyAll(v_00_u03b1_1580_, v_xs_1581_, v_prio_1582_, v_a_1583_);
lean_dec_ref(v_a_1583_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__0(lean_object* v_a_1586_, lean_object* v_x_1587_){
_start:
{
if (lean_obj_tag(v_x_1587_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1597_; 
lean_dec_ref(v_a_1586_);
v_a_1589_ = lean_ctor_get(v_x_1587_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_x_1587_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1591_ = v_x_1587_;
v_isShared_1592_ = v_isSharedCheck_1597_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v_x_1587_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1597_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
lean_object* v___x_1595_; 
v___x_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
return v___x_1595_;
}
}
}
else
{
lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1607_; 
v_isSharedCheck_1607_ = !lean_is_exclusive(v_x_1587_);
if (v_isSharedCheck_1607_ == 0)
{
lean_object* v_unused_1608_; 
v_unused_1608_ = lean_ctor_get(v_x_1587_, 0);
lean_dec(v_unused_1608_);
v___x_1599_ = v_x_1587_;
v_isShared_1600_ = v_isSharedCheck_1607_;
goto v_resetjp_1598_;
}
else
{
lean_dec(v_x_1587_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1607_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1604_; 
v___x_1601_ = lean_box(2);
v___x_1602_ = l_Std_CancellationContext_cancel(v_a_1586_, v___x_1601_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v___x_1602_);
v___x_1604_ = v___x_1599_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1602_);
v___x_1604_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1605_; 
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
return v___x_1605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__0___boxed(lean_object* v_a_1609_, lean_object* v_x_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Std_Async_ContextAsync_background___redArg___lam__0(v_a_1609_, v_x_1610_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__1(lean_object* v_action_1613_, lean_object* v_a_1614_, lean_object* v___f_1615_){
_start:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; uint8_t v___x_1619_; lean_object* v___x_1620_; 
v___x_1617_ = lean_apply_2(v_action_1613_, v_a_1614_, lean_box(0));
v___x_1618_ = lean_unsigned_to_nat(0u);
v___x_1619_ = 0;
v___x_1620_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1618_, v___x_1619_, v___x_1617_, v___f_1615_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__1___boxed(lean_object* v_action_1621_, lean_object* v_a_1622_, lean_object* v___f_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Std_Async_ContextAsync_background___redArg___lam__1(v_action_1621_, v_a_1622_, v___f_1623_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__2(lean_object* v_action_1630_, lean_object* v_prio_1631_, lean_object* v_x_1632_){
_start:
{
if (lean_obj_tag(v_x_1632_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1642_; 
lean_dec(v_prio_1631_);
lean_dec_ref(v_action_1630_);
v_a_1634_ = lean_ctor_get(v_x_1632_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_x_1632_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1636_ = v_x_1632_;
v_isShared_1637_ = v_isSharedCheck_1642_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v_x_1632_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1642_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
lean_object* v___x_1640_; 
v___x_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
return v___x_1640_;
}
}
}
else
{
lean_object* v_a_1643_; lean_object* v___f_1644_; lean_object* v___f_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v_a_1643_ = lean_ctor_get(v_x_1632_, 0);
lean_inc_n(v_a_1643_, 2);
lean_dec_ref(v_x_1632_);
v___f_1644_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_background___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1644_, 0, v_a_1643_);
v___f_1645_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_background___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1645_, 0, v_action_1630_);
lean_closure_set(v___f_1645_, 1, v_a_1643_);
lean_closure_set(v___f_1645_, 2, v___f_1644_);
v___x_1646_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1646_, 0, lean_box(0));
lean_closure_set(v___x_1646_, 1, v___f_1645_);
v___x_1647_ = lean_io_as_task(v___x_1646_, v_prio_1631_);
lean_dec_ref(v___x_1647_);
v___x_1648_ = ((lean_object*)(l_Std_Async_ContextAsync_background___redArg___lam__2___closed__1));
return v___x_1648_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__2___boxed(lean_object* v_action_1649_, lean_object* v_prio_1650_, lean_object* v_x_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Std_Async_ContextAsync_background___redArg___lam__2(v_action_1649_, v_prio_1650_, v_x_1651_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__3(lean_object* v___f_1654_, lean_object* v_x_1655_){
_start:
{
if (lean_obj_tag(v_x_1655_) == 0)
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1665_; 
lean_dec_ref(v___f_1654_);
v_a_1657_ = lean_ctor_get(v_x_1655_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_x_1655_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1659_ = v_x_1655_;
v_isShared_1660_ = v_isSharedCheck_1665_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v_x_1655_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1665_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1663_; 
v___x_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
return v___x_1663_;
}
}
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1678_; 
v_a_1666_ = lean_ctor_get(v_x_1655_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v_x_1655_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1668_ = v_x_1655_;
v_isShared_1669_ = v_isSharedCheck_1678_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v_x_1655_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1678_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1670_; lean_object* v___x_1672_; 
v___x_1670_ = l_Std_CancellationContext_fork(v_a_1666_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 0, v___x_1670_);
v___x_1672_ = v___x_1668_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; lean_object* v___x_1676_; 
v___x_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
v___x_1674_ = lean_unsigned_to_nat(0u);
v___x_1675_ = 0;
v___x_1676_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1674_, v___x_1675_, v___x_1673_, v___f_1654_);
return v___x_1676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___lam__3___boxed(lean_object* v___f_1679_, lean_object* v_x_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Std_Async_ContextAsync_background___redArg___lam__3(v___f_1679_, v_x_1680_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg(lean_object* v_action_1683_, lean_object* v_prio_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v___f_1687_; lean_object* v___f_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; lean_object* v___x_1693_; 
v___f_1687_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_background___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1687_, 0, v_action_1683_);
lean_closure_set(v___f_1687_, 1, v_prio_1684_);
v___f_1688_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_background___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1688_, 0, v___f_1687_);
lean_inc_ref(v_a_1685_);
v___x_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1689_, 0, v_a_1685_);
v___x_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
v___x_1691_ = lean_unsigned_to_nat(0u);
v___x_1692_ = 0;
v___x_1693_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1691_, v___x_1692_, v___x_1690_, v___f_1688_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___redArg___boxed(lean_object* v_action_1694_, lean_object* v_prio_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Std_Async_ContextAsync_background___redArg(v_action_1694_, v_prio_1695_, v_a_1696_);
lean_dec_ref(v_a_1696_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background(lean_object* v_00_u03b1_1699_, lean_object* v_action_1700_, lean_object* v_prio_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v___f_1704_; lean_object* v___f_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; lean_object* v___x_1710_; 
v___f_1704_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_background___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1704_, 0, v_action_1700_);
lean_closure_set(v___f_1704_, 1, v_prio_1701_);
v___f_1705_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_background___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1705_, 0, v___f_1704_);
lean_inc_ref(v_a_1702_);
v___x_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1706_, 0, v_a_1702_);
v___x_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1706_);
v___x_1708_ = lean_unsigned_to_nat(0u);
v___x_1709_ = 0;
v___x_1710_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1708_, v___x_1709_, v___x_1707_, v___f_1705_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_background___boxed(lean_object* v_00_u03b1_1711_, lean_object* v_action_1712_, lean_object* v_prio_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Std_Async_ContextAsync_background(v_00_u03b1_1711_, v_action_1712_, v_prio_1713_, v_a_1714_);
lean_dec_ref(v_a_1714_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg___lam__0(lean_object* v_action_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = lean_apply_2(v_action_1717_, v_a_1718_, lean_box(0));
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg___lam__0___boxed(lean_object* v_action_1721_, lean_object* v_a_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Std_Async_ContextAsync_disown___redArg___lam__0(v_action_1721_, v_a_1722_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg___lam__1(lean_object* v_action_1725_, lean_object* v_prio_1726_, lean_object* v_x_1727_){
_start:
{
if (lean_obj_tag(v_x_1727_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1737_; 
lean_dec(v_prio_1726_);
lean_dec_ref(v_action_1725_);
v_a_1729_ = lean_ctor_get(v_x_1727_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v_x_1727_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1731_ = v_x_1727_;
v_isShared_1732_ = v_isSharedCheck_1737_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v_x_1727_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1737_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
lean_object* v___x_1735_; 
v___x_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1734_);
return v___x_1735_;
}
}
}
else
{
lean_object* v_a_1738_; lean_object* v___f_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v_a_1738_ = lean_ctor_get(v_x_1727_, 0);
lean_inc(v_a_1738_);
lean_dec_ref(v_x_1727_);
v___f_1739_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_disown___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1739_, 0, v_action_1725_);
lean_closure_set(v___f_1739_, 1, v_a_1738_);
v___x_1740_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1740_, 0, lean_box(0));
lean_closure_set(v___x_1740_, 1, v___f_1739_);
v___x_1741_ = lean_io_as_task(v___x_1740_, v_prio_1726_);
lean_dec_ref(v___x_1741_);
v___x_1742_ = ((lean_object*)(l_Std_Async_ContextAsync_background___redArg___lam__2___closed__1));
return v___x_1742_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg___lam__1___boxed(lean_object* v_action_1743_, lean_object* v_prio_1744_, lean_object* v_x_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Std_Async_ContextAsync_disown___redArg___lam__1(v_action_1743_, v_prio_1744_, v_x_1745_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg(lean_object* v_action_1748_, lean_object* v_prio_1749_){
_start:
{
lean_object* v___x_1751_; lean_object* v___f_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; lean_object* v___x_1757_; 
v___x_1751_ = l_Std_CancellationContext_new();
v___f_1752_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_disown___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1752_, 0, v_action_1748_);
lean_closure_set(v___f_1752_, 1, v_prio_1749_);
v___x_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1751_);
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
v___x_1755_ = lean_unsigned_to_nat(0u);
v___x_1756_ = 0;
v___x_1757_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1755_, v___x_1756_, v___x_1754_, v___f_1752_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___redArg___boxed(lean_object* v_action_1758_, lean_object* v_prio_1759_, lean_object* v_a_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Std_Async_ContextAsync_disown___redArg(v_action_1758_, v_prio_1759_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown(lean_object* v_00_u03b1_1762_, lean_object* v_action_1763_, lean_object* v_prio_1764_, lean_object* v_a_1765_){
_start:
{
lean_object* v___x_1767_; lean_object* v___f_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; uint8_t v___x_1772_; lean_object* v___x_1773_; 
v___x_1767_ = l_Std_CancellationContext_new();
v___f_1768_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_disown___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1768_, 0, v_action_1763_);
lean_closure_set(v___f_1768_, 1, v_prio_1764_);
v___x_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1767_);
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
v___x_1771_ = lean_unsigned_to_nat(0u);
v___x_1772_ = 0;
v___x_1773_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1771_, v___x_1772_, v___x_1770_, v___f_1768_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_disown___boxed(lean_object* v_00_u03b1_1774_, lean_object* v_action_1775_, lean_object* v_prio_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Std_Async_ContextAsync_disown(v_00_u03b1_1774_, v_action_1775_, v_prio_1776_, v_a_1777_);
lean_dec_ref(v_a_1777_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__2(lean_object* v_a_1780_, lean_object* v_x_1781_){
_start:
{
if (lean_obj_tag(v_x_1781_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1791_; 
lean_dec_ref(v_a_1780_);
v_a_1783_ = lean_ctor_get(v_x_1781_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_x_1781_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1785_ = v_x_1781_;
v_isShared_1786_ = v_isSharedCheck_1791_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v_x_1781_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1791_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
lean_object* v___x_1789_; 
v___x_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1788_);
return v___x_1789_;
}
}
}
else
{
lean_object* v___x_1792_; 
lean_dec_ref(v_x_1781_);
v___x_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1792_, 0, v_a_1780_);
return v___x_1792_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__2___boxed(lean_object* v_a_1793_, lean_object* v_x_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__2(v_a_1793_, v_x_1794_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__0(lean_object* v_a_1797_, lean_object* v_x_1798_){
_start:
{
if (lean_obj_tag(v_x_1798_) == 0)
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1808_; 
lean_dec_ref(v_a_1797_);
v_a_1800_ = lean_ctor_get(v_x_1798_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v_x_1798_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1802_ = v_x_1798_;
v_isShared_1803_ = v_isSharedCheck_1808_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v_x_1798_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1808_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_object* v___x_1806_; 
v___x_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
return v___x_1806_;
}
}
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1823_; 
v_a_1809_ = lean_ctor_get(v_x_1798_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_x_1798_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1811_ = v_x_1798_;
v_isShared_1812_ = v_isSharedCheck_1823_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v_x_1798_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1823_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___f_1815_; lean_object* v___x_1817_; 
v___x_1813_ = lean_box(2);
v___x_1814_ = l_Std_CancellationContext_cancel(v_a_1797_, v___x_1813_);
v___f_1815_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1815_, 0, v_a_1809_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v___x_1814_);
v___x_1817_ = v___x_1811_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1814_);
v___x_1817_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; lean_object* v___x_1821_; 
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
v___x_1819_ = lean_unsigned_to_nat(0u);
v___x_1820_ = 0;
v___x_1821_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1819_, v___x_1820_, v___x_1818_, v___f_1815_);
return v___x_1821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__0___boxed(lean_object* v_a_1824_, lean_object* v_x_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__0(v_a_1824_, v_x_1825_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__1(lean_object* v_a_1828_, lean_object* v_x_1829_){
_start:
{
if (lean_obj_tag(v_x_1829_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1840_; 
v_a_1831_ = lean_ctor_get(v_x_1829_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_x_1829_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1833_ = v_x_1829_;
v_isShared_1834_ = v_isSharedCheck_1840_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v_x_1829_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1840_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1831_);
v___x_1836_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = lean_io_promise_resolve(v___x_1836_, v_a_1828_);
v___x_1838_ = ((lean_object*)(l_Std_Async_ContextAsync_background___redArg___lam__2___closed__1));
return v___x_1838_;
}
}
}
else
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1841_, 0, v_x_1829_);
return v___x_1841_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__1___boxed(lean_object* v_a_1842_, lean_object* v_x_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__1(v_a_1842_, v_x_1843_);
lean_dec(v_a_1842_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__3(lean_object* v_a_1846_, lean_object* v_x_1847_){
_start:
{
if (lean_obj_tag(v_x_1847_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1857_; 
v_a_1849_ = lean_ctor_get(v_x_1847_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v_x_1847_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1851_ = v_x_1847_;
v_isShared_1852_ = v_isSharedCheck_1857_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v_x_1847_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1857_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1855_; 
v___x_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
return v___x_1855_;
}
}
}
else
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1858_ = lean_io_promise_resolve(v_x_1847_, v_a_1846_);
v___x_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
v___x_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
return v___x_1860_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__3___boxed(lean_object* v_a_1861_, lean_object* v_x_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__3(v_a_1861_, v_x_1862_);
lean_dec(v_a_1861_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__4(lean_object* v_a_1865_, lean_object* v_x_1866_){
_start:
{
if (lean_obj_tag(v_x_1866_) == 0)
{
lean_object* v___x_1868_; 
lean_dec_ref(v_a_1865_);
v___x_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1868_, 0, v_x_1866_);
return v___x_1868_;
}
else
{
lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1878_; 
v_isSharedCheck_1878_ = !lean_is_exclusive(v_x_1866_);
if (v_isSharedCheck_1878_ == 0)
{
lean_object* v_unused_1879_; 
v_unused_1879_ = lean_ctor_get(v_x_1866_, 0);
lean_dec(v_unused_1879_);
v___x_1870_ = v_x_1866_;
v_isShared_1871_ = v_isSharedCheck_1878_;
goto v_resetjp_1869_;
}
else
{
lean_dec(v_x_1866_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1878_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1875_; 
v___x_1872_ = lean_box(2);
v___x_1873_ = l_Std_CancellationContext_cancel(v_a_1865_, v___x_1872_);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v___x_1873_);
v___x_1875_ = v___x_1870_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1873_);
v___x_1875_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
lean_object* v___x_1876_; 
v___x_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
return v___x_1876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__4___boxed(lean_object* v_a_1880_, lean_object* v_x_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__4(v_a_1880_, v_x_1881_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__5(lean_object* v_a_1884_, lean_object* v___x_1885_, lean_object* v___f_1886_, lean_object* v___f_1887_, lean_object* v___f_1888_){
_start:
{
lean_object* v___x_1890_; uint8_t v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1890_, 0, v_a_1884_);
v___x_1891_ = 0;
lean_inc_n(v___x_1885_, 2);
v___x_1892_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1885_, v___x_1891_, v___x_1890_, v___f_1886_);
v___x_1893_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1885_, v___x_1891_, v___x_1892_, v___f_1887_);
v___x_1894_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1885_, v___x_1891_, v___x_1893_, v___f_1888_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__5___boxed(lean_object* v_a_1895_, lean_object* v___x_1896_, lean_object* v___f_1897_, lean_object* v___f_1898_, lean_object* v___f_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__5(v_a_1895_, v___x_1896_, v___f_1897_, v___f_1898_, v___f_1899_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__6(lean_object* v_a_1902_, lean_object* v___x_1903_, lean_object* v___f_1904_, lean_object* v___f_1905_, lean_object* v_x_1906_){
_start:
{
if (lean_obj_tag(v_x_1906_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1916_; 
lean_dec_ref(v___f_1905_);
lean_dec_ref(v___f_1904_);
lean_dec(v___x_1903_);
lean_dec_ref(v_a_1902_);
v_a_1908_ = lean_ctor_get(v_x_1906_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v_x_1906_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1910_ = v_x_1906_;
v_isShared_1911_ = v_isSharedCheck_1916_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v_x_1906_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1916_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1914_; 
v___x_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
return v___x_1914_;
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___f_1918_; lean_object* v___f_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v_a_1917_ = lean_ctor_get(v_x_1906_, 0);
lean_inc(v_a_1917_);
lean_dec_ref(v_x_1906_);
v___f_1918_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1918_, 0, v_a_1917_);
lean_inc(v___x_1903_);
v___f_1919_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v___f_1919_, 0, v_a_1902_);
lean_closure_set(v___f_1919_, 1, v___x_1903_);
lean_closure_set(v___f_1919_, 2, v___f_1904_);
lean_closure_set(v___f_1919_, 3, v___f_1905_);
lean_closure_set(v___f_1919_, 4, v___f_1918_);
v___x_1920_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1920_, 0, lean_box(0));
lean_closure_set(v___x_1920_, 1, v___f_1919_);
v___x_1921_ = lean_io_as_task(v___x_1920_, v___x_1903_);
lean_dec_ref(v___x_1921_);
v___x_1922_ = ((lean_object*)(l_Std_Async_ContextAsync_background___redArg___lam__2___closed__1));
return v___x_1922_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__6___boxed(lean_object* v_a_1923_, lean_object* v___x_1924_, lean_object* v___f_1925_, lean_object* v___f_1926_, lean_object* v_x_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__6(v_a_1923_, v___x_1924_, v___f_1925_, v___f_1926_, v_x_1927_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__7(lean_object* v___x_1930_, lean_object* v___f_1931_, lean_object* v_x_1932_){
_start:
{
if (lean_obj_tag(v_x_1932_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1942_; 
lean_dec_ref(v___f_1931_);
lean_dec(v___x_1930_);
v_a_1934_ = lean_ctor_get(v_x_1932_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_x_1932_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1936_ = v_x_1932_;
v_isShared_1937_ = v_isSharedCheck_1942_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v_x_1932_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1942_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
lean_object* v___x_1940_; 
v___x_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
return v___x_1940_;
}
}
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1954_; 
v_a_1943_ = lean_ctor_get(v_x_1932_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v_x_1932_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1945_ = v_x_1932_;
v_isShared_1946_ = v_isSharedCheck_1954_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v_x_1932_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1954_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1947_; lean_object* v___x_1949_; 
v___x_1947_ = l_Std_CancellationContext_fork(v_a_1943_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 0, v___x_1947_);
v___x_1949_ = v___x_1945_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1947_);
v___x_1949_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
lean_object* v___x_1950_; uint8_t v___x_1951_; lean_object* v___x_1952_; 
v___x_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
v___x_1951_ = 0;
v___x_1952_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1930_, v___x_1951_, v___x_1950_, v___f_1931_);
return v___x_1952_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__7___boxed(lean_object* v___x_1955_, lean_object* v___f_1956_, lean_object* v_x_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__7(v___x_1955_, v___f_1956_, v_x_1957_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__8(lean_object* v___f_1960_, lean_object* v___f_1961_, lean_object* v___y_1962_, lean_object* v_x_1963_){
_start:
{
if (lean_obj_tag(v_x_1963_) == 0)
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1973_; 
lean_dec_ref(v___f_1961_);
lean_dec_ref(v___f_1960_);
v_a_1965_ = lean_ctor_get(v_x_1963_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_x_1963_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1967_ = v_x_1963_;
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v_x_1963_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
lean_object* v___x_1971_; 
v___x_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
return v___x_1971_;
}
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1987_; 
v_a_1974_ = lean_ctor_get(v_x_1963_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v_x_1963_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1976_ = v_x_1963_;
v_isShared_1977_ = v_isSharedCheck_1987_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v_x_1963_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1987_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1978_; lean_object* v___f_1979_; lean_object* v___f_1980_; lean_object* v___x_1982_; 
v___x_1978_ = lean_unsigned_to_nat(0u);
v___f_1979_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_1979_, 0, v_a_1974_);
lean_closure_set(v___f_1979_, 1, v___x_1978_);
lean_closure_set(v___f_1979_, 2, v___f_1960_);
lean_closure_set(v___f_1979_, 3, v___f_1961_);
v___f_1980_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_1980_, 0, v___x_1978_);
lean_closure_set(v___f_1980_, 1, v___f_1979_);
lean_inc_ref(v___y_1962_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v___y_1962_);
v___x_1982_ = v___x_1976_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___y_1962_);
v___x_1982_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v___x_1983_; uint8_t v___x_1984_; lean_object* v___x_1985_; 
v___x_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
v___x_1984_ = 0;
v___x_1985_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1978_, v___x_1984_, v___x_1983_, v___f_1980_);
return v___x_1985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__8___boxed(lean_object* v___f_1988_, lean_object* v___f_1989_, lean_object* v___y_1990_, lean_object* v_x_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__8(v___f_1988_, v___f_1989_, v___y_1990_, v_x_1991_);
lean_dec_ref(v___y_1990_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__10(lean_object* v_x_1994_, lean_object* v_prio_1995_, lean_object* v___f_1996_, lean_object* v___f_1997_, lean_object* v_x_1998_){
_start:
{
if (lean_obj_tag(v_x_1998_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2008_; 
lean_dec_ref(v___f_1997_);
lean_dec_ref(v___f_1996_);
lean_dec(v_prio_1995_);
lean_dec_ref(v_x_1994_);
v_a_2000_ = lean_ctor_get(v_x_1998_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v_x_1998_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2002_ = v_x_1998_;
v_isShared_2003_ = v_isSharedCheck_2008_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v_x_1998_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2008_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
lean_object* v___x_2006_; 
v___x_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2005_);
return v___x_2006_;
}
}
}
else
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2025_; 
v_a_2009_ = lean_ctor_get(v_x_1998_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v_x_1998_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2011_ = v_x_1998_;
v_isShared_2012_ = v_isSharedCheck_2025_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v_x_1998_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2025_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___f_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; uint8_t v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2020_; 
v___f_2013_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_2013_, 0, v_x_1994_);
lean_closure_set(v___f_2013_, 1, v_a_2009_);
v___x_2014_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2014_, 0, lean_box(0));
lean_closure_set(v___x_2014_, 1, v___f_2013_);
v___x_2015_ = lean_io_as_task(v___x_2014_, v_prio_1995_);
v___x_2016_ = lean_unsigned_to_nat(0u);
v___x_2017_ = 1;
v___x_2018_ = lean_task_bind(v___x_2015_, v___f_1996_, v___x_2016_, v___x_2017_);
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 0, v___x_2018_);
v___x_2020_ = v___x_2011_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2021_; uint8_t v___x_2022_; lean_object* v___x_2023_; 
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
v___x_2022_ = 0;
v___x_2023_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2016_, v___x_2022_, v___x_2021_, v___f_1997_);
return v___x_2023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__10___boxed(lean_object* v_x_2026_, lean_object* v_prio_2027_, lean_object* v___f_2028_, lean_object* v___f_2029_, lean_object* v_x_2030_, lean_object* v___y_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__10(v_x_2026_, v_prio_2027_, v___f_2028_, v___f_2029_, v_x_2030_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__9(lean_object* v_a_2033_, lean_object* v___f_2034_, lean_object* v___f_2035_, lean_object* v_prio_2036_, lean_object* v___f_2037_, lean_object* v_x_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v___x_2041_; lean_object* v___f_2042_; lean_object* v___f_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; lean_object* v___x_2048_; 
v___x_2041_ = l_Std_CancellationContext_fork(v_a_2033_);
lean_inc_ref(v___y_2039_);
v___f_2042_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_2042_, 0, v___f_2034_);
lean_closure_set(v___f_2042_, 1, v___f_2035_);
lean_closure_set(v___f_2042_, 2, v___y_2039_);
v___f_2043_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__10___boxed), 6, 4);
lean_closure_set(v___f_2043_, 0, v_x_2038_);
lean_closure_set(v___f_2043_, 1, v_prio_2036_);
lean_closure_set(v___f_2043_, 2, v___f_2037_);
lean_closure_set(v___f_2043_, 3, v___f_2042_);
v___x_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2041_);
v___x_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2044_);
v___x_2046_ = lean_unsigned_to_nat(0u);
v___x_2047_ = 0;
v___x_2048_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2046_, v___x_2047_, v___x_2045_, v___f_2043_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__9___boxed(lean_object* v_a_2049_, lean_object* v___f_2050_, lean_object* v___f_2051_, lean_object* v_prio_2052_, lean_object* v___f_2053_, lean_object* v_x_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__9(v_a_2049_, v___f_2050_, v___f_2051_, v_prio_2052_, v___f_2053_, v_x_2054_, v___y_2055_);
lean_dec_ref(v___y_2055_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__12(lean_object* v_a_2058_, lean_object* v_prio_2059_, lean_object* v___f_2060_, lean_object* v_inst_2061_, lean_object* v_xs_2062_, lean_object* v_a_2063_, lean_object* v___f_2064_, lean_object* v___f_2065_, lean_object* v_x_2066_){
_start:
{
if (lean_obj_tag(v_x_2066_) == 0)
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2076_; 
lean_dec_ref(v___f_2065_);
lean_dec_ref(v___f_2064_);
lean_dec(v_xs_2062_);
lean_dec_ref(v_inst_2061_);
lean_dec_ref(v___f_2060_);
lean_dec(v_prio_2059_);
lean_dec_ref(v_a_2058_);
v_a_2068_ = lean_ctor_get(v_x_2066_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_x_2066_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2070_ = v_x_2066_;
v_isShared_2071_ = v_isSharedCheck_2076_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v_x_2066_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2076_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
lean_object* v___x_2074_; 
v___x_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2073_);
return v___x_2074_;
}
}
}
else
{
lean_object* v_a_2077_; lean_object* v___f_2078_; lean_object* v___f_2079_; lean_object* v___f_2080_; lean_object* v___x_2081_; lean_object* v___f_2082_; lean_object* v___x_2083_; uint8_t v___x_2084_; lean_object* v___x_2085_; 
v_a_2077_ = lean_ctor_get(v_x_2066_, 0);
lean_inc_n(v_a_2077_, 3);
lean_dec_ref(v_x_2066_);
v___f_2078_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2078_, 0, v_a_2077_);
v___f_2079_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2079_, 0, v_a_2077_);
v___f_2080_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__9___boxed), 8, 5);
lean_closure_set(v___f_2080_, 0, v_a_2058_);
lean_closure_set(v___f_2080_, 1, v___f_2079_);
lean_closure_set(v___f_2080_, 2, v___f_2078_);
lean_closure_set(v___f_2080_, 3, v_prio_2059_);
lean_closure_set(v___f_2080_, 4, v___f_2060_);
lean_inc_ref(v_a_2063_);
v___x_2081_ = lean_apply_4(v_inst_2061_, v_xs_2062_, v___f_2080_, v_a_2063_, lean_box(0));
v___f_2082_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_race___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_2082_, 0, v_a_2077_);
lean_closure_set(v___f_2082_, 1, v___f_2064_);
lean_closure_set(v___f_2082_, 2, v___f_2065_);
v___x_2083_ = lean_unsigned_to_nat(0u);
v___x_2084_ = 0;
v___x_2085_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2083_, v___x_2084_, v___x_2081_, v___f_2082_);
return v___x_2085_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__12___boxed(lean_object* v_a_2086_, lean_object* v_prio_2087_, lean_object* v___f_2088_, lean_object* v_inst_2089_, lean_object* v_xs_2090_, lean_object* v_a_2091_, lean_object* v___f_2092_, lean_object* v___f_2093_, lean_object* v_x_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__12(v_a_2086_, v_prio_2087_, v___f_2088_, v_inst_2089_, v_xs_2090_, v_a_2091_, v___f_2092_, v___f_2093_, v_x_2094_);
lean_dec_ref(v_a_2091_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__11(lean_object* v_prio_2097_, lean_object* v___f_2098_, lean_object* v_inst_2099_, lean_object* v_xs_2100_, lean_object* v_a_2101_, lean_object* v___f_2102_, lean_object* v_x_2103_){
_start:
{
if (lean_obj_tag(v_x_2103_) == 0)
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2113_; 
lean_dec_ref(v___f_2102_);
lean_dec(v_xs_2100_);
lean_dec_ref(v_inst_2099_);
lean_dec_ref(v___f_2098_);
lean_dec(v_prio_2097_);
v_a_2105_ = lean_ctor_get(v_x_2103_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v_x_2103_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2107_ = v_x_2103_;
v_isShared_2108_ = v_isSharedCheck_2113_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v_x_2103_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2113_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2111_; 
v___x_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2110_);
return v___x_2111_;
}
}
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2128_; 
v_a_2114_ = lean_ctor_get(v_x_2103_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v_x_2103_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2116_ = v_x_2103_;
v_isShared_2117_ = v_isSharedCheck_2128_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v_x_2103_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2128_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2118_; lean_object* v___f_2119_; lean_object* v___f_2120_; lean_object* v___x_2122_; 
v___x_2118_ = lean_io_promise_new();
lean_inc(v_a_2114_);
v___f_2119_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2119_, 0, v_a_2114_);
lean_inc_ref(v_a_2101_);
v___f_2120_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__12___boxed), 10, 8);
lean_closure_set(v___f_2120_, 0, v_a_2114_);
lean_closure_set(v___f_2120_, 1, v_prio_2097_);
lean_closure_set(v___f_2120_, 2, v___f_2098_);
lean_closure_set(v___f_2120_, 3, v_inst_2099_);
lean_closure_set(v___f_2120_, 4, v_xs_2100_);
lean_closure_set(v___f_2120_, 5, v_a_2101_);
lean_closure_set(v___f_2120_, 6, v___f_2102_);
lean_closure_set(v___f_2120_, 7, v___f_2119_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 0, v___x_2118_);
v___x_2122_ = v___x_2116_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2118_);
v___x_2122_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; lean_object* v___x_2126_; 
v___x_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
v___x_2124_ = lean_unsigned_to_nat(0u);
v___x_2125_ = 0;
v___x_2126_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2124_, v___x_2125_, v___x_2123_, v___f_2120_);
return v___x_2126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___lam__11___boxed(lean_object* v_prio_2129_, lean_object* v___f_2130_, lean_object* v_inst_2131_, lean_object* v_xs_2132_, lean_object* v_a_2133_, lean_object* v___f_2134_, lean_object* v_x_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__11(v_prio_2129_, v___f_2130_, v_inst_2131_, v_xs_2132_, v_a_2133_, v___f_2134_, v_x_2135_);
lean_dec_ref(v_a_2133_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg(lean_object* v_inst_2138_, lean_object* v_xs_2139_, lean_object* v_prio_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v___f_2143_; lean_object* v___f_2144_; lean_object* v___f_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; uint8_t v___x_2149_; lean_object* v___x_2150_; 
v___f_2143_ = ((lean_object*)(l_Std_Async_ContextAsync_race___redArg___closed__1));
v___f_2144_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
lean_inc_ref_n(v_a_2141_, 2);
v___f_2145_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_raceAll___redArg___lam__11___boxed), 8, 6);
lean_closure_set(v___f_2145_, 0, v_prio_2140_);
lean_closure_set(v___f_2145_, 1, v___f_2144_);
lean_closure_set(v___f_2145_, 2, v_inst_2138_);
lean_closure_set(v___f_2145_, 3, v_xs_2139_);
lean_closure_set(v___f_2145_, 4, v_a_2141_);
lean_closure_set(v___f_2145_, 5, v___f_2143_);
v___x_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2146_, 0, v_a_2141_);
v___x_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
v___x_2148_ = lean_unsigned_to_nat(0u);
v___x_2149_ = 0;
v___x_2150_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2148_, v___x_2149_, v___x_2147_, v___f_2145_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___redArg___boxed(lean_object* v_inst_2151_, lean_object* v_xs_2152_, lean_object* v_prio_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Std_Async_ContextAsync_raceAll___redArg(v_inst_2151_, v_xs_2152_, v_prio_2153_, v_a_2154_);
lean_dec_ref(v_a_2154_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll(lean_object* v_c_2157_, lean_object* v_00_u03b1_2158_, lean_object* v_inst_2159_, lean_object* v_xs_2160_, lean_object* v_prio_2161_, lean_object* v_a_2162_){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = l_Std_Async_ContextAsync_raceAll___redArg(v_inst_2159_, v_xs_2160_, v_prio_2161_, v_a_2162_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_raceAll___boxed(lean_object* v_c_2165_, lean_object* v_00_u03b1_2166_, lean_object* v_inst_2167_, lean_object* v_xs_2168_, lean_object* v_prio_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Std_Async_ContextAsync_raceAll(v_c_2165_, v_00_u03b1_2166_, v_inst_2167_, v_xs_2168_, v_prio_2169_, v_a_2170_);
lean_dec_ref(v_a_2170_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg___lam__3(lean_object* v___x_2173_, lean_object* v___f_2174_, lean_object* v___f_2175_){
_start:
{
lean_object* v___x_2177_; uint8_t v___x_2178_; lean_object* v___x_2179_; lean_object* v___y_2181_; 
v___x_2177_ = lean_unsigned_to_nat(0u);
v___x_2178_ = 0;
v___x_2179_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_2173_, v___f_2174_, v___x_2177_, v___x_2178_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2183_; 
lean_dec(v___f_2175_);
v_a_2183_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2183_);
lean_dec_ref(v___x_2179_);
if (lean_obj_tag(v_a_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
v_a_2184_ = lean_ctor_get(v_a_2183_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_a_2183_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v_a_2183_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v_a_2183_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
v___y_2181_ = v___x_2189_;
goto v___jp_2180_;
}
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2200_; 
v_a_2192_ = lean_ctor_get(v_a_2183_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v_a_2183_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2194_ = v_a_2183_;
v_isShared_2195_ = v_isSharedCheck_2200_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v_a_2183_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2200_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v_fst_2196_; lean_object* v___x_2198_; 
v_fst_2196_ = lean_ctor_get(v_a_2192_, 0);
lean_inc(v_fst_2196_);
lean_dec(v_a_2192_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v_fst_2196_);
v___x_2198_ = v___x_2194_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_fst_2196_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
v___y_2181_ = v___x_2198_;
goto v___jp_2180_;
}
}
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2210_; 
v_a_2201_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2203_ = v___x_2179_;
v_isShared_2204_ = v_isSharedCheck_2210_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2179_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2210_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2208_; 
v___x_2205_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_2205_, 0, lean_box(0));
lean_closure_set(v___x_2205_, 1, lean_box(0));
lean_closure_set(v___x_2205_, 2, lean_box(0));
lean_closure_set(v___x_2205_, 3, v___f_2175_);
v___x_2206_ = lean_task_map(v___x_2205_, v_a_2201_, v___x_2177_, v___x_2178_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 0, v___x_2206_);
v___x_2208_ = v___x_2203_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2206_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
v___jp_2180_:
{
lean_object* v___x_2182_; 
v___x_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2182_, 0, v___y_2181_);
return v___x_2182_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg___lam__3___boxed(lean_object* v___x_2211_, lean_object* v___f_2212_, lean_object* v___f_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Std_Async_ContextAsync_async___redArg___lam__3(v___x_2211_, v___f_2212_, v___f_2213_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg___lam__0(lean_object* v_x_2216_, lean_object* v___f_2217_, lean_object* v_prio_2218_, lean_object* v___f_2219_, lean_object* v_x_2220_){
_start:
{
if (lean_obj_tag(v_x_2220_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2230_; 
lean_dec_ref(v___f_2219_);
lean_dec(v_prio_2218_);
lean_dec(v___f_2217_);
lean_dec_ref(v_x_2216_);
v_a_2222_ = lean_ctor_get(v_x_2220_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_x_2220_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2224_ = v_x_2220_;
v_isShared_2225_ = v_isSharedCheck_2230_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v_x_2220_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2230_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2222_);
v___x_2227_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
lean_object* v___x_2228_; 
v___x_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
return v___x_2228_;
}
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2248_; 
v_a_2231_ = lean_ctor_get(v_x_2220_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v_x_2220_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2233_ = v_x_2220_;
v_isShared_2234_ = v_isSharedCheck_2248_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v_x_2220_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2248_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___f_2237_; lean_object* v___f_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; uint8_t v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2245_; 
lean_inc(v_a_2231_);
v___x_2235_ = lean_apply_1(v_x_2216_, v_a_2231_);
v___x_2236_ = lean_box(2);
v___f_2237_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_concurrently___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_2237_, 0, v_a_2231_);
lean_closure_set(v___f_2237_, 1, v___x_2236_);
v___f_2238_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_async___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_2238_, 0, v___x_2235_);
lean_closure_set(v___f_2238_, 1, v___f_2237_);
lean_closure_set(v___f_2238_, 2, v___f_2217_);
v___x_2239_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2239_, 0, lean_box(0));
lean_closure_set(v___x_2239_, 1, v___f_2238_);
v___x_2240_ = lean_io_as_task(v___x_2239_, v_prio_2218_);
v___x_2241_ = lean_unsigned_to_nat(0u);
v___x_2242_ = 1;
v___x_2243_ = lean_task_bind(v___x_2240_, v___f_2219_, v___x_2241_, v___x_2242_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 0, v___x_2243_);
v___x_2245_ = v___x_2233_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v___x_2243_);
v___x_2245_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
lean_object* v___x_2246_; 
v___x_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
return v___x_2246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg___lam__0___boxed(lean_object* v_x_2249_, lean_object* v___f_2250_, lean_object* v_prio_2251_, lean_object* v___f_2252_, lean_object* v_x_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Std_Async_ContextAsync_async___redArg___lam__0(v_x_2249_, v___f_2250_, v_prio_2251_, v___f_2252_, v_x_2253_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg(lean_object* v_x_2256_, lean_object* v_prio_2257_, lean_object* v_ctx_2258_){
_start:
{
lean_object* v___x_2260_; lean_object* v___f_2261_; lean_object* v___f_2262_; lean_object* v___f_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; uint8_t v___x_2267_; lean_object* v___x_2268_; 
lean_inc_ref(v_ctx_2258_);
v___x_2260_ = l_Std_CancellationContext_fork(v_ctx_2258_);
v___f_2261_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__1));
v___f_2262_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_2263_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_async___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_2263_, 0, v_x_2256_);
lean_closure_set(v___f_2263_, 1, v___f_2261_);
lean_closure_set(v___f_2263_, 2, v_prio_2257_);
lean_closure_set(v___f_2263_, 3, v___f_2262_);
v___x_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2260_);
v___x_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
v___x_2266_ = lean_unsigned_to_nat(0u);
v___x_2267_ = 0;
v___x_2268_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2266_, v___x_2267_, v___x_2265_, v___f_2263_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___redArg___boxed(lean_object* v_x_2269_, lean_object* v_prio_2270_, lean_object* v_ctx_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Std_Async_ContextAsync_async___redArg(v_x_2269_, v_prio_2270_, v_ctx_2271_);
lean_dec_ref(v_ctx_2271_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async(lean_object* v_00_u03b1_2274_, lean_object* v_x_2275_, lean_object* v_prio_2276_, lean_object* v_ctx_2277_){
_start:
{
lean_object* v___x_2279_; lean_object* v___f_2280_; lean_object* v___f_2281_; lean_object* v___f_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; uint8_t v___x_2286_; lean_object* v___x_2287_; 
lean_inc_ref(v_ctx_2277_);
v___x_2279_ = l_Std_CancellationContext_fork(v_ctx_2277_);
v___f_2280_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__1));
v___f_2281_ = ((lean_object*)(l_Std_Async_ContextAsync_concurrently___redArg___closed__0));
v___f_2282_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_async___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_2282_, 0, v_x_2275_);
lean_closure_set(v___f_2282_, 1, v___f_2280_);
lean_closure_set(v___f_2282_, 2, v_prio_2276_);
lean_closure_set(v___f_2282_, 3, v___f_2281_);
v___x_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2279_);
v___x_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
v___x_2285_ = lean_unsigned_to_nat(0u);
v___x_2286_ = 0;
v___x_2287_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2285_, v___x_2286_, v___x_2284_, v___f_2282_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_async___boxed(lean_object* v_00_u03b1_2288_, lean_object* v_x_2289_, lean_object* v_prio_2290_, lean_object* v_ctx_2291_, lean_object* v_a_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Std_Async_ContextAsync_async(v_00_u03b1_2288_, v_x_2289_, v_prio_2290_, v_ctx_2291_);
lean_dec_ref(v_ctx_2291_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5(lean_object* v___f_2294_, lean_object* v___f_2295_, lean_object* v_00_u03b1_2296_, lean_object* v_x_2297_, lean_object* v_prio_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v___x_2301_; lean_object* v___f_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; uint8_t v___x_2306_; lean_object* v___x_2307_; 
lean_inc_ref(v___y_2299_);
v___x_2301_ = l_Std_CancellationContext_fork(v___y_2299_);
v___f_2302_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_async___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_2302_, 0, v_x_2297_);
lean_closure_set(v___f_2302_, 1, v___f_2294_);
lean_closure_set(v___f_2302_, 2, v_prio_2298_);
lean_closure_set(v___f_2302_, 3, v___f_2295_);
v___x_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2301_);
v___x_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
v___x_2305_ = lean_unsigned_to_nat(0u);
v___x_2306_ = 0;
v___x_2307_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2305_, v___x_2306_, v___x_2304_, v___f_2302_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5___boxed(lean_object* v___f_2308_, lean_object* v___f_2309_, lean_object* v_00_u03b1_2310_, lean_object* v_x_2311_, lean_object* v_prio_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5(v___f_2308_, v___f_2309_, v_00_u03b1_2310_, v_x_2311_, v_prio_2312_, v___y_2313_);
lean_dec_ref(v___y_2313_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instFunctor___lam__0(lean_object* v_00_u03b1_2320_, lean_object* v_00_u03b2_2321_, lean_object* v_f_2322_, lean_object* v_x_2323_, lean_object* v_ctx_2324_){
_start:
{
lean_object* v___x_2326_; lean_object* v___y_2328_; 
v___x_2326_ = lean_apply_2(v_x_2323_, v_ctx_2324_, lean_box(0));
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2330_; 
v_a_2330_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2330_);
lean_dec_ref(v___x_2326_);
if (lean_obj_tag(v_a_2330_) == 0)
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
lean_dec(v_f_2322_);
v_a_2331_ = lean_ctor_get(v_a_2330_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v_a_2330_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2333_ = v_a_2330_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v_a_2330_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
v___y_2328_ = v___x_2336_;
goto v___jp_2327_;
}
}
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2347_; 
v_a_2339_ = lean_ctor_get(v_a_2330_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v_a_2330_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2341_ = v_a_2330_;
v_isShared_2342_ = v_isSharedCheck_2347_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v_a_2330_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2347_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2343_; lean_object* v___x_2345_; 
v___x_2343_ = lean_apply_1(v_f_2322_, v_a_2339_);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 0, v___x_2343_);
v___x_2345_ = v___x_2341_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2343_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
v___y_2328_ = v___x_2345_;
goto v___jp_2327_;
}
}
}
}
else
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2359_; 
v_a_2348_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2350_ = v___x_2326_;
v_isShared_2351_ = v_isSharedCheck_2359_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2326_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2359_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; uint8_t v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2357_; 
v___x_2352_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_2352_, 0, lean_box(0));
lean_closure_set(v___x_2352_, 1, lean_box(0));
lean_closure_set(v___x_2352_, 2, lean_box(0));
lean_closure_set(v___x_2352_, 3, v_f_2322_);
v___x_2353_ = lean_unsigned_to_nat(0u);
v___x_2354_ = 0;
v___x_2355_ = lean_task_map(v___x_2352_, v_a_2348_, v___x_2353_, v___x_2354_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v___x_2355_);
v___x_2357_ = v___x_2350_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2355_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
v___jp_2327_:
{
lean_object* v___x_2329_; 
v___x_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2329_, 0, v___y_2328_);
return v___x_2329_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instFunctor___lam__0___boxed(lean_object* v_00_u03b1_2360_, lean_object* v_00_u03b2_2361_, lean_object* v_f_2362_, lean_object* v_x_2363_, lean_object* v_ctx_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Std_Async_ContextAsync_instFunctor___lam__0(v_00_u03b1_2360_, v_00_u03b2_2361_, v_f_2362_, v_x_2363_, v_ctx_2364_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instFunctor___lam__1(lean_object* v___f_2367_, lean_object* v_00_u03b1_2368_, lean_object* v_00_u03b2_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2374_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_2374_, 0, lean_box(0));
lean_closure_set(v___x_2374_, 1, lean_box(0));
lean_closure_set(v___x_2374_, 2, v___y_2370_);
lean_inc_ref(v___y_2372_);
v___x_2375_ = lean_apply_6(v___f_2367_, lean_box(0), lean_box(0), v___x_2374_, v___y_2371_, v___y_2372_, lean_box(0));
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instFunctor___lam__1___boxed(lean_object* v___f_2376_, lean_object* v_00_u03b1_2377_, lean_object* v_00_u03b2_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Std_Async_ContextAsync_instFunctor___lam__1(v___f_2376_, v_00_u03b1_2377_, v_00_u03b2_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
lean_dec_ref(v___y_2381_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__0(lean_object* v_00_u03b1_2391_, lean_object* v_a_2392_, lean_object* v_x_2393_){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2395_, 0, v_a_2392_);
v___x_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__0___boxed(lean_object* v_00_u03b1_2397_, lean_object* v_a_2398_, lean_object* v_x_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l_Std_Async_ContextAsync_instMonad___lam__0(v_00_u03b1_2397_, v_a_2398_, v_x_2399_);
lean_dec_ref(v_x_2399_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__1(lean_object* v_f_2402_, lean_object* v_ctx_2403_, lean_object* v_x_2404_){
_start:
{
if (lean_obj_tag(v_x_2404_) == 0)
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2414_; 
lean_dec_ref(v_ctx_2403_);
lean_dec_ref(v_f_2402_);
v_a_2406_ = lean_ctor_get(v_x_2404_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v_x_2404_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2408_ = v_x_2404_;
v_isShared_2409_ = v_isSharedCheck_2414_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v_x_2404_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2414_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2406_);
v___x_2411_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
lean_object* v___x_2412_; 
v___x_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2411_);
return v___x_2412_;
}
}
}
else
{
lean_object* v_a_2415_; lean_object* v___x_2416_; 
v_a_2415_ = lean_ctor_get(v_x_2404_, 0);
lean_inc(v_a_2415_);
lean_dec_ref(v_x_2404_);
v___x_2416_ = lean_apply_3(v_f_2402_, v_a_2415_, v_ctx_2403_, lean_box(0));
return v___x_2416_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__1___boxed(lean_object* v_f_2417_, lean_object* v_ctx_2418_, lean_object* v_x_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l_Std_Async_ContextAsync_instMonad___lam__1(v_f_2417_, v_ctx_2418_, v_x_2419_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__2(lean_object* v_00_u03b1_2422_, lean_object* v_00_u03b2_2423_, lean_object* v_x_2424_, lean_object* v_f_2425_, lean_object* v_ctx_2426_){
_start:
{
lean_object* v___x_2428_; lean_object* v___f_2429_; lean_object* v___x_2430_; uint8_t v___x_2431_; lean_object* v___x_2432_; 
lean_inc_ref(v_ctx_2426_);
v___x_2428_ = lean_apply_2(v_x_2424_, v_ctx_2426_, lean_box(0));
v___f_2429_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_instMonad___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2429_, 0, v_f_2425_);
lean_closure_set(v___f_2429_, 1, v_ctx_2426_);
v___x_2430_ = lean_unsigned_to_nat(0u);
v___x_2431_ = 0;
v___x_2432_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2430_, v___x_2431_, v___x_2428_, v___f_2429_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonad___lam__2___boxed(lean_object* v_00_u03b1_2433_, lean_object* v_00_u03b2_2434_, lean_object* v_x_2435_, lean_object* v_f_2436_, lean_object* v_ctx_2437_, lean_object* v___y_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_Std_Async_ContextAsync_instMonad___lam__2(v_00_u03b1_2433_, v_00_u03b2_2434_, v_x_2435_, v_f_2436_, v_ctx_2437_);
return v_res_2439_;
}
}
static lean_object* _init_l_Std_Async_ContextAsync_instMonad(void){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v_toApplicative_2444_; lean_object* v_toSeq_2445_; lean_object* v_toSeqLeft_2446_; lean_object* v_toSeqRight_2447_; lean_object* v___f_2448_; lean_object* v___f_2449_; lean_object* v___f_2450_; lean_object* v___f_2451_; lean_object* v___f_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2442_ = ((lean_object*)(l_Std_Async_ContextAsync_instFunctor));
v___x_2443_ = lean_obj_once(&l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1, &l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1_once, _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1);
v_toApplicative_2444_ = lean_ctor_get(v___x_2443_, 0);
v_toSeq_2445_ = lean_ctor_get(v_toApplicative_2444_, 2);
v_toSeqLeft_2446_ = lean_ctor_get(v_toApplicative_2444_, 3);
v_toSeqRight_2447_ = lean_ctor_get(v_toApplicative_2444_, 4);
v___f_2448_ = ((lean_object*)(l_Std_Async_ContextAsync_instMonad___closed__0));
v___f_2449_ = ((lean_object*)(l_Std_Async_ContextAsync_instMonad___closed__1));
lean_inc(v_toSeqRight_2447_);
v___f_2450_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2450_, 0, v_toSeqRight_2447_);
lean_inc(v_toSeqLeft_2446_);
v___f_2451_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2451_, 0, v_toSeqLeft_2446_);
lean_inc(v_toSeq_2445_);
v___f_2452_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2452_, 0, v_toSeq_2445_);
v___x_2453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2442_);
lean_ctor_set(v___x_2453_, 1, v___f_2448_);
lean_ctor_set(v___x_2453_, 2, v___f_2452_);
lean_ctor_set(v___x_2453_, 3, v___f_2451_);
lean_ctor_set(v___x_2453_, 4, v___f_2450_);
v___x_2454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2453_);
lean_ctor_set(v___x_2454_, 1, v___f_2449_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___lam__0(lean_object* v_a_2455_){
_start:
{
lean_object* v___x_2456_; 
v___x_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2456_, 0, v_a_2455_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___lam__1(lean_object* v___f_2457_, lean_object* v_x_2458_){
_start:
{
if (lean_obj_tag(v_x_2458_) == 0)
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2468_; 
lean_dec_ref(v___f_2457_);
v_a_2460_ = lean_ctor_get(v_x_2458_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v_x_2458_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2462_ = v_x_2458_;
v_isShared_2463_ = v_isSharedCheck_2468_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v_x_2458_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2468_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
lean_object* v___x_2466_; 
v___x_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2465_);
return v___x_2466_;
}
}
}
else
{
lean_object* v_a_2469_; 
v_a_2469_ = lean_ctor_get(v_x_2458_, 0);
lean_inc(v_a_2469_);
lean_dec_ref(v_x_2458_);
if (lean_obj_tag(v_a_2469_) == 0)
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2478_; 
lean_dec_ref(v___f_2457_);
v_a_2470_ = lean_ctor_get(v_a_2469_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v_a_2469_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2472_ = v_a_2469_;
v_isShared_2473_ = v_isSharedCheck_2478_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v_a_2469_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2478_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_object* v___x_2476_; 
v___x_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
return v___x_2476_;
}
}
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2480_; uint8_t v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v_a_2479_ = lean_ctor_get(v_a_2469_, 0);
lean_inc(v_a_2479_);
lean_dec_ref(v_a_2469_);
v___x_2480_ = lean_unsigned_to_nat(0u);
v___x_2481_ = 0;
v___x_2482_ = lean_task_map(v___f_2457_, v_a_2479_, v___x_2480_, v___x_2481_);
v___x_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
return v___x_2483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___lam__1___boxed(lean_object* v___f_2484_, lean_object* v_x_2485_, lean_object* v___y_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_Std_Async_ContextAsync_instMonadLiftIO___lam__1(v___f_2484_, v_x_2485_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___lam__2(lean_object* v___f_2488_, lean_object* v_00_u03b1_2489_, lean_object* v_x_2490_, lean_object* v_x_2491_){
_start:
{
lean_object* v_val_2494_; lean_object* v___x_2500_; 
v___x_2500_ = lean_apply_1(v_x_2490_, lean_box(0));
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2509_; 
v_a_2501_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2503_ = v___x_2500_;
v_isShared_2504_ = v_isSharedCheck_2509_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2500_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2509_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2505_; lean_object* v___x_2507_; 
v___x_2505_ = lean_task_pure(v_a_2501_);
if (v_isShared_2504_ == 0)
{
lean_ctor_set_tag(v___x_2503_, 1);
lean_ctor_set(v___x_2503_, 0, v___x_2505_);
v___x_2507_ = v___x_2503_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2505_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
v_val_2494_ = v___x_2507_;
goto v___jp_2493_;
}
}
}
else
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2517_; 
v_a_2510_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2512_ = v___x_2500_;
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2500_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2513_ == 0)
{
lean_ctor_set_tag(v___x_2512_, 0);
v___x_2515_ = v___x_2512_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_a_2510_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
v_val_2494_ = v___x_2515_;
goto v___jp_2493_;
}
}
}
v___jp_2493_:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; uint8_t v___x_2498_; lean_object* v___x_2499_; 
v___x_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2495_, 0, v_val_2494_);
v___x_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2495_);
v___x_2497_ = lean_unsigned_to_nat(0u);
v___x_2498_ = 0;
v___x_2499_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2497_, v___x_2498_, v___x_2496_, v___f_2488_);
return v___x_2499_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftIO___lam__2___boxed(lean_object* v___f_2518_, lean_object* v_00_u03b1_2519_, lean_object* v_x_2520_, lean_object* v_x_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l_Std_Async_ContextAsync_instMonadLiftIO___lam__2(v___f_2518_, v_00_u03b1_2519_, v_x_2520_, v_x_2521_);
lean_dec_ref(v_x_2521_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0(lean_object* v_00_u03b1_2530_, lean_object* v_x_2531_, lean_object* v_x_2532_){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2534_ = lean_apply_1(v_x_2531_, lean_box(0));
v___x_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2534_);
v___x_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2535_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0___boxed(lean_object* v_00_u03b1_2537_, lean_object* v_x_2538_, lean_object* v_x_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0(v_00_u03b1_2537_, v_x_2538_, v_x_2539_);
lean_dec_ref(v_x_2539_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__0(lean_object* v_00_u03b1_2544_, lean_object* v_e_2545_, lean_object* v_x_2546_){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2548_, 0, v_e_2545_);
v___x_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2548_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__0___boxed(lean_object* v_00_u03b1_2550_, lean_object* v_e_2551_, lean_object* v_x_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Std_Async_ContextAsync_instMonadExceptError___lam__0(v_00_u03b1_2550_, v_e_2551_, v_x_2552_);
lean_dec_ref(v_x_2552_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__1(lean_object* v_h_2555_, lean_object* v_ctx_2556_, lean_object* v_x_2557_){
_start:
{
if (lean_obj_tag(v_x_2557_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2560_; 
v_a_2559_ = lean_ctor_get(v_x_2557_, 0);
lean_inc(v_a_2559_);
lean_dec_ref(v_x_2557_);
v___x_2560_ = lean_apply_3(v_h_2555_, v_a_2559_, v_ctx_2556_, lean_box(0));
return v___x_2560_;
}
else
{
lean_object* v___x_2561_; 
lean_dec_ref(v_ctx_2556_);
lean_dec_ref(v_h_2555_);
v___x_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2561_, 0, v_x_2557_);
return v___x_2561_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__1___boxed(lean_object* v_h_2562_, lean_object* v_ctx_2563_, lean_object* v_x_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Std_Async_ContextAsync_instMonadExceptError___lam__1(v_h_2562_, v_ctx_2563_, v_x_2564_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__2(lean_object* v_00_u03b1_2567_, lean_object* v_x_2568_, lean_object* v_h_2569_, lean_object* v_ctx_2570_){
_start:
{
lean_object* v___x_2572_; lean_object* v___f_2573_; lean_object* v___x_2574_; uint8_t v___x_2575_; lean_object* v___x_2576_; 
lean_inc_ref(v_ctx_2570_);
v___x_2572_ = lean_apply_2(v_x_2568_, v_ctx_2570_, lean_box(0));
v___f_2573_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_instMonadExceptError___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2573_, 0, v_h_2569_);
lean_closure_set(v___f_2573_, 1, v_ctx_2570_);
v___x_2574_ = lean_unsigned_to_nat(0u);
v___x_2575_ = 0;
v___x_2576_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2574_, v___x_2575_, v___x_2572_, v___f_2573_);
return v___x_2576_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadExceptError___lam__2___boxed(lean_object* v_00_u03b1_2577_, lean_object* v_x_2578_, lean_object* v_h_2579_, lean_object* v_ctx_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Std_Async_ContextAsync_instMonadExceptError___lam__2(v_00_u03b1_2577_, v_x_2578_, v_h_2579_, v_ctx_2580_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadFinally___lam__0(lean_object* v_f_2589_, lean_object* v_ctx_2590_, lean_object* v_opt_2591_){
_start:
{
lean_object* v___x_2593_; 
v___x_2593_ = lean_apply_3(v_f_2589_, v_opt_2591_, v_ctx_2590_, lean_box(0));
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadFinally___lam__0___boxed(lean_object* v_f_2594_, lean_object* v_ctx_2595_, lean_object* v_opt_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v_res_2598_; 
v_res_2598_ = l_Std_Async_ContextAsync_instMonadFinally___lam__0(v_f_2594_, v_ctx_2595_, v_opt_2596_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadFinally___lam__1(lean_object* v_00_u03b1_2599_, lean_object* v_00_u03b2_2600_, lean_object* v_x_2601_, lean_object* v_f_2602_, lean_object* v_ctx_2603_){
_start:
{
lean_object* v___f_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; uint8_t v___x_2608_; lean_object* v___x_2609_; 
lean_inc_ref(v_ctx_2603_);
v___f_2605_ = lean_alloc_closure((void*)(l_Std_Async_ContextAsync_instMonadFinally___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2605_, 0, v_f_2602_);
lean_closure_set(v___f_2605_, 1, v_ctx_2603_);
v___x_2606_ = lean_apply_1(v_x_2601_, v_ctx_2603_);
v___x_2607_ = lean_unsigned_to_nat(0u);
v___x_2608_ = 0;
v___x_2609_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_2606_, v___f_2605_, v___x_2607_, v___x_2608_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadFinally___lam__1___boxed(lean_object* v_00_u03b1_2610_, lean_object* v_00_u03b2_2611_, lean_object* v_x_2612_, lean_object* v_f_2613_, lean_object* v_ctx_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v_res_2616_; 
v_res_2616_ = l_Std_Async_ContextAsync_instMonadFinally___lam__1(v_00_u03b1_2610_, v_00_u03b2_2611_, v_x_2612_, v_f_2613_, v_ctx_2614_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited___lam__0(lean_object* v_x_2626_){
_start:
{
lean_object* v___x_2628_; 
v___x_2628_ = ((lean_object*)(l_Std_Async_ContextAsync_instInhabited___lam__0___closed__3));
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited___lam__0___boxed(lean_object* v_x_2629_, lean_object* v___y_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l_Std_Async_ContextAsync_instInhabited___lam__0(v_x_2629_);
lean_dec_ref(v_x_2629_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited(lean_object* v_00_u03b1_2633_, lean_object* v_inst_2634_){
_start:
{
lean_object* v___f_2635_; 
v___f_2635_ = ((lean_object*)(l_Std_Async_ContextAsync_instInhabited___closed__0));
return v___f_2635_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instInhabited___boxed(lean_object* v_00_u03b1_2636_, lean_object* v_inst_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Std_Async_ContextAsync_instInhabited(v_00_u03b1_2636_, v_inst_2637_);
lean_dec(v_inst_2637_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0(lean_object* v_00_u03b1_2639_, lean_object* v_t_2640_, lean_object* v_x_2641_){
_start:
{
lean_object* v___x_2643_; 
v___x_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2643_, 0, v_t_2640_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0___boxed(lean_object* v_00_u03b1_2644_, lean_object* v_t_2645_, lean_object* v_x_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0(v_00_u03b1_2644_, v_t_2645_, v_x_2646_);
lean_dec_ref(v_x_2646_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selector_cancelled(lean_object* v_a_2651_){
_start:
{
lean_object* v___f_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; uint8_t v___x_2657_; lean_object* v___x_2658_; 
v___f_2653_ = ((lean_object*)(l_Std_Async_ContextAsync_doneSelector___closed__0));
lean_inc_ref(v_a_2651_);
v___x_2654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2654_, 0, v_a_2651_);
v___x_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2654_);
v___x_2656_ = lean_unsigned_to_nat(0u);
v___x_2657_ = 0;
v___x_2658_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2656_, v___x_2657_, v___x_2655_, v___f_2653_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selector_cancelled___boxed(lean_object* v_a_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Std_Async_Selector_cancelled(v_a_2659_);
lean_dec_ref(v_a_2659_);
return v_res_2661_;
}
}
lean_object* runtime_initialize_Std_Internal_UV(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_Timer(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_CancellationContext(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Async_ContextAsync(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
