// Lean compiler output
// Module: Std.Async.Basic
// Imports: public import Init.System.Promise public import Init.While
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
lean_object* l_Except_pure(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_instMonadBaseIO___aux__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* l_liftM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Function_const___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
uint8_t lean_io_get_task_state(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_io_promise_new();
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_MonadExcept_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Functor_mapRev___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitStateTOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitStateTOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitStateTOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitStateTOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___closed__0 = (const lean_object*)&l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitExceptTOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitExceptTOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitReaderTOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitReaderTOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitReaderTOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitReaderTOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitReaderTOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitStateRefT_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitStateRefT_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitStateTOfMonad__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitStateTOfMonad__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAsyncReaderT___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAsyncReaderT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAsyncReaderT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAsyncStateRefT_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAsyncStateRefT_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___closed__0 = (const lean_object*)&l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_pure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_pure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_map___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_map___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_ETask_map___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_ETask_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_bind___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_bind___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_ETask_bind___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_ETask_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_bindEIO___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_bindEIO___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_bindEIO___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_ETask_bindEIO___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_bindEIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_ETask_bindEIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_mapEIO___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_mapEIO___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_mapEIO___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_ETask_mapEIO___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_mapEIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_ETask_mapEIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_block___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_block___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_block(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_block___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_ofPromise_x21___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_ofPromise_x21___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_ofPromise_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_ofPromise_x21___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ETask_ofPurePromise___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_pure, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Async_ETask_ofPurePromise___redArg___closed__0 = (const lean_object*)&l_Std_Async_ETask_ofPurePromise___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_ETask_ofPurePromise___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_ofPurePromise___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_ofPurePromise(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_ofPurePromise___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Async_ETask_getState___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_getState___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Async_ETask_getState(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_getState___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_instFunctor___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_instFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ETask_instFunctor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ETask_instFunctor___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ETask_instFunctor___closed__0 = (const lean_object*)&l_Std_Async_ETask_instFunctor___closed__0_value;
static const lean_closure_object l_Std_Async_ETask_instFunctor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ETask_instFunctor___lam__0, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_ETask_instFunctor___closed__0_value)} };
static const lean_object* l_Std_Async_ETask_instFunctor___closed__1 = (const lean_object*)&l_Std_Async_ETask_instFunctor___closed__1_value;
static const lean_ctor_object l_Std_Async_ETask_instFunctor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_ETask_instFunctor___closed__0_value),((lean_object*)&l_Std_Async_ETask_instFunctor___closed__1_value)}};
static const lean_object* l_Std_Async_ETask_instFunctor___closed__2 = (const lean_object*)&l_Std_Async_ETask_instFunctor___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Async_ETask_instFunctor(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___lam__9(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ETask_instMonad___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ETask_instMonad___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ETask_instMonad___closed__0 = (const lean_object*)&l_Std_Async_ETask_instMonad___closed__0_value;
static const lean_closure_object l_Std_Async_ETask_instMonad___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ETask_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ETask_instMonad___closed__1 = (const lean_object*)&l_Std_Async_ETask_instMonad___closed__1_value;
static const lean_closure_object l_Std_Async_ETask_instMonad___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ETask_instMonad___lam__5, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ETask_instMonad___closed__2 = (const lean_object*)&l_Std_Async_ETask_instMonad___closed__2_value;
static const lean_closure_object l_Std_Async_ETask_instMonad___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ETask_instMonad___lam__7, .m_arity = 6, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Async_ETask_instMonad___closed__0_value),((lean_object*)&l_Std_Async_ETask_instMonad___closed__2_value)} };
static const lean_object* l_Std_Async_ETask_instMonad___closed__3 = (const lean_object*)&l_Std_Async_ETask_instMonad___closed__3_value;
static const lean_closure_object l_Std_Async_ETask_instMonad___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ETask_instMonad___lam__9, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ETask_instMonad___closed__4 = (const lean_object*)&l_Std_Async_ETask_instMonad___closed__4_value;
static lean_once_cell_t l_Std_Async_ETask_instMonad___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_ETask_instMonad___closed__5;
static lean_once_cell_t l_Std_Async_ETask_instMonad___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_ETask_instMonad___closed__6;
static lean_once_cell_t l_Std_Async_ETask_instMonad___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_ETask_instMonad___closed__7;
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapIO___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapIO___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapIO___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapIO___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_pure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_pure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bind___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bind___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bind___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_map___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_map___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_map___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bindIO___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bindIO___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bindIO___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bindIO___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bindIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bindIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapTaskIO___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapTaskIO___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapTaskIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapTaskIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_block___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_block___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_block(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_block___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPromise___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPromise___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPromise___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPromise___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPromise(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPromise___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPurePromise___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPurePromise___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPurePromise___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPurePromise(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPurePromise___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Async_AsyncTask_getState___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_getState___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Async_AsyncTask_getState(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_getState___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_pure_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_pure_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ofTask_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ofTask_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_toTask___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_toTask(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_get___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_map___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_map___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_map(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_bind___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_bind___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_bind___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_joinTask___redArg___lam__0(lean_object*);
static const lean_closure_object l_Std_Async_MaybeTask_joinTask___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_MaybeTask_joinTask___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_MaybeTask_joinTask___redArg___closed__0 = (const lean_object*)&l_Std_Async_MaybeTask_joinTask___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_joinTask___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_joinTask(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instFunctor___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_MaybeTask_instFunctor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_MaybeTask_instFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_MaybeTask_instFunctor___closed__0 = (const lean_object*)&l_Std_Async_MaybeTask_instFunctor___closed__0_value;
static const lean_closure_object l_Std_Async_MaybeTask_instFunctor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_MaybeTask_instFunctor___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_MaybeTask_instFunctor___closed__0_value)} };
static const lean_object* l_Std_Async_MaybeTask_instFunctor___closed__1 = (const lean_object*)&l_Std_Async_MaybeTask_instFunctor___closed__1_value;
static const lean_ctor_object l_Std_Async_MaybeTask_instFunctor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_MaybeTask_instFunctor___closed__0_value),((lean_object*)&l_Std_Async_MaybeTask_instFunctor___closed__1_value)}};
static const lean_object* l_Std_Async_MaybeTask_instFunctor___closed__2 = (const lean_object*)&l_Std_Async_MaybeTask_instFunctor___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_Async_MaybeTask_instFunctor = (const lean_object*)&l_Std_Async_MaybeTask_instFunctor___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__10(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_MaybeTask_instMonad___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_MaybeTask_instMonad___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_MaybeTask_instMonad___closed__0 = (const lean_object*)&l_Std_Async_MaybeTask_instMonad___closed__0_value;
static const lean_closure_object l_Std_Async_MaybeTask_instMonad___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_MaybeTask_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_MaybeTask_instMonad___closed__1 = (const lean_object*)&l_Std_Async_MaybeTask_instMonad___closed__1_value;
static const lean_closure_object l_Std_Async_MaybeTask_instMonad___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_MaybeTask_instMonad___lam__5, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_MaybeTask_instMonad___closed__2 = (const lean_object*)&l_Std_Async_MaybeTask_instMonad___closed__2_value;
static const lean_closure_object l_Std_Async_MaybeTask_instMonad___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_MaybeTask_instMonad___lam__7, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_MaybeTask_instMonad___closed__2_value)} };
static const lean_object* l_Std_Async_MaybeTask_instMonad___closed__3 = (const lean_object*)&l_Std_Async_MaybeTask_instMonad___closed__3_value;
static const lean_closure_object l_Std_Async_MaybeTask_instMonad___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_MaybeTask_instMonad___lam__10, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_MaybeTask_instMonad___closed__4 = (const lean_object*)&l_Std_Async_MaybeTask_instMonad___closed__4_value;
static const lean_ctor_object l_Std_Async_MaybeTask_instMonad___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_MaybeTask_instFunctor___closed__2_value),((lean_object*)&l_Std_Async_MaybeTask_instMonad___closed__0_value),((lean_object*)&l_Std_Async_MaybeTask_instMonad___closed__1_value),((lean_object*)&l_Std_Async_MaybeTask_instMonad___closed__3_value),((lean_object*)&l_Std_Async_MaybeTask_instMonad___closed__4_value)}};
static const lean_object* l_Std_Async_MaybeTask_instMonad___closed__5 = (const lean_object*)&l_Std_Async_MaybeTask_instMonad___closed__5_value;
static const lean_ctor_object l_Std_Async_MaybeTask_instMonad___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_MaybeTask_instMonad___closed__5_value),((lean_object*)&l_Std_Async_MaybeTask_instMonad___closed__2_value)}};
static const lean_object* l_Std_Async_MaybeTask_instMonad___closed__6 = (const lean_object*)&l_Std_Async_MaybeTask_instMonad___closed__6_value;
LEAN_EXPORT const lean_object* l_Std_Async_MaybeTask_instMonad = (const lean_object*)&l_Std_Async_MaybeTask_instMonad___closed__6_value;
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_mk___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_mk___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_mk(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_mk___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toRawBaseIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toRawBaseIO___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toRawBaseIO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toRawBaseIO___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toBaseIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toBaseIO___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toBaseIO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toBaseIO___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofTask___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofTask___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofTask(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofTask___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_pure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_pure___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_pure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_pure___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_map___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_map___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_bind___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_bind___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_lift___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_lift___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_lift(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_lift___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_wait___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_wait___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_wait(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_wait___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_asTask___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_asTask___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_asTask(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_asTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_await___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_await___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_await(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_await___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_async___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_async___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_async(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_async___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instFunctor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instFunctor___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instFunctor___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_BaseAsync_instFunctor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_BaseAsync_instFunctor___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_BaseAsync_instFunctor___closed__0 = (const lean_object*)&l_Std_Async_BaseAsync_instFunctor___closed__0_value;
static const lean_closure_object l_Std_Async_BaseAsync_instFunctor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_BaseAsync_instFunctor___lam__1___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_BaseAsync_instFunctor___closed__0_value)} };
static const lean_object* l_Std_Async_BaseAsync_instFunctor___closed__1 = (const lean_object*)&l_Std_Async_BaseAsync_instFunctor___closed__1_value;
static const lean_ctor_object l_Std_Async_BaseAsync_instFunctor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_BaseAsync_instFunctor___closed__0_value),((lean_object*)&l_Std_Async_BaseAsync_instFunctor___closed__1_value)}};
static const lean_object* l_Std_Async_BaseAsync_instFunctor___closed__2 = (const lean_object*)&l_Std_Async_BaseAsync_instFunctor___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_Async_BaseAsync_instFunctor = (const lean_object*)&l_Std_Async_BaseAsync_instFunctor___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_BaseAsync_instMonad___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_BaseAsync_instMonad___lam__1___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_BaseAsync_instMonad___closed__0 = (const lean_object*)&l_Std_Async_BaseAsync_instMonad___closed__0_value;
static const lean_closure_object l_Std_Async_BaseAsync_instMonad___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_BaseAsync_instMonad___lam__2___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_BaseAsync_instMonad___closed__1 = (const lean_object*)&l_Std_Async_BaseAsync_instMonad___closed__1_value;
static const lean_closure_object l_Std_Async_BaseAsync_instMonad___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_BaseAsync_instMonad___lam__5___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_BaseAsync_instMonad___closed__1_value)} };
static const lean_object* l_Std_Async_BaseAsync_instMonad___closed__2 = (const lean_object*)&l_Std_Async_BaseAsync_instMonad___closed__2_value;
static const lean_closure_object l_Std_Async_BaseAsync_instMonad___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_BaseAsync_instMonad___lam__7___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_BaseAsync_instMonad___closed__3 = (const lean_object*)&l_Std_Async_BaseAsync_instMonad___closed__3_value;
static const lean_closure_object l_Std_Async_BaseAsync_instMonad___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_BaseAsync_pure___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_BaseAsync_instMonad___closed__4 = (const lean_object*)&l_Std_Async_BaseAsync_instMonad___closed__4_value;
static const lean_ctor_object l_Std_Async_BaseAsync_instMonad___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_BaseAsync_instFunctor___closed__2_value),((lean_object*)&l_Std_Async_BaseAsync_instMonad___closed__4_value),((lean_object*)&l_Std_Async_BaseAsync_instMonad___closed__0_value),((lean_object*)&l_Std_Async_BaseAsync_instMonad___closed__2_value),((lean_object*)&l_Std_Async_BaseAsync_instMonad___closed__3_value)}};
static const lean_object* l_Std_Async_BaseAsync_instMonad___closed__5 = (const lean_object*)&l_Std_Async_BaseAsync_instMonad___closed__5_value;
static const lean_ctor_object l_Std_Async_BaseAsync_instMonad___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_BaseAsync_instMonad___closed__5_value),((lean_object*)&l_Std_Async_BaseAsync_instMonad___closed__1_value)}};
static const lean_object* l_Std_Async_BaseAsync_instMonad___closed__6 = (const lean_object*)&l_Std_Async_BaseAsync_instMonad___closed__6_value;
LEAN_EXPORT const lean_object* l_Std_Async_BaseAsync_instMonad = (const lean_object*)&l_Std_Async_BaseAsync_instMonad___closed__6_value;
static const lean_closure_object l_Std_Async_BaseAsync_instMonadLiftBaseIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_BaseAsync_lift___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_BaseAsync_instMonadLiftBaseIO___closed__0 = (const lean_object*)&l_Std_Async_BaseAsync_instMonadLiftBaseIO___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_BaseAsync_instMonadLiftBaseIO = (const lean_object*)&l_Std_Async_BaseAsync_instMonadLiftBaseIO___closed__0_value;
static const lean_closure_object l_Std_Async_BaseAsync_instMonadAwaitTask___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_BaseAsync_await___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_BaseAsync_instMonadAwaitTask___closed__0 = (const lean_object*)&l_Std_Async_BaseAsync_instMonadAwaitTask___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_BaseAsync_instMonadAwaitTask = (const lean_object*)&l_Std_Async_BaseAsync_instMonadAwaitTask___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadAsyncTask___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadAsyncTask___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_BaseAsync_instMonadAsyncTask___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_BaseAsync_instMonadAsyncTask___lam__1___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_MaybeTask_joinTask___redArg___closed__0_value)} };
static const lean_object* l_Std_Async_BaseAsync_instMonadAsyncTask___closed__0 = (const lean_object*)&l_Std_Async_BaseAsync_instMonadAsyncTask___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_BaseAsync_instMonadAsyncTask = (const lean_object*)&l_Std_Async_BaseAsync_instMonadAsyncTask___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instInhabited___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadFinally___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadFinally___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadFinally___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadFinally___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadFinally___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_BaseAsync_instMonadFinally___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_BaseAsync_instMonadFinally___lam__2___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_BaseAsync_instMonadFinally___closed__0 = (const lean_object*)&l_Std_Async_BaseAsync_instMonadFinally___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_BaseAsync_instMonadFinally = (const lean_object*)&l_Std_Async_BaseAsync_instMonadFinally___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofExcept___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofExcept___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofExcept(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofExcept___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_BaseAsync_race___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_BaseAsync_race___redArg___closed__0 = (const lean_object*)&l_Std_Async_BaseAsync_race___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_BaseAsync_await___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0___closed__0 = (const lean_object*)&l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_BaseAsync_concurrentlyAll___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_BaseAsync_instMonad___closed__6_value)} };
static const lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___closed__0 = (const lean_object*)&l_Std_Async_BaseAsync_concurrentlyAll___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toBaseIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toBaseIO___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toBaseIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toBaseIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofTask___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofTask___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofTask(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toEIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toEIO___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toEIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toEIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofETask___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofETask___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofETask(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofETask___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_pure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_pure___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_pure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_map___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_lift___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_lift___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_lift(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_wait___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_wait___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_wait(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_wait___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_asTask___redArg___lam__0(lean_object*);
static const lean_closure_object l_Std_Async_EAsync_asTask___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_asTask___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_asTask___redArg___closed__0 = (const lean_object*)&l_Std_Async_EAsync_asTask___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_asTask___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_asTask___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_asTask(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_asTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_block___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_block___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_block(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_block___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_throw___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_throw___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_throw(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_throw___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_await___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_await___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_await(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_await___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_async___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_async___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_async(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_async___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instFunctor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instFunctor___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_instFunctor___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instFunctor___closed__0_value;
static const lean_closure_object l_Std_Async_EAsync_instFunctor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instFunctor___lam__1___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_EAsync_instFunctor___closed__0_value)} };
static const lean_object* l_Std_Async_EAsync_instFunctor___closed__1 = (const lean_object*)&l_Std_Async_EAsync_instFunctor___closed__1_value;
static const lean_ctor_object l_Std_Async_EAsync_instFunctor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_EAsync_instFunctor___closed__0_value),((lean_object*)&l_Std_Async_EAsync_instFunctor___closed__1_value)}};
static const lean_object* l_Std_Async_EAsync_instFunctor___closed__2 = (const lean_object*)&l_Std_Async_EAsync_instFunctor___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instMonad___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonad___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_instMonad___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonad___closed__0_value;
static const lean_closure_object l_Std_Async_EAsync_instMonad___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonad___lam__2___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_instMonad___closed__1 = (const lean_object*)&l_Std_Async_EAsync_instMonad___closed__1_value;
static const lean_closure_object l_Std_Async_EAsync_instMonad___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonad___lam__5___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_EAsync_instMonad___closed__0_value)} };
static const lean_object* l_Std_Async_EAsync_instMonad___closed__2 = (const lean_object*)&l_Std_Async_EAsync_instMonad___closed__2_value;
static const lean_closure_object l_Std_Async_EAsync_instMonad___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonad___lam__7___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_instMonad___closed__3 = (const lean_object*)&l_Std_Async_EAsync_instMonad___closed__3_value;
static lean_once_cell_t l_Std_Async_EAsync_instMonad___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_EAsync_instMonad___closed__4;
static lean_once_cell_t l_Std_Async_EAsync_instMonad___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_EAsync_instMonad___closed__5;
static const lean_closure_object l_Std_Async_EAsync_instMonad___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_bind___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Async_EAsync_instMonad___closed__6 = (const lean_object*)&l_Std_Async_EAsync_instMonad___closed__6_value;
static lean_once_cell_t l_Std_Async_EAsync_instMonad___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_EAsync_instMonad___closed__7;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad(lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instMonadLiftEIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_lift___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Async_EAsync_instMonadLiftEIO___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonadLiftEIO___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExcept___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExcept___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instMonadExcept___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadExcept___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_instMonadExcept___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonadExcept___closed__0_value;
static const lean_closure_object l_Std_Async_EAsync_instMonadExcept___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_throw___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Async_EAsync_instMonadExcept___closed__1 = (const lean_object*)&l_Std_Async_EAsync_instMonadExcept___closed__1_value;
static const lean_ctor_object l_Std_Async_EAsync_instMonadExcept___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_EAsync_instMonadExcept___closed__1_value),((lean_object*)&l_Std_Async_EAsync_instMonadExcept___closed__0_value)}};
static const lean_object* l_Std_Async_EAsync_instMonadExcept___closed__2 = (const lean_object*)&l_Std_Async_EAsync_instMonadExcept___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExcept(lean_object*);
static const lean_ctor_object l_Std_Async_EAsync_instMonadExceptOf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_EAsync_instMonadExcept___closed__1_value),((lean_object*)&l_Std_Async_EAsync_instMonadExcept___closed__0_value)}};
static const lean_object* l_Std_Async_EAsync_instMonadExceptOf___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonadExceptOf___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExceptOf(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadFinally___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadFinally___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instMonadFinally___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadFinally___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_instMonadFinally___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonadFinally___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadFinally(lean_object*);
static lean_once_cell_t l_Std_Async_EAsync_instOrElse___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_EAsync_instOrElse___closed__0;
static lean_once_cell_t l_Std_Async_EAsync_instOrElse___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_EAsync_instOrElse___closed__1;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instOrElse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instInhabited___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instInhabited(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitETask___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitETask___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instMonadAwaitETask___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadAwaitETask___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_instMonadAwaitETask___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonadAwaitETask___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitETask(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitTask___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitTask___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instMonadAwaitTask___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadAwaitTask___lam__1___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___closed__0_value)} };
static const lean_object* l_Std_Async_EAsync_instMonadAwaitTask___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonadAwaitTask___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitTask(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_EAsync_instMonadAwaitAsyncTaskError = (const lean_object*)&l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitPromise___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitPromise___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instMonadAwaitPromise___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadAwaitPromise___lam__1___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___closed__0_value)} };
static const lean_object* l_Std_Async_EAsync_instMonadAwaitPromise___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonadAwaitPromise___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitPromise(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncETask___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncETask___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instMonadAsyncETask___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadAsyncETask___lam__1___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_EAsync_asTask___redArg___closed__0_value)} };
static const lean_object* l_Std_Async_EAsync_instMonadAsyncETask___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonadAsyncETask___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncETask(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0_value;
static const lean_closure_object l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__1___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0_value)} };
static const lean_object* l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__1 = (const lean_object*)&l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Async_EAsync_instMonadAsyncAsyncTaskError = (const lean_object*)&l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instMonadLiftBaseIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadLiftBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonadLiftBaseIO___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instMonadLiftEIO__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadLiftEIO__1___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonadLiftEIO__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instMonadLiftBaseAsync___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadLiftBaseAsync___lam__1___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___closed__0_value)} };
static const lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonadLiftBaseAsync___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instForInLoopUnit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instForInLoopUnit___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_instForInLoopUnit___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instForInLoopUnit___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofExcept___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofExcept___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofExcept(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofExcept___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_race___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_race___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_race___redArg___closed__0 = (const lean_object*)&l_Std_Async_EAsync_race___redArg___closed__0_value;
static const lean_closure_object l_Std_Async_EAsync_race___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_race___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_race___redArg___closed__1 = (const lean_object*)&l_Std_Async_EAsync_race___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0;
static const lean_closure_object l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_concurrentlyAll___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1 = (const lean_object*)&l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1_value;
static lean_once_cell_t l_Std_Async_EAsync_concurrentlyAll___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___closed__2;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_toIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_toIO___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_toIO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_toIO___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_block___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_block___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_block(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_block___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofAsyncTask___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofAsyncTask___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofAsyncTask(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofAsyncTask___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Async_ofIOTask___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Async_ofIOTask___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_Async_ofIOTask___redArg___closed__0 = (const lean_object*)&l_Std_Async_Async_ofIOTask___redArg___closed__0_value;
static const lean_closure_object l_Std_Async_Async_ofIOTask___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Async_ofIOTask___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_Async_ofIOTask___redArg___closed__0_value)} };
static const lean_object* l_Std_Async_Async_ofIOTask___redArg___closed__1 = (const lean_object*)&l_Std_Async_Async_ofIOTask___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofExcept___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofExcept___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofExcept(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofExcept___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofTask___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofTask___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofTask(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofTask___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPurePromise___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPurePromise___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPurePromise(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPurePromise___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Std_Async_Async_instMonadAsyncAsyncTask = (const lean_object*)&l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Async_instMonadAwaitAsyncTask___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_Async_instMonadAwaitAsyncTask___closed__0 = (const lean_object*)&l_Std_Async_Async_instMonadAwaitAsyncTask___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_Async_instMonadAwaitAsyncTask = (const lean_object*)&l_Std_Async_Async_instMonadAwaitAsyncTask___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitPromise___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitPromise___aux__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitPromise___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitPromise___aux__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Async_instMonadAwaitPromise___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Async_instMonadAwaitPromise___aux__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_Async_instMonadAwaitPromise___closed__0 = (const lean_object*)&l_Std_Async_Async_instMonadAwaitPromise___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_Async_instMonadAwaitPromise = (const lean_object*)&l_Std_Async_Async_instMonadAwaitPromise___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Async_race___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Async_race___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_Async_race___redArg___closed__0 = (const lean_object*)&l_Std_Async_Async_race___redArg___closed__0_value;
static const lean_closure_object l_Std_Async_Async_race___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Async_race___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_Async_race___redArg___closed__1 = (const lean_object*)&l_Std_Async_Async_race___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_race(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_race___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Async_concurrentlyAll___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Async_Async_concurrentlyAll___redArg___lam__0___closed__0 = (const lean_object*)&l_Std_Async_Async_concurrentlyAll___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Async_Async_concurrentlyAll___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_Async_concurrentlyAll___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_background___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_background(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitStateTOfMonad___redArg___lam__0(lean_object* v___y_1_, lean_object* v_toPure_2_, lean_object* v_a_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4_, 0, v_a_3_);
lean_ctor_set(v___x_4_, 1, v___y_1_);
v___x_5_ = lean_apply_2(v_toPure_2_, lean_box(0), v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitStateTOfMonad___redArg___lam__1(lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_00_u03b1_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_toApplicative_11_; lean_object* v_toBind_12_; lean_object* v_toPure_13_; lean_object* v___x_14_; lean_object* v___f_15_; lean_object* v___x_16_; 
v_toApplicative_11_ = lean_ctor_get(v_inst_6_, 0);
lean_inc_ref(v_toApplicative_11_);
v_toBind_12_ = lean_ctor_get(v_inst_6_, 1);
lean_inc(v_toBind_12_);
lean_dec_ref(v_inst_6_);
v_toPure_13_ = lean_ctor_get(v_toApplicative_11_, 1);
lean_inc(v_toPure_13_);
lean_dec_ref(v_toApplicative_11_);
v___x_14_ = lean_apply_2(v_inst_7_, lean_box(0), v___y_9_);
v___f_15_ = lean_alloc_closure((void*)(l_Std_Async_instMonadAwaitStateTOfMonad___redArg___lam__0), 3, 2);
lean_closure_set(v___f_15_, 0, v___y_10_);
lean_closure_set(v___f_15_, 1, v_toPure_13_);
v___x_16_ = lean_apply_4(v_toBind_12_, lean_box(0), lean_box(0), v___x_14_, v___f_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitStateTOfMonad___redArg(lean_object* v_inst_17_, lean_object* v_inst_18_){
_start:
{
lean_object* v___f_19_; 
v___f_19_ = lean_alloc_closure((void*)(l_Std_Async_instMonadAwaitStateTOfMonad___redArg___lam__1), 5, 2);
lean_closure_set(v___f_19_, 0, v_inst_17_);
lean_closure_set(v___f_19_, 1, v_inst_18_);
return v___f_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitStateTOfMonad(lean_object* v_m_20_, lean_object* v_t_21_, lean_object* v_n_22_, lean_object* v_inst_23_, lean_object* v_inst_24_){
_start:
{
lean_object* v___f_25_; 
v___f_25_ = lean_alloc_closure((void*)(l_Std_Async_instMonadAwaitStateTOfMonad___redArg___lam__1), 5, 2);
lean_closure_set(v___f_25_, 0, v_inst_23_);
lean_closure_set(v___f_25_, 1, v_inst_24_);
return v___f_25_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___lam__0(lean_object* v_a_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_27_, 0, v_a_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___lam__1(lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v___f_30_, lean_object* v_00_u03b1_31_, lean_object* v___y_32_){
_start:
{
lean_object* v_toApplicative_33_; lean_object* v_toFunctor_34_; lean_object* v_map_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v_toApplicative_33_ = lean_ctor_get(v_inst_28_, 0);
lean_inc_ref(v_toApplicative_33_);
lean_dec_ref(v_inst_28_);
v_toFunctor_34_ = lean_ctor_get(v_toApplicative_33_, 0);
lean_inc_ref(v_toFunctor_34_);
lean_dec_ref(v_toApplicative_33_);
v_map_35_ = lean_ctor_get(v_toFunctor_34_, 0);
lean_inc(v_map_35_);
lean_dec_ref(v_toFunctor_34_);
v___x_36_ = lean_apply_2(v_inst_29_, lean_box(0), v___y_32_);
v___x_37_ = lean_apply_4(v_map_35_, lean_box(0), lean_box(0), v___f_30_, v___x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitExceptTOfMonad___redArg(lean_object* v_inst_39_, lean_object* v_inst_40_){
_start:
{
lean_object* v___f_41_; lean_object* v___f_42_; 
v___f_41_ = ((lean_object*)(l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___closed__0));
v___f_42_ = lean_alloc_closure((void*)(l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___lam__1), 5, 3);
lean_closure_set(v___f_42_, 0, v_inst_39_);
lean_closure_set(v___f_42_, 1, v_inst_40_);
lean_closure_set(v___f_42_, 2, v___f_41_);
return v___f_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitExceptTOfMonad(lean_object* v_m_43_, lean_object* v_t_44_, lean_object* v_n_45_, lean_object* v_inst_46_, lean_object* v_inst_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Std_Async_instMonadAwaitExceptTOfMonad___redArg(v_inst_46_, v_inst_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitReaderTOfMonad___redArg___lam__0(lean_object* v_inst_49_, lean_object* v_00_u03b1_50_, lean_object* v___y_51_, lean_object* v___y_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lean_apply_2(v_inst_49_, lean_box(0), v___y_51_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitReaderTOfMonad___redArg___lam__0___boxed(lean_object* v_inst_54_, lean_object* v_00_u03b1_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Std_Async_instMonadAwaitReaderTOfMonad___redArg___lam__0(v_inst_54_, v_00_u03b1_55_, v___y_56_, v___y_57_);
lean_dec(v___y_57_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitReaderTOfMonad___redArg(lean_object* v_inst_59_){
_start:
{
lean_object* v___f_60_; 
v___f_60_ = lean_alloc_closure((void*)(l_Std_Async_instMonadAwaitReaderTOfMonad___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_60_, 0, v_inst_59_);
return v___f_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitReaderTOfMonad(lean_object* v_m_61_, lean_object* v_t_62_, lean_object* v_n_63_, lean_object* v_inst_64_, lean_object* v_inst_65_){
_start:
{
lean_object* v___f_66_; 
v___f_66_ = lean_alloc_closure((void*)(l_Std_Async_instMonadAwaitReaderTOfMonad___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_66_, 0, v_inst_65_);
return v___f_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitReaderTOfMonad___boxed(lean_object* v_m_67_, lean_object* v_t_68_, lean_object* v_n_69_, lean_object* v_inst_70_, lean_object* v_inst_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Std_Async_instMonadAwaitReaderTOfMonad(v_m_67_, v_t_68_, v_n_69_, v_inst_70_, v_inst_71_);
lean_dec_ref(v_inst_70_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitStateRefT_x27___redArg(lean_object* v_inst_73_){
_start:
{
lean_object* v___f_74_; 
v___f_74_ = lean_alloc_closure((void*)(l_Std_Async_instMonadAwaitReaderTOfMonad___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_74_, 0, v_inst_73_);
return v___f_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitStateRefT_x27(lean_object* v_t_75_, lean_object* v_m_76_, lean_object* v_s_77_, lean_object* v_n_78_, lean_object* v_inst_79_){
_start:
{
lean_object* v___f_80_; 
v___f_80_ = lean_alloc_closure((void*)(l_Std_Async_instMonadAwaitReaderTOfMonad___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_80_, 0, v_inst_79_);
return v___f_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitStateTOfMonad__1___redArg(lean_object* v_inst_81_, lean_object* v_inst_82_){
_start:
{
lean_object* v___f_83_; 
v___f_83_ = lean_alloc_closure((void*)(l_Std_Async_instMonadAwaitStateTOfMonad___redArg___lam__1), 5, 2);
lean_closure_set(v___f_83_, 0, v_inst_81_);
lean_closure_set(v___f_83_, 1, v_inst_82_);
return v___f_83_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAwaitStateTOfMonad__1(lean_object* v_m_84_, lean_object* v_t_85_, lean_object* v_s_86_, lean_object* v_inst_87_, lean_object* v_inst_88_){
_start:
{
lean_object* v___f_89_; 
v___f_89_ = lean_alloc_closure((void*)(l_Std_Async_instMonadAwaitStateTOfMonad___redArg___lam__1), 5, 2);
lean_closure_set(v___f_89_, 0, v_inst_87_);
lean_closure_set(v___f_89_, 1, v_inst_88_);
return v___f_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAsyncReaderT___redArg___lam__0(lean_object* v_inst_90_, lean_object* v_00_u03b1_91_, lean_object* v_p_92_, lean_object* v_prio_93_, lean_object* v___y_94_){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = lean_apply_1(v_p_92_, v___y_94_);
v___x_96_ = lean_apply_3(v_inst_90_, lean_box(0), v___x_95_, v_prio_93_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAsyncReaderT___redArg(lean_object* v_inst_97_){
_start:
{
lean_object* v___f_98_; 
v___f_98_ = lean_alloc_closure((void*)(l_Std_Async_instMonadAsyncReaderT___redArg___lam__0), 5, 1);
lean_closure_set(v___f_98_, 0, v_inst_97_);
return v___f_98_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAsyncReaderT(lean_object* v_t_99_, lean_object* v_m_100_, lean_object* v_n_101_, lean_object* v_inst_102_){
_start:
{
lean_object* v___f_103_; 
v___f_103_ = lean_alloc_closure((void*)(l_Std_Async_instMonadAsyncReaderT___redArg___lam__0), 5, 1);
lean_closure_set(v___f_103_, 0, v_inst_102_);
return v___f_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAsyncStateRefT_x27___redArg(lean_object* v_inst_104_){
_start:
{
lean_object* v___f_105_; 
v___f_105_ = lean_alloc_closure((void*)(l_Std_Async_instMonadAsyncReaderT___redArg___lam__0), 5, 1);
lean_closure_set(v___f_105_, 0, v_inst_104_);
return v___f_105_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAsyncStateRefT_x27(lean_object* v_t_106_, lean_object* v_m_107_, lean_object* v_s_108_, lean_object* v_n_109_, lean_object* v_inst_110_){
_start:
{
lean_object* v___f_111_; 
v___f_111_ = lean_alloc_closure((void*)(l_Std_Async_instMonadAsyncReaderT___redArg___lam__0), 5, 1);
lean_closure_set(v___f_111_, 0, v_inst_110_);
return v___f_111_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___lam__0(lean_object* v_self_112_){
_start:
{
lean_object* v_fst_113_; 
v_fst_113_ = lean_ctor_get(v_self_112_, 0);
lean_inc(v_fst_113_);
return v_fst_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___lam__0___boxed(lean_object* v_self_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___lam__0(v_self_114_);
lean_dec_ref(v_self_114_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___lam__1(lean_object* v_inst_116_, lean_object* v___f_117_, lean_object* v_s_118_, lean_object* v_toPure_119_, lean_object* v_t_120_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_121_ = l_Functor_mapRev___redArg(v_inst_116_, v_t_120_, v___f_117_);
v___x_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
lean_ctor_set(v___x_122_, 1, v_s_118_);
v___x_123_ = lean_apply_2(v_toPure_119_, lean_box(0), v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___lam__2(lean_object* v_inst_124_, lean_object* v___f_125_, lean_object* v_toPure_126_, lean_object* v_inst_127_, lean_object* v_toBind_128_, lean_object* v_00_u03b1_129_, lean_object* v_p_130_, lean_object* v_prio_131_, lean_object* v_s_132_){
_start:
{
lean_object* v___f_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
lean_inc(v_s_132_);
v___f_133_ = lean_alloc_closure((void*)(l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_133_, 0, v_inst_124_);
lean_closure_set(v___f_133_, 1, v___f_125_);
lean_closure_set(v___f_133_, 2, v_s_132_);
lean_closure_set(v___f_133_, 3, v_toPure_126_);
v___x_134_ = lean_apply_1(v_p_130_, v_s_132_);
v___x_135_ = lean_apply_3(v_inst_127_, lean_box(0), v___x_134_, v_prio_131_);
v___x_136_ = lean_apply_4(v_toBind_128_, lean_box(0), lean_box(0), v___x_135_, v___f_133_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg(lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_inst_140_){
_start:
{
lean_object* v_toApplicative_141_; lean_object* v_toBind_142_; lean_object* v_toPure_143_; lean_object* v___f_144_; lean_object* v___f_145_; 
v_toApplicative_141_ = lean_ctor_get(v_inst_138_, 0);
lean_inc_ref(v_toApplicative_141_);
v_toBind_142_ = lean_ctor_get(v_inst_138_, 1);
lean_inc(v_toBind_142_);
lean_dec_ref(v_inst_138_);
v_toPure_143_ = lean_ctor_get(v_toApplicative_141_, 1);
lean_inc(v_toPure_143_);
lean_dec_ref(v_toApplicative_141_);
v___f_144_ = ((lean_object*)(l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___closed__0));
v___f_145_ = lean_alloc_closure((void*)(l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___lam__2), 9, 5);
lean_closure_set(v___f_145_, 0, v_inst_139_);
lean_closure_set(v___f_145_, 1, v___f_144_);
lean_closure_set(v___f_145_, 2, v_toPure_143_);
lean_closure_set(v___f_145_, 3, v_inst_140_);
lean_closure_set(v___f_145_, 4, v_toBind_142_);
return v___f_145_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor(lean_object* v_m_146_, lean_object* v_t_147_, lean_object* v_s_148_, lean_object* v_inst_149_, lean_object* v_inst_150_, lean_object* v_inst_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg(v_inst_149_, v_inst_150_, v_inst_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_pure___redArg(lean_object* v_x_153_){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_154_, 0, v_x_153_);
v___x_155_ = lean_task_pure(v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_pure(lean_object* v_00_u03b1_156_, lean_object* v_00_u03b5_157_, lean_object* v_x_158_){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_159_, 0, v_x_158_);
v___x_160_ = lean_task_pure(v___x_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_map___redArg___lam__0(lean_object* v_f_161_, lean_object* v_x_162_){
_start:
{
if (lean_obj_tag(v_x_162_) == 0)
{
lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_170_; 
lean_dec(v_f_161_);
v_a_163_ = lean_ctor_get(v_x_162_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v_x_162_);
if (v_isSharedCheck_170_ == 0)
{
v___x_165_ = v_x_162_;
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_dec(v_x_162_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_168_; 
if (v_isShared_166_ == 0)
{
v___x_168_ = v___x_165_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_a_163_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_179_; 
v_a_171_ = lean_ctor_get(v_x_162_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v_x_162_);
if (v_isSharedCheck_179_ == 0)
{
v___x_173_ = v_x_162_;
v_isShared_174_ = v_isSharedCheck_179_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v_x_162_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_179_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_175_ = lean_apply_1(v_f_161_, v_a_171_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 0, v___x_175_);
v___x_177_ = v___x_173_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_map___redArg(lean_object* v_f_180_, lean_object* v_x_181_, lean_object* v_prio_182_, uint8_t v_sync_183_){
_start:
{
lean_object* v___f_184_; lean_object* v___x_185_; 
v___f_184_ = lean_alloc_closure((void*)(l_Std_Async_ETask_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_184_, 0, v_f_180_);
v___x_185_ = lean_task_map(v___f_184_, v_x_181_, v_prio_182_, v_sync_183_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_map___redArg___boxed(lean_object* v_f_186_, lean_object* v_x_187_, lean_object* v_prio_188_, lean_object* v_sync_189_){
_start:
{
uint8_t v_sync_boxed_190_; lean_object* v_res_191_; 
v_sync_boxed_190_ = lean_unbox(v_sync_189_);
v_res_191_ = l_Std_Async_ETask_map___redArg(v_f_186_, v_x_187_, v_prio_188_, v_sync_boxed_190_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_map(lean_object* v_00_u03b1_192_, lean_object* v_00_u03b2_193_, lean_object* v_00_u03b5_194_, lean_object* v_f_195_, lean_object* v_x_196_, lean_object* v_prio_197_, uint8_t v_sync_198_){
_start:
{
lean_object* v___f_199_; lean_object* v___x_200_; 
v___f_199_ = lean_alloc_closure((void*)(l_Std_Async_ETask_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_199_, 0, v_f_195_);
v___x_200_ = lean_task_map(v___f_199_, v_x_196_, v_prio_197_, v_sync_198_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_map___boxed(lean_object* v_00_u03b1_201_, lean_object* v_00_u03b2_202_, lean_object* v_00_u03b5_203_, lean_object* v_f_204_, lean_object* v_x_205_, lean_object* v_prio_206_, lean_object* v_sync_207_){
_start:
{
uint8_t v_sync_boxed_208_; lean_object* v_res_209_; 
v_sync_boxed_208_ = lean_unbox(v_sync_207_);
v_res_209_ = l_Std_Async_ETask_map(v_00_u03b1_201_, v_00_u03b2_202_, v_00_u03b5_203_, v_f_204_, v_x_205_, v_prio_206_, v_sync_boxed_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_bind___redArg___lam__0(lean_object* v_f_210_, lean_object* v_x_211_){
_start:
{
if (lean_obj_tag(v_x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_220_; 
lean_dec_ref(v_f_210_);
v_a_212_ = lean_ctor_get(v_x_211_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v_x_211_);
if (v_isSharedCheck_220_ == 0)
{
v___x_214_ = v_x_211_;
v_isShared_215_ = v_isSharedCheck_220_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v_x_211_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_220_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_212_);
v___x_217_ = v_reuseFailAlloc_219_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
lean_object* v___x_218_; 
v___x_218_ = lean_task_pure(v___x_217_);
return v___x_218_;
}
}
}
else
{
lean_object* v_a_221_; lean_object* v___x_222_; 
v_a_221_ = lean_ctor_get(v_x_211_, 0);
lean_inc(v_a_221_);
lean_dec_ref(v_x_211_);
v___x_222_ = lean_apply_1(v_f_210_, v_a_221_);
return v___x_222_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_bind___redArg(lean_object* v_x_223_, lean_object* v_f_224_, lean_object* v_prio_225_, uint8_t v_sync_226_){
_start:
{
lean_object* v___f_227_; lean_object* v___x_228_; 
v___f_227_ = lean_alloc_closure((void*)(l_Std_Async_ETask_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_227_, 0, v_f_224_);
v___x_228_ = lean_task_bind(v_x_223_, v___f_227_, v_prio_225_, v_sync_226_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_bind___redArg___boxed(lean_object* v_x_229_, lean_object* v_f_230_, lean_object* v_prio_231_, lean_object* v_sync_232_){
_start:
{
uint8_t v_sync_boxed_233_; lean_object* v_res_234_; 
v_sync_boxed_233_ = lean_unbox(v_sync_232_);
v_res_234_ = l_Std_Async_ETask_bind___redArg(v_x_229_, v_f_230_, v_prio_231_, v_sync_boxed_233_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_bind(lean_object* v_00_u03b5_235_, lean_object* v_00_u03b1_236_, lean_object* v_00_u03b2_237_, lean_object* v_x_238_, lean_object* v_f_239_, lean_object* v_prio_240_, uint8_t v_sync_241_){
_start:
{
lean_object* v___f_242_; lean_object* v___x_243_; 
v___f_242_ = lean_alloc_closure((void*)(l_Std_Async_ETask_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_242_, 0, v_f_239_);
v___x_243_ = lean_task_bind(v_x_238_, v___f_242_, v_prio_240_, v_sync_241_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_bind___boxed(lean_object* v_00_u03b5_244_, lean_object* v_00_u03b1_245_, lean_object* v_00_u03b2_246_, lean_object* v_x_247_, lean_object* v_f_248_, lean_object* v_prio_249_, lean_object* v_sync_250_){
_start:
{
uint8_t v_sync_boxed_251_; lean_object* v_res_252_; 
v_sync_boxed_251_ = lean_unbox(v_sync_250_);
v_res_252_ = l_Std_Async_ETask_bind(v_00_u03b5_244_, v_00_u03b1_245_, v_00_u03b2_246_, v_x_247_, v_f_248_, v_prio_249_, v_sync_boxed_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_bindEIO___redArg___lam__0(lean_object* v_f_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_a_257_; 
if (lean_obj_tag(v_a_254_) == 0)
{
lean_object* v_a_260_; 
lean_dec_ref(v_f_253_);
v_a_260_ = lean_ctor_get(v_a_254_, 0);
lean_inc(v_a_260_);
lean_dec_ref(v_a_254_);
v_a_257_ = v_a_260_;
goto v___jp_256_;
}
else
{
lean_object* v_a_261_; lean_object* v___x_262_; 
v_a_261_ = lean_ctor_get(v_a_254_, 0);
lean_inc(v_a_261_);
lean_dec_ref(v_a_254_);
v___x_262_ = lean_apply_2(v_f_253_, v_a_261_, lean_box(0));
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_a_263_);
lean_dec_ref(v___x_262_);
return v_a_263_;
}
else
{
lean_object* v_a_264_; 
v_a_264_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_a_264_);
lean_dec_ref(v___x_262_);
v_a_257_ = v_a_264_;
goto v___jp_256_;
}
}
v___jp_256_:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v_a_257_);
v___x_259_ = lean_task_pure(v___x_258_);
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_bindEIO___redArg___lam__0___boxed(lean_object* v_f_265_, lean_object* v_a_266_, lean_object* v___y_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Std_Async_ETask_bindEIO___redArg___lam__0(v_f_265_, v_a_266_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_bindEIO___redArg(lean_object* v_x_269_, lean_object* v_f_270_, lean_object* v_prio_271_, uint8_t v_sync_272_){
_start:
{
lean_object* v___f_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___f_274_ = lean_alloc_closure((void*)(l_Std_Async_ETask_bindEIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_274_, 0, v_f_270_);
v___x_275_ = lean_io_bind_task(v_x_269_, v___f_274_, v_prio_271_, v_sync_272_);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_bindEIO___redArg___boxed(lean_object* v_x_277_, lean_object* v_f_278_, lean_object* v_prio_279_, lean_object* v_sync_280_, lean_object* v_a_281_){
_start:
{
uint8_t v_sync_boxed_282_; lean_object* v_res_283_; 
v_sync_boxed_282_ = lean_unbox(v_sync_280_);
v_res_283_ = l_Std_Async_ETask_bindEIO___redArg(v_x_277_, v_f_278_, v_prio_279_, v_sync_boxed_282_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_bindEIO(lean_object* v_00_u03b5_284_, lean_object* v_00_u03b1_285_, lean_object* v_00_u03b2_286_, lean_object* v_x_287_, lean_object* v_f_288_, lean_object* v_prio_289_, uint8_t v_sync_290_){
_start:
{
lean_object* v___f_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___f_292_ = lean_alloc_closure((void*)(l_Std_Async_ETask_bindEIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_292_, 0, v_f_288_);
v___x_293_ = lean_io_bind_task(v_x_287_, v___f_292_, v_prio_289_, v_sync_290_);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_bindEIO___boxed(lean_object* v_00_u03b5_295_, lean_object* v_00_u03b1_296_, lean_object* v_00_u03b2_297_, lean_object* v_x_298_, lean_object* v_f_299_, lean_object* v_prio_300_, lean_object* v_sync_301_, lean_object* v_a_302_){
_start:
{
uint8_t v_sync_boxed_303_; lean_object* v_res_304_; 
v_sync_boxed_303_ = lean_unbox(v_sync_301_);
v_res_304_ = l_Std_Async_ETask_bindEIO(v_00_u03b5_295_, v_00_u03b1_296_, v_00_u03b2_297_, v_x_298_, v_f_299_, v_prio_300_, v_sync_boxed_303_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_mapEIO___redArg___lam__0(lean_object* v_f_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_a_309_; 
if (lean_obj_tag(v_a_306_) == 0)
{
lean_object* v_a_311_; 
lean_dec_ref(v_f_305_);
v_a_311_ = lean_ctor_get(v_a_306_, 0);
lean_inc(v_a_311_);
lean_dec_ref(v_a_306_);
v_a_309_ = v_a_311_;
goto v___jp_308_;
}
else
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_322_; 
v_a_312_ = lean_ctor_get(v_a_306_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v_a_306_);
if (v_isSharedCheck_322_ == 0)
{
v___x_314_ = v_a_306_;
v_isShared_315_ = v_isSharedCheck_322_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v_a_306_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_322_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; 
v___x_316_ = lean_apply_2(v_f_305_, v_a_312_, lean_box(0));
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; lean_object* v___x_319_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_a_317_);
lean_dec_ref(v___x_316_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v_a_317_);
v___x_319_ = v___x_314_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
else
{
lean_object* v_a_321_; 
lean_del_object(v___x_314_);
v_a_321_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_a_321_);
lean_dec_ref(v___x_316_);
v_a_309_ = v_a_321_;
goto v___jp_308_;
}
}
}
v___jp_308_:
{
lean_object* v___x_310_; 
v___x_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_310_, 0, v_a_309_);
return v___x_310_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_mapEIO___redArg___lam__0___boxed(lean_object* v_f_323_, lean_object* v_a_324_, lean_object* v___y_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Std_Async_ETask_mapEIO___redArg___lam__0(v_f_323_, v_a_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_mapEIO___redArg(lean_object* v_f_327_, lean_object* v_x_328_, lean_object* v_prio_329_, uint8_t v_sync_330_){
_start:
{
lean_object* v___f_332_; lean_object* v___x_333_; 
v___f_332_ = lean_alloc_closure((void*)(l_Std_Async_ETask_mapEIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_332_, 0, v_f_327_);
v___x_333_ = lean_io_map_task(v___f_332_, v_x_328_, v_prio_329_, v_sync_330_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_mapEIO___redArg___boxed(lean_object* v_f_334_, lean_object* v_x_335_, lean_object* v_prio_336_, lean_object* v_sync_337_, lean_object* v_a_338_){
_start:
{
uint8_t v_sync_boxed_339_; lean_object* v_res_340_; 
v_sync_boxed_339_ = lean_unbox(v_sync_337_);
v_res_340_ = l_Std_Async_ETask_mapEIO___redArg(v_f_334_, v_x_335_, v_prio_336_, v_sync_boxed_339_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_mapEIO(lean_object* v_00_u03b1_341_, lean_object* v_00_u03b5_342_, lean_object* v_00_u03b2_343_, lean_object* v_f_344_, lean_object* v_x_345_, lean_object* v_prio_346_, uint8_t v_sync_347_){
_start:
{
lean_object* v___f_349_; lean_object* v___x_350_; 
v___f_349_ = lean_alloc_closure((void*)(l_Std_Async_ETask_mapEIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_349_, 0, v_f_344_);
v___x_350_ = lean_io_map_task(v___f_349_, v_x_345_, v_prio_346_, v_sync_347_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_mapEIO___boxed(lean_object* v_00_u03b1_351_, lean_object* v_00_u03b5_352_, lean_object* v_00_u03b2_353_, lean_object* v_f_354_, lean_object* v_x_355_, lean_object* v_prio_356_, lean_object* v_sync_357_, lean_object* v_a_358_){
_start:
{
uint8_t v_sync_boxed_359_; lean_object* v_res_360_; 
v_sync_boxed_359_ = lean_unbox(v_sync_357_);
v_res_360_ = l_Std_Async_ETask_mapEIO(v_00_u03b1_351_, v_00_u03b5_352_, v_00_u03b2_353_, v_f_354_, v_x_355_, v_prio_356_, v_sync_boxed_359_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_block___redArg(lean_object* v_x_361_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = lean_task_get_own(v_x_361_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_363_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_363_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
lean_ctor_set_tag(v___x_366_, 1);
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
else
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
v_a_372_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_363_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_363_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
lean_ctor_set_tag(v___x_374_, 0);
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_block___redArg___boxed(lean_object* v_x_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Std_Async_ETask_block___redArg(v_x_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_block(lean_object* v_00_u03b5_383_, lean_object* v_00_u03b1_384_, lean_object* v_x_385_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = lean_task_get_own(v_x_385_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_387_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_387_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
lean_ctor_set_tag(v___x_390_, 1);
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
else
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
v_a_396_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_387_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_387_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
lean_ctor_set_tag(v___x_398_, 0);
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_block___boxed(lean_object* v_00_u03b5_404_, lean_object* v_00_u03b1_405_, lean_object* v_x_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Std_Async_ETask_block(v_00_u03b5_404_, v_00_u03b1_405_, v_x_406_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_ofPromise_x21___redArg(lean_object* v_x_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_IO_Promise_result_x21___redArg(v_x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_ofPromise_x21___redArg___boxed(lean_object* v_x_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Std_Async_ETask_ofPromise_x21___redArg(v_x_411_);
lean_dec(v_x_411_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_ofPromise_x21(lean_object* v_00_u03b5_413_, lean_object* v_00_u03b1_414_, lean_object* v_x_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_IO_Promise_result_x21___redArg(v_x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_ofPromise_x21___boxed(lean_object* v_00_u03b5_417_, lean_object* v_00_u03b1_418_, lean_object* v_x_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Std_Async_ETask_ofPromise_x21(v_00_u03b5_417_, v_00_u03b1_418_, v_x_419_);
lean_dec(v_x_419_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_ofPurePromise___redArg(lean_object* v_x_422_){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; lean_object* v___x_427_; 
v___x_423_ = ((lean_object*)(l_Std_Async_ETask_ofPurePromise___redArg___closed__0));
v___x_424_ = l_IO_Promise_result_x21___redArg(v_x_422_);
v___x_425_ = lean_unsigned_to_nat(0u);
v___x_426_ = 1;
v___x_427_ = lean_task_map(v___x_423_, v___x_424_, v___x_425_, v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_ofPurePromise___redArg___boxed(lean_object* v_x_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Std_Async_ETask_ofPurePromise___redArg(v_x_428_);
lean_dec(v_x_428_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_ofPurePromise(lean_object* v_00_u03b1_430_, lean_object* v_00_u03b5_431_, lean_object* v_x_432_){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; uint8_t v___x_436_; lean_object* v___x_437_; 
v___x_433_ = ((lean_object*)(l_Std_Async_ETask_ofPurePromise___redArg___closed__0));
v___x_434_ = l_IO_Promise_result_x21___redArg(v_x_432_);
v___x_435_ = lean_unsigned_to_nat(0u);
v___x_436_ = 1;
v___x_437_ = lean_task_map(v___x_433_, v___x_434_, v___x_435_, v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_ofPurePromise___boxed(lean_object* v_00_u03b1_438_, lean_object* v_00_u03b5_439_, lean_object* v_x_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Std_Async_ETask_ofPurePromise(v_00_u03b1_438_, v_00_u03b5_439_, v_x_440_);
lean_dec(v_x_440_);
return v_res_441_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_ETask_getState___redArg(lean_object* v_x_442_){
_start:
{
uint8_t v___x_444_; 
v___x_444_ = lean_io_get_task_state(v_x_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_getState___redArg___boxed(lean_object* v_x_445_, lean_object* v_a_446_){
_start:
{
uint8_t v_res_447_; lean_object* v_r_448_; 
v_res_447_ = l_Std_Async_ETask_getState___redArg(v_x_445_);
lean_dec_ref(v_x_445_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_ETask_getState(lean_object* v_00_u03b5_449_, lean_object* v_00_u03b1_450_, lean_object* v_x_451_){
_start:
{
uint8_t v___x_453_; 
v___x_453_ = lean_io_get_task_state(v_x_451_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_getState___boxed(lean_object* v_00_u03b5_454_, lean_object* v_00_u03b1_455_, lean_object* v_x_456_, lean_object* v_a_457_){
_start:
{
uint8_t v_res_458_; lean_object* v_r_459_; 
v_res_458_ = l_Std_Async_ETask_getState(v_00_u03b5_454_, v_00_u03b1_455_, v_x_456_);
lean_dec_ref(v_x_456_);
v_r_459_ = lean_box(v_res_458_);
return v_r_459_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instFunctor___lam__1(lean_object* v_00_u03b1_460_, lean_object* v_00_u03b2_461_, lean_object* v_f_462_, lean_object* v_x_463_){
_start:
{
lean_object* v___f_464_; lean_object* v___x_465_; uint8_t v___x_466_; lean_object* v___x_467_; 
v___f_464_ = lean_alloc_closure((void*)(l_Std_Async_ETask_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_464_, 0, v_f_462_);
v___x_465_ = lean_unsigned_to_nat(0u);
v___x_466_ = 0;
v___x_467_ = lean_task_map(v___f_464_, v_x_463_, v___x_465_, v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instFunctor___lam__0(lean_object* v___f_468_, lean_object* v_00_u03b1_469_, lean_object* v_00_u03b2_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_473_, 0, lean_box(0));
lean_closure_set(v___x_473_, 1, lean_box(0));
lean_closure_set(v___x_473_, 2, v___y_471_);
v___x_474_ = lean_apply_4(v___f_468_, lean_box(0), lean_box(0), v___x_473_, v___y_472_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instFunctor(lean_object* v_00_u03b5_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = ((lean_object*)(l_Std_Async_ETask_instFunctor___closed__2));
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___lam__0(lean_object* v_00_u03b1_483_, lean_object* v___y_484_){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_485_, 0, v___y_484_);
v___x_486_ = lean_task_pure(v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___lam__1(lean_object* v_a_487_, lean_object* v_x_488_){
_start:
{
if (lean_obj_tag(v_x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
lean_dec(v_a_487_);
v_a_489_ = lean_ctor_get(v_x_488_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v_x_488_);
if (v_isSharedCheck_496_ == 0)
{
v___x_491_ = v_x_488_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v_x_488_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_489_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_505_; 
v_a_497_ = lean_ctor_get(v_x_488_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v_x_488_);
if (v_isSharedCheck_505_ == 0)
{
v___x_499_ = v_x_488_;
v_isShared_500_ = v_isSharedCheck_505_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v_x_488_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_505_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_501_ = lean_apply_1(v_a_487_, v_a_497_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_501_);
v___x_503_ = v___x_499_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___lam__2(lean_object* v_x_506_, lean_object* v_x_507_){
_start:
{
if (lean_obj_tag(v_x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_516_; 
lean_dec_ref(v_x_506_);
v_a_508_ = lean_ctor_get(v_x_507_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v_x_507_);
if (v_isSharedCheck_516_ == 0)
{
v___x_510_ = v_x_507_;
v_isShared_511_ = v_isSharedCheck_516_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v_x_507_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_516_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_515_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_514_; 
v___x_514_ = lean_task_pure(v___x_513_);
return v___x_514_;
}
}
}
else
{
lean_object* v_a_517_; lean_object* v___f_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; lean_object* v___x_523_; 
v_a_517_ = lean_ctor_get(v_x_507_, 0);
lean_inc(v_a_517_);
lean_dec_ref(v_x_507_);
v___f_518_ = lean_alloc_closure((void*)(l_Std_Async_ETask_instMonad___lam__1), 2, 1);
lean_closure_set(v___f_518_, 0, v_a_517_);
v___x_519_ = lean_box(0);
v___x_520_ = lean_apply_1(v_x_506_, v___x_519_);
v___x_521_ = lean_unsigned_to_nat(0u);
v___x_522_ = 0;
v___x_523_ = lean_task_map(v___f_518_, v___x_520_, v___x_521_, v___x_522_);
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___lam__3(lean_object* v_00_u03b1_524_, lean_object* v_00_u03b2_525_, lean_object* v_f_526_, lean_object* v_x_527_){
_start:
{
lean_object* v___f_528_; lean_object* v___x_529_; uint8_t v___x_530_; lean_object* v___x_531_; 
v___f_528_ = lean_alloc_closure((void*)(l_Std_Async_ETask_instMonad___lam__2), 2, 1);
lean_closure_set(v___f_528_, 0, v_x_527_);
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = 0;
v___x_531_ = lean_task_bind(v_f_526_, v___f_528_, v___x_529_, v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___lam__5(lean_object* v_00_u03b1_532_, lean_object* v_00_u03b2_533_, lean_object* v_x_534_, lean_object* v_f_535_){
_start:
{
lean_object* v___f_536_; lean_object* v___x_537_; uint8_t v___x_538_; lean_object* v___x_539_; 
v___f_536_ = lean_alloc_closure((void*)(l_Std_Async_ETask_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_536_, 0, v_f_535_);
v___x_537_ = lean_unsigned_to_nat(0u);
v___x_538_ = 0;
v___x_539_ = lean_task_bind(v_x_534_, v___f_536_, v___x_537_, v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___lam__4(lean_object* v___f_540_, lean_object* v_a_541_, lean_object* v_x_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = lean_apply_2(v___f_540_, lean_box(0), v_a_541_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___lam__4___boxed(lean_object* v___f_544_, lean_object* v_a_545_, lean_object* v_x_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Std_Async_ETask_instMonad___lam__4(v___f_544_, v_a_545_, v_x_546_);
lean_dec(v_x_546_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___lam__6(lean_object* v___f_548_, lean_object* v_y_549_, lean_object* v___f_550_, lean_object* v_a_551_){
_start:
{
lean_object* v___f_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___f_552_ = lean_alloc_closure((void*)(l_Std_Async_ETask_instMonad___lam__4___boxed), 3, 2);
lean_closure_set(v___f_552_, 0, v___f_548_);
lean_closure_set(v___f_552_, 1, v_a_551_);
v___x_553_ = lean_box(0);
v___x_554_ = lean_apply_1(v_y_549_, v___x_553_);
v___x_555_ = lean_apply_4(v___f_550_, lean_box(0), lean_box(0), v___x_554_, v___f_552_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___lam__7(lean_object* v___f_556_, lean_object* v___f_557_, lean_object* v_00_u03b1_558_, lean_object* v_00_u03b2_559_, lean_object* v_x_560_, lean_object* v_y_561_){
_start:
{
lean_object* v___f_562_; lean_object* v___x_563_; 
lean_inc_ref(v___f_557_);
v___f_562_ = lean_alloc_closure((void*)(l_Std_Async_ETask_instMonad___lam__6), 4, 3);
lean_closure_set(v___f_562_, 0, v___f_556_);
lean_closure_set(v___f_562_, 1, v_y_561_);
lean_closure_set(v___f_562_, 2, v___f_557_);
v___x_563_ = lean_apply_4(v___f_557_, lean_box(0), lean_box(0), v_x_560_, v___f_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___lam__8(lean_object* v_y_564_, lean_object* v_x_565_){
_start:
{
if (lean_obj_tag(v_x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_574_; 
lean_dec_ref(v_y_564_);
v_a_566_ = lean_ctor_get(v_x_565_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v_x_565_);
if (v_isSharedCheck_574_ == 0)
{
v___x_568_ = v_x_565_;
v_isShared_569_ = v_isSharedCheck_574_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v_x_565_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_574_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_566_);
v___x_571_ = v_reuseFailAlloc_573_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
lean_object* v___x_572_; 
v___x_572_ = lean_task_pure(v___x_571_);
return v___x_572_;
}
}
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; 
lean_dec_ref(v_x_565_);
v___x_575_ = lean_box(0);
v___x_576_ = lean_apply_1(v_y_564_, v___x_575_);
return v___x_576_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___lam__9(lean_object* v_00_u03b1_577_, lean_object* v_00_u03b2_578_, lean_object* v_x_579_, lean_object* v_y_580_){
_start:
{
lean_object* v___f_581_; lean_object* v___x_582_; uint8_t v___x_583_; lean_object* v___x_584_; 
v___f_581_ = lean_alloc_closure((void*)(l_Std_Async_ETask_instMonad___lam__8), 2, 1);
lean_closure_set(v___f_581_, 0, v_y_580_);
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = 0;
v___x_584_ = lean_task_bind(v_x_579_, v___f_581_, v___x_582_, v___x_583_);
return v___x_584_;
}
}
static lean_object* _init_l_Std_Async_ETask_instMonad___closed__5(void){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Std_Async_ETask_instFunctor(lean_box(0));
return v___x_592_;
}
}
static lean_object* _init_l_Std_Async_ETask_instMonad___closed__6(void){
_start:
{
lean_object* v___f_593_; lean_object* v___f_594_; lean_object* v___f_595_; lean_object* v___f_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___f_593_ = ((lean_object*)(l_Std_Async_ETask_instMonad___closed__4));
v___f_594_ = ((lean_object*)(l_Std_Async_ETask_instMonad___closed__3));
v___f_595_ = ((lean_object*)(l_Std_Async_ETask_instMonad___closed__1));
v___f_596_ = ((lean_object*)(l_Std_Async_ETask_instMonad___closed__0));
v___x_597_ = lean_obj_once(&l_Std_Async_ETask_instMonad___closed__5, &l_Std_Async_ETask_instMonad___closed__5_once, _init_l_Std_Async_ETask_instMonad___closed__5);
v___x_598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
lean_ctor_set(v___x_598_, 1, v___f_596_);
lean_ctor_set(v___x_598_, 2, v___f_595_);
lean_ctor_set(v___x_598_, 3, v___f_594_);
lean_ctor_set(v___x_598_, 4, v___f_593_);
return v___x_598_;
}
}
static lean_object* _init_l_Std_Async_ETask_instMonad___closed__7(void){
_start:
{
lean_object* v___f_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___f_599_ = ((lean_object*)(l_Std_Async_ETask_instMonad___closed__2));
v___x_600_ = lean_obj_once(&l_Std_Async_ETask_instMonad___closed__6, &l_Std_Async_ETask_instMonad___closed__6_once, _init_l_Std_Async_ETask_instMonad___closed__6);
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v___f_599_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad(lean_object* v_00_u03b5_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = lean_obj_once(&l_Std_Async_ETask_instMonad___closed__7, &l_Std_Async_ETask_instMonad___closed__7_once, _init_l_Std_Async_ETask_instMonad___closed__7);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapIO___redArg___lam__0(lean_object* v_f_604_, lean_object* v_a_605_){
_start:
{
lean_object* v_a_608_; 
if (lean_obj_tag(v_a_605_) == 0)
{
lean_object* v_a_610_; 
lean_dec_ref(v_f_604_);
v_a_610_ = lean_ctor_get(v_a_605_, 0);
lean_inc(v_a_610_);
lean_dec_ref(v_a_605_);
v_a_608_ = v_a_610_;
goto v___jp_607_;
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_621_; 
v_a_611_ = lean_ctor_get(v_a_605_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v_a_605_);
if (v_isSharedCheck_621_ == 0)
{
v___x_613_ = v_a_605_;
v_isShared_614_ = v_isSharedCheck_621_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v_a_605_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_621_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; 
v___x_615_ = lean_apply_2(v_f_604_, v_a_611_, lean_box(0));
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_618_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_616_);
lean_dec_ref(v___x_615_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v_a_616_);
v___x_618_ = v___x_613_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
else
{
lean_object* v_a_620_; 
lean_del_object(v___x_613_);
v_a_620_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_620_);
lean_dec_ref(v___x_615_);
v_a_608_ = v_a_620_;
goto v___jp_607_;
}
}
}
v___jp_607_:
{
lean_object* v___x_609_; 
v___x_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_609_, 0, v_a_608_);
return v___x_609_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapIO___redArg___lam__0___boxed(lean_object* v_f_622_, lean_object* v_a_623_, lean_object* v___y_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Std_Async_AsyncTask_mapIO___redArg___lam__0(v_f_622_, v_a_623_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapIO___redArg(lean_object* v_f_626_, lean_object* v_x_627_, lean_object* v_prio_628_, uint8_t v_sync_629_){
_start:
{
lean_object* v___f_631_; lean_object* v___x_632_; 
v___f_631_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_mapIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_631_, 0, v_f_626_);
v___x_632_ = lean_io_map_task(v___f_631_, v_x_627_, v_prio_628_, v_sync_629_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapIO___redArg___boxed(lean_object* v_f_633_, lean_object* v_x_634_, lean_object* v_prio_635_, lean_object* v_sync_636_, lean_object* v_a_637_){
_start:
{
uint8_t v_sync_boxed_638_; lean_object* v_res_639_; 
v_sync_boxed_638_ = lean_unbox(v_sync_636_);
v_res_639_ = l_Std_Async_AsyncTask_mapIO___redArg(v_f_633_, v_x_634_, v_prio_635_, v_sync_boxed_638_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapIO(lean_object* v_00_u03b1_640_, lean_object* v_00_u03b2_641_, lean_object* v_f_642_, lean_object* v_x_643_, lean_object* v_prio_644_, uint8_t v_sync_645_){
_start:
{
lean_object* v___f_647_; lean_object* v___x_648_; 
v___f_647_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_mapIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_647_, 0, v_f_642_);
v___x_648_ = lean_io_map_task(v___f_647_, v_x_643_, v_prio_644_, v_sync_645_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapIO___boxed(lean_object* v_00_u03b1_649_, lean_object* v_00_u03b2_650_, lean_object* v_f_651_, lean_object* v_x_652_, lean_object* v_prio_653_, lean_object* v_sync_654_, lean_object* v_a_655_){
_start:
{
uint8_t v_sync_boxed_656_; lean_object* v_res_657_; 
v_sync_boxed_656_ = lean_unbox(v_sync_654_);
v_res_657_ = l_Std_Async_AsyncTask_mapIO(v_00_u03b1_649_, v_00_u03b2_650_, v_f_651_, v_x_652_, v_prio_653_, v_sync_boxed_656_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_pure___redArg(lean_object* v_x_658_){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_659_, 0, v_x_658_);
v___x_660_ = lean_task_pure(v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_pure(lean_object* v_00_u03b1_661_, lean_object* v_x_662_){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_663_, 0, v_x_662_);
v___x_664_ = lean_task_pure(v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bind___redArg___lam__0(lean_object* v_f_665_, lean_object* v_x_666_){
_start:
{
if (lean_obj_tag(v_x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_675_; 
lean_dec_ref(v_f_665_);
v_a_667_ = lean_ctor_get(v_x_666_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v_x_666_);
if (v_isSharedCheck_675_ == 0)
{
v___x_669_ = v_x_666_;
v_isShared_670_ = v_isSharedCheck_675_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v_x_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_675_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_674_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_673_; 
v___x_673_ = lean_task_pure(v___x_672_);
return v___x_673_;
}
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_677_; 
v_a_676_ = lean_ctor_get(v_x_666_, 0);
lean_inc(v_a_676_);
lean_dec_ref(v_x_666_);
v___x_677_ = lean_apply_1(v_f_665_, v_a_676_);
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bind___redArg(lean_object* v_x_678_, lean_object* v_f_679_, lean_object* v_prio_680_, uint8_t v_sync_681_){
_start:
{
lean_object* v___f_682_; lean_object* v___x_683_; 
v___f_682_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_682_, 0, v_f_679_);
v___x_683_ = lean_task_bind(v_x_678_, v___f_682_, v_prio_680_, v_sync_681_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bind___redArg___boxed(lean_object* v_x_684_, lean_object* v_f_685_, lean_object* v_prio_686_, lean_object* v_sync_687_){
_start:
{
uint8_t v_sync_boxed_688_; lean_object* v_res_689_; 
v_sync_boxed_688_ = lean_unbox(v_sync_687_);
v_res_689_ = l_Std_Async_AsyncTask_bind___redArg(v_x_684_, v_f_685_, v_prio_686_, v_sync_boxed_688_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bind(lean_object* v_00_u03b1_690_, lean_object* v_00_u03b2_691_, lean_object* v_x_692_, lean_object* v_f_693_, lean_object* v_prio_694_, uint8_t v_sync_695_){
_start:
{
lean_object* v___f_696_; lean_object* v___x_697_; 
v___f_696_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_696_, 0, v_f_693_);
v___x_697_ = lean_task_bind(v_x_692_, v___f_696_, v_prio_694_, v_sync_695_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bind___boxed(lean_object* v_00_u03b1_698_, lean_object* v_00_u03b2_699_, lean_object* v_x_700_, lean_object* v_f_701_, lean_object* v_prio_702_, lean_object* v_sync_703_){
_start:
{
uint8_t v_sync_boxed_704_; lean_object* v_res_705_; 
v_sync_boxed_704_ = lean_unbox(v_sync_703_);
v_res_705_ = l_Std_Async_AsyncTask_bind(v_00_u03b1_698_, v_00_u03b2_699_, v_x_700_, v_f_701_, v_prio_702_, v_sync_boxed_704_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_map___redArg___lam__0(lean_object* v_f_706_, lean_object* v_x_707_){
_start:
{
if (lean_obj_tag(v_x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec(v_f_706_);
v_a_708_ = lean_ctor_get(v_x_707_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v_x_707_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v_x_707_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v_x_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_724_; 
v_a_716_ = lean_ctor_get(v_x_707_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v_x_707_);
if (v_isSharedCheck_724_ == 0)
{
v___x_718_ = v_x_707_;
v_isShared_719_ = v_isSharedCheck_724_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v_x_707_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_724_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_720_ = lean_apply_1(v_f_706_, v_a_716_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_720_);
v___x_722_ = v___x_718_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_map___redArg(lean_object* v_f_725_, lean_object* v_x_726_, lean_object* v_prio_727_, uint8_t v_sync_728_){
_start:
{
lean_object* v___f_729_; lean_object* v___x_730_; 
v___f_729_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_729_, 0, v_f_725_);
v___x_730_ = lean_task_map(v___f_729_, v_x_726_, v_prio_727_, v_sync_728_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_map___redArg___boxed(lean_object* v_f_731_, lean_object* v_x_732_, lean_object* v_prio_733_, lean_object* v_sync_734_){
_start:
{
uint8_t v_sync_boxed_735_; lean_object* v_res_736_; 
v_sync_boxed_735_ = lean_unbox(v_sync_734_);
v_res_736_ = l_Std_Async_AsyncTask_map___redArg(v_f_731_, v_x_732_, v_prio_733_, v_sync_boxed_735_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_map(lean_object* v_00_u03b1_737_, lean_object* v_00_u03b2_738_, lean_object* v_f_739_, lean_object* v_x_740_, lean_object* v_prio_741_, uint8_t v_sync_742_){
_start:
{
lean_object* v___f_743_; lean_object* v___x_744_; 
v___f_743_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_743_, 0, v_f_739_);
v___x_744_ = lean_task_map(v___f_743_, v_x_740_, v_prio_741_, v_sync_742_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_map___boxed(lean_object* v_00_u03b1_745_, lean_object* v_00_u03b2_746_, lean_object* v_f_747_, lean_object* v_x_748_, lean_object* v_prio_749_, lean_object* v_sync_750_){
_start:
{
uint8_t v_sync_boxed_751_; lean_object* v_res_752_; 
v_sync_boxed_751_ = lean_unbox(v_sync_750_);
v_res_752_ = l_Std_Async_AsyncTask_map(v_00_u03b1_745_, v_00_u03b2_746_, v_f_747_, v_x_748_, v_prio_749_, v_sync_boxed_751_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bindIO___redArg___lam__0(lean_object* v_f_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_a_757_; 
if (lean_obj_tag(v_a_754_) == 0)
{
lean_object* v_a_760_; 
lean_dec_ref(v_f_753_);
v_a_760_ = lean_ctor_get(v_a_754_, 0);
lean_inc(v_a_760_);
lean_dec_ref(v_a_754_);
v_a_757_ = v_a_760_;
goto v___jp_756_;
}
else
{
lean_object* v_a_761_; lean_object* v___x_762_; 
v_a_761_ = lean_ctor_get(v_a_754_, 0);
lean_inc(v_a_761_);
lean_dec_ref(v_a_754_);
v___x_762_ = lean_apply_2(v_f_753_, v_a_761_, lean_box(0));
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_763_);
lean_dec_ref(v___x_762_);
return v_a_763_;
}
else
{
lean_object* v_a_764_; 
v_a_764_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_764_);
lean_dec_ref(v___x_762_);
v_a_757_ = v_a_764_;
goto v___jp_756_;
}
}
v___jp_756_:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_758_, 0, v_a_757_);
v___x_759_ = lean_task_pure(v___x_758_);
return v___x_759_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bindIO___redArg___lam__0___boxed(lean_object* v_f_765_, lean_object* v_a_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Std_Async_AsyncTask_bindIO___redArg___lam__0(v_f_765_, v_a_766_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bindIO___redArg(lean_object* v_x_769_, lean_object* v_f_770_, lean_object* v_prio_771_, uint8_t v_sync_772_){
_start:
{
lean_object* v___f_774_; lean_object* v___x_775_; 
v___f_774_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_bindIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_774_, 0, v_f_770_);
v___x_775_ = lean_io_bind_task(v_x_769_, v___f_774_, v_prio_771_, v_sync_772_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bindIO___redArg___boxed(lean_object* v_x_776_, lean_object* v_f_777_, lean_object* v_prio_778_, lean_object* v_sync_779_, lean_object* v_a_780_){
_start:
{
uint8_t v_sync_boxed_781_; lean_object* v_res_782_; 
v_sync_boxed_781_ = lean_unbox(v_sync_779_);
v_res_782_ = l_Std_Async_AsyncTask_bindIO___redArg(v_x_776_, v_f_777_, v_prio_778_, v_sync_boxed_781_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bindIO(lean_object* v_00_u03b1_783_, lean_object* v_00_u03b2_784_, lean_object* v_x_785_, lean_object* v_f_786_, lean_object* v_prio_787_, uint8_t v_sync_788_){
_start:
{
lean_object* v___f_790_; lean_object* v___x_791_; 
v___f_790_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_bindIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_790_, 0, v_f_786_);
v___x_791_ = lean_io_bind_task(v_x_785_, v___f_790_, v_prio_787_, v_sync_788_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bindIO___boxed(lean_object* v_00_u03b1_792_, lean_object* v_00_u03b2_793_, lean_object* v_x_794_, lean_object* v_f_795_, lean_object* v_prio_796_, lean_object* v_sync_797_, lean_object* v_a_798_){
_start:
{
uint8_t v_sync_boxed_799_; lean_object* v_res_800_; 
v_sync_boxed_799_ = lean_unbox(v_sync_797_);
v_res_800_ = l_Std_Async_AsyncTask_bindIO(v_00_u03b1_792_, v_00_u03b2_793_, v_x_794_, v_f_795_, v_prio_796_, v_sync_boxed_799_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapTaskIO___redArg(lean_object* v_f_801_, lean_object* v_x_802_, lean_object* v_prio_803_, uint8_t v_sync_804_){
_start:
{
lean_object* v___f_806_; lean_object* v___x_807_; 
v___f_806_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_mapIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_806_, 0, v_f_801_);
v___x_807_ = lean_io_map_task(v___f_806_, v_x_802_, v_prio_803_, v_sync_804_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapTaskIO___redArg___boxed(lean_object* v_f_808_, lean_object* v_x_809_, lean_object* v_prio_810_, lean_object* v_sync_811_, lean_object* v_a_812_){
_start:
{
uint8_t v_sync_boxed_813_; lean_object* v_res_814_; 
v_sync_boxed_813_ = lean_unbox(v_sync_811_);
v_res_814_ = l_Std_Async_AsyncTask_mapTaskIO___redArg(v_f_808_, v_x_809_, v_prio_810_, v_sync_boxed_813_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapTaskIO(lean_object* v_00_u03b1_815_, lean_object* v_00_u03b2_816_, lean_object* v_f_817_, lean_object* v_x_818_, lean_object* v_prio_819_, uint8_t v_sync_820_){
_start:
{
lean_object* v___f_822_; lean_object* v___x_823_; 
v___f_822_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_mapIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_822_, 0, v_f_817_);
v___x_823_ = lean_io_map_task(v___f_822_, v_x_818_, v_prio_819_, v_sync_820_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapTaskIO___boxed(lean_object* v_00_u03b1_824_, lean_object* v_00_u03b2_825_, lean_object* v_f_826_, lean_object* v_x_827_, lean_object* v_prio_828_, lean_object* v_sync_829_, lean_object* v_a_830_){
_start:
{
uint8_t v_sync_boxed_831_; lean_object* v_res_832_; 
v_sync_boxed_831_ = lean_unbox(v_sync_829_);
v_res_832_ = l_Std_Async_AsyncTask_mapTaskIO(v_00_u03b1_824_, v_00_u03b2_825_, v_f_826_, v_x_827_, v_prio_828_, v_sync_boxed_831_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_block___redArg(lean_object* v_x_833_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = lean_task_get_own(v_x_833_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_835_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_835_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
lean_ctor_set_tag(v___x_838_, 1);
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
v_a_844_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_835_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_835_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set_tag(v___x_846_, 0);
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_block___redArg___boxed(lean_object* v_x_852_, lean_object* v_a_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Std_Async_AsyncTask_block___redArg(v_x_852_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_block(lean_object* v_00_u03b1_855_, lean_object* v_x_856_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Std_Async_AsyncTask_block___redArg(v_x_856_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_block___boxed(lean_object* v_00_u03b1_859_, lean_object* v_x_860_, lean_object* v_a_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Std_Async_AsyncTask_block(v_00_u03b1_859_, v_x_860_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPromise___redArg___lam__0(lean_object* v_error_863_, lean_object* v_x_864_){
_start:
{
if (lean_obj_tag(v_x_864_) == 0)
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = lean_mk_io_user_error(v_error_863_);
v___x_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
return v___x_866_;
}
else
{
lean_object* v_val_867_; 
lean_dec_ref(v_error_863_);
v_val_867_ = lean_ctor_get(v_x_864_, 0);
lean_inc(v_val_867_);
return v_val_867_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPromise___redArg___lam__0___boxed(lean_object* v_error_868_, lean_object* v_x_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Std_Async_AsyncTask_ofPromise___redArg___lam__0(v_error_868_, v_x_869_);
lean_dec(v_x_869_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPromise___redArg(lean_object* v_x_871_, lean_object* v_error_872_){
_start:
{
lean_object* v___f_873_; lean_object* v___x_874_; lean_object* v___x_875_; uint8_t v___x_876_; lean_object* v___x_877_; 
v___f_873_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPromise___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_873_, 0, v_error_872_);
v___x_874_ = lean_io_promise_result_opt(v_x_871_);
v___x_875_ = lean_unsigned_to_nat(0u);
v___x_876_ = 0;
v___x_877_ = lean_task_map(v___f_873_, v___x_874_, v___x_875_, v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPromise___redArg___boxed(lean_object* v_x_878_, lean_object* v_error_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Std_Async_AsyncTask_ofPromise___redArg(v_x_878_, v_error_879_);
lean_dec(v_x_878_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPromise(lean_object* v_00_u03b1_881_, lean_object* v_x_882_, lean_object* v_error_883_){
_start:
{
lean_object* v___f_884_; lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; lean_object* v___x_888_; 
v___f_884_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPromise___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_884_, 0, v_error_883_);
v___x_885_ = lean_io_promise_result_opt(v_x_882_);
v___x_886_ = lean_unsigned_to_nat(0u);
v___x_887_ = 0;
v___x_888_ = lean_task_map(v___f_884_, v___x_885_, v___x_886_, v___x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPromise___boxed(lean_object* v_00_u03b1_889_, lean_object* v_x_890_, lean_object* v_error_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Std_Async_AsyncTask_ofPromise(v_00_u03b1_889_, v_x_890_, v_error_891_);
lean_dec(v_x_890_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPurePromise___redArg___lam__0(lean_object* v_error_893_, lean_object* v_x_894_){
_start:
{
if (lean_obj_tag(v_x_894_) == 0)
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = lean_mk_io_user_error(v_error_893_);
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
return v___x_896_;
}
else
{
lean_object* v_val_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_dec_ref(v_error_893_);
v_val_897_ = lean_ctor_get(v_x_894_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v_x_894_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v_x_894_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_val_897_);
lean_dec(v_x_894_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
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
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_val_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPurePromise___redArg(lean_object* v_x_905_, lean_object* v_error_906_){
_start:
{
lean_object* v___f_907_; lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; lean_object* v___x_911_; 
v___f_907_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPurePromise___redArg___lam__0), 2, 1);
lean_closure_set(v___f_907_, 0, v_error_906_);
v___x_908_ = lean_io_promise_result_opt(v_x_905_);
v___x_909_ = lean_unsigned_to_nat(0u);
v___x_910_ = 1;
v___x_911_ = lean_task_map(v___f_907_, v___x_908_, v___x_909_, v___x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPurePromise___redArg___boxed(lean_object* v_x_912_, lean_object* v_error_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Std_Async_AsyncTask_ofPurePromise___redArg(v_x_912_, v_error_913_);
lean_dec(v_x_912_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPurePromise(lean_object* v_00_u03b1_915_, lean_object* v_x_916_, lean_object* v_error_917_){
_start:
{
lean_object* v___f_918_; lean_object* v___x_919_; lean_object* v___x_920_; uint8_t v___x_921_; lean_object* v___x_922_; 
v___f_918_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPurePromise___redArg___lam__0), 2, 1);
lean_closure_set(v___f_918_, 0, v_error_917_);
v___x_919_ = lean_io_promise_result_opt(v_x_916_);
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = 1;
v___x_922_ = lean_task_map(v___f_918_, v___x_919_, v___x_920_, v___x_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPurePromise___boxed(lean_object* v_00_u03b1_923_, lean_object* v_x_924_, lean_object* v_error_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Std_Async_AsyncTask_ofPurePromise(v_00_u03b1_923_, v_x_924_, v_error_925_);
lean_dec(v_x_924_);
return v_res_926_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_AsyncTask_getState___redArg(lean_object* v_x_927_){
_start:
{
uint8_t v___x_929_; 
v___x_929_ = lean_io_get_task_state(v_x_927_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_getState___redArg___boxed(lean_object* v_x_930_, lean_object* v_a_931_){
_start:
{
uint8_t v_res_932_; lean_object* v_r_933_; 
v_res_932_ = l_Std_Async_AsyncTask_getState___redArg(v_x_930_);
lean_dec_ref(v_x_930_);
v_r_933_ = lean_box(v_res_932_);
return v_r_933_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_AsyncTask_getState(lean_object* v_00_u03b1_934_, lean_object* v_x_935_){
_start:
{
uint8_t v___x_937_; 
v___x_937_ = lean_io_get_task_state(v_x_935_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_getState___boxed(lean_object* v_00_u03b1_938_, lean_object* v_x_939_, lean_object* v_a_940_){
_start:
{
uint8_t v_res_941_; lean_object* v_r_942_; 
v_res_941_ = l_Std_Async_AsyncTask_getState(v_00_u03b1_938_, v_x_939_);
lean_dec_ref(v_x_939_);
v_r_942_ = lean_box(v_res_941_);
return v_r_942_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorIdx___redArg(lean_object* v_x_943_){
_start:
{
if (lean_obj_tag(v_x_943_) == 0)
{
lean_object* v___x_944_; 
v___x_944_ = lean_unsigned_to_nat(0u);
return v___x_944_;
}
else
{
lean_object* v___x_945_; 
v___x_945_ = lean_unsigned_to_nat(1u);
return v___x_945_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorIdx___redArg___boxed(lean_object* v_x_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Std_Async_MaybeTask_ctorIdx___redArg(v_x_946_);
lean_dec_ref(v_x_946_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorIdx(lean_object* v_00_u03b1_948_, lean_object* v_x_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Std_Async_MaybeTask_ctorIdx___redArg(v_x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorIdx___boxed(lean_object* v_00_u03b1_951_, lean_object* v_x_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Std_Async_MaybeTask_ctorIdx(v_00_u03b1_951_, v_x_952_);
lean_dec_ref(v_x_952_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorElim___redArg(lean_object* v_t_954_, lean_object* v_k_955_){
_start:
{
if (lean_obj_tag(v_t_954_) == 0)
{
lean_object* v_a_956_; lean_object* v___x_957_; 
v_a_956_ = lean_ctor_get(v_t_954_, 0);
lean_inc(v_a_956_);
lean_dec_ref(v_t_954_);
v___x_957_ = lean_apply_1(v_k_955_, v_a_956_);
return v___x_957_;
}
else
{
lean_object* v_a_958_; lean_object* v___x_959_; 
v_a_958_ = lean_ctor_get(v_t_954_, 0);
lean_inc_ref(v_a_958_);
lean_dec_ref(v_t_954_);
v___x_959_ = lean_apply_1(v_k_955_, v_a_958_);
return v___x_959_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorElim(lean_object* v_00_u03b1_960_, lean_object* v_motive_961_, lean_object* v_ctorIdx_962_, lean_object* v_t_963_, lean_object* v_h_964_, lean_object* v_k_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Std_Async_MaybeTask_ctorElim___redArg(v_t_963_, v_k_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorElim___boxed(lean_object* v_00_u03b1_967_, lean_object* v_motive_968_, lean_object* v_ctorIdx_969_, lean_object* v_t_970_, lean_object* v_h_971_, lean_object* v_k_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Std_Async_MaybeTask_ctorElim(v_00_u03b1_967_, v_motive_968_, v_ctorIdx_969_, v_t_970_, v_h_971_, v_k_972_);
lean_dec(v_ctorIdx_969_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_pure_elim___redArg(lean_object* v_t_974_, lean_object* v_pure_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Std_Async_MaybeTask_ctorElim___redArg(v_t_974_, v_pure_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_pure_elim(lean_object* v_00_u03b1_977_, lean_object* v_motive_978_, lean_object* v_t_979_, lean_object* v_h_980_, lean_object* v_pure_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Std_Async_MaybeTask_ctorElim___redArg(v_t_979_, v_pure_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ofTask_elim___redArg(lean_object* v_t_983_, lean_object* v_ofTask_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Std_Async_MaybeTask_ctorElim___redArg(v_t_983_, v_ofTask_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ofTask_elim(lean_object* v_00_u03b1_986_, lean_object* v_motive_987_, lean_object* v_t_988_, lean_object* v_h_989_, lean_object* v_ofTask_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Std_Async_MaybeTask_ctorElim___redArg(v_t_988_, v_ofTask_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_toTask___redArg(lean_object* v_x_992_){
_start:
{
if (lean_obj_tag(v_x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_994_; 
v_a_993_ = lean_ctor_get(v_x_992_, 0);
lean_inc(v_a_993_);
lean_dec_ref(v_x_992_);
v___x_994_ = lean_task_pure(v_a_993_);
return v___x_994_;
}
else
{
lean_object* v_a_995_; 
v_a_995_ = lean_ctor_get(v_x_992_, 0);
lean_inc_ref(v_a_995_);
lean_dec_ref(v_x_992_);
return v_a_995_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_toTask(lean_object* v_00_u03b1_996_, lean_object* v_x_997_){
_start:
{
if (lean_obj_tag(v_x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_999_; 
v_a_998_ = lean_ctor_get(v_x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref(v_x_997_);
v___x_999_ = lean_task_pure(v_a_998_);
return v___x_999_;
}
else
{
lean_object* v_a_1000_; 
v_a_1000_ = lean_ctor_get(v_x_997_, 0);
lean_inc_ref(v_a_1000_);
lean_dec_ref(v_x_997_);
return v_a_1000_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_get___redArg(lean_object* v_x_1001_){
_start:
{
if (lean_obj_tag(v_x_1001_) == 0)
{
lean_object* v_a_1002_; 
v_a_1002_ = lean_ctor_get(v_x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref(v_x_1001_);
return v_a_1002_;
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1004_; 
v_a_1003_ = lean_ctor_get(v_x_1001_, 0);
lean_inc_ref(v_a_1003_);
lean_dec_ref(v_x_1001_);
v___x_1004_ = lean_task_get_own(v_a_1003_);
return v___x_1004_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_get(lean_object* v_00_u03b1_1005_, lean_object* v_x_1006_){
_start:
{
if (lean_obj_tag(v_x_1006_) == 0)
{
lean_object* v_a_1007_; 
v_a_1007_ = lean_ctor_get(v_x_1006_, 0);
lean_inc(v_a_1007_);
lean_dec_ref(v_x_1006_);
return v_a_1007_;
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1009_; 
v_a_1008_ = lean_ctor_get(v_x_1006_, 0);
lean_inc_ref(v_a_1008_);
lean_dec_ref(v_x_1006_);
v___x_1009_ = lean_task_get_own(v_a_1008_);
return v___x_1009_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_map___redArg(lean_object* v_f_1010_, lean_object* v_prio_1011_, uint8_t v_sync_1012_, lean_object* v_x_1013_){
_start:
{
if (lean_obj_tag(v_x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1022_; 
lean_dec(v_prio_1011_);
v_a_1014_ = lean_ctor_get(v_x_1013_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_x_1013_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1016_ = v_x_1013_;
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v_x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1020_; 
v___x_1018_ = lean_apply_1(v_f_1010_, v_a_1014_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1018_);
v___x_1020_ = v___x_1016_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1018_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1031_; 
v_a_1023_ = lean_ctor_get(v_x_1013_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_x_1013_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1025_ = v_x_1013_;
v_isShared_1026_ = v_isSharedCheck_1031_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v_x_1013_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1031_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1027_ = lean_task_map(v_f_1010_, v_a_1023_, v_prio_1011_, v_sync_1012_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1027_);
v___x_1029_ = v___x_1025_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_map___redArg___boxed(lean_object* v_f_1032_, lean_object* v_prio_1033_, lean_object* v_sync_1034_, lean_object* v_x_1035_){
_start:
{
uint8_t v_sync_boxed_1036_; lean_object* v_res_1037_; 
v_sync_boxed_1036_ = lean_unbox(v_sync_1034_);
v_res_1037_ = l_Std_Async_MaybeTask_map___redArg(v_f_1032_, v_prio_1033_, v_sync_boxed_1036_, v_x_1035_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_map(lean_object* v_00_u03b1_1038_, lean_object* v_00_u03b2_1039_, lean_object* v_f_1040_, lean_object* v_prio_1041_, uint8_t v_sync_1042_, lean_object* v_x_1043_){
_start:
{
if (lean_obj_tag(v_x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1052_; 
lean_dec(v_prio_1041_);
v_a_1044_ = lean_ctor_get(v_x_1043_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_x_1043_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1046_ = v_x_1043_;
v_isShared_1047_ = v_isSharedCheck_1052_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v_x_1043_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1052_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1048_ = lean_apply_1(v_f_1040_, v_a_1044_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v___x_1048_);
v___x_1050_ = v___x_1046_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1061_; 
v_a_1053_ = lean_ctor_get(v_x_1043_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_x_1043_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1055_ = v_x_1043_;
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v_x_1043_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1057_ = lean_task_map(v_f_1040_, v_a_1053_, v_prio_1041_, v_sync_1042_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1057_);
v___x_1059_ = v___x_1055_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_map___boxed(lean_object* v_00_u03b1_1062_, lean_object* v_00_u03b2_1063_, lean_object* v_f_1064_, lean_object* v_prio_1065_, lean_object* v_sync_1066_, lean_object* v_x_1067_){
_start:
{
uint8_t v_sync_boxed_1068_; lean_object* v_res_1069_; 
v_sync_boxed_1068_ = lean_unbox(v_sync_1066_);
v_res_1069_ = l_Std_Async_MaybeTask_map(v_00_u03b1_1062_, v_00_u03b2_1063_, v_f_1064_, v_prio_1065_, v_sync_boxed_1068_, v_x_1067_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_bind___redArg___lam__0(lean_object* v_f_1070_, lean_object* v_x_1071_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_apply_1(v_f_1070_, v_x_1071_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1074_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
lean_dec_ref(v___x_1072_);
v___x_1074_ = lean_task_pure(v_a_1073_);
return v___x_1074_;
}
else
{
lean_object* v_a_1075_; 
v_a_1075_ = lean_ctor_get(v___x_1072_, 0);
lean_inc_ref(v_a_1075_);
lean_dec_ref(v___x_1072_);
return v_a_1075_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_bind___redArg(lean_object* v_t_1076_, lean_object* v_f_1077_, lean_object* v_prio_1078_, uint8_t v_sync_1079_){
_start:
{
if (lean_obj_tag(v_t_1076_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1081_; 
lean_dec(v_prio_1078_);
v_a_1080_ = lean_ctor_get(v_t_1076_, 0);
lean_inc(v_a_1080_);
lean_dec_ref(v_t_1076_);
v___x_1081_ = lean_apply_1(v_f_1077_, v_a_1080_);
return v___x_1081_;
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1091_; 
v_a_1082_ = lean_ctor_get(v_t_1076_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_t_1076_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1084_ = v_t_1076_;
v_isShared_1085_ = v_isSharedCheck_1091_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v_t_1076_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1091_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___f_1086_; lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___f_1086_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1086_, 0, v_f_1077_);
v___x_1087_ = lean_task_bind(v_a_1082_, v___f_1086_, v_prio_1078_, v_sync_1079_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1087_);
v___x_1089_ = v___x_1084_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_bind___redArg___boxed(lean_object* v_t_1092_, lean_object* v_f_1093_, lean_object* v_prio_1094_, lean_object* v_sync_1095_){
_start:
{
uint8_t v_sync_boxed_1096_; lean_object* v_res_1097_; 
v_sync_boxed_1096_ = lean_unbox(v_sync_1095_);
v_res_1097_ = l_Std_Async_MaybeTask_bind___redArg(v_t_1092_, v_f_1093_, v_prio_1094_, v_sync_boxed_1096_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_bind(lean_object* v_00_u03b1_1098_, lean_object* v_00_u03b2_1099_, lean_object* v_t_1100_, lean_object* v_f_1101_, lean_object* v_prio_1102_, uint8_t v_sync_1103_){
_start:
{
if (lean_obj_tag(v_t_1100_) == 0)
{
lean_object* v_a_1104_; lean_object* v___x_1105_; 
lean_dec(v_prio_1102_);
v_a_1104_ = lean_ctor_get(v_t_1100_, 0);
lean_inc(v_a_1104_);
lean_dec_ref(v_t_1100_);
v___x_1105_ = lean_apply_1(v_f_1101_, v_a_1104_);
return v___x_1105_;
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1115_; 
v_a_1106_ = lean_ctor_get(v_t_1100_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_t_1100_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1108_ = v_t_1100_;
v_isShared_1109_ = v_isSharedCheck_1115_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v_t_1100_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1115_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___f_1110_; lean_object* v___x_1111_; lean_object* v___x_1113_; 
v___f_1110_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1110_, 0, v_f_1101_);
v___x_1111_ = lean_task_bind(v_a_1106_, v___f_1110_, v_prio_1102_, v_sync_1103_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v___x_1111_);
v___x_1113_ = v___x_1108_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1111_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_bind___boxed(lean_object* v_00_u03b1_1116_, lean_object* v_00_u03b2_1117_, lean_object* v_t_1118_, lean_object* v_f_1119_, lean_object* v_prio_1120_, lean_object* v_sync_1121_){
_start:
{
uint8_t v_sync_boxed_1122_; lean_object* v_res_1123_; 
v_sync_boxed_1122_ = lean_unbox(v_sync_1121_);
v_res_1123_ = l_Std_Async_MaybeTask_bind(v_00_u03b1_1116_, v_00_u03b2_1117_, v_t_1118_, v_f_1119_, v_prio_1120_, v_sync_boxed_1122_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_joinTask___redArg___lam__0(lean_object* v_x_1124_){
_start:
{
if (lean_obj_tag(v_x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1126_; 
v_a_1125_ = lean_ctor_get(v_x_1124_, 0);
lean_inc(v_a_1125_);
lean_dec_ref(v_x_1124_);
v___x_1126_ = lean_task_pure(v_a_1125_);
return v___x_1126_;
}
else
{
lean_object* v_a_1127_; 
v_a_1127_ = lean_ctor_get(v_x_1124_, 0);
lean_inc_ref(v_a_1127_);
lean_dec_ref(v_x_1124_);
return v_a_1127_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_joinTask___redArg(lean_object* v_t_1129_){
_start:
{
lean_object* v___f_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; lean_object* v___x_1133_; 
v___f_1130_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___x_1131_ = lean_unsigned_to_nat(0u);
v___x_1132_ = 1;
v___x_1133_ = lean_task_bind(v_t_1129_, v___f_1130_, v___x_1131_, v___x_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_joinTask(lean_object* v_00_u03b1_1134_, lean_object* v_t_1135_){
_start:
{
lean_object* v___f_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; lean_object* v___x_1139_; 
v___f_1136_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___x_1137_ = lean_unsigned_to_nat(0u);
v___x_1138_ = 1;
v___x_1139_ = lean_task_bind(v_t_1135_, v___f_1136_, v___x_1137_, v___x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instFunctor___lam__0(lean_object* v_00_u03b1_1140_, lean_object* v_00_u03b2_1141_, lean_object* v_f_1142_, lean_object* v___y_1143_){
_start:
{
if (lean_obj_tag(v___y_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1152_; 
v_a_1144_ = lean_ctor_get(v___y_1143_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___y_1143_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1146_ = v___y_1143_;
v_isShared_1147_ = v_isSharedCheck_1152_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___y_1143_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1152_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1148_ = lean_apply_1(v_f_1142_, v_a_1144_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1148_);
v___x_1150_ = v___x_1146_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1163_; 
v_a_1153_ = lean_ctor_get(v___y_1143_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___y_1143_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1155_ = v___y_1143_;
v_isShared_1156_ = v_isSharedCheck_1163_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___y_1143_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1163_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1157_; uint8_t v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1157_ = lean_unsigned_to_nat(0u);
v___x_1158_ = 0;
v___x_1159_ = lean_task_map(v_f_1142_, v_a_1153_, v___x_1157_, v___x_1158_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 0, v___x_1159_);
v___x_1161_ = v___x_1155_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instFunctor___lam__1(lean_object* v___f_1164_, lean_object* v_00_u03b1_1165_, lean_object* v_00_u03b2_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_1169_, 0, lean_box(0));
lean_closure_set(v___x_1169_, 1, lean_box(0));
lean_closure_set(v___x_1169_, 2, v___y_1167_);
v___x_1170_ = lean_apply_4(v___f_1164_, lean_box(0), lean_box(0), v___x_1169_, v___y_1168_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__0(lean_object* v_00_u03b1_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___y_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__1(lean_object* v_x_1181_, lean_object* v_y_1182_){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = lean_box(0);
v___x_1184_ = lean_apply_1(v_x_1181_, v___x_1183_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1193_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1187_ = v___x_1184_;
v_isShared_1188_ = v_isSharedCheck_1193_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1184_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1193_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1189_ = lean_apply_1(v_y_1182_, v_a_1185_);
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 0, v___x_1189_);
v___x_1191_ = v___x_1187_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1204_; 
v_a_1194_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1196_ = v___x_1184_;
v_isShared_1197_ = v_isSharedCheck_1204_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1184_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1204_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1198_; uint8_t v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1198_ = lean_unsigned_to_nat(0u);
v___x_1199_ = 0;
v___x_1200_ = lean_task_map(v_y_1182_, v_a_1194_, v___x_1198_, v___x_1199_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1200_);
v___x_1202_ = v___x_1196_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__2(lean_object* v___f_1205_, lean_object* v_x_1206_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_apply_1(v___f_1205_, v_x_1206_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v_a_1208_; lean_object* v___x_1209_; 
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_a_1208_);
lean_dec_ref(v___x_1207_);
v___x_1209_ = lean_task_pure(v_a_1208_);
return v___x_1209_;
}
else
{
lean_object* v_a_1210_; 
v_a_1210_ = lean_ctor_get(v___x_1207_, 0);
lean_inc_ref(v_a_1210_);
lean_dec_ref(v___x_1207_);
return v_a_1210_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__3(lean_object* v_00_u03b1_1211_, lean_object* v_00_u03b2_1212_, lean_object* v_f_1213_, lean_object* v_x_1214_){
_start:
{
lean_object* v___f_1215_; 
lean_inc_ref(v_x_1214_);
v___f_1215_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_instMonad___lam__1), 2, 1);
lean_closure_set(v___f_1215_, 0, v_x_1214_);
if (lean_obj_tag(v_f_1213_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1217_; 
lean_dec_ref(v___f_1215_);
v_a_1216_ = lean_ctor_get(v_f_1213_, 0);
lean_inc(v_a_1216_);
lean_dec_ref(v_f_1213_);
v___x_1217_ = l_Std_Async_MaybeTask_instMonad___lam__1(v_x_1214_, v_a_1216_);
return v___x_1217_;
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1229_; 
lean_dec_ref(v_x_1214_);
v_a_1218_ = lean_ctor_get(v_f_1213_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_f_1213_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1220_ = v_f_1213_;
v_isShared_1221_ = v_isSharedCheck_1229_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v_f_1213_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1229_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___f_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1227_; 
v___f_1222_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_instMonad___lam__2), 2, 1);
lean_closure_set(v___f_1222_, 0, v___f_1215_);
v___x_1223_ = lean_unsigned_to_nat(0u);
v___x_1224_ = 0;
v___x_1225_ = lean_task_bind(v_a_1218_, v___f_1222_, v___x_1223_, v___x_1224_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1225_);
v___x_1227_ = v___x_1220_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__5(lean_object* v_00_u03b1_1230_, lean_object* v_00_u03b2_1231_, lean_object* v_t_1232_, lean_object* v_f_1233_){
_start:
{
if (lean_obj_tag(v_t_1232_) == 0)
{
lean_object* v_a_1234_; lean_object* v___x_1235_; 
v_a_1234_ = lean_ctor_get(v_t_1232_, 0);
lean_inc(v_a_1234_);
lean_dec_ref(v_t_1232_);
v___x_1235_ = lean_apply_1(v_f_1233_, v_a_1234_);
return v___x_1235_;
}
else
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1247_; 
v_a_1236_ = lean_ctor_get(v_t_1232_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_t_1232_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1238_ = v_t_1232_;
v_isShared_1239_ = v_isSharedCheck_1247_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v_t_1232_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1247_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___f_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1245_; 
v___f_1240_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1240_, 0, v_f_1233_);
v___x_1241_ = lean_unsigned_to_nat(0u);
v___x_1242_ = 0;
v___x_1243_ = lean_task_bind(v_a_1236_, v___f_1240_, v___x_1241_, v___x_1242_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1243_);
v___x_1245_ = v___x_1238_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1243_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__4(lean_object* v_a_1248_, lean_object* v_x_1249_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1250_, 0, v_a_1248_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__4___boxed(lean_object* v_a_1251_, lean_object* v_x_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Std_Async_MaybeTask_instMonad___lam__4(v_a_1251_, v_x_1252_);
lean_dec(v_x_1252_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__6(lean_object* v_y_1254_, lean_object* v___f_1255_, lean_object* v_a_1256_){
_start:
{
lean_object* v___f_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___f_1257_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_instMonad___lam__4___boxed), 2, 1);
lean_closure_set(v___f_1257_, 0, v_a_1256_);
v___x_1258_ = lean_box(0);
v___x_1259_ = lean_apply_1(v_y_1254_, v___x_1258_);
v___x_1260_ = lean_apply_4(v___f_1255_, lean_box(0), lean_box(0), v___x_1259_, v___f_1257_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__7(lean_object* v___f_1261_, lean_object* v_00_u03b1_1262_, lean_object* v_00_u03b2_1263_, lean_object* v_x_1264_, lean_object* v_y_1265_){
_start:
{
lean_object* v___f_1266_; lean_object* v___x_1267_; 
lean_inc_ref(v___f_1261_);
v___f_1266_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_instMonad___lam__6), 3, 2);
lean_closure_set(v___f_1266_, 0, v_y_1265_);
lean_closure_set(v___f_1266_, 1, v___f_1261_);
v___x_1267_ = lean_apply_4(v___f_1261_, lean_box(0), lean_box(0), v_x_1264_, v___f_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__8(lean_object* v_y_1268_, lean_object* v_x_1269_){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1270_ = lean_box(0);
v___x_1271_ = lean_apply_1(v_y_1268_, v___x_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__8___boxed(lean_object* v_y_1272_, lean_object* v_x_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Std_Async_MaybeTask_instMonad___lam__8(v_y_1272_, v_x_1273_);
lean_dec(v_x_1273_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__9(lean_object* v___f_1275_, lean_object* v_x_1276_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = lean_apply_1(v___f_1275_, v_x_1276_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1279_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_a_1278_);
lean_dec_ref(v___x_1277_);
v___x_1279_ = lean_task_pure(v_a_1278_);
return v___x_1279_;
}
else
{
lean_object* v_a_1280_; 
v_a_1280_ = lean_ctor_get(v___x_1277_, 0);
lean_inc_ref(v_a_1280_);
lean_dec_ref(v___x_1277_);
return v_a_1280_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__10(lean_object* v_00_u03b1_1281_, lean_object* v_00_u03b2_1282_, lean_object* v_x_1283_, lean_object* v_y_1284_){
_start:
{
lean_object* v___f_1285_; 
lean_inc_ref(v_y_1284_);
v___f_1285_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_instMonad___lam__8___boxed), 2, 1);
lean_closure_set(v___f_1285_, 0, v_y_1284_);
if (lean_obj_tag(v_x_1283_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1287_; 
lean_dec_ref(v___f_1285_);
v_a_1286_ = lean_ctor_get(v_x_1283_, 0);
lean_inc(v_a_1286_);
lean_dec_ref(v_x_1283_);
v___x_1287_ = l_Std_Async_MaybeTask_instMonad___lam__8(v_y_1284_, v_a_1286_);
lean_dec(v_a_1286_);
return v___x_1287_;
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1299_; 
lean_dec_ref(v_y_1284_);
v_a_1288_ = lean_ctor_get(v_x_1283_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v_x_1283_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1290_ = v_x_1283_;
v_isShared_1291_ = v_isSharedCheck_1299_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v_x_1283_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1299_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___f_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1297_; 
v___f_1292_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_instMonad___lam__9), 2, 1);
lean_closure_set(v___f_1292_, 0, v___f_1285_);
v___x_1293_ = lean_unsigned_to_nat(0u);
v___x_1294_ = 0;
v___x_1295_ = lean_task_bind(v_a_1288_, v___f_1292_, v___x_1293_, v___x_1294_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v___x_1295_);
v___x_1297_ = v___x_1290_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1295_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_mk___redArg(lean_object* v_x_1316_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = lean_apply_1(v_x_1316_, lean_box(0));
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_mk___redArg___boxed(lean_object* v_x_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Std_Async_BaseAsync_mk___redArg(v_x_1319_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_mk(lean_object* v_00_u03b1_1322_, lean_object* v_x_1323_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = lean_apply_1(v_x_1323_, lean_box(0));
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_mk___boxed(lean_object* v_00_u03b1_1326_, lean_object* v_x_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Std_Async_BaseAsync_mk(v_00_u03b1_1326_, v_x_1327_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toRawBaseIO___redArg(lean_object* v_x_1330_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = lean_apply_1(v_x_1330_, lean_box(0));
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toRawBaseIO___redArg___boxed(lean_object* v_x_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Std_Async_BaseAsync_toRawBaseIO___redArg(v_x_1333_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toRawBaseIO(lean_object* v_00_u03b1_1336_, lean_object* v_x_1337_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = lean_apply_1(v_x_1337_, lean_box(0));
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toRawBaseIO___boxed(lean_object* v_00_u03b1_1340_, lean_object* v_x_1341_, lean_object* v_a_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Std_Async_BaseAsync_toRawBaseIO(v_00_u03b1_1340_, v_x_1341_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toBaseIO___redArg(lean_object* v_x_1344_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = lean_apply_1(v_x_1344_, lean_box(0));
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1348_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_a_1347_);
lean_dec_ref(v___x_1346_);
v___x_1348_ = lean_task_pure(v_a_1347_);
return v___x_1348_;
}
else
{
lean_object* v_a_1349_; 
v_a_1349_ = lean_ctor_get(v___x_1346_, 0);
lean_inc_ref(v_a_1349_);
lean_dec_ref(v___x_1346_);
return v_a_1349_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toBaseIO___redArg___boxed(lean_object* v_x_1350_, lean_object* v_a_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Std_Async_BaseAsync_toBaseIO___redArg(v_x_1350_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toBaseIO(lean_object* v_00_u03b1_1353_, lean_object* v_x_1354_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = lean_apply_1(v_x_1354_, lean_box(0));
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1358_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_a_1357_);
lean_dec_ref(v___x_1356_);
v___x_1358_ = lean_task_pure(v_a_1357_);
return v___x_1358_;
}
else
{
lean_object* v_a_1359_; 
v_a_1359_ = lean_ctor_get(v___x_1356_, 0);
lean_inc_ref(v_a_1359_);
lean_dec_ref(v___x_1356_);
return v_a_1359_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toBaseIO___boxed(lean_object* v_00_u03b1_1360_, lean_object* v_x_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Std_Async_BaseAsync_toBaseIO(v_00_u03b1_1360_, v_x_1361_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofTask___redArg(lean_object* v_x_1364_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1366_, 0, v_x_1364_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofTask___redArg___boxed(lean_object* v_x_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Std_Async_BaseAsync_ofTask___redArg(v_x_1367_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofTask(lean_object* v_00_u03b1_1370_, lean_object* v_x_1371_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1373_, 0, v_x_1371_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofTask___boxed(lean_object* v_00_u03b1_1374_, lean_object* v_x_1375_, lean_object* v_a_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Std_Async_BaseAsync_ofTask(v_00_u03b1_1374_, v_x_1375_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_pure___redArg(lean_object* v_a_1378_){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1380_, 0, v_a_1378_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_pure___redArg___boxed(lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Std_Async_BaseAsync_pure___redArg(v_a_1381_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_pure(lean_object* v_00_u03b1_1384_, lean_object* v_a_1385_){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1387_, 0, v_a_1385_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_pure___boxed(lean_object* v_00_u03b1_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Std_Async_BaseAsync_pure(v_00_u03b1_1388_, v_a_1389_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_map___redArg(lean_object* v_f_1392_, lean_object* v_self_1393_, lean_object* v_prio_1394_, uint8_t v_sync_1395_){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = lean_apply_1(v_self_1393_, lean_box(0));
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1406_; 
lean_dec(v_prio_1394_);
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1400_ = v___x_1397_;
v_isShared_1401_ = v_isSharedCheck_1406_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1397_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1406_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1402_ = lean_apply_1(v_f_1392_, v_a_1398_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v___x_1402_);
v___x_1404_ = v___x_1400_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1415_; 
v_a_1407_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1409_ = v___x_1397_;
v_isShared_1410_ = v_isSharedCheck_1415_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1397_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1415_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1411_ = lean_task_map(v_f_1392_, v_a_1407_, v_prio_1394_, v_sync_1395_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1411_);
v___x_1413_ = v___x_1409_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_map___redArg___boxed(lean_object* v_f_1416_, lean_object* v_self_1417_, lean_object* v_prio_1418_, lean_object* v_sync_1419_, lean_object* v_a_1420_){
_start:
{
uint8_t v_sync_boxed_1421_; lean_object* v_res_1422_; 
v_sync_boxed_1421_ = lean_unbox(v_sync_1419_);
v_res_1422_ = l_Std_Async_BaseAsync_map___redArg(v_f_1416_, v_self_1417_, v_prio_1418_, v_sync_boxed_1421_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_map(lean_object* v_00_u03b1_1423_, lean_object* v_00_u03b2_1424_, lean_object* v_f_1425_, lean_object* v_self_1426_, lean_object* v_prio_1427_, uint8_t v_sync_1428_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = lean_apply_1(v_self_1426_, lean_box(0));
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1439_; 
lean_dec(v_prio_1427_);
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1433_ = v___x_1430_;
v_isShared_1434_ = v_isSharedCheck_1439_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1430_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1439_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1435_ = lean_apply_1(v_f_1425_, v_a_1431_);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 0, v___x_1435_);
v___x_1437_ = v___x_1433_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1448_; 
v_a_1440_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1442_ = v___x_1430_;
v_isShared_1443_ = v_isSharedCheck_1448_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1430_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1448_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1444_ = lean_task_map(v_f_1425_, v_a_1440_, v_prio_1427_, v_sync_1428_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 0, v___x_1444_);
v___x_1446_ = v___x_1442_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_map___boxed(lean_object* v_00_u03b1_1449_, lean_object* v_00_u03b2_1450_, lean_object* v_f_1451_, lean_object* v_self_1452_, lean_object* v_prio_1453_, lean_object* v_sync_1454_, lean_object* v_a_1455_){
_start:
{
uint8_t v_sync_boxed_1456_; lean_object* v_res_1457_; 
v_sync_boxed_1456_ = lean_unbox(v_sync_1454_);
v_res_1457_ = l_Std_Async_BaseAsync_map(v_00_u03b1_1449_, v_00_u03b2_1450_, v_f_1451_, v_self_1452_, v_prio_1453_, v_sync_boxed_1456_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___lam__0(lean_object* v_f_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = lean_apply_2(v_f_1458_, v_a_1459_, lean_box(0));
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1463_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
lean_dec_ref(v___x_1461_);
v___x_1463_ = lean_task_pure(v_a_1462_);
return v___x_1463_;
}
else
{
lean_object* v_a_1464_; 
v_a_1464_ = lean_ctor_get(v___x_1461_, 0);
lean_inc_ref(v_a_1464_);
lean_dec_ref(v___x_1461_);
return v_a_1464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___lam__0___boxed(lean_object* v_f_1465_, lean_object* v_a_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___lam__0(v_f_1465_, v_a_1466_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(lean_object* v_prio_1469_, uint8_t v_sync_1470_, lean_object* v_t_1471_, lean_object* v_f_1472_){
_start:
{
if (lean_obj_tag(v_t_1471_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1475_; 
lean_dec(v_prio_1469_);
v_a_1474_ = lean_ctor_get(v_t_1471_, 0);
lean_inc(v_a_1474_);
lean_dec_ref(v_t_1471_);
v___x_1475_ = lean_apply_2(v_f_1472_, v_a_1474_, lean_box(0));
return v___x_1475_;
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1485_; 
v_a_1476_ = lean_ctor_get(v_t_1471_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v_t_1471_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1478_ = v_t_1471_;
v_isShared_1479_ = v_isSharedCheck_1485_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v_t_1471_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1485_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___f_1480_; lean_object* v___x_1481_; lean_object* v___x_1483_; 
v___f_1480_ = lean_alloc_closure((void*)(l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1480_, 0, v_f_1472_);
v___x_1481_ = lean_io_bind_task(v_a_1476_, v___f_1480_, v_prio_1469_, v_sync_1470_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v___x_1481_);
v___x_1483_ = v___x_1478_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1481_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___boxed(lean_object* v_prio_1486_, lean_object* v_sync_1487_, lean_object* v_t_1488_, lean_object* v_f_1489_, lean_object* v_a_1490_){
_start:
{
uint8_t v_sync_boxed_1491_; lean_object* v_res_1492_; 
v_sync_boxed_1491_ = lean_unbox(v_sync_1487_);
v_res_1492_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_1486_, v_sync_boxed_1491_, v_t_1488_, v_f_1489_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object* v_00_u03b1_1493_, lean_object* v_00_u03b2_1494_, lean_object* v_prio_1495_, uint8_t v_sync_1496_, lean_object* v_t_1497_, lean_object* v_f_1498_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_1495_, v_sync_1496_, v_t_1497_, v_f_1498_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___boxed(lean_object* v_00_u03b1_1501_, lean_object* v_00_u03b2_1502_, lean_object* v_prio_1503_, lean_object* v_sync_1504_, lean_object* v_t_1505_, lean_object* v_f_1506_, lean_object* v_a_1507_){
_start:
{
uint8_t v_sync_boxed_1508_; lean_object* v_res_1509_; 
v_sync_boxed_1508_ = lean_unbox(v_sync_1504_);
v_res_1509_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(v_00_u03b1_1501_, v_00_u03b2_1502_, v_prio_1503_, v_sync_boxed_1508_, v_t_1505_, v_f_1506_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_bind___redArg(lean_object* v_self_1510_, lean_object* v_f_1511_, lean_object* v_prio_1512_, uint8_t v_sync_1513_){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = lean_apply_1(v_self_1510_, lean_box(0));
v___x_1516_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_1512_, v_sync_1513_, v___x_1515_, v_f_1511_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_bind___redArg___boxed(lean_object* v_self_1517_, lean_object* v_f_1518_, lean_object* v_prio_1519_, lean_object* v_sync_1520_, lean_object* v_a_1521_){
_start:
{
uint8_t v_sync_boxed_1522_; lean_object* v_res_1523_; 
v_sync_boxed_1522_ = lean_unbox(v_sync_1520_);
v_res_1523_ = l_Std_Async_BaseAsync_bind___redArg(v_self_1517_, v_f_1518_, v_prio_1519_, v_sync_boxed_1522_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_bind(lean_object* v_00_u03b1_1524_, lean_object* v_00_u03b2_1525_, lean_object* v_self_1526_, lean_object* v_f_1527_, lean_object* v_prio_1528_, uint8_t v_sync_1529_){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = lean_apply_1(v_self_1526_, lean_box(0));
v___x_1532_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_1528_, v_sync_1529_, v___x_1531_, v_f_1527_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_bind___boxed(lean_object* v_00_u03b1_1533_, lean_object* v_00_u03b2_1534_, lean_object* v_self_1535_, lean_object* v_f_1536_, lean_object* v_prio_1537_, lean_object* v_sync_1538_, lean_object* v_a_1539_){
_start:
{
uint8_t v_sync_boxed_1540_; lean_object* v_res_1541_; 
v_sync_boxed_1540_ = lean_unbox(v_sync_1538_);
v_res_1541_ = l_Std_Async_BaseAsync_bind(v_00_u03b1_1533_, v_00_u03b2_1534_, v_self_1535_, v_f_1536_, v_prio_1537_, v_sync_boxed_1540_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_lift___redArg(lean_object* v_x_1542_){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = lean_apply_1(v_x_1542_, lean_box(0));
v___x_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_lift___redArg___boxed(lean_object* v_x_1546_, lean_object* v_a_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_Std_Async_BaseAsync_lift___redArg(v_x_1546_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_lift(lean_object* v_00_u03b1_1549_, lean_object* v_x_1550_){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = lean_apply_1(v_x_1550_, lean_box(0));
v___x_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_lift___boxed(lean_object* v_00_u03b1_1554_, lean_object* v_x_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Std_Async_BaseAsync_lift(v_00_u03b1_1554_, v_x_1555_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_wait___redArg(lean_object* v_self_1558_){
_start:
{
lean_object* v___x_1560_; lean_object* v_val_1562_; 
v___x_1560_ = lean_apply_1(v_self_1558_, lean_box(0));
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1565_; 
v_a_1564_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1564_);
lean_dec_ref(v___x_1560_);
v___x_1565_ = lean_task_pure(v_a_1564_);
v_val_1562_ = v___x_1565_;
goto v___jp_1561_;
}
else
{
lean_object* v_a_1566_; 
v_a_1566_ = lean_ctor_get(v___x_1560_, 0);
lean_inc_ref(v_a_1566_);
lean_dec_ref(v___x_1560_);
v_val_1562_ = v_a_1566_;
goto v___jp_1561_;
}
v___jp_1561_:
{
lean_object* v___x_1563_; 
v___x_1563_ = lean_task_get_own(v_val_1562_);
return v___x_1563_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_wait___redArg___boxed(lean_object* v_self_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Std_Async_BaseAsync_wait___redArg(v_self_1567_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_wait(lean_object* v_00_u03b1_1570_, lean_object* v_self_1571_){
_start:
{
lean_object* v_val_1574_; lean_object* v___x_1576_; 
v___x_1576_ = lean_apply_1(v_self_1571_, lean_box(0));
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1578_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1577_);
lean_dec_ref(v___x_1576_);
v___x_1578_ = lean_task_pure(v_a_1577_);
v_val_1574_ = v___x_1578_;
goto v___jp_1573_;
}
else
{
lean_object* v_a_1579_; 
v_a_1579_ = lean_ctor_get(v___x_1576_, 0);
lean_inc_ref(v_a_1579_);
lean_dec_ref(v___x_1576_);
v_val_1574_ = v_a_1579_;
goto v___jp_1573_;
}
v___jp_1573_:
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_task_get_own(v_val_1574_);
return v___x_1575_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_wait___boxed(lean_object* v_00_u03b1_1580_, lean_object* v_self_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Std_Async_BaseAsync_wait(v_00_u03b1_1580_, v_self_1581_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_asTask___redArg(lean_object* v_x_1584_, lean_object* v_prio_1585_){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___f_1589_; lean_object* v___x_1590_; uint8_t v___x_1591_; lean_object* v___x_1592_; 
v___x_1587_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1587_, 0, lean_box(0));
lean_closure_set(v___x_1587_, 1, v_x_1584_);
v___x_1588_ = lean_io_as_task(v___x_1587_, v_prio_1585_);
v___f_1589_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___x_1590_ = lean_unsigned_to_nat(0u);
v___x_1591_ = 1;
v___x_1592_ = lean_task_bind(v___x_1588_, v___f_1589_, v___x_1590_, v___x_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_asTask___redArg___boxed(lean_object* v_x_1593_, lean_object* v_prio_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Std_Async_BaseAsync_asTask___redArg(v_x_1593_, v_prio_1594_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_asTask(lean_object* v_00_u03b1_1597_, lean_object* v_x_1598_, lean_object* v_prio_1599_){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___f_1603_; lean_object* v___x_1604_; uint8_t v___x_1605_; lean_object* v___x_1606_; 
v___x_1601_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1601_, 0, lean_box(0));
lean_closure_set(v___x_1601_, 1, v_x_1598_);
v___x_1602_ = lean_io_as_task(v___x_1601_, v_prio_1599_);
v___f_1603_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___x_1604_ = lean_unsigned_to_nat(0u);
v___x_1605_ = 1;
v___x_1606_ = lean_task_bind(v___x_1602_, v___f_1603_, v___x_1604_, v___x_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_asTask___boxed(lean_object* v_00_u03b1_1607_, lean_object* v_x_1608_, lean_object* v_prio_1609_, lean_object* v_a_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Std_Async_BaseAsync_asTask(v_00_u03b1_1607_, v_x_1608_, v_prio_1609_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_await___redArg(lean_object* v_t_1612_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1614_, 0, v_t_1612_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_await___redArg___boxed(lean_object* v_t_1615_, lean_object* v_a_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_Std_Async_BaseAsync_await___redArg(v_t_1615_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_await(lean_object* v_00_u03b1_1618_, lean_object* v_t_1619_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1621_, 0, v_t_1619_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_await___boxed(lean_object* v_00_u03b1_1622_, lean_object* v_t_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Std_Async_BaseAsync_await(v_00_u03b1_1622_, v_t_1623_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_async___redArg(lean_object* v_self_1626_, lean_object* v_prio_1627_){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___f_1631_; lean_object* v___x_1632_; uint8_t v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1629_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1629_, 0, lean_box(0));
lean_closure_set(v___x_1629_, 1, v_self_1626_);
v___x_1630_ = lean_io_as_task(v___x_1629_, v_prio_1627_);
v___f_1631_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___x_1632_ = lean_unsigned_to_nat(0u);
v___x_1633_ = 1;
v___x_1634_ = lean_task_bind(v___x_1630_, v___f_1631_, v___x_1632_, v___x_1633_);
v___x_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_async___redArg___boxed(lean_object* v_self_1636_, lean_object* v_prio_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Std_Async_BaseAsync_async___redArg(v_self_1636_, v_prio_1637_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_async(lean_object* v_00_u03b1_1640_, lean_object* v_self_1641_, lean_object* v_prio_1642_){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___f_1646_; lean_object* v___x_1647_; uint8_t v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1644_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1644_, 0, lean_box(0));
lean_closure_set(v___x_1644_, 1, v_self_1641_);
v___x_1645_ = lean_io_as_task(v___x_1644_, v_prio_1642_);
v___f_1646_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___x_1647_ = lean_unsigned_to_nat(0u);
v___x_1648_ = 1;
v___x_1649_ = lean_task_bind(v___x_1645_, v___f_1646_, v___x_1647_, v___x_1648_);
v___x_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_async___boxed(lean_object* v_00_u03b1_1651_, lean_object* v_self_1652_, lean_object* v_prio_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Std_Async_BaseAsync_async(v_00_u03b1_1651_, v_self_1652_, v_prio_1653_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instFunctor___lam__0(lean_object* v_00_u03b1_1656_, lean_object* v_00_u03b2_1657_, lean_object* v_f_1658_, lean_object* v_self_1659_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = lean_apply_1(v_self_1659_, lean_box(0));
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1670_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1670_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1670_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; lean_object* v___x_1668_; 
v___x_1666_ = lean_apply_1(v_f_1658_, v_a_1662_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1666_);
v___x_1668_ = v___x_1664_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
else
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1681_; 
v_a_1671_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1673_ = v___x_1661_;
v_isShared_1674_ = v_isSharedCheck_1681_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1661_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1681_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; uint8_t v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1675_ = lean_unsigned_to_nat(0u);
v___x_1676_ = 0;
v___x_1677_ = lean_task_map(v_f_1658_, v_a_1671_, v___x_1675_, v___x_1676_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1677_);
v___x_1679_ = v___x_1673_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instFunctor___lam__0___boxed(lean_object* v_00_u03b1_1682_, lean_object* v_00_u03b2_1683_, lean_object* v_f_1684_, lean_object* v_self_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Std_Async_BaseAsync_instFunctor___lam__0(v_00_u03b1_1682_, v_00_u03b2_1683_, v_f_1684_, v_self_1685_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instFunctor___lam__1(lean_object* v___f_1688_, lean_object* v_00_u03b1_1689_, lean_object* v_00_u03b2_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_1694_, 0, lean_box(0));
lean_closure_set(v___x_1694_, 1, lean_box(0));
lean_closure_set(v___x_1694_, 2, v___y_1691_);
v___x_1695_ = lean_apply_5(v___f_1688_, lean_box(0), lean_box(0), v___x_1694_, v___y_1692_, lean_box(0));
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instFunctor___lam__1___boxed(lean_object* v___f_1696_, lean_object* v_00_u03b1_1697_, lean_object* v_00_u03b2_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Std_Async_BaseAsync_instFunctor___lam__1(v___f_1696_, v_00_u03b1_1697_, v_00_u03b2_1698_, v___y_1699_, v___y_1700_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__0(lean_object* v_x_1710_, lean_object* v_y_1711_){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = lean_box(0);
v___x_1714_ = lean_apply_2(v_x_1710_, v___x_1713_, lean_box(0));
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1723_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1717_ = v___x_1714_;
v_isShared_1718_ = v_isSharedCheck_1723_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1714_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1723_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1719_; lean_object* v___x_1721_; 
v___x_1719_ = lean_apply_1(v_y_1711_, v_a_1715_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v___x_1719_);
v___x_1721_ = v___x_1717_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1719_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1734_; 
v_a_1724_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1726_ = v___x_1714_;
v_isShared_1727_ = v_isSharedCheck_1734_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1714_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1734_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1728_; uint8_t v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1732_; 
v___x_1728_ = lean_unsigned_to_nat(0u);
v___x_1729_ = 0;
v___x_1730_ = lean_task_map(v_y_1711_, v_a_1724_, v___x_1728_, v___x_1729_);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 0, v___x_1730_);
v___x_1732_ = v___x_1726_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1730_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__0___boxed(lean_object* v_x_1735_, lean_object* v_y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Std_Async_BaseAsync_instMonad___lam__0(v_x_1735_, v_y_1736_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__1(lean_object* v_00_u03b1_1739_, lean_object* v_00_u03b2_1740_, lean_object* v_f_1741_, lean_object* v_x_1742_){
_start:
{
lean_object* v___x_1744_; lean_object* v___f_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; lean_object* v___x_1748_; 
v___x_1744_ = lean_apply_1(v_f_1741_, lean_box(0));
v___f_1745_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_instMonad___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1745_, 0, v_x_1742_);
v___x_1746_ = lean_unsigned_to_nat(0u);
v___x_1747_ = 0;
v___x_1748_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_1746_, v___x_1747_, v___x_1744_, v___f_1745_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__1___boxed(lean_object* v_00_u03b1_1749_, lean_object* v_00_u03b2_1750_, lean_object* v_f_1751_, lean_object* v_x_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Std_Async_BaseAsync_instMonad___lam__1(v_00_u03b1_1749_, v_00_u03b2_1750_, v_f_1751_, v_x_1752_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__2(lean_object* v_00_u03b1_1755_, lean_object* v_00_u03b2_1756_, lean_object* v_self_1757_, lean_object* v_f_1758_){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; uint8_t v___x_1762_; lean_object* v___x_1763_; 
v___x_1760_ = lean_apply_1(v_self_1757_, lean_box(0));
v___x_1761_ = lean_unsigned_to_nat(0u);
v___x_1762_ = 0;
v___x_1763_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_1761_, v___x_1762_, v___x_1760_, v_f_1758_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__2___boxed(lean_object* v_00_u03b1_1764_, lean_object* v_00_u03b2_1765_, lean_object* v_self_1766_, lean_object* v_f_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Std_Async_BaseAsync_instMonad___lam__2(v_00_u03b1_1764_, v_00_u03b2_1765_, v_self_1766_, v_f_1767_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__3(lean_object* v_a_1770_, lean_object* v_x_1771_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1773_, 0, v_a_1770_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__3___boxed(lean_object* v_a_1774_, lean_object* v_x_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Std_Async_BaseAsync_instMonad___lam__3(v_a_1774_, v_x_1775_);
lean_dec(v_x_1775_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__4(lean_object* v_y_1778_, lean_object* v___f_1779_, lean_object* v_a_1780_){
_start:
{
lean_object* v___f_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___f_1782_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_instMonad___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1782_, 0, v_a_1780_);
v___x_1783_ = lean_box(0);
v___x_1784_ = lean_apply_1(v_y_1778_, v___x_1783_);
v___x_1785_ = lean_apply_5(v___f_1779_, lean_box(0), lean_box(0), v___x_1784_, v___f_1782_, lean_box(0));
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__4___boxed(lean_object* v_y_1786_, lean_object* v___f_1787_, lean_object* v_a_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Std_Async_BaseAsync_instMonad___lam__4(v_y_1786_, v___f_1787_, v_a_1788_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__5(lean_object* v___f_1791_, lean_object* v_00_u03b1_1792_, lean_object* v_00_u03b2_1793_, lean_object* v_x_1794_, lean_object* v_y_1795_){
_start:
{
lean_object* v___f_1797_; lean_object* v___x_1798_; 
lean_inc_ref(v___f_1791_);
v___f_1797_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_instMonad___lam__4___boxed), 4, 2);
lean_closure_set(v___f_1797_, 0, v_y_1795_);
lean_closure_set(v___f_1797_, 1, v___f_1791_);
v___x_1798_ = lean_apply_5(v___f_1791_, lean_box(0), lean_box(0), v_x_1794_, v___f_1797_, lean_box(0));
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__5___boxed(lean_object* v___f_1799_, lean_object* v_00_u03b1_1800_, lean_object* v_00_u03b2_1801_, lean_object* v_x_1802_, lean_object* v_y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Std_Async_BaseAsync_instMonad___lam__5(v___f_1799_, v_00_u03b1_1800_, v_00_u03b2_1801_, v_x_1802_, v_y_1803_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__6(lean_object* v_y_1806_, lean_object* v_x_1807_){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = lean_box(0);
v___x_1810_ = lean_apply_2(v_y_1806_, v___x_1809_, lean_box(0));
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__6___boxed(lean_object* v_y_1811_, lean_object* v_x_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Std_Async_BaseAsync_instMonad___lam__6(v_y_1811_, v_x_1812_);
lean_dec(v_x_1812_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__7(lean_object* v_00_u03b1_1815_, lean_object* v_00_u03b2_1816_, lean_object* v_x_1817_, lean_object* v_y_1818_){
_start:
{
lean_object* v___x_1820_; lean_object* v___f_1821_; lean_object* v___x_1822_; uint8_t v___x_1823_; lean_object* v___x_1824_; 
v___x_1820_ = lean_apply_1(v_x_1817_, lean_box(0));
v___f_1821_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_instMonad___lam__6___boxed), 3, 1);
lean_closure_set(v___f_1821_, 0, v_y_1818_);
v___x_1822_ = lean_unsigned_to_nat(0u);
v___x_1823_ = 0;
v___x_1824_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_1822_, v___x_1823_, v___x_1820_, v___f_1821_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__7___boxed(lean_object* v_00_u03b1_1825_, lean_object* v_00_u03b2_1826_, lean_object* v_x_1827_, lean_object* v_y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Std_Async_BaseAsync_instMonad___lam__7(v_00_u03b1_1825_, v_00_u03b2_1826_, v_x_1827_, v_y_1828_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadAsyncTask___lam__1(lean_object* v___f_1851_, lean_object* v_00_u03b1_1852_, lean_object* v_t_1853_, lean_object* v_prio_1854_){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; uint8_t v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1856_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1856_, 0, lean_box(0));
lean_closure_set(v___x_1856_, 1, v_t_1853_);
v___x_1857_ = lean_io_as_task(v___x_1856_, v_prio_1854_);
v___x_1858_ = lean_unsigned_to_nat(0u);
v___x_1859_ = 1;
v___x_1860_ = lean_task_bind(v___x_1857_, v___f_1851_, v___x_1858_, v___x_1859_);
v___x_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadAsyncTask___lam__1___boxed(lean_object* v___f_1862_, lean_object* v_00_u03b1_1863_, lean_object* v_t_1864_, lean_object* v_prio_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Std_Async_BaseAsync_instMonadAsyncTask___lam__1(v___f_1862_, v_00_u03b1_1863_, v_t_1864_, v_prio_1865_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instInhabited___redArg(lean_object* v_inst_1871_){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1872_, 0, v_inst_1871_);
v___x_1873_ = lean_alloc_closure((void*)(l_instMonadBaseIO___aux__5___boxed), 3, 2);
lean_closure_set(v___x_1873_, 0, lean_box(0));
lean_closure_set(v___x_1873_, 1, v___x_1872_);
v___x_1874_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_mk___boxed), 3, 2);
lean_closure_set(v___x_1874_, 0, lean_box(0));
lean_closure_set(v___x_1874_, 1, v___x_1873_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instInhabited(lean_object* v_00_u03b1_1875_, lean_object* v_inst_1876_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_Std_Async_BaseAsync_instInhabited___redArg(v_inst_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadFinally___lam__0(lean_object* v_res_1878_, lean_object* v_snd_1879_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1880_, 0, v_res_1878_);
lean_ctor_set(v___x_1880_, 1, v_snd_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadFinally___lam__1(lean_object* v_f_1881_, lean_object* v_res_1882_){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
lean_inc(v_res_1882_);
v___x_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1884_, 0, v_res_1882_);
v___x_1885_ = lean_apply_2(v_f_1881_, v___x_1884_, lean_box(0));
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1894_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1888_ = v___x_1885_;
v_isShared_1889_ = v_isSharedCheck_1894_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1885_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1894_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; lean_object* v___x_1892_; 
v___x_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1890_, 0, v_res_1882_);
lean_ctor_set(v___x_1890_, 1, v_a_1886_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v___x_1890_);
v___x_1892_ = v___x_1888_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1890_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1906_; 
v_a_1895_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1897_ = v___x_1885_;
v_isShared_1898_ = v_isSharedCheck_1906_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1885_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1906_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___f_1899_; lean_object* v___x_1900_; uint8_t v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1904_; 
v___f_1899_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_instMonadFinally___lam__0), 2, 1);
lean_closure_set(v___f_1899_, 0, v_res_1882_);
v___x_1900_ = lean_unsigned_to_nat(0u);
v___x_1901_ = 0;
v___x_1902_ = lean_task_map(v___f_1899_, v_a_1895_, v___x_1900_, v___x_1901_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v___x_1902_);
v___x_1904_ = v___x_1897_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v___x_1902_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadFinally___lam__1___boxed(lean_object* v_f_1907_, lean_object* v_res_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Std_Async_BaseAsync_instMonadFinally___lam__1(v_f_1907_, v_res_1908_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadFinally___lam__2(lean_object* v_00_u03b1_1911_, lean_object* v_00_u03b2_1912_, lean_object* v_x_1913_, lean_object* v_f_1914_){
_start:
{
lean_object* v___x_1916_; lean_object* v___f_1917_; lean_object* v___x_1918_; uint8_t v___x_1919_; lean_object* v___x_1920_; 
v___x_1916_ = lean_apply_1(v_x_1913_, lean_box(0));
v___f_1917_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_instMonadFinally___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1917_, 0, v_f_1914_);
v___x_1918_ = lean_unsigned_to_nat(0u);
v___x_1919_ = 0;
v___x_1920_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_1918_, v___x_1919_, v___x_1916_, v___f_1917_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadFinally___lam__2___boxed(lean_object* v_00_u03b1_1921_, lean_object* v_00_u03b2_1922_, lean_object* v_x_1923_, lean_object* v_f_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Std_Async_BaseAsync_instMonadFinally___lam__2(v_00_u03b1_1921_, v_00_u03b2_1922_, v_x_1923_, v_f_1924_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofExcept___redArg(lean_object* v_except_1929_){
_start:
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
v_a_1931_ = lean_ctor_get(v_except_1929_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_except_1929_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v_except_1929_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v_except_1929_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set_tag(v___x_1933_, 0);
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofExcept___redArg___boxed(lean_object* v_except_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Std_Async_BaseAsync_ofExcept___redArg(v_except_1939_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofExcept(lean_object* v_00_u03b1_1942_, lean_object* v_except_1943_){
_start:
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
v_a_1945_ = lean_ctor_get(v_except_1943_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v_except_1943_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v_except_1943_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v_except_1943_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
lean_ctor_set_tag(v___x_1947_, 0);
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofExcept___boxed(lean_object* v_00_u03b1_1953_, lean_object* v_except_1954_, lean_object* v_a_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Std_Async_BaseAsync_ofExcept(v_00_u03b1_1953_, v_except_1954_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__1(lean_object* v_resultX_1957_, lean_object* v_resultY_1958_){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1960_, 0, v_resultX_1957_);
lean_ctor_set(v___x_1960_, 1, v_resultY_1958_);
v___x_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__1___boxed(lean_object* v_resultX_1962_, lean_object* v_resultY_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Std_Async_BaseAsync_concurrently___redArg___lam__1(v_resultX_1962_, v_resultY_1963_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__0(lean_object* v_taskY_1966_, lean_object* v_resultX_1967_){
_start:
{
lean_object* v___f_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; lean_object* v___x_1973_; 
v___f_1969_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrently___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1969_, 0, v_resultX_1967_);
v___x_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1970_, 0, v_taskY_1966_);
v___x_1971_ = lean_unsigned_to_nat(0u);
v___x_1972_ = 0;
v___x_1973_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_1971_, v___x_1972_, v___x_1970_, v___f_1969_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__0___boxed(lean_object* v_taskY_1974_, lean_object* v_resultX_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_Std_Async_BaseAsync_concurrently___redArg___lam__0(v_taskY_1974_, v_resultX_1975_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__2(lean_object* v_taskX_1978_, lean_object* v_taskY_1979_){
_start:
{
lean_object* v___f_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; uint8_t v___x_1984_; lean_object* v___x_1985_; 
v___f_1981_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrently___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1981_, 0, v_taskY_1979_);
v___x_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1982_, 0, v_taskX_1978_);
v___x_1983_ = lean_unsigned_to_nat(0u);
v___x_1984_ = 0;
v___x_1985_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_1983_, v___x_1984_, v___x_1982_, v___f_1981_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__2___boxed(lean_object* v_taskX_1986_, lean_object* v_taskY_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Std_Async_BaseAsync_concurrently___redArg___lam__2(v_taskX_1986_, v_taskY_1987_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__3(lean_object* v_y_1990_, lean_object* v_prio_1991_, lean_object* v___f_1992_, lean_object* v_taskX_1993_){
_start:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___f_1997_; lean_object* v___x_1998_; uint8_t v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; uint8_t v___x_2002_; lean_object* v___x_2003_; 
v___x_1995_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1995_, 0, lean_box(0));
lean_closure_set(v___x_1995_, 1, v_y_1990_);
v___x_1996_ = lean_io_as_task(v___x_1995_, v_prio_1991_);
v___f_1997_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrently___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1997_, 0, v_taskX_1993_);
v___x_1998_ = lean_unsigned_to_nat(0u);
v___x_1999_ = 1;
v___x_2000_ = lean_task_bind(v___x_1996_, v___f_1992_, v___x_1998_, v___x_1999_);
v___x_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
v___x_2002_ = 0;
v___x_2003_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_1998_, v___x_2002_, v___x_2001_, v___f_1997_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__3___boxed(lean_object* v_y_2004_, lean_object* v_prio_2005_, lean_object* v___f_2006_, lean_object* v_taskX_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Std_Async_BaseAsync_concurrently___redArg___lam__3(v_y_2004_, v_prio_2005_, v___f_2006_, v_taskX_2007_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg(lean_object* v_x_2010_, lean_object* v_y_2011_, lean_object* v_prio_2012_){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___f_2016_; lean_object* v___f_2017_; lean_object* v___x_2018_; uint8_t v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; uint8_t v___x_2022_; lean_object* v___x_2023_; 
v___x_2014_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2014_, 0, lean_box(0));
lean_closure_set(v___x_2014_, 1, v_x_2010_);
lean_inc(v_prio_2012_);
v___x_2015_ = lean_io_as_task(v___x_2014_, v_prio_2012_);
v___f_2016_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___f_2017_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrently___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2017_, 0, v_y_2011_);
lean_closure_set(v___f_2017_, 1, v_prio_2012_);
lean_closure_set(v___f_2017_, 2, v___f_2016_);
v___x_2018_ = lean_unsigned_to_nat(0u);
v___x_2019_ = 1;
v___x_2020_ = lean_task_bind(v___x_2015_, v___f_2016_, v___x_2018_, v___x_2019_);
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
v___x_2022_ = 0;
v___x_2023_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2018_, v___x_2022_, v___x_2021_, v___f_2017_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___boxed(lean_object* v_x_2024_, lean_object* v_y_2025_, lean_object* v_prio_2026_, lean_object* v_a_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l_Std_Async_BaseAsync_concurrently___redArg(v_x_2024_, v_y_2025_, v_prio_2026_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently(lean_object* v_00_u03b1_2029_, lean_object* v_00_u03b2_2030_, lean_object* v_x_2031_, lean_object* v_y_2032_, lean_object* v_prio_2033_){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___f_2037_; lean_object* v___f_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; uint8_t v___x_2043_; lean_object* v___x_2044_; 
v___x_2035_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2035_, 0, lean_box(0));
lean_closure_set(v___x_2035_, 1, v_x_2031_);
lean_inc(v_prio_2033_);
v___x_2036_ = lean_io_as_task(v___x_2035_, v_prio_2033_);
v___f_2037_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___f_2038_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrently___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2038_, 0, v_y_2032_);
lean_closure_set(v___f_2038_, 1, v_prio_2033_);
lean_closure_set(v___f_2038_, 2, v___f_2037_);
v___x_2039_ = lean_unsigned_to_nat(0u);
v___x_2040_ = 1;
v___x_2041_ = lean_task_bind(v___x_2036_, v___f_2037_, v___x_2039_, v___x_2040_);
v___x_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
v___x_2043_ = 0;
v___x_2044_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2039_, v___x_2043_, v___x_2042_, v___f_2038_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___boxed(lean_object* v_00_u03b1_2045_, lean_object* v_00_u03b2_2046_, lean_object* v_x_2047_, lean_object* v_y_2048_, lean_object* v_prio_2049_, lean_object* v_a_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Std_Async_BaseAsync_concurrently(v_00_u03b1_2045_, v_00_u03b2_2046_, v_x_2047_, v_y_2048_, v_prio_2049_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__2(lean_object* v_promise_2052_, lean_object* v_value_2053_){
_start:
{
lean_object* v___x_2055_; 
v___x_2055_ = lean_io_promise_resolve(v_value_2053_, v_promise_2052_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__2___boxed(lean_object* v_promise_2056_, lean_object* v_value_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Std_Async_BaseAsync_race___redArg___lam__2(v_promise_2056_, v_value_2057_);
lean_dec(v_promise_2056_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__0(lean_object* v_promise_2060_, lean_object* v_____r_2061_){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2063_ = l_IO_Promise_result_x21___redArg(v_promise_2060_);
v___x_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__0___boxed(lean_object* v_promise_2065_, lean_object* v_____r_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Std_Async_BaseAsync_race___redArg___lam__0(v_promise_2065_, v_____r_2066_);
lean_dec(v_promise_2065_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__1(lean_object* v_task_u2082_2069_, lean_object* v___x_2070_, lean_object* v___x_2071_, uint8_t v___x_2072_, lean_object* v___f_2073_, lean_object* v_____r_2074_){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_inc(v___x_2071_);
v___x_2076_ = l_BaseIO_chainTask___redArg(v_task_u2082_2069_, v___x_2070_, v___x_2071_, v___x_2072_);
v___x_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
v___x_2078_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2071_, v___x_2072_, v___x_2077_, v___f_2073_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__1___boxed(lean_object* v_task_u2082_2079_, lean_object* v___x_2080_, lean_object* v___x_2081_, lean_object* v___x_2082_, lean_object* v___f_2083_, lean_object* v_____r_2084_, lean_object* v___y_2085_){
_start:
{
uint8_t v___x_616__boxed_2086_; lean_object* v_res_2087_; 
v___x_616__boxed_2086_ = lean_unbox(v___x_2082_);
v_res_2087_ = l_Std_Async_BaseAsync_race___redArg___lam__1(v_task_u2082_2079_, v___x_2080_, v___x_2081_, v___x_616__boxed_2086_, v___f_2083_, v_____r_2084_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__3(lean_object* v___f_2088_, lean_object* v___f_2089_, lean_object* v_task_u2081_2090_, lean_object* v___f_2091_, lean_object* v_task_u2082_2092_){
_start:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; uint8_t v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___f_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2094_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_2094_, 0, lean_box(0));
lean_closure_set(v___x_2094_, 1, lean_box(0));
lean_closure_set(v___x_2094_, 2, v___f_2088_);
lean_closure_set(v___x_2094_, 3, lean_box(0));
v___x_2095_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_2095_, 0, lean_box(0));
lean_closure_set(v___x_2095_, 1, lean_box(0));
lean_closure_set(v___x_2095_, 2, lean_box(0));
lean_closure_set(v___x_2095_, 3, v___x_2094_);
lean_closure_set(v___x_2095_, 4, v___f_2089_);
v___x_2096_ = lean_unsigned_to_nat(0u);
v___x_2097_ = 0;
lean_inc_ref(v___x_2095_);
v___x_2098_ = l_BaseIO_chainTask___redArg(v_task_u2081_2090_, v___x_2095_, v___x_2096_, v___x_2097_);
v___x_2099_ = lean_box(v___x_2097_);
v___f_2100_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2100_, 0, v_task_u2082_2092_);
lean_closure_set(v___f_2100_, 1, v___x_2095_);
lean_closure_set(v___f_2100_, 2, v___x_2096_);
lean_closure_set(v___f_2100_, 3, v___x_2099_);
lean_closure_set(v___f_2100_, 4, v___f_2091_);
v___x_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2098_);
v___x_2102_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2096_, v___x_2097_, v___x_2101_, v___f_2100_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__3___boxed(lean_object* v___f_2103_, lean_object* v___f_2104_, lean_object* v_task_u2081_2105_, lean_object* v___f_2106_, lean_object* v_task_u2082_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Std_Async_BaseAsync_race___redArg___lam__3(v___f_2103_, v___f_2104_, v_task_u2081_2105_, v___f_2106_, v_task_u2082_2107_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__4(lean_object* v_y_2110_, lean_object* v_prio_2111_, lean_object* v___f_2112_, lean_object* v___f_2113_, lean_object* v___f_2114_, lean_object* v___f_2115_, lean_object* v_task_u2081_2116_){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___f_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; lean_object* v___x_2126_; 
v___x_2118_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2118_, 0, lean_box(0));
lean_closure_set(v___x_2118_, 1, v_y_2110_);
v___x_2119_ = lean_io_as_task(v___x_2118_, v_prio_2111_);
v___f_2120_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_2120_, 0, v___f_2112_);
lean_closure_set(v___f_2120_, 1, v___f_2113_);
lean_closure_set(v___f_2120_, 2, v_task_u2081_2116_);
lean_closure_set(v___f_2120_, 3, v___f_2114_);
v___x_2121_ = lean_unsigned_to_nat(0u);
v___x_2122_ = 1;
v___x_2123_ = lean_task_bind(v___x_2119_, v___f_2115_, v___x_2121_, v___x_2122_);
v___x_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
v___x_2125_ = 0;
v___x_2126_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2121_, v___x_2125_, v___x_2124_, v___f_2120_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__4___boxed(lean_object* v_y_2127_, lean_object* v_prio_2128_, lean_object* v___f_2129_, lean_object* v___f_2130_, lean_object* v___f_2131_, lean_object* v___f_2132_, lean_object* v_task_u2081_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l_Std_Async_BaseAsync_race___redArg___lam__4(v_y_2127_, v_prio_2128_, v___f_2129_, v___f_2130_, v___f_2131_, v___f_2132_, v_task_u2081_2133_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__5(lean_object* v_x_2136_, lean_object* v_prio_2137_, lean_object* v_y_2138_, lean_object* v___f_2139_, lean_object* v___f_2140_, lean_object* v___f_2141_, lean_object* v_promise_2142_){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___f_2146_; lean_object* v___f_2147_; lean_object* v___f_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; uint8_t v___x_2153_; lean_object* v___x_2154_; 
v___x_2144_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2144_, 0, lean_box(0));
lean_closure_set(v___x_2144_, 1, v_x_2136_);
lean_inc(v_prio_2137_);
v___x_2145_ = lean_io_as_task(v___x_2144_, v_prio_2137_);
lean_inc(v_promise_2142_);
v___f_2146_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2146_, 0, v_promise_2142_);
v___f_2147_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2147_, 0, v_promise_2142_);
v___f_2148_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__4___boxed), 8, 6);
lean_closure_set(v___f_2148_, 0, v_y_2138_);
lean_closure_set(v___f_2148_, 1, v_prio_2137_);
lean_closure_set(v___f_2148_, 2, v___f_2139_);
lean_closure_set(v___f_2148_, 3, v___f_2146_);
lean_closure_set(v___f_2148_, 4, v___f_2147_);
lean_closure_set(v___f_2148_, 5, v___f_2140_);
v___x_2149_ = lean_unsigned_to_nat(0u);
v___x_2150_ = 1;
v___x_2151_ = lean_task_bind(v___x_2145_, v___f_2141_, v___x_2149_, v___x_2150_);
v___x_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
v___x_2153_ = 0;
v___x_2154_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2149_, v___x_2153_, v___x_2152_, v___f_2148_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__5___boxed(lean_object* v_x_2155_, lean_object* v_prio_2156_, lean_object* v_y_2157_, lean_object* v___f_2158_, lean_object* v___f_2159_, lean_object* v___f_2160_, lean_object* v_promise_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l_Std_Async_BaseAsync_race___redArg___lam__5(v_x_2155_, v_prio_2156_, v_y_2157_, v___f_2158_, v___f_2159_, v___f_2160_, v_promise_2161_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg(lean_object* v_x_2165_, lean_object* v_y_2166_, lean_object* v_prio_2167_){
_start:
{
lean_object* v___x_2169_; lean_object* v___f_2170_; lean_object* v___f_2171_; lean_object* v___f_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; lean_object* v___x_2176_; 
v___x_2169_ = lean_io_promise_new();
v___f_2170_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___f_2171_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_2172_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__5___boxed), 8, 6);
lean_closure_set(v___f_2172_, 0, v_x_2165_);
lean_closure_set(v___f_2172_, 1, v_prio_2167_);
lean_closure_set(v___f_2172_, 2, v_y_2166_);
lean_closure_set(v___f_2172_, 3, v___f_2171_);
lean_closure_set(v___f_2172_, 4, v___f_2170_);
lean_closure_set(v___f_2172_, 5, v___f_2170_);
v___x_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2169_);
v___x_2174_ = lean_unsigned_to_nat(0u);
v___x_2175_ = 0;
v___x_2176_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2174_, v___x_2175_, v___x_2173_, v___f_2172_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___boxed(lean_object* v_x_2177_, lean_object* v_y_2178_, lean_object* v_prio_2179_, lean_object* v_a_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l_Std_Async_BaseAsync_race___redArg(v_x_2177_, v_y_2178_, v_prio_2179_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race(lean_object* v_00_u03b1_2182_, lean_object* v_inst_2183_, lean_object* v_x_2184_, lean_object* v_y_2185_, lean_object* v_prio_2186_){
_start:
{
lean_object* v___x_2188_; lean_object* v___f_2189_; lean_object* v___f_2190_; lean_object* v___f_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; uint8_t v___x_2194_; lean_object* v___x_2195_; 
v___x_2188_ = lean_io_promise_new();
v___f_2189_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___f_2190_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_2191_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__5___boxed), 8, 6);
lean_closure_set(v___f_2191_, 0, v_x_2184_);
lean_closure_set(v___f_2191_, 1, v_prio_2186_);
lean_closure_set(v___f_2191_, 2, v_y_2185_);
lean_closure_set(v___f_2191_, 3, v___f_2190_);
lean_closure_set(v___f_2191_, 4, v___f_2189_);
lean_closure_set(v___f_2191_, 5, v___f_2189_);
v___x_2192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2188_);
v___x_2193_ = lean_unsigned_to_nat(0u);
v___x_2194_ = 0;
v___x_2195_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2193_, v___x_2194_, v___x_2192_, v___f_2191_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___boxed(lean_object* v_00_u03b1_2196_, lean_object* v_inst_2197_, lean_object* v_x_2198_, lean_object* v_y_2199_, lean_object* v_prio_2200_, lean_object* v_a_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Std_Async_BaseAsync_race(v_00_u03b1_2196_, v_inst_2197_, v_x_2198_, v_y_2199_, v_prio_2200_);
lean_dec(v_inst_2197_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1(lean_object* v_prio_2203_, lean_object* v___f_2204_, lean_object* v_x_2205_){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; uint8_t v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2207_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2207_, 0, lean_box(0));
lean_closure_set(v___x_2207_, 1, v_x_2205_);
v___x_2208_ = lean_io_as_task(v___x_2207_, v_prio_2203_);
v___x_2209_ = lean_unsigned_to_nat(0u);
v___x_2210_ = 1;
v___x_2211_ = lean_task_bind(v___x_2208_, v___f_2204_, v___x_2209_, v___x_2210_);
v___x_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1___boxed(lean_object* v_prio_2213_, lean_object* v___f_2214_, lean_object* v_x_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1(v_prio_2213_, v___f_2214_, v_x_2215_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0(lean_object* v___x_2219_, lean_object* v_tasks_2220_){
_start:
{
lean_object* v___x_2222_; size_t v_sz_2223_; size_t v___x_2224_; lean_object* v___x_218__overap_2225_; lean_object* v___x_2226_; 
v___x_2222_ = ((lean_object*)(l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0___closed__0));
v_sz_2223_ = lean_array_size(v_tasks_2220_);
v___x_2224_ = ((size_t)0ULL);
v___x_218__overap_2225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2219_, v___x_2222_, v_sz_2223_, v___x_2224_, v_tasks_2220_);
v___x_2226_ = lean_apply_1(v___x_218__overap_2225_, lean_box(0));
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0___boxed(lean_object* v___x_2227_, lean_object* v_tasks_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0(v___x_2227_, v_tasks_2228_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg(lean_object* v_xs_2233_, lean_object* v_prio_2234_){
_start:
{
lean_object* v___f_2236_; lean_object* v___f_2237_; lean_object* v___x_2238_; size_t v_sz_2239_; size_t v___x_2240_; lean_object* v___x_167__overap_2241_; lean_object* v___x_2242_; lean_object* v___f_2243_; lean_object* v___x_2244_; uint8_t v___x_2245_; lean_object* v___x_2246_; 
v___f_2236_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___f_2237_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2237_, 0, v_prio_2234_);
lean_closure_set(v___f_2237_, 1, v___f_2236_);
v___x_2238_ = ((lean_object*)(l_Std_Async_BaseAsync_instMonad));
v_sz_2239_ = lean_array_size(v_xs_2233_);
v___x_2240_ = ((size_t)0ULL);
v___x_167__overap_2241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2238_, v___f_2237_, v_sz_2239_, v___x_2240_, v_xs_2233_);
v___x_2242_ = lean_apply_1(v___x_167__overap_2241_, lean_box(0));
v___f_2243_ = ((lean_object*)(l_Std_Async_BaseAsync_concurrentlyAll___redArg___closed__0));
v___x_2244_ = lean_unsigned_to_nat(0u);
v___x_2245_ = 0;
v___x_2246_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2244_, v___x_2245_, v___x_2242_, v___f_2243_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___boxed(lean_object* v_xs_2247_, lean_object* v_prio_2248_, lean_object* v_a_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Std_Async_BaseAsync_concurrentlyAll___redArg(v_xs_2247_, v_prio_2248_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll(lean_object* v_00_u03b1_2251_, lean_object* v_xs_2252_, lean_object* v_prio_2253_){
_start:
{
lean_object* v___f_2255_; lean_object* v___f_2256_; lean_object* v___x_2257_; size_t v_sz_2258_; size_t v___x_2259_; lean_object* v___x_188__overap_2260_; lean_object* v___x_2261_; lean_object* v___f_2262_; lean_object* v___x_2263_; uint8_t v___x_2264_; lean_object* v___x_2265_; 
v___f_2255_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___f_2256_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2256_, 0, v_prio_2253_);
lean_closure_set(v___f_2256_, 1, v___f_2255_);
v___x_2257_ = ((lean_object*)(l_Std_Async_BaseAsync_instMonad));
v_sz_2258_ = lean_array_size(v_xs_2252_);
v___x_2259_ = ((size_t)0ULL);
v___x_188__overap_2260_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2257_, v___f_2256_, v_sz_2258_, v___x_2259_, v_xs_2252_);
v___x_2261_ = lean_apply_1(v___x_188__overap_2260_, lean_box(0));
v___f_2262_ = ((lean_object*)(l_Std_Async_BaseAsync_concurrentlyAll___redArg___closed__0));
v___x_2263_ = lean_unsigned_to_nat(0u);
v___x_2264_ = 0;
v___x_2265_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2263_, v___x_2264_, v___x_2261_, v___f_2262_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___boxed(lean_object* v_00_u03b1_2266_, lean_object* v_xs_2267_, lean_object* v_prio_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_Std_Async_BaseAsync_concurrentlyAll(v_00_u03b1_2266_, v_xs_2267_, v_prio_2268_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__2(lean_object* v___f_2271_, lean_object* v___f_2272_, lean_object* v_task_u2081_2273_){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2275_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_2275_, 0, lean_box(0));
lean_closure_set(v___x_2275_, 1, lean_box(0));
lean_closure_set(v___x_2275_, 2, v___f_2271_);
lean_closure_set(v___x_2275_, 3, lean_box(0));
v___x_2276_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_2276_, 0, lean_box(0));
lean_closure_set(v___x_2276_, 1, lean_box(0));
lean_closure_set(v___x_2276_, 2, lean_box(0));
lean_closure_set(v___x_2276_, 3, v___x_2275_);
lean_closure_set(v___x_2276_, 4, v___f_2272_);
v___x_2277_ = lean_unsigned_to_nat(0u);
v___x_2278_ = 0;
v___x_2279_ = l_BaseIO_chainTask___redArg(v_task_u2081_2273_, v___x_2276_, v___x_2277_, v___x_2278_);
v___x_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__2___boxed(lean_object* v___f_2281_, lean_object* v___f_2282_, lean_object* v_task_u2081_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Std_Async_BaseAsync_raceAll___redArg___lam__2(v___f_2281_, v___f_2282_, v_task_u2081_2283_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__0(lean_object* v_prio_2286_, lean_object* v___f_2287_, lean_object* v___f_2288_, lean_object* v_x_2289_){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; uint8_t v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; uint8_t v___x_2297_; lean_object* v___x_2298_; 
v___x_2291_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2291_, 0, lean_box(0));
lean_closure_set(v___x_2291_, 1, v_x_2289_);
v___x_2292_ = lean_io_as_task(v___x_2291_, v_prio_2286_);
v___x_2293_ = lean_unsigned_to_nat(0u);
v___x_2294_ = 1;
v___x_2295_ = lean_task_bind(v___x_2292_, v___f_2287_, v___x_2293_, v___x_2294_);
v___x_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
v___x_2297_ = 0;
v___x_2298_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2293_, v___x_2297_, v___x_2296_, v___f_2288_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__0___boxed(lean_object* v_prio_2299_, lean_object* v___f_2300_, lean_object* v___f_2301_, lean_object* v_x_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Std_Async_BaseAsync_raceAll___redArg___lam__0(v_prio_2299_, v___f_2300_, v___f_2301_, v_x_2302_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__3(lean_object* v___f_2305_, lean_object* v_prio_2306_, lean_object* v___f_2307_, lean_object* v_inst_2308_, lean_object* v_xs_2309_, lean_object* v_promise_2310_){
_start:
{
lean_object* v___f_2312_; lean_object* v___f_2313_; lean_object* v___f_2314_; lean_object* v___x_2315_; lean_object* v___f_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; lean_object* v___x_2319_; 
lean_inc(v_promise_2310_);
v___f_2312_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2312_, 0, v_promise_2310_);
v___f_2313_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_raceAll___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2313_, 0, v___f_2305_);
lean_closure_set(v___f_2313_, 1, v___f_2312_);
v___f_2314_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_raceAll___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2314_, 0, v_prio_2306_);
lean_closure_set(v___f_2314_, 1, v___f_2307_);
lean_closure_set(v___f_2314_, 2, v___f_2313_);
v___x_2315_ = lean_apply_3(v_inst_2308_, v_xs_2309_, v___f_2314_, lean_box(0));
v___f_2316_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2316_, 0, v_promise_2310_);
v___x_2317_ = lean_unsigned_to_nat(0u);
v___x_2318_ = 0;
v___x_2319_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2317_, v___x_2318_, v___x_2315_, v___f_2316_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__3___boxed(lean_object* v___f_2320_, lean_object* v_prio_2321_, lean_object* v___f_2322_, lean_object* v_inst_2323_, lean_object* v_xs_2324_, lean_object* v_promise_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Std_Async_BaseAsync_raceAll___redArg___lam__3(v___f_2320_, v_prio_2321_, v___f_2322_, v_inst_2323_, v_xs_2324_, v_promise_2325_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg(lean_object* v_inst_2328_, lean_object* v_xs_2329_, lean_object* v_prio_2330_){
_start:
{
lean_object* v___x_2332_; lean_object* v___f_2333_; lean_object* v___f_2334_; lean_object* v___f_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; uint8_t v___x_2338_; lean_object* v___x_2339_; 
v___x_2332_ = lean_io_promise_new();
v___f_2333_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___f_2334_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_2335_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_raceAll___redArg___lam__3___boxed), 7, 5);
lean_closure_set(v___f_2335_, 0, v___f_2334_);
lean_closure_set(v___f_2335_, 1, v_prio_2330_);
lean_closure_set(v___f_2335_, 2, v___f_2333_);
lean_closure_set(v___f_2335_, 3, v_inst_2328_);
lean_closure_set(v___f_2335_, 4, v_xs_2329_);
v___x_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2332_);
v___x_2337_ = lean_unsigned_to_nat(0u);
v___x_2338_ = 0;
v___x_2339_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2337_, v___x_2338_, v___x_2336_, v___f_2335_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___boxed(lean_object* v_inst_2340_, lean_object* v_xs_2341_, lean_object* v_prio_2342_, lean_object* v_a_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Std_Async_BaseAsync_raceAll___redArg(v_inst_2340_, v_xs_2341_, v_prio_2342_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll(lean_object* v_00_u03b1_2345_, lean_object* v_c_2346_, lean_object* v_inst_2347_, lean_object* v_inst_2348_, lean_object* v_xs_2349_, lean_object* v_prio_2350_){
_start:
{
lean_object* v___x_2352_; lean_object* v___f_2353_; lean_object* v___f_2354_; lean_object* v___f_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; uint8_t v___x_2358_; lean_object* v___x_2359_; 
v___x_2352_ = lean_io_promise_new();
v___f_2353_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___f_2354_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_2355_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_raceAll___redArg___lam__3___boxed), 7, 5);
lean_closure_set(v___f_2355_, 0, v___f_2354_);
lean_closure_set(v___f_2355_, 1, v_prio_2350_);
lean_closure_set(v___f_2355_, 2, v___f_2353_);
lean_closure_set(v___f_2355_, 3, v_inst_2348_);
lean_closure_set(v___f_2355_, 4, v_xs_2349_);
v___x_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2352_);
v___x_2357_ = lean_unsigned_to_nat(0u);
v___x_2358_ = 0;
v___x_2359_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2357_, v___x_2358_, v___x_2356_, v___f_2355_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___boxed(lean_object* v_00_u03b1_2360_, lean_object* v_c_2361_, lean_object* v_inst_2362_, lean_object* v_inst_2363_, lean_object* v_xs_2364_, lean_object* v_prio_2365_, lean_object* v_a_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Std_Async_BaseAsync_raceAll(v_00_u03b1_2360_, v_c_2361_, v_inst_2362_, v_inst_2363_, v_xs_2364_, v_prio_2365_);
lean_dec(v_inst_2362_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toBaseIO___redArg(lean_object* v_x_2368_){
_start:
{
lean_object* v___x_2370_; 
v___x_2370_ = lean_apply_1(v_x_2368_, lean_box(0));
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v___x_2372_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_a_2371_);
lean_dec_ref(v___x_2370_);
v___x_2372_ = lean_task_pure(v_a_2371_);
return v___x_2372_;
}
else
{
lean_object* v_a_2373_; 
v_a_2373_ = lean_ctor_get(v___x_2370_, 0);
lean_inc_ref(v_a_2373_);
lean_dec_ref(v___x_2370_);
return v_a_2373_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toBaseIO___redArg___boxed(lean_object* v_x_2374_, lean_object* v_a_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Std_Async_EAsync_toBaseIO___redArg(v_x_2374_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toBaseIO(lean_object* v_00_u03b5_2377_, lean_object* v_00_u03b1_2378_, lean_object* v_x_2379_){
_start:
{
lean_object* v___x_2381_; 
v___x_2381_ = lean_apply_1(v_x_2379_, lean_box(0));
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v_a_2382_; lean_object* v___x_2383_; 
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_a_2382_);
lean_dec_ref(v___x_2381_);
v___x_2383_ = lean_task_pure(v_a_2382_);
return v___x_2383_;
}
else
{
lean_object* v_a_2384_; 
v_a_2384_ = lean_ctor_get(v___x_2381_, 0);
lean_inc_ref(v_a_2384_);
lean_dec_ref(v___x_2381_);
return v_a_2384_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toBaseIO___boxed(lean_object* v_00_u03b5_2385_, lean_object* v_00_u03b1_2386_, lean_object* v_x_2387_, lean_object* v_a_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_Std_Async_EAsync_toBaseIO(v_00_u03b5_2385_, v_00_u03b1_2386_, v_x_2387_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofTask___redArg(lean_object* v_x_2390_){
_start:
{
lean_object* v___x_2392_; 
v___x_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2392_, 0, v_x_2390_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofTask___redArg___boxed(lean_object* v_x_2393_, lean_object* v_a_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l_Std_Async_EAsync_ofTask___redArg(v_x_2393_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofTask(lean_object* v_00_u03b5_2396_, lean_object* v_00_u03b1_2397_, lean_object* v_x_2398_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2400_, 0, v_x_2398_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofTask___boxed(lean_object* v_00_u03b5_2401_, lean_object* v_00_u03b1_2402_, lean_object* v_x_2403_, lean_object* v_a_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Std_Async_EAsync_ofTask(v_00_u03b5_2401_, v_00_u03b1_2402_, v_x_2403_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toEIO___redArg(lean_object* v_x_2406_){
_start:
{
lean_object* v___x_2408_; 
v___x_2408_ = lean_apply_1(v_x_2406_, lean_box(0));
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2417_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2411_ = v___x_2408_;
v_isShared_2412_ = v_isSharedCheck_2417_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2408_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2417_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2413_; lean_object* v___x_2415_; 
v___x_2413_ = lean_task_pure(v_a_2409_);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 0, v___x_2413_);
v___x_2415_ = v___x_2411_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2413_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
else
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2425_; 
v_a_2418_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2420_ = v___x_2408_;
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2408_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2423_; 
if (v_isShared_2421_ == 0)
{
lean_ctor_set_tag(v___x_2420_, 0);
v___x_2423_ = v___x_2420_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2418_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toEIO___redArg___boxed(lean_object* v_x_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_Std_Async_EAsync_toEIO___redArg(v_x_2426_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toEIO(lean_object* v_00_u03b5_2429_, lean_object* v_00_u03b1_2430_, lean_object* v_x_2431_){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = lean_apply_1(v_x_2431_, lean_box(0));
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2442_; 
v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2436_ = v___x_2433_;
v_isShared_2437_ = v_isSharedCheck_2442_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2433_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2442_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2438_; lean_object* v___x_2440_; 
v___x_2438_ = lean_task_pure(v_a_2434_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 0, v___x_2438_);
v___x_2440_ = v___x_2436_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2438_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
v_a_2443_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2433_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2433_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
lean_ctor_set_tag(v___x_2445_, 0);
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toEIO___boxed(lean_object* v_00_u03b5_2451_, lean_object* v_00_u03b1_2452_, lean_object* v_x_2453_, lean_object* v_a_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l_Std_Async_EAsync_toEIO(v_00_u03b5_2451_, v_00_u03b1_2452_, v_x_2453_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofETask___redArg(lean_object* v_x_2456_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2458_, 0, v_x_2456_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofETask___redArg___boxed(lean_object* v_x_2459_, lean_object* v_a_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_Std_Async_EAsync_ofETask___redArg(v_x_2459_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofETask(lean_object* v_00_u03b5_2462_, lean_object* v_00_u03b1_2463_, lean_object* v_x_2464_){
_start:
{
lean_object* v___x_2466_; 
v___x_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2466_, 0, v_x_2464_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofETask___boxed(lean_object* v_00_u03b5_2467_, lean_object* v_00_u03b1_2468_, lean_object* v_x_2469_, lean_object* v_a_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l_Std_Async_EAsync_ofETask(v_00_u03b5_2467_, v_00_u03b1_2468_, v_x_2469_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_pure___redArg(lean_object* v_a_2472_){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2474_, 0, v_a_2472_);
v___x_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_pure___redArg___boxed(lean_object* v_a_2476_, lean_object* v_a_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Std_Async_EAsync_pure___redArg(v_a_2476_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_pure(lean_object* v_00_u03b1_2479_, lean_object* v_00_u03b5_2480_, lean_object* v_a_2481_){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2483_, 0, v_a_2481_);
v___x_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2483_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_pure___boxed(lean_object* v_00_u03b1_2485_, lean_object* v_00_u03b5_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l_Std_Async_EAsync_pure(v_00_u03b1_2485_, v_00_u03b5_2486_, v_a_2487_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_map___redArg(lean_object* v_f_2490_, lean_object* v_self_2491_){
_start:
{
lean_object* v___x_2493_; lean_object* v___y_2495_; 
v___x_2493_ = lean_apply_1(v_self_2491_, lean_box(0));
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v_a_2497_; 
v_a_2497_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_a_2497_);
lean_dec_ref(v___x_2493_);
if (lean_obj_tag(v_a_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
lean_dec(v_f_2490_);
v_a_2498_ = lean_ctor_get(v_a_2497_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v_a_2497_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2500_ = v_a_2497_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v_a_2497_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
v___y_2495_ = v___x_2503_;
goto v___jp_2494_;
}
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2514_; 
v_a_2506_ = lean_ctor_get(v_a_2497_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v_a_2497_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2508_ = v_a_2497_;
v_isShared_2509_ = v_isSharedCheck_2514_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v_a_2497_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2514_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2510_; lean_object* v___x_2512_; 
v___x_2510_ = lean_apply_1(v_f_2490_, v_a_2506_);
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 0, v___x_2510_);
v___x_2512_ = v___x_2508_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2510_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
v___y_2495_ = v___x_2512_;
goto v___jp_2494_;
}
}
}
}
else
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2526_; 
v_a_2515_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2517_ = v___x_2493_;
v_isShared_2518_ = v_isSharedCheck_2526_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2493_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2526_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; uint8_t v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2524_; 
v___x_2519_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_2519_, 0, lean_box(0));
lean_closure_set(v___x_2519_, 1, lean_box(0));
lean_closure_set(v___x_2519_, 2, lean_box(0));
lean_closure_set(v___x_2519_, 3, v_f_2490_);
v___x_2520_ = lean_unsigned_to_nat(0u);
v___x_2521_ = 0;
v___x_2522_ = lean_task_map(v___x_2519_, v_a_2515_, v___x_2520_, v___x_2521_);
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 0, v___x_2522_);
v___x_2524_ = v___x_2517_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2522_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
v___jp_2494_:
{
lean_object* v___x_2496_; 
v___x_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2496_, 0, v___y_2495_);
return v___x_2496_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_map___redArg___boxed(lean_object* v_f_2527_, lean_object* v_self_2528_, lean_object* v_a_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_Std_Async_EAsync_map___redArg(v_f_2527_, v_self_2528_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_map(lean_object* v_00_u03b1_2531_, lean_object* v_00_u03b2_2532_, lean_object* v_00_u03b5_2533_, lean_object* v_f_2534_, lean_object* v_self_2535_){
_start:
{
lean_object* v___x_2537_; lean_object* v___y_2539_; 
v___x_2537_ = lean_apply_1(v_self_2535_, lean_box(0));
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v_a_2541_; 
v_a_2541_ = lean_ctor_get(v___x_2537_, 0);
lean_inc(v_a_2541_);
lean_dec_ref(v___x_2537_);
if (lean_obj_tag(v_a_2541_) == 0)
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
lean_dec(v_f_2534_);
v_a_2542_ = lean_ctor_get(v_a_2541_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v_a_2541_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v_a_2541_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v_a_2541_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
v___y_2539_ = v___x_2547_;
goto v___jp_2538_;
}
}
}
else
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2558_; 
v_a_2550_ = lean_ctor_get(v_a_2541_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v_a_2541_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2552_ = v_a_2541_;
v_isShared_2553_ = v_isSharedCheck_2558_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v_a_2541_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2558_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2554_; lean_object* v___x_2556_; 
v___x_2554_ = lean_apply_1(v_f_2534_, v_a_2550_);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 0, v___x_2554_);
v___x_2556_ = v___x_2552_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2554_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
v___y_2539_ = v___x_2556_;
goto v___jp_2538_;
}
}
}
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2570_; 
v_a_2559_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2561_ = v___x_2537_;
v_isShared_2562_ = v_isSharedCheck_2570_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2537_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2570_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; uint8_t v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2568_; 
v___x_2563_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_2563_, 0, lean_box(0));
lean_closure_set(v___x_2563_, 1, lean_box(0));
lean_closure_set(v___x_2563_, 2, lean_box(0));
lean_closure_set(v___x_2563_, 3, v_f_2534_);
v___x_2564_ = lean_unsigned_to_nat(0u);
v___x_2565_ = 0;
v___x_2566_ = lean_task_map(v___x_2563_, v_a_2559_, v___x_2564_, v___x_2565_);
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v___x_2566_);
v___x_2568_ = v___x_2561_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2566_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
v___jp_2538_:
{
lean_object* v___x_2540_; 
v___x_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2540_, 0, v___y_2539_);
return v___x_2540_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_map___boxed(lean_object* v_00_u03b1_2571_, lean_object* v_00_u03b2_2572_, lean_object* v_00_u03b5_2573_, lean_object* v_f_2574_, lean_object* v_self_2575_, lean_object* v_a_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_Std_Async_EAsync_map(v_00_u03b1_2571_, v_00_u03b2_2572_, v_00_u03b5_2573_, v_f_2574_, v_self_2575_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind___redArg___lam__0(lean_object* v_f_2578_, lean_object* v_x_2579_){
_start:
{
if (lean_obj_tag(v_x_2579_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2589_; 
lean_dec_ref(v_f_2578_);
v_a_2581_ = lean_ctor_get(v_x_2579_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v_x_2579_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2583_ = v_x_2579_;
v_isShared_2584_ = v_isSharedCheck_2589_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v_x_2579_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2589_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2581_);
v___x_2586_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
lean_object* v___x_2587_; 
v___x_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2586_);
return v___x_2587_;
}
}
}
else
{
lean_object* v_a_2590_; lean_object* v___x_2591_; 
v_a_2590_ = lean_ctor_get(v_x_2579_, 0);
lean_inc(v_a_2590_);
lean_dec_ref(v_x_2579_);
v___x_2591_ = lean_apply_2(v_f_2578_, v_a_2590_, lean_box(0));
return v___x_2591_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind___redArg___lam__0___boxed(lean_object* v_f_2592_, lean_object* v_x_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Std_Async_EAsync_bind___redArg___lam__0(v_f_2592_, v_x_2593_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind___redArg(lean_object* v_self_2596_, lean_object* v_f_2597_){
_start:
{
lean_object* v___x_2599_; lean_object* v___f_2600_; lean_object* v___x_2601_; uint8_t v___x_2602_; lean_object* v___x_2603_; 
v___x_2599_ = lean_apply_1(v_self_2596_, lean_box(0));
v___f_2600_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_bind___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2600_, 0, v_f_2597_);
v___x_2601_ = lean_unsigned_to_nat(0u);
v___x_2602_ = 0;
v___x_2603_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2601_, v___x_2602_, v___x_2599_, v___f_2600_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind___redArg___boxed(lean_object* v_self_2604_, lean_object* v_f_2605_, lean_object* v_a_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l_Std_Async_EAsync_bind___redArg(v_self_2604_, v_f_2605_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind(lean_object* v_00_u03b5_2608_, lean_object* v_00_u03b1_2609_, lean_object* v_00_u03b2_2610_, lean_object* v_self_2611_, lean_object* v_f_2612_){
_start:
{
lean_object* v___x_2614_; lean_object* v___f_2615_; lean_object* v___x_2616_; uint8_t v___x_2617_; lean_object* v___x_2618_; 
v___x_2614_ = lean_apply_1(v_self_2611_, lean_box(0));
v___f_2615_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_bind___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2615_, 0, v_f_2612_);
v___x_2616_ = lean_unsigned_to_nat(0u);
v___x_2617_ = 0;
v___x_2618_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2616_, v___x_2617_, v___x_2614_, v___f_2615_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind___boxed(lean_object* v_00_u03b5_2619_, lean_object* v_00_u03b1_2620_, lean_object* v_00_u03b2_2621_, lean_object* v_self_2622_, lean_object* v_f_2623_, lean_object* v_a_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l_Std_Async_EAsync_bind(v_00_u03b5_2619_, v_00_u03b1_2620_, v_00_u03b2_2621_, v_self_2622_, v_f_2623_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_lift___redArg(lean_object* v_x_2626_){
_start:
{
lean_object* v_val_2629_; lean_object* v___x_2631_; 
v___x_2631_ = lean_apply_1(v_x_2626_, lean_box(0));
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2631_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2631_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
lean_ctor_set_tag(v___x_2634_, 1);
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
v_val_2629_ = v___x_2637_;
goto v___jp_2628_;
}
}
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
v_a_2640_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2642_ = v___x_2631_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2631_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
lean_ctor_set_tag(v___x_2642_, 0);
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
v_val_2629_ = v___x_2645_;
goto v___jp_2628_;
}
}
}
v___jp_2628_:
{
lean_object* v___x_2630_; 
v___x_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2630_, 0, v_val_2629_);
return v___x_2630_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_lift___redArg___boxed(lean_object* v_x_2648_, lean_object* v_a_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l_Std_Async_EAsync_lift___redArg(v_x_2648_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_lift(lean_object* v_00_u03b5_2651_, lean_object* v_00_u03b1_2652_, lean_object* v_x_2653_){
_start:
{
lean_object* v_val_2656_; lean_object* v___x_2658_; 
v___x_2658_ = lean_apply_1(v_x_2653_, lean_box(0));
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2661_ = v___x_2658_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2658_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
lean_ctor_set_tag(v___x_2661_, 1);
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2659_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
v_val_2656_ = v___x_2664_;
goto v___jp_2655_;
}
}
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
v_a_2667_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2658_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2658_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
lean_ctor_set_tag(v___x_2669_, 0);
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
v_val_2656_ = v___x_2672_;
goto v___jp_2655_;
}
}
}
v___jp_2655_:
{
lean_object* v___x_2657_; 
v___x_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2657_, 0, v_val_2656_);
return v___x_2657_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_lift___boxed(lean_object* v_00_u03b5_2675_, lean_object* v_00_u03b1_2676_, lean_object* v_x_2677_, lean_object* v_a_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_Std_Async_EAsync_lift(v_00_u03b5_2675_, v_00_u03b1_2676_, v_x_2677_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_wait___redArg(lean_object* v_self_2680_){
_start:
{
lean_object* v___x_2682_; lean_object* v_val_2684_; 
v___x_2682_ = lean_apply_1(v_self_2680_, lean_box(0));
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2702_; lean_object* v___x_2703_; 
v_a_2702_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2702_);
lean_dec_ref(v___x_2682_);
v___x_2703_ = lean_task_pure(v_a_2702_);
v_val_2684_ = v___x_2703_;
goto v___jp_2683_;
}
else
{
lean_object* v_a_2704_; 
v_a_2704_ = lean_ctor_get(v___x_2682_, 0);
lean_inc_ref(v_a_2704_);
lean_dec_ref(v___x_2682_);
v_val_2684_ = v_a_2704_;
goto v___jp_2683_;
}
v___jp_2683_:
{
lean_object* v___x_2685_; 
v___x_2685_ = lean_task_get_own(v_val_2684_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2685_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2685_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
lean_ctor_set_tag(v___x_2688_, 1);
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
v_a_2694_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2685_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2685_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
lean_ctor_set_tag(v___x_2696_, 0);
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_wait___redArg___boxed(lean_object* v_self_2705_, lean_object* v_a_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_Std_Async_EAsync_wait___redArg(v_self_2705_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_wait(lean_object* v_00_u03b5_2708_, lean_object* v_00_u03b1_2709_, lean_object* v_self_2710_){
_start:
{
lean_object* v_val_2713_; lean_object* v___x_2731_; 
v___x_2731_ = lean_apply_1(v_self_2710_, lean_box(0));
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; lean_object* v___x_2733_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2732_);
lean_dec_ref(v___x_2731_);
v___x_2733_ = lean_task_pure(v_a_2732_);
v_val_2713_ = v___x_2733_;
goto v___jp_2712_;
}
else
{
lean_object* v_a_2734_; 
v_a_2734_ = lean_ctor_get(v___x_2731_, 0);
lean_inc_ref(v_a_2734_);
lean_dec_ref(v___x_2731_);
v_val_2713_ = v_a_2734_;
goto v___jp_2712_;
}
v___jp_2712_:
{
lean_object* v___x_2714_; 
v___x_2714_ = lean_task_get_own(v_val_2713_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2717_ = v___x_2714_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2714_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2718_ == 0)
{
lean_ctor_set_tag(v___x_2717_, 1);
v___x_2720_ = v___x_2717_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
v_a_2723_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2714_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2714_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
lean_ctor_set_tag(v___x_2725_, 0);
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_wait___boxed(lean_object* v_00_u03b5_2735_, lean_object* v_00_u03b1_2736_, lean_object* v_self_2737_, lean_object* v_a_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Std_Async_EAsync_wait(v_00_u03b5_2735_, v_00_u03b1_2736_, v_self_2737_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_asTask___redArg___lam__0(lean_object* v_x_2740_){
_start:
{
if (lean_obj_tag(v_x_2740_) == 0)
{
lean_object* v_a_2741_; lean_object* v___x_2742_; 
v_a_2741_ = lean_ctor_get(v_x_2740_, 0);
lean_inc(v_a_2741_);
lean_dec_ref(v_x_2740_);
v___x_2742_ = lean_task_pure(v_a_2741_);
return v___x_2742_;
}
else
{
lean_object* v_a_2743_; 
v_a_2743_ = lean_ctor_get(v_x_2740_, 0);
lean_inc_ref(v_a_2743_);
lean_dec_ref(v_x_2740_);
return v_a_2743_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_asTask___redArg(lean_object* v_x_2745_, lean_object* v_prio_2746_){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___f_2750_; lean_object* v___x_2751_; uint8_t v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2748_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2748_, 0, lean_box(0));
lean_closure_set(v___x_2748_, 1, v_x_2745_);
v___x_2749_ = lean_io_as_task(v___x_2748_, v_prio_2746_);
v___f_2750_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___x_2751_ = lean_unsigned_to_nat(0u);
v___x_2752_ = 1;
v___x_2753_ = lean_task_bind(v___x_2749_, v___f_2750_, v___x_2751_, v___x_2752_);
v___x_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_asTask___redArg___boxed(lean_object* v_x_2755_, lean_object* v_prio_2756_, lean_object* v_a_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Std_Async_EAsync_asTask___redArg(v_x_2755_, v_prio_2756_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_asTask(lean_object* v_00_u03b5_2759_, lean_object* v_00_u03b1_2760_, lean_object* v_x_2761_, lean_object* v_prio_2762_){
_start:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___f_2766_; lean_object* v___x_2767_; uint8_t v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2764_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2764_, 0, lean_box(0));
lean_closure_set(v___x_2764_, 1, v_x_2761_);
v___x_2765_ = lean_io_as_task(v___x_2764_, v_prio_2762_);
v___f_2766_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___x_2767_ = lean_unsigned_to_nat(0u);
v___x_2768_ = 1;
v___x_2769_ = lean_task_bind(v___x_2765_, v___f_2766_, v___x_2767_, v___x_2768_);
v___x_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2769_);
return v___x_2770_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_asTask___boxed(lean_object* v_00_u03b5_2771_, lean_object* v_00_u03b1_2772_, lean_object* v_x_2773_, lean_object* v_prio_2774_, lean_object* v_a_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l_Std_Async_EAsync_asTask(v_00_u03b5_2771_, v_00_u03b1_2772_, v_x_2773_, v_prio_2774_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_block___redArg(lean_object* v_x_2777_, lean_object* v_prio_2778_){
_start:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___f_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2780_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2780_, 0, lean_box(0));
lean_closure_set(v___x_2780_, 1, v_x_2777_);
v___x_2781_ = lean_io_as_task(v___x_2780_, v_prio_2778_);
v___f_2782_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___x_2783_ = lean_unsigned_to_nat(0u);
v___x_2784_ = 1;
v___x_2785_ = lean_task_bind(v___x_2781_, v___f_2782_, v___x_2783_, v___x_2784_);
v___x_2786_ = lean_task_get_own(v___x_2785_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___x_2786_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2786_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
lean_ctor_set_tag(v___x_2789_, 1);
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
v_a_2795_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2786_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2786_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
lean_ctor_set_tag(v___x_2797_, 0);
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_block___redArg___boxed(lean_object* v_x_2803_, lean_object* v_prio_2804_, lean_object* v_a_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Std_Async_EAsync_block___redArg(v_x_2803_, v_prio_2804_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_block(lean_object* v_00_u03b5_2807_, lean_object* v_00_u03b1_2808_, lean_object* v_x_2809_, lean_object* v_prio_2810_){
_start:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___f_2814_; lean_object* v___x_2815_; uint8_t v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2812_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2812_, 0, lean_box(0));
lean_closure_set(v___x_2812_, 1, v_x_2809_);
v___x_2813_ = lean_io_as_task(v___x_2812_, v_prio_2810_);
v___f_2814_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___x_2815_ = lean_unsigned_to_nat(0u);
v___x_2816_ = 1;
v___x_2817_ = lean_task_bind(v___x_2813_, v___f_2814_, v___x_2815_, v___x_2816_);
v___x_2818_ = lean_task_get_own(v___x_2817_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2818_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2818_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
lean_ctor_set_tag(v___x_2821_, 1);
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
else
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
v_a_2827_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2818_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2818_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
lean_ctor_set_tag(v___x_2829_, 0);
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2827_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_block___boxed(lean_object* v_00_u03b5_2835_, lean_object* v_00_u03b1_2836_, lean_object* v_x_2837_, lean_object* v_prio_2838_, lean_object* v_a_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l_Std_Async_EAsync_block(v_00_u03b5_2835_, v_00_u03b1_2836_, v_x_2837_, v_prio_2838_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_throw___redArg(lean_object* v_e_2841_){
_start:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2843_, 0, v_e_2841_);
v___x_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_throw___redArg___boxed(lean_object* v_e_2845_, lean_object* v_a_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l_Std_Async_EAsync_throw___redArg(v_e_2845_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_throw(lean_object* v_00_u03b5_2848_, lean_object* v_00_u03b1_2849_, lean_object* v_e_2850_){
_start:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2852_, 0, v_e_2850_);
v___x_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_throw___boxed(lean_object* v_00_u03b5_2854_, lean_object* v_00_u03b1_2855_, lean_object* v_e_2856_, lean_object* v_a_2857_){
_start:
{
lean_object* v_res_2858_; 
v_res_2858_ = l_Std_Async_EAsync_throw(v_00_u03b5_2854_, v_00_u03b1_2855_, v_e_2856_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch___redArg___lam__0(lean_object* v_f_2859_, lean_object* v_x_2860_){
_start:
{
if (lean_obj_tag(v_x_2860_) == 0)
{
lean_object* v_a_2862_; lean_object* v___x_2863_; 
v_a_2862_ = lean_ctor_get(v_x_2860_, 0);
lean_inc(v_a_2862_);
lean_dec_ref(v_x_2860_);
v___x_2863_ = lean_apply_2(v_f_2859_, v_a_2862_, lean_box(0));
return v___x_2863_;
}
else
{
lean_object* v___x_2864_; 
lean_dec_ref(v_f_2859_);
v___x_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2864_, 0, v_x_2860_);
return v___x_2864_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch___redArg___lam__0___boxed(lean_object* v_f_2865_, lean_object* v_x_2866_, lean_object* v___y_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = l_Std_Async_EAsync_tryCatch___redArg___lam__0(v_f_2865_, v_x_2866_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch___redArg(lean_object* v_x_2869_, lean_object* v_f_2870_, lean_object* v_prio_2871_, uint8_t v_sync_2872_){
_start:
{
lean_object* v___x_2874_; lean_object* v___f_2875_; lean_object* v___x_2876_; 
v___x_2874_ = lean_apply_1(v_x_2869_, lean_box(0));
v___f_2875_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_tryCatch___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2875_, 0, v_f_2870_);
v___x_2876_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_2871_, v_sync_2872_, v___x_2874_, v___f_2875_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch___redArg___boxed(lean_object* v_x_2877_, lean_object* v_f_2878_, lean_object* v_prio_2879_, lean_object* v_sync_2880_, lean_object* v_a_2881_){
_start:
{
uint8_t v_sync_boxed_2882_; lean_object* v_res_2883_; 
v_sync_boxed_2882_ = lean_unbox(v_sync_2880_);
v_res_2883_ = l_Std_Async_EAsync_tryCatch___redArg(v_x_2877_, v_f_2878_, v_prio_2879_, v_sync_boxed_2882_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch(lean_object* v_00_u03b5_2884_, lean_object* v_00_u03b1_2885_, lean_object* v_x_2886_, lean_object* v_f_2887_, lean_object* v_prio_2888_, uint8_t v_sync_2889_){
_start:
{
lean_object* v___x_2891_; lean_object* v___f_2892_; lean_object* v___x_2893_; 
v___x_2891_ = lean_apply_1(v_x_2886_, lean_box(0));
v___f_2892_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_tryCatch___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2892_, 0, v_f_2887_);
v___x_2893_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_2888_, v_sync_2889_, v___x_2891_, v___f_2892_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch___boxed(lean_object* v_00_u03b5_2894_, lean_object* v_00_u03b1_2895_, lean_object* v_x_2896_, lean_object* v_f_2897_, lean_object* v_prio_2898_, lean_object* v_sync_2899_, lean_object* v_a_2900_){
_start:
{
uint8_t v_sync_boxed_2901_; lean_object* v_res_2902_; 
v_sync_boxed_2901_ = lean_unbox(v_sync_2899_);
v_res_2902_ = l_Std_Async_EAsync_tryCatch(v_00_u03b5_2894_, v_00_u03b1_2895_, v_x_2896_, v_f_2897_, v_prio_2898_, v_sync_boxed_2901_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__0(lean_object* v_a_2903_, lean_object* v_____do__lift_2904_){
_start:
{
if (lean_obj_tag(v_____do__lift_2904_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2914_; 
lean_dec(v_a_2903_);
v_a_2906_ = lean_ctor_get(v_____do__lift_2904_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v_____do__lift_2904_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2908_ = v_____do__lift_2904_;
v_isShared_2909_ = v_isSharedCheck_2914_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v_____do__lift_2904_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2914_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
lean_object* v___x_2912_; 
v___x_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2911_);
return v___x_2912_;
}
}
}
else
{
lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2922_; 
v_isSharedCheck_2922_ = !lean_is_exclusive(v_____do__lift_2904_);
if (v_isSharedCheck_2922_ == 0)
{
lean_object* v_unused_2923_; 
v_unused_2923_ = lean_ctor_get(v_____do__lift_2904_, 0);
lean_dec(v_unused_2923_);
v___x_2916_ = v_____do__lift_2904_;
v_isShared_2917_ = v_isSharedCheck_2922_;
goto v_resetjp_2915_;
}
else
{
lean_dec(v_____do__lift_2904_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2922_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
lean_ctor_set_tag(v___x_2916_, 0);
lean_ctor_set(v___x_2916_, 0, v_a_2903_);
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2903_);
v___x_2919_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
lean_object* v___x_2920_; 
v___x_2920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2919_);
return v___x_2920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__0___boxed(lean_object* v_a_2924_, lean_object* v_____do__lift_2925_, lean_object* v___y_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l_Std_Async_EAsync_tryFinally_x27___redArg___lam__0(v_a_2924_, v_____do__lift_2925_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__1(lean_object* v_a_2928_, lean_object* v_____do__lift_2929_){
_start:
{
if (lean_obj_tag(v_____do__lift_2929_) == 0)
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2939_; 
lean_dec(v_a_2928_);
v_a_2931_ = lean_ctor_get(v_____do__lift_2929_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v_____do__lift_2929_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2933_ = v_____do__lift_2929_;
v_isShared_2934_ = v_isSharedCheck_2939_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v_____do__lift_2929_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2939_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_a_2931_);
v___x_2936_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
lean_object* v___x_2937_; 
v___x_2937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2936_);
return v___x_2937_;
}
}
}
else
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2949_; 
v_a_2940_ = lean_ctor_get(v_____do__lift_2929_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v_____do__lift_2929_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2942_ = v_____do__lift_2929_;
v_isShared_2943_ = v_isSharedCheck_2949_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v_____do__lift_2929_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2949_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2944_; lean_object* v___x_2946_; 
v___x_2944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2944_, 0, v_a_2928_);
lean_ctor_set(v___x_2944_, 1, v_a_2940_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 0, v___x_2944_);
v___x_2946_ = v___x_2942_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v___x_2944_);
v___x_2946_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
lean_object* v___x_2947_; 
v___x_2947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2946_);
return v___x_2947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__1___boxed(lean_object* v_a_2950_, lean_object* v_____do__lift_2951_, lean_object* v___y_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l_Std_Async_EAsync_tryFinally_x27___redArg___lam__1(v_a_2950_, v_____do__lift_2951_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__2(lean_object* v_f_2954_, lean_object* v_x_2955_){
_start:
{
if (lean_obj_tag(v_x_2955_) == 0)
{
lean_object* v_a_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___f_2960_; lean_object* v___x_2961_; uint8_t v___x_2962_; lean_object* v___x_2963_; 
v_a_2957_ = lean_ctor_get(v_x_2955_, 0);
lean_inc(v_a_2957_);
lean_dec_ref(v_x_2955_);
v___x_2958_ = lean_box(0);
v___x_2959_ = lean_apply_2(v_f_2954_, v___x_2958_, lean_box(0));
v___f_2960_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_tryFinally_x27___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2960_, 0, v_a_2957_);
v___x_2961_ = lean_unsigned_to_nat(0u);
v___x_2962_ = 0;
v___x_2963_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2961_, v___x_2962_, v___x_2959_, v___f_2960_);
return v___x_2963_;
}
else
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2976_; 
v_a_2964_ = lean_ctor_get(v_x_2955_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v_x_2955_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2966_ = v_x_2955_;
v_isShared_2967_ = v_isSharedCheck_2976_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v_x_2955_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2976_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2969_; 
lean_inc(v_a_2964_);
if (v_isShared_2967_ == 0)
{
v___x_2969_ = v___x_2966_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2964_);
v___x_2969_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
lean_object* v___x_2970_; lean_object* v___f_2971_; lean_object* v___x_2972_; uint8_t v___x_2973_; lean_object* v___x_2974_; 
v___x_2970_ = lean_apply_2(v_f_2954_, v___x_2969_, lean_box(0));
v___f_2971_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_tryFinally_x27___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2971_, 0, v_a_2964_);
v___x_2972_ = lean_unsigned_to_nat(0u);
v___x_2973_ = 0;
v___x_2974_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2972_, v___x_2973_, v___x_2970_, v___f_2971_);
return v___x_2974_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__2___boxed(lean_object* v_f_2977_, lean_object* v_x_2978_, lean_object* v___y_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l_Std_Async_EAsync_tryFinally_x27___redArg___lam__2(v_f_2977_, v_x_2978_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg(lean_object* v_x_2981_, lean_object* v_f_2982_, lean_object* v_prio_2983_, uint8_t v_sync_2984_){
_start:
{
lean_object* v___x_2986_; lean_object* v___f_2987_; lean_object* v___x_2988_; 
v___x_2986_ = lean_apply_1(v_x_2981_, lean_box(0));
v___f_2987_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_tryFinally_x27___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2987_, 0, v_f_2982_);
v___x_2988_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_2983_, v_sync_2984_, v___x_2986_, v___f_2987_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___boxed(lean_object* v_x_2989_, lean_object* v_f_2990_, lean_object* v_prio_2991_, lean_object* v_sync_2992_, lean_object* v_a_2993_){
_start:
{
uint8_t v_sync_boxed_2994_; lean_object* v_res_2995_; 
v_sync_boxed_2994_ = lean_unbox(v_sync_2992_);
v_res_2995_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v_x_2989_, v_f_2990_, v_prio_2991_, v_sync_boxed_2994_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27(lean_object* v_00_u03b5_2996_, lean_object* v_00_u03b1_2997_, lean_object* v_00_u03b2_2998_, lean_object* v_x_2999_, lean_object* v_f_3000_, lean_object* v_prio_3001_, uint8_t v_sync_3002_){
_start:
{
lean_object* v___x_3004_; 
v___x_3004_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v_x_2999_, v_f_3000_, v_prio_3001_, v_sync_3002_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___boxed(lean_object* v_00_u03b5_3005_, lean_object* v_00_u03b1_3006_, lean_object* v_00_u03b2_3007_, lean_object* v_x_3008_, lean_object* v_f_3009_, lean_object* v_prio_3010_, lean_object* v_sync_3011_, lean_object* v_a_3012_){
_start:
{
uint8_t v_sync_boxed_3013_; lean_object* v_res_3014_; 
v_sync_boxed_3013_ = lean_unbox(v_sync_3011_);
v_res_3014_ = l_Std_Async_EAsync_tryFinally_x27(v_00_u03b5_3005_, v_00_u03b1_3006_, v_00_u03b2_3007_, v_x_3008_, v_f_3009_, v_prio_3010_, v_sync_boxed_3013_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_await___redArg(lean_object* v_x_3015_){
_start:
{
lean_object* v___x_3017_; 
v___x_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3017_, 0, v_x_3015_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_await___redArg___boxed(lean_object* v_x_3018_, lean_object* v_a_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l_Std_Async_EAsync_await___redArg(v_x_3018_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_await(lean_object* v_00_u03b5_3021_, lean_object* v_00_u03b1_3022_, lean_object* v_x_3023_){
_start:
{
lean_object* v___x_3025_; 
v___x_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3025_, 0, v_x_3023_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_await___boxed(lean_object* v_00_u03b5_3026_, lean_object* v_00_u03b1_3027_, lean_object* v_x_3028_, lean_object* v_a_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_Std_Async_EAsync_await(v_00_u03b5_3026_, v_00_u03b1_3027_, v_x_3028_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_async___redArg(lean_object* v_self_3031_, lean_object* v_prio_3032_){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___f_3036_; lean_object* v___x_3037_; uint8_t v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3034_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_3034_, 0, lean_box(0));
lean_closure_set(v___x_3034_, 1, v_self_3031_);
v___x_3035_ = lean_io_as_task(v___x_3034_, v_prio_3032_);
v___f_3036_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___x_3037_ = lean_unsigned_to_nat(0u);
v___x_3038_ = 1;
v___x_3039_ = lean_task_bind(v___x_3035_, v___f_3036_, v___x_3037_, v___x_3038_);
v___x_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
v___x_3041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3040_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_async___redArg___boxed(lean_object* v_self_3042_, lean_object* v_prio_3043_, lean_object* v_a_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l_Std_Async_EAsync_async___redArg(v_self_3042_, v_prio_3043_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_async(lean_object* v_00_u03b5_3046_, lean_object* v_00_u03b1_3047_, lean_object* v_self_3048_, lean_object* v_prio_3049_){
_start:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___f_3053_; lean_object* v___x_3054_; uint8_t v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3051_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_3051_, 0, lean_box(0));
lean_closure_set(v___x_3051_, 1, v_self_3048_);
v___x_3052_ = lean_io_as_task(v___x_3051_, v_prio_3049_);
v___f_3053_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___x_3054_ = lean_unsigned_to_nat(0u);
v___x_3055_ = 1;
v___x_3056_ = lean_task_bind(v___x_3052_, v___f_3053_, v___x_3054_, v___x_3055_);
v___x_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3056_);
v___x_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3057_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_async___boxed(lean_object* v_00_u03b5_3059_, lean_object* v_00_u03b1_3060_, lean_object* v_self_3061_, lean_object* v_prio_3062_, lean_object* v_a_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_Std_Async_EAsync_async(v_00_u03b5_3059_, v_00_u03b1_3060_, v_self_3061_, v_prio_3062_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___lam__0(lean_object* v_00_u03b1_3065_, lean_object* v_00_u03b2_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_){
_start:
{
lean_object* v___x_3070_; lean_object* v___y_3072_; 
v___x_3070_ = lean_apply_1(v___y_3068_, lean_box(0));
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v_a_3074_; 
v_a_3074_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_a_3074_);
lean_dec_ref(v___x_3070_);
if (lean_obj_tag(v_a_3074_) == 0)
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
lean_dec(v___y_3067_);
v_a_3075_ = lean_ctor_get(v_a_3074_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v_a_3074_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3077_ = v_a_3074_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v_a_3074_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3075_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
v___y_3072_ = v___x_3080_;
goto v___jp_3071_;
}
}
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3091_; 
v_a_3083_ = lean_ctor_get(v_a_3074_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v_a_3074_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3085_ = v_a_3074_;
v_isShared_3086_ = v_isSharedCheck_3091_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v_a_3074_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3091_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3087_; lean_object* v___x_3089_; 
v___x_3087_ = lean_apply_1(v___y_3067_, v_a_3083_);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 0, v___x_3087_);
v___x_3089_ = v___x_3085_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v___x_3087_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
v___y_3072_ = v___x_3089_;
goto v___jp_3071_;
}
}
}
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3103_; 
v_a_3092_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3094_ = v___x_3070_;
v_isShared_3095_ = v_isSharedCheck_3103_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3070_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3103_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; uint8_t v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3101_; 
v___x_3096_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_3096_, 0, lean_box(0));
lean_closure_set(v___x_3096_, 1, lean_box(0));
lean_closure_set(v___x_3096_, 2, lean_box(0));
lean_closure_set(v___x_3096_, 3, v___y_3067_);
v___x_3097_ = lean_unsigned_to_nat(0u);
v___x_3098_ = 0;
v___x_3099_ = lean_task_map(v___x_3096_, v_a_3092_, v___x_3097_, v___x_3098_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v___x_3099_);
v___x_3101_ = v___x_3094_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3099_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
v___jp_3071_:
{
lean_object* v___x_3073_; 
v___x_3073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3073_, 0, v___y_3072_);
return v___x_3073_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___lam__0___boxed(lean_object* v_00_u03b1_3104_, lean_object* v_00_u03b2_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v_res_3109_; 
v_res_3109_ = l_Std_Async_EAsync_instFunctor___lam__0(v_00_u03b1_3104_, v_00_u03b2_3105_, v___y_3106_, v___y_3107_);
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___lam__1(lean_object* v___f_3110_, lean_object* v_00_u03b1_3111_, lean_object* v_00_u03b2_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3116_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_3116_, 0, lean_box(0));
lean_closure_set(v___x_3116_, 1, lean_box(0));
lean_closure_set(v___x_3116_, 2, v___y_3113_);
v___x_3117_ = lean_apply_5(v___f_3110_, lean_box(0), lean_box(0), v___x_3116_, v___y_3114_, lean_box(0));
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___lam__1___boxed(lean_object* v___f_3118_, lean_object* v_00_u03b1_3119_, lean_object* v_00_u03b2_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l_Std_Async_EAsync_instFunctor___lam__1(v___f_3118_, v_00_u03b1_3119_, v_00_u03b2_3120_, v___y_3121_, v___y_3122_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor(lean_object* v_00_u03b5_3131_){
_start:
{
lean_object* v___x_3132_; 
v___x_3132_ = ((lean_object*)(l_Std_Async_EAsync_instFunctor___closed__2));
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__0(lean_object* v_00_u03b1_3133_, lean_object* v___y_3134_){
_start:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3136_, 0, v___y_3134_);
v___x_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3136_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__0___boxed(lean_object* v_00_u03b1_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_){
_start:
{
lean_object* v_res_3141_; 
v_res_3141_ = l_Std_Async_EAsync_instMonad___lam__0(v_00_u03b1_3138_, v___y_3139_);
return v_res_3141_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__1(lean_object* v_x_3142_, lean_object* v_x_3143_){
_start:
{
if (lean_obj_tag(v_x_3143_) == 0)
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3153_; 
lean_dec_ref(v_x_3142_);
v_a_3145_ = lean_ctor_get(v_x_3143_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v_x_3143_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3147_ = v_x_3143_;
v_isShared_3148_ = v_isSharedCheck_3153_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v_x_3143_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3153_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_a_3145_);
v___x_3150_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
lean_object* v___x_3151_; 
v___x_3151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3150_);
return v___x_3151_;
}
}
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___y_3158_; 
v_a_3154_ = lean_ctor_get(v_x_3143_, 0);
lean_inc(v_a_3154_);
lean_dec_ref(v_x_3143_);
v___x_3155_ = lean_box(0);
v___x_3156_ = lean_apply_2(v_x_3142_, v___x_3155_, lean_box(0));
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_object* v_a_3160_; 
v_a_3160_ = lean_ctor_get(v___x_3156_, 0);
lean_inc(v_a_3160_);
lean_dec_ref(v___x_3156_);
if (lean_obj_tag(v_a_3160_) == 0)
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
lean_dec(v_a_3154_);
v_a_3161_ = lean_ctor_get(v_a_3160_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v_a_3160_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v_a_3160_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v_a_3160_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
v___y_3158_ = v___x_3166_;
goto v___jp_3157_;
}
}
}
else
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3177_; 
v_a_3169_ = lean_ctor_get(v_a_3160_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v_a_3160_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3171_ = v_a_3160_;
v_isShared_3172_ = v_isSharedCheck_3177_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v_a_3160_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3177_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3173_; lean_object* v___x_3175_; 
v___x_3173_ = lean_apply_1(v_a_3154_, v_a_3169_);
if (v_isShared_3172_ == 0)
{
lean_ctor_set(v___x_3171_, 0, v___x_3173_);
v___x_3175_ = v___x_3171_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v___x_3173_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
v___y_3158_ = v___x_3175_;
goto v___jp_3157_;
}
}
}
}
else
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3189_; 
v_a_3178_ = lean_ctor_get(v___x_3156_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3180_ = v___x_3156_;
v_isShared_3181_ = v_isSharedCheck_3189_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3156_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3189_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; uint8_t v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3187_; 
v___x_3182_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_3182_, 0, lean_box(0));
lean_closure_set(v___x_3182_, 1, lean_box(0));
lean_closure_set(v___x_3182_, 2, lean_box(0));
lean_closure_set(v___x_3182_, 3, v_a_3154_);
v___x_3183_ = lean_unsigned_to_nat(0u);
v___x_3184_ = 0;
v___x_3185_ = lean_task_map(v___x_3182_, v_a_3178_, v___x_3183_, v___x_3184_);
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 0, v___x_3185_);
v___x_3187_ = v___x_3180_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3185_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
v___jp_3157_:
{
lean_object* v___x_3159_; 
v___x_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3159_, 0, v___y_3158_);
return v___x_3159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__1___boxed(lean_object* v_x_3190_, lean_object* v_x_3191_, lean_object* v___y_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l_Std_Async_EAsync_instMonad___lam__1(v_x_3190_, v_x_3191_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__2(lean_object* v_00_u03b1_3194_, lean_object* v_00_u03b2_3195_, lean_object* v_f_3196_, lean_object* v_x_3197_){
_start:
{
lean_object* v___x_3199_; lean_object* v___f_3200_; lean_object* v___x_3201_; uint8_t v___x_3202_; lean_object* v___x_3203_; 
v___x_3199_ = lean_apply_1(v_f_3196_, lean_box(0));
v___f_3200_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_instMonad___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3200_, 0, v_x_3197_);
v___x_3201_ = lean_unsigned_to_nat(0u);
v___x_3202_ = 0;
v___x_3203_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3201_, v___x_3202_, v___x_3199_, v___f_3200_);
return v___x_3203_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__2___boxed(lean_object* v_00_u03b1_3204_, lean_object* v_00_u03b2_3205_, lean_object* v_f_3206_, lean_object* v_x_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l_Std_Async_EAsync_instMonad___lam__2(v_00_u03b1_3204_, v_00_u03b2_3205_, v_f_3206_, v_x_3207_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__3(lean_object* v___f_3210_, lean_object* v_a_3211_, lean_object* v_x_3212_){
_start:
{
if (lean_obj_tag(v_x_3212_) == 0)
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3222_; 
lean_dec(v_a_3211_);
lean_dec_ref(v___f_3210_);
v_a_3214_ = lean_ctor_get(v_x_3212_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v_x_3212_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3216_ = v_x_3212_;
v_isShared_3217_ = v_isSharedCheck_3222_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v_x_3212_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3222_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3219_; 
if (v_isShared_3217_ == 0)
{
v___x_3219_ = v___x_3216_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3214_);
v___x_3219_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
lean_object* v___x_3220_; 
v___x_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3219_);
return v___x_3220_;
}
}
}
else
{
lean_object* v___x_3223_; 
lean_dec_ref(v_x_3212_);
v___x_3223_ = lean_apply_3(v___f_3210_, lean_box(0), v_a_3211_, lean_box(0));
return v___x_3223_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__3___boxed(lean_object* v___f_3224_, lean_object* v_a_3225_, lean_object* v_x_3226_, lean_object* v___y_3227_){
_start:
{
lean_object* v_res_3228_; 
v_res_3228_ = l_Std_Async_EAsync_instMonad___lam__3(v___f_3224_, v_a_3225_, v_x_3226_);
return v_res_3228_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__4(lean_object* v_y_3229_, lean_object* v___f_3230_, lean_object* v_x_3231_){
_start:
{
if (lean_obj_tag(v_x_3231_) == 0)
{
lean_object* v___x_3233_; 
lean_dec_ref(v___f_3230_);
lean_dec_ref(v_y_3229_);
v___x_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3233_, 0, v_x_3231_);
return v___x_3233_;
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___f_3237_; lean_object* v___x_3238_; uint8_t v___x_3239_; lean_object* v___x_3240_; 
v_a_3234_ = lean_ctor_get(v_x_3231_, 0);
lean_inc(v_a_3234_);
lean_dec_ref(v_x_3231_);
v___x_3235_ = lean_box(0);
v___x_3236_ = lean_apply_2(v_y_3229_, v___x_3235_, lean_box(0));
v___f_3237_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_instMonad___lam__3___boxed), 4, 2);
lean_closure_set(v___f_3237_, 0, v___f_3230_);
lean_closure_set(v___f_3237_, 1, v_a_3234_);
v___x_3238_ = lean_unsigned_to_nat(0u);
v___x_3239_ = 0;
v___x_3240_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3238_, v___x_3239_, v___x_3236_, v___f_3237_);
return v___x_3240_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__4___boxed(lean_object* v_y_3241_, lean_object* v___f_3242_, lean_object* v_x_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l_Std_Async_EAsync_instMonad___lam__4(v_y_3241_, v___f_3242_, v_x_3243_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__5(lean_object* v___f_3246_, lean_object* v_00_u03b1_3247_, lean_object* v_00_u03b2_3248_, lean_object* v_x_3249_, lean_object* v_y_3250_){
_start:
{
lean_object* v___x_3252_; lean_object* v___f_3253_; lean_object* v___x_3254_; uint8_t v___x_3255_; lean_object* v___x_3256_; 
v___x_3252_ = lean_apply_1(v_x_3249_, lean_box(0));
v___f_3253_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_instMonad___lam__4___boxed), 4, 2);
lean_closure_set(v___f_3253_, 0, v_y_3250_);
lean_closure_set(v___f_3253_, 1, v___f_3246_);
v___x_3254_ = lean_unsigned_to_nat(0u);
v___x_3255_ = 0;
v___x_3256_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3254_, v___x_3255_, v___x_3252_, v___f_3253_);
return v___x_3256_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__5___boxed(lean_object* v___f_3257_, lean_object* v_00_u03b1_3258_, lean_object* v_00_u03b2_3259_, lean_object* v_x_3260_, lean_object* v_y_3261_, lean_object* v___y_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l_Std_Async_EAsync_instMonad___lam__5(v___f_3257_, v_00_u03b1_3258_, v_00_u03b2_3259_, v_x_3260_, v_y_3261_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__6(lean_object* v_y_3264_, lean_object* v_x_3265_){
_start:
{
if (lean_obj_tag(v_x_3265_) == 0)
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3275_; 
lean_dec_ref(v_y_3264_);
v_a_3267_ = lean_ctor_get(v_x_3265_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v_x_3265_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3269_ = v_x_3265_;
v_isShared_3270_ = v_isSharedCheck_3275_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v_x_3265_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3275_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3272_; 
if (v_isShared_3270_ == 0)
{
v___x_3272_ = v___x_3269_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_a_3267_);
v___x_3272_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
lean_object* v___x_3273_; 
v___x_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3272_);
return v___x_3273_;
}
}
}
else
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
lean_dec_ref(v_x_3265_);
v___x_3276_ = lean_box(0);
v___x_3277_ = lean_apply_2(v_y_3264_, v___x_3276_, lean_box(0));
return v___x_3277_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__6___boxed(lean_object* v_y_3278_, lean_object* v_x_3279_, lean_object* v___y_3280_){
_start:
{
lean_object* v_res_3281_; 
v_res_3281_ = l_Std_Async_EAsync_instMonad___lam__6(v_y_3278_, v_x_3279_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__7(lean_object* v_00_u03b1_3282_, lean_object* v_00_u03b2_3283_, lean_object* v_x_3284_, lean_object* v_y_3285_){
_start:
{
lean_object* v___x_3287_; lean_object* v___f_3288_; lean_object* v___x_3289_; uint8_t v___x_3290_; lean_object* v___x_3291_; 
v___x_3287_ = lean_apply_1(v_x_3284_, lean_box(0));
v___f_3288_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_instMonad___lam__6___boxed), 3, 1);
lean_closure_set(v___f_3288_, 0, v_y_3285_);
v___x_3289_ = lean_unsigned_to_nat(0u);
v___x_3290_ = 0;
v___x_3291_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3289_, v___x_3290_, v___x_3287_, v___f_3288_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___lam__7___boxed(lean_object* v_00_u03b1_3292_, lean_object* v_00_u03b2_3293_, lean_object* v_x_3294_, lean_object* v_y_3295_, lean_object* v___y_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l_Std_Async_EAsync_instMonad___lam__7(v_00_u03b1_3292_, v_00_u03b2_3293_, v_x_3294_, v_y_3295_);
return v_res_3297_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonad___closed__4(void){
_start:
{
lean_object* v___x_3303_; 
v___x_3303_ = l_Std_Async_EAsync_instFunctor(lean_box(0));
return v___x_3303_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonad___closed__5(void){
_start:
{
lean_object* v___f_3304_; lean_object* v___f_3305_; lean_object* v___f_3306_; lean_object* v___f_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___f_3304_ = ((lean_object*)(l_Std_Async_EAsync_instMonad___closed__3));
v___f_3305_ = ((lean_object*)(l_Std_Async_EAsync_instMonad___closed__2));
v___f_3306_ = ((lean_object*)(l_Std_Async_EAsync_instMonad___closed__1));
v___f_3307_ = ((lean_object*)(l_Std_Async_EAsync_instMonad___closed__0));
v___x_3308_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___closed__4, &l_Std_Async_EAsync_instMonad___closed__4_once, _init_l_Std_Async_EAsync_instMonad___closed__4);
v___x_3309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3308_);
lean_ctor_set(v___x_3309_, 1, v___f_3307_);
lean_ctor_set(v___x_3309_, 2, v___f_3306_);
lean_ctor_set(v___x_3309_, 3, v___f_3305_);
lean_ctor_set(v___x_3309_, 4, v___f_3304_);
return v___x_3309_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonad___closed__7(void){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3311_ = ((lean_object*)(l_Std_Async_EAsync_instMonad___closed__6));
v___x_3312_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___closed__5, &l_Std_Async_EAsync_instMonad___closed__5_once, _init_l_Std_Async_EAsync_instMonad___closed__5);
v___x_3313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3312_);
lean_ctor_set(v___x_3313_, 1, v___x_3311_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad(lean_object* v_00_u03b5_3314_){
_start:
{
lean_object* v___x_3315_; 
v___x_3315_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___closed__7, &l_Std_Async_EAsync_instMonad___closed__7_once, _init_l_Std_Async_EAsync_instMonad___closed__7);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO(lean_object* v_00_u03b5_3317_){
_start:
{
lean_object* v___x_3318_; 
v___x_3318_ = ((lean_object*)(l_Std_Async_EAsync_instMonadLiftEIO___closed__0));
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExcept___lam__1(lean_object* v_00_u03b1_3319_, lean_object* v_x_3320_, lean_object* v_f_3321_){
_start:
{
lean_object* v___x_3323_; lean_object* v___f_3324_; lean_object* v___x_3325_; uint8_t v___x_3326_; lean_object* v___x_3327_; 
v___x_3323_ = lean_apply_1(v_x_3320_, lean_box(0));
v___f_3324_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_tryCatch___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3324_, 0, v_f_3321_);
v___x_3325_ = lean_unsigned_to_nat(0u);
v___x_3326_ = 0;
v___x_3327_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3325_, v___x_3326_, v___x_3323_, v___f_3324_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExcept___lam__1___boxed(lean_object* v_00_u03b1_3328_, lean_object* v_x_3329_, lean_object* v_f_3330_, lean_object* v___y_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = l_Std_Async_EAsync_instMonadExcept___lam__1(v_00_u03b1_3328_, v_x_3329_, v_f_3330_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExcept(lean_object* v_00_u03b5_3338_){
_start:
{
lean_object* v___x_3339_; 
v___x_3339_ = ((lean_object*)(l_Std_Async_EAsync_instMonadExcept___closed__2));
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExceptOf(lean_object* v_00_u03b5_3343_){
_start:
{
lean_object* v___x_3344_; 
v___x_3344_ = ((lean_object*)(l_Std_Async_EAsync_instMonadExceptOf___closed__0));
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadFinally___lam__0(lean_object* v_00_u03b1_3345_, lean_object* v_00_u03b2_3346_, lean_object* v_x_3347_, lean_object* v_f_3348_){
_start:
{
lean_object* v___x_3350_; uint8_t v___x_3351_; lean_object* v___x_3352_; 
v___x_3350_ = lean_unsigned_to_nat(0u);
v___x_3351_ = 0;
v___x_3352_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v_x_3347_, v_f_3348_, v___x_3350_, v___x_3351_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadFinally___lam__0___boxed(lean_object* v_00_u03b1_3353_, lean_object* v_00_u03b2_3354_, lean_object* v_x_3355_, lean_object* v_f_3356_, lean_object* v___y_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l_Std_Async_EAsync_instMonadFinally___lam__0(v_00_u03b1_3353_, v_00_u03b2_3354_, v_x_3355_, v_f_3356_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadFinally(lean_object* v_00_u03b5_3360_){
_start:
{
lean_object* v___f_3361_; 
v___f_3361_ = ((lean_object*)(l_Std_Async_EAsync_instMonadFinally___closed__0));
return v___f_3361_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instOrElse___closed__0(void){
_start:
{
lean_object* v___x_3362_; 
v___x_3362_ = l_Std_Async_EAsync_instMonadExcept(lean_box(0));
return v___x_3362_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instOrElse___closed__1(void){
_start:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3363_ = lean_obj_once(&l_Std_Async_EAsync_instOrElse___closed__0, &l_Std_Async_EAsync_instOrElse___closed__0_once, _init_l_Std_Async_EAsync_instOrElse___closed__0);
v___x_3364_ = lean_alloc_closure((void*)(l_MonadExcept_orElse), 6, 4);
lean_closure_set(v___x_3364_, 0, lean_box(0));
lean_closure_set(v___x_3364_, 1, lean_box(0));
lean_closure_set(v___x_3364_, 2, v___x_3363_);
lean_closure_set(v___x_3364_, 3, lean_box(0));
return v___x_3364_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instOrElse(lean_object* v_00_u03b5_3365_, lean_object* v_00_u03b1_3366_){
_start:
{
lean_object* v___x_3367_; 
v___x_3367_ = lean_obj_once(&l_Std_Async_EAsync_instOrElse___closed__1, &l_Std_Async_EAsync_instOrElse___closed__1_once, _init_l_Std_Async_EAsync_instOrElse___closed__1);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instInhabited___redArg(lean_object* v_inst_3368_){
_start:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___x_3369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3369_, 0, v_inst_3368_);
v___x_3370_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_pure___boxed), 3, 2);
lean_closure_set(v___x_3370_, 0, lean_box(0));
lean_closure_set(v___x_3370_, 1, v___x_3369_);
v___x_3371_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_mk___boxed), 3, 2);
lean_closure_set(v___x_3371_, 0, lean_box(0));
lean_closure_set(v___x_3371_, 1, v___x_3370_);
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instInhabited(lean_object* v_00_u03b5_3372_, lean_object* v_00_u03b1_3373_, lean_object* v_inst_3374_){
_start:
{
lean_object* v___x_3375_; 
v___x_3375_ = l_Std_Async_EAsync_instInhabited___redArg(v_inst_3374_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitETask___lam__0(lean_object* v_00_u03b1_3376_, lean_object* v_t_3377_){
_start:
{
lean_object* v___x_3379_; 
v___x_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3379_, 0, v_t_3377_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitETask___lam__0___boxed(lean_object* v_00_u03b1_3380_, lean_object* v_t_3381_, lean_object* v___y_3382_){
_start:
{
lean_object* v_res_3383_; 
v_res_3383_ = l_Std_Async_EAsync_instMonadAwaitETask___lam__0(v_00_u03b1_3380_, v_t_3381_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitETask(lean_object* v_00_u03b5_3385_){
_start:
{
lean_object* v___f_3386_; 
v___f_3386_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAwaitETask___closed__0));
return v___f_3386_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitTask___lam__1(lean_object* v___f_3387_, lean_object* v_00_u03b1_3388_, lean_object* v_t_3389_){
_start:
{
lean_object* v___x_3391_; uint8_t v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3391_ = lean_unsigned_to_nat(0u);
v___x_3392_ = 0;
v___x_3393_ = lean_task_map(v___f_3387_, v_t_3389_, v___x_3391_, v___x_3392_);
v___x_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3393_);
return v___x_3394_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitTask___lam__1___boxed(lean_object* v___f_3395_, lean_object* v_00_u03b1_3396_, lean_object* v_t_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v_res_3399_; 
v_res_3399_ = l_Std_Async_EAsync_instMonadAwaitTask___lam__1(v___f_3395_, v_00_u03b1_3396_, v_t_3397_);
return v_res_3399_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitTask(lean_object* v_00_u03b5_3402_){
_start:
{
lean_object* v___f_3403_; 
v___f_3403_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAwaitTask___closed__0));
return v___f_3403_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___lam__0(lean_object* v_00_u03b1_3404_, lean_object* v_t_3405_){
_start:
{
lean_object* v___x_3407_; 
v___x_3407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3407_, 0, v_t_3405_);
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___lam__0___boxed(lean_object* v_00_u03b1_3408_, lean_object* v_t_3409_, lean_object* v___y_3410_){
_start:
{
lean_object* v_res_3411_; 
v_res_3411_ = l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___lam__0(v_00_u03b1_3408_, v_t_3409_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitPromise___lam__1(lean_object* v___f_3414_, lean_object* v_00_u03b1_3415_, lean_object* v_t_3416_){
_start:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; uint8_t v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3418_ = l_IO_Promise_result_x21___redArg(v_t_3416_);
v___x_3419_ = lean_unsigned_to_nat(0u);
v___x_3420_ = 0;
v___x_3421_ = lean_task_map(v___f_3414_, v___x_3418_, v___x_3419_, v___x_3420_);
v___x_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3421_);
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitPromise___lam__1___boxed(lean_object* v___f_3423_, lean_object* v_00_u03b1_3424_, lean_object* v_t_3425_, lean_object* v___y_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l_Std_Async_EAsync_instMonadAwaitPromise___lam__1(v___f_3423_, v_00_u03b1_3424_, v_t_3425_);
lean_dec(v_t_3425_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitPromise(lean_object* v_00_u03b5_3430_){
_start:
{
lean_object* v___f_3431_; 
v___f_3431_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAwaitPromise___closed__0));
return v___f_3431_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncETask___lam__1(lean_object* v___f_3432_, lean_object* v_00_u03b1_3433_, lean_object* v_t_3434_, lean_object* v_prio_3435_){
_start:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; uint8_t v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3437_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_3437_, 0, lean_box(0));
lean_closure_set(v___x_3437_, 1, v_t_3434_);
v___x_3438_ = lean_io_as_task(v___x_3437_, v_prio_3435_);
v___x_3439_ = lean_unsigned_to_nat(0u);
v___x_3440_ = 1;
v___x_3441_ = lean_task_bind(v___x_3438_, v___f_3432_, v___x_3439_, v___x_3440_);
v___x_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3441_);
v___x_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3442_);
return v___x_3443_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncETask___lam__1___boxed(lean_object* v___f_3444_, lean_object* v_00_u03b1_3445_, lean_object* v_t_3446_, lean_object* v_prio_3447_, lean_object* v___y_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l_Std_Async_EAsync_instMonadAsyncETask___lam__1(v___f_3444_, v_00_u03b1_3445_, v_t_3446_, v_prio_3447_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncETask(lean_object* v_00_u03b5_3452_){
_start:
{
lean_object* v___f_3453_; 
v___f_3453_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncETask___closed__0));
return v___f_3453_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__0(lean_object* v_x_3454_){
_start:
{
if (lean_obj_tag(v_x_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v___x_3456_; 
v_a_3455_ = lean_ctor_get(v_x_3454_, 0);
lean_inc(v_a_3455_);
lean_dec_ref(v_x_3454_);
v___x_3456_ = lean_task_pure(v_a_3455_);
return v___x_3456_;
}
else
{
lean_object* v_a_3457_; 
v_a_3457_ = lean_ctor_get(v_x_3454_, 0);
lean_inc_ref(v_a_3457_);
lean_dec_ref(v_x_3454_);
return v_a_3457_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__1(lean_object* v___f_3458_, lean_object* v_00_u03b1_3459_, lean_object* v_t_3460_, lean_object* v_prio_3461_){
_start:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; uint8_t v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3463_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_3463_, 0, lean_box(0));
lean_closure_set(v___x_3463_, 1, v_t_3460_);
v___x_3464_ = lean_io_as_task(v___x_3463_, v_prio_3461_);
v___x_3465_ = lean_unsigned_to_nat(0u);
v___x_3466_ = 1;
v___x_3467_ = lean_task_bind(v___x_3464_, v___f_3458_, v___x_3465_, v___x_3466_);
v___x_3468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3467_);
v___x_3469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3468_);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__1___boxed(lean_object* v___f_3470_, lean_object* v_00_u03b1_3471_, lean_object* v_t_3472_, lean_object* v_prio_3473_, lean_object* v___y_3474_){
_start:
{
lean_object* v_res_3475_; 
v_res_3475_ = l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__1(v___f_3470_, v_00_u03b1_3471_, v_t_3472_, v_prio_3473_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO___lam__0(lean_object* v_00_u03b1_3480_, lean_object* v_x_3481_){
_start:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3483_ = lean_apply_1(v_x_3481_, lean_box(0));
v___x_3484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3483_);
v___x_3485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3484_);
return v___x_3485_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO___lam__0___boxed(lean_object* v_00_u03b1_3486_, lean_object* v_x_3487_, lean_object* v___y_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l_Std_Async_EAsync_instMonadLiftBaseIO___lam__0(v_00_u03b1_3486_, v_x_3487_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO(lean_object* v_00_u03b5_3491_){
_start:
{
lean_object* v___f_3492_; 
v___f_3492_ = ((lean_object*)(l_Std_Async_EAsync_instMonadLiftBaseIO___closed__0));
return v___f_3492_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1___lam__0(lean_object* v_00_u03b1_3493_, lean_object* v_x_3494_){
_start:
{
lean_object* v_val_3497_; lean_object* v___x_3499_; 
v___x_3499_ = lean_apply_1(v_x_3494_, lean_box(0));
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3507_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3502_ = v___x_3499_;
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_dec(v___x_3499_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3505_; 
if (v_isShared_3503_ == 0)
{
lean_ctor_set_tag(v___x_3502_, 1);
v___x_3505_ = v___x_3502_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_a_3500_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
v_val_3497_ = v___x_3505_;
goto v___jp_3496_;
}
}
}
else
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
v_a_3508_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___x_3499_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3499_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
lean_ctor_set_tag(v___x_3510_, 0);
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
v_val_3497_ = v___x_3513_;
goto v___jp_3496_;
}
}
}
v___jp_3496_:
{
lean_object* v___x_3498_; 
v___x_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3498_, 0, v_val_3497_);
return v___x_3498_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1___lam__0___boxed(lean_object* v_00_u03b1_3516_, lean_object* v_x_3517_, lean_object* v___y_3518_){
_start:
{
lean_object* v_res_3519_; 
v_res_3519_ = l_Std_Async_EAsync_instMonadLiftEIO__1___lam__0(v_00_u03b1_3516_, v_x_3517_);
return v_res_3519_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1(lean_object* v_00_u03b5_3521_){
_start:
{
lean_object* v___f_3522_; 
v___f_3522_ = ((lean_object*)(l_Std_Async_EAsync_instMonadLiftEIO__1___closed__0));
return v___f_3522_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___lam__1(lean_object* v___f_3523_, lean_object* v_00_u03b1_3524_, lean_object* v_x_3525_){
_start:
{
lean_object* v___x_3527_; 
v___x_3527_ = lean_apply_1(v_x_3525_, lean_box(0));
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3536_; 
lean_dec_ref(v___f_3523_);
v_a_3528_ = lean_ctor_get(v___x_3527_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3527_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3530_ = v___x_3527_;
v_isShared_3531_ = v_isSharedCheck_3536_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_3527_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3536_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3532_; lean_object* v___x_3534_; 
v___x_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3532_, 0, v_a_3528_);
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 0, v___x_3532_);
v___x_3534_ = v___x_3530_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3532_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
else
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3547_; 
v_a_3537_ = lean_ctor_get(v___x_3527_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3527_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3539_ = v___x_3527_;
v_isShared_3540_ = v_isSharedCheck_3547_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3527_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3547_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3541_; uint8_t v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3545_; 
v___x_3541_ = lean_unsigned_to_nat(0u);
v___x_3542_ = 0;
v___x_3543_ = lean_task_map(v___f_3523_, v_a_3537_, v___x_3541_, v___x_3542_);
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 0, v___x_3543_);
v___x_3545_ = v___x_3539_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v___x_3543_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___lam__1___boxed(lean_object* v___f_3548_, lean_object* v_00_u03b1_3549_, lean_object* v_x_3550_, lean_object* v___y_3551_){
_start:
{
lean_object* v_res_3552_; 
v_res_3552_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___lam__1(v___f_3548_, v_00_u03b1_3549_, v_x_3550_);
return v_res_3552_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync(lean_object* v_00_u03b5_3555_){
_start:
{
lean_object* v___f_3556_; 
v___f_3556_ = ((lean_object*)(l_Std_Async_EAsync_instMonadLiftBaseAsync___closed__0));
return v___f_3556_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___lam__0___boxed(lean_object* v_promise_3557_, lean_object* v_f_3558_, lean_object* v_prio_3559_, lean_object* v_x_3560_, lean_object* v___y_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___lam__0(v_promise_3557_, v_f_3558_, v_prio_3559_, v_x_3560_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(lean_object* v_f_3563_, lean_object* v_prio_3564_, lean_object* v_promise_3565_, lean_object* v_b_3566_){
_start:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3568_ = lean_box(0);
lean_inc_ref(v_f_3563_);
v___x_3569_ = lean_apply_3(v_f_3563_, v___x_3568_, v_b_3566_, lean_box(0));
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_object* v_a_3570_; 
v_a_3570_ = lean_ctor_get(v___x_3569_, 0);
lean_inc(v_a_3570_);
lean_dec_ref(v___x_3569_);
if (lean_obj_tag(v_a_3570_) == 0)
{
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3579_; 
lean_dec(v_prio_3564_);
lean_dec_ref(v_f_3563_);
v_a_3571_ = lean_ctor_get(v_a_3570_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v_a_3570_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3573_ = v_a_3570_;
v_isShared_3574_ = v_isSharedCheck_3579_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v_a_3570_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3579_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3576_; 
if (v_isShared_3574_ == 0)
{
v___x_3576_ = v___x_3573_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_a_3571_);
v___x_3576_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
lean_object* v___x_3577_; 
v___x_3577_ = lean_io_promise_resolve(v___x_3576_, v_promise_3565_);
lean_dec(v_promise_3565_);
return v___x_3577_;
}
}
}
else
{
lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3591_; 
v_a_3580_ = lean_ctor_get(v_a_3570_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v_a_3570_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3582_ = v_a_3570_;
v_isShared_3583_ = v_isSharedCheck_3591_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v_a_3570_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3591_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
if (lean_obj_tag(v_a_3580_) == 0)
{
lean_object* v_a_3584_; lean_object* v___x_3586_; 
lean_dec(v_prio_3564_);
lean_dec_ref(v_f_3563_);
v_a_3584_ = lean_ctor_get(v_a_3580_, 0);
lean_inc(v_a_3584_);
lean_dec_ref(v_a_3580_);
if (v_isShared_3583_ == 0)
{
lean_ctor_set(v___x_3582_, 0, v_a_3584_);
v___x_3586_ = v___x_3582_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_a_3584_);
v___x_3586_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
lean_object* v___x_3587_; 
v___x_3587_ = lean_io_promise_resolve(v___x_3586_, v_promise_3565_);
lean_dec(v_promise_3565_);
return v___x_3587_;
}
}
else
{
lean_object* v_a_3589_; 
lean_del_object(v___x_3582_);
v_a_3589_ = lean_ctor_get(v_a_3580_, 0);
lean_inc(v_a_3589_);
lean_dec_ref(v_a_3580_);
v_b_3566_ = v_a_3589_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3592_; lean_object* v___f_3593_; uint8_t v___x_3594_; lean_object* v___x_3595_; 
v_a_3592_ = lean_ctor_get(v___x_3569_, 0);
lean_inc_ref(v_a_3592_);
lean_dec_ref(v___x_3569_);
lean_inc(v_prio_3564_);
v___f_3593_ = lean_alloc_closure((void*)(l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3593_, 0, v_promise_3565_);
lean_closure_set(v___f_3593_, 1, v_f_3563_);
lean_closure_set(v___f_3593_, 2, v_prio_3564_);
v___x_3594_ = 0;
v___x_3595_ = l_BaseIO_chainTask___redArg(v_a_3592_, v___f_3593_, v_prio_3564_, v___x_3594_);
return v___x_3595_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___lam__0(lean_object* v_promise_3596_, lean_object* v_f_3597_, lean_object* v_prio_3598_, lean_object* v_x_3599_){
_start:
{
if (lean_obj_tag(v_x_3599_) == 0)
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3609_; 
lean_dec(v_prio_3598_);
lean_dec_ref(v_f_3597_);
v_a_3601_ = lean_ctor_get(v_x_3599_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v_x_3599_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3603_ = v_x_3599_;
v_isShared_3604_ = v_isSharedCheck_3609_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v_x_3599_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3609_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3606_; 
if (v_isShared_3604_ == 0)
{
v___x_3606_ = v___x_3603_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_a_3601_);
v___x_3606_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
lean_object* v___x_3607_; 
v___x_3607_ = lean_io_promise_resolve(v___x_3606_, v_promise_3596_);
lean_dec(v_promise_3596_);
return v___x_3607_;
}
}
}
else
{
lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3621_; 
v_a_3610_ = lean_ctor_get(v_x_3599_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v_x_3599_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3612_ = v_x_3599_;
v_isShared_3613_ = v_isSharedCheck_3621_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v_x_3599_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3621_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
if (lean_obj_tag(v_a_3610_) == 0)
{
lean_object* v_a_3614_; lean_object* v___x_3616_; 
lean_dec(v_prio_3598_);
lean_dec_ref(v_f_3597_);
v_a_3614_ = lean_ctor_get(v_a_3610_, 0);
lean_inc(v_a_3614_);
lean_dec_ref(v_a_3610_);
if (v_isShared_3613_ == 0)
{
lean_ctor_set(v___x_3612_, 0, v_a_3614_);
v___x_3616_ = v___x_3612_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3614_);
v___x_3616_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
lean_object* v___x_3617_; 
v___x_3617_ = lean_io_promise_resolve(v___x_3616_, v_promise_3596_);
lean_dec(v_promise_3596_);
return v___x_3617_;
}
}
else
{
lean_object* v_a_3619_; lean_object* v___x_3620_; 
lean_del_object(v___x_3612_);
v_a_3619_ = lean_ctor_get(v_a_3610_, 0);
lean_inc(v_a_3619_);
lean_dec_ref(v_a_3610_);
v___x_3620_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(v_f_3597_, v_prio_3598_, v_promise_3596_, v_a_3619_);
return v___x_3620_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___boxed(lean_object* v_f_3622_, lean_object* v_prio_3623_, lean_object* v_promise_3624_, lean_object* v_b_3625_, lean_object* v_a_3626_){
_start:
{
lean_object* v_res_3627_; 
v_res_3627_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(v_f_3622_, v_prio_3623_, v_promise_3624_, v_b_3625_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_object* v_00_u03b5_3628_, lean_object* v_00_u03b2_3629_, lean_object* v_f_3630_, lean_object* v_prio_3631_, lean_object* v_promise_3632_, lean_object* v_b_3633_){
_start:
{
lean_object* v___x_3635_; 
v___x_3635_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(v_f_3630_, v_prio_3631_, v_promise_3632_, v_b_3633_);
return v___x_3635_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___boxed(lean_object* v_00_u03b5_3636_, lean_object* v_00_u03b2_3637_, lean_object* v_f_3638_, lean_object* v_prio_3639_, lean_object* v_promise_3640_, lean_object* v_b_3641_, lean_object* v_a_3642_){
_start:
{
lean_object* v_res_3643_; 
v_res_3643_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(v_00_u03b5_3636_, v_00_u03b2_3637_, v_f_3638_, v_prio_3639_, v_promise_3640_, v_b_3641_);
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg___lam__0(lean_object* v_a_3644_, lean_object* v_x_3645_){
_start:
{
if (lean_obj_tag(v_x_3645_) == 0)
{
lean_object* v_a_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3655_; 
v_a_3647_ = lean_ctor_get(v_x_3645_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v_x_3645_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3649_ = v_x_3645_;
v_isShared_3650_ = v_isSharedCheck_3655_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_a_3647_);
lean_dec(v_x_3645_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3655_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___x_3652_; 
if (v_isShared_3650_ == 0)
{
v___x_3652_ = v___x_3649_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_a_3647_);
v___x_3652_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
lean_object* v___x_3653_; 
v___x_3653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3652_);
return v___x_3653_;
}
}
}
else
{
lean_object* v___x_3656_; lean_object* v___x_3657_; 
lean_dec_ref(v_x_3645_);
v___x_3656_ = l_IO_Promise_result_x21___redArg(v_a_3644_);
v___x_3657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3656_);
return v___x_3657_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg___lam__0___boxed(lean_object* v_a_3658_, lean_object* v_x_3659_, lean_object* v___y_3660_){
_start:
{
lean_object* v_res_3661_; 
v_res_3661_ = l_Std_Async_EAsync_forIn___redArg___lam__0(v_a_3658_, v_x_3659_);
lean_dec(v_a_3658_);
return v_res_3661_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg___lam__1(lean_object* v_f_3662_, lean_object* v_prio_3663_, lean_object* v_init_3664_, lean_object* v_x_3665_){
_start:
{
if (lean_obj_tag(v_x_3665_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3675_; 
lean_dec(v_init_3664_);
lean_dec(v_prio_3663_);
lean_dec_ref(v_f_3662_);
v_a_3667_ = lean_ctor_get(v_x_3665_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v_x_3665_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3669_ = v_x_3665_;
v_isShared_3670_ = v_isSharedCheck_3675_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v_x_3665_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3675_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3672_; 
if (v_isShared_3670_ == 0)
{
v___x_3672_ = v___x_3669_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_a_3667_);
v___x_3672_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
lean_object* v___x_3673_; 
v___x_3673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3673_, 0, v___x_3672_);
return v___x_3673_;
}
}
}
else
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3689_; 
v_a_3676_ = lean_ctor_get(v_x_3665_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v_x_3665_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3678_ = v_x_3665_;
v_isShared_3679_ = v_isSharedCheck_3689_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v_x_3665_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3689_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3680_; lean_object* v___f_3681_; lean_object* v___x_3683_; 
lean_inc(v_a_3676_);
v___x_3680_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(v_f_3662_, v_prio_3663_, v_a_3676_, v_init_3664_);
v___f_3681_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_forIn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3681_, 0, v_a_3676_);
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 0, v___x_3680_);
v___x_3683_ = v___x_3678_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3680_);
v___x_3683_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; uint8_t v___x_3686_; lean_object* v___x_3687_; 
v___x_3684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3684_, 0, v___x_3683_);
v___x_3685_ = lean_unsigned_to_nat(0u);
v___x_3686_ = 0;
v___x_3687_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3685_, v___x_3686_, v___x_3684_, v___f_3681_);
return v___x_3687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg___lam__1___boxed(lean_object* v_f_3690_, lean_object* v_prio_3691_, lean_object* v_init_3692_, lean_object* v_x_3693_, lean_object* v___y_3694_){
_start:
{
lean_object* v_res_3695_; 
v_res_3695_ = l_Std_Async_EAsync_forIn___redArg___lam__1(v_f_3690_, v_prio_3691_, v_init_3692_, v_x_3693_);
return v_res_3695_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg(lean_object* v_init_3696_, lean_object* v_f_3697_, lean_object* v_prio_3698_){
_start:
{
lean_object* v___x_3700_; lean_object* v___f_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; uint8_t v___x_3705_; lean_object* v___x_3706_; 
v___x_3700_ = lean_io_promise_new();
v___f_3701_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_forIn___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_3701_, 0, v_f_3697_);
lean_closure_set(v___f_3701_, 1, v_prio_3698_);
lean_closure_set(v___f_3701_, 2, v_init_3696_);
v___x_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3700_);
v___x_3703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3702_);
v___x_3704_ = lean_unsigned_to_nat(0u);
v___x_3705_ = 0;
v___x_3706_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3704_, v___x_3705_, v___x_3703_, v___f_3701_);
return v___x_3706_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg___boxed(lean_object* v_init_3707_, lean_object* v_f_3708_, lean_object* v_prio_3709_, lean_object* v_a_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l_Std_Async_EAsync_forIn___redArg(v_init_3707_, v_f_3708_, v_prio_3709_);
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn(lean_object* v_00_u03b5_3712_, lean_object* v_00_u03b2_3713_, lean_object* v_init_3714_, lean_object* v_f_3715_, lean_object* v_prio_3716_){
_start:
{
lean_object* v___x_3718_; lean_object* v___f_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; uint8_t v___x_3723_; lean_object* v___x_3724_; 
v___x_3718_ = lean_io_promise_new();
v___f_3719_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_forIn___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_3719_, 0, v_f_3715_);
lean_closure_set(v___f_3719_, 1, v_prio_3716_);
lean_closure_set(v___f_3719_, 2, v_init_3714_);
v___x_3720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3718_);
v___x_3721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3720_);
v___x_3722_ = lean_unsigned_to_nat(0u);
v___x_3723_ = 0;
v___x_3724_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3722_, v___x_3723_, v___x_3721_, v___f_3719_);
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___boxed(lean_object* v_00_u03b5_3725_, lean_object* v_00_u03b2_3726_, lean_object* v_init_3727_, lean_object* v_f_3728_, lean_object* v_prio_3729_, lean_object* v_a_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l_Std_Async_EAsync_forIn(v_00_u03b5_3725_, v_00_u03b2_3726_, v_init_3727_, v_f_3728_, v_prio_3729_);
return v_res_3731_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___lam__1(lean_object* v_f_3732_, lean_object* v___x_3733_, lean_object* v_init_3734_, lean_object* v_x_3735_){
_start:
{
if (lean_obj_tag(v_x_3735_) == 0)
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3745_; 
lean_dec(v_init_3734_);
lean_dec(v___x_3733_);
lean_dec_ref(v_f_3732_);
v_a_3737_ = lean_ctor_get(v_x_3735_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v_x_3735_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3739_ = v_x_3735_;
v_isShared_3740_ = v_isSharedCheck_3745_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v_x_3735_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3745_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3742_; 
if (v_isShared_3740_ == 0)
{
v___x_3742_ = v___x_3739_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3737_);
v___x_3742_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
lean_object* v___x_3743_; 
v___x_3743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3742_);
return v___x_3743_;
}
}
}
else
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3758_; 
v_a_3746_ = lean_ctor_get(v_x_3735_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v_x_3735_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3748_ = v_x_3735_;
v_isShared_3749_ = v_isSharedCheck_3758_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v_x_3735_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3758_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3750_; lean_object* v___f_3751_; lean_object* v___x_3753_; 
lean_inc(v_a_3746_);
lean_inc(v___x_3733_);
v___x_3750_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(v_f_3732_, v___x_3733_, v_a_3746_, v_init_3734_);
v___f_3751_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_forIn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3751_, 0, v_a_3746_);
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 0, v___x_3750_);
v___x_3753_ = v___x_3748_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v___x_3750_);
v___x_3753_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
lean_object* v___x_3754_; uint8_t v___x_3755_; lean_object* v___x_3756_; 
v___x_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3753_);
v___x_3755_ = 0;
v___x_3756_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3733_, v___x_3755_, v___x_3754_, v___f_3751_);
return v___x_3756_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___lam__1___boxed(lean_object* v_f_3759_, lean_object* v___x_3760_, lean_object* v_init_3761_, lean_object* v_x_3762_, lean_object* v___y_3763_){
_start:
{
lean_object* v_res_3764_; 
v_res_3764_ = l_Std_Async_EAsync_instForInLoopUnit___lam__1(v_f_3759_, v___x_3760_, v_init_3761_, v_x_3762_);
return v_res_3764_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___lam__0(lean_object* v_00_u03b2_3765_, lean_object* v_x_3766_, lean_object* v_init_3767_, lean_object* v_f_3768_){
_start:
{
lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___f_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; uint8_t v___x_3775_; lean_object* v___x_3776_; 
v___x_3770_ = lean_io_promise_new();
v___x_3771_ = lean_unsigned_to_nat(0u);
v___f_3772_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_instForInLoopUnit___lam__1___boxed), 5, 3);
lean_closure_set(v___f_3772_, 0, v_f_3768_);
lean_closure_set(v___f_3772_, 1, v___x_3771_);
lean_closure_set(v___f_3772_, 2, v_init_3767_);
v___x_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3770_);
v___x_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3773_);
v___x_3775_ = 0;
v___x_3776_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3771_, v___x_3775_, v___x_3774_, v___f_3772_);
return v___x_3776_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___lam__0___boxed(lean_object* v_00_u03b2_3777_, lean_object* v_x_3778_, lean_object* v_init_3779_, lean_object* v_f_3780_, lean_object* v___y_3781_){
_start:
{
lean_object* v_res_3782_; 
v_res_3782_ = l_Std_Async_EAsync_instForInLoopUnit___lam__0(v_00_u03b2_3777_, v_x_3778_, v_init_3779_, v_f_3780_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit(lean_object* v_00_u03b5_3784_){
_start:
{
lean_object* v___f_3785_; 
v___f_3785_ = ((lean_object*)(l_Std_Async_EAsync_instForInLoopUnit___closed__0));
return v___f_3785_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofExcept___redArg(lean_object* v_except_3786_){
_start:
{
lean_object* v___x_3788_; 
v___x_3788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3788_, 0, v_except_3786_);
return v___x_3788_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofExcept___redArg___boxed(lean_object* v_except_3789_, lean_object* v_a_3790_){
_start:
{
lean_object* v_res_3791_; 
v_res_3791_ = l_Std_Async_EAsync_ofExcept___redArg(v_except_3789_);
return v_res_3791_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofExcept(lean_object* v_00_u03b5_3792_, lean_object* v_00_u03b1_3793_, lean_object* v_except_3794_){
_start:
{
lean_object* v___x_3796_; 
v___x_3796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3796_, 0, v_except_3794_);
return v___x_3796_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofExcept___boxed(lean_object* v_00_u03b5_3797_, lean_object* v_00_u03b1_3798_, lean_object* v_except_3799_, lean_object* v_a_3800_){
_start:
{
lean_object* v_res_3801_; 
v_res_3801_ = l_Std_Async_EAsync_ofExcept(v_00_u03b5_3797_, v_00_u03b1_3798_, v_except_3799_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__1(lean_object* v_a_3802_, lean_object* v_x_3803_){
_start:
{
if (lean_obj_tag(v_x_3803_) == 0)
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3813_; 
lean_dec(v_a_3802_);
v_a_3805_ = lean_ctor_get(v_x_3803_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v_x_3803_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3807_ = v_x_3803_;
v_isShared_3808_ = v_isSharedCheck_3813_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v_x_3803_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3813_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3810_; 
if (v_isShared_3808_ == 0)
{
v___x_3810_ = v___x_3807_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3805_);
v___x_3810_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
lean_object* v___x_3811_; 
v___x_3811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3810_);
return v___x_3811_;
}
}
}
else
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3823_; 
v_a_3814_ = lean_ctor_get(v_x_3803_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v_x_3803_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3816_ = v_x_3803_;
v_isShared_3817_ = v_isSharedCheck_3823_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v_x_3803_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3823_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3818_; lean_object* v___x_3820_; 
v___x_3818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3818_, 0, v_a_3802_);
lean_ctor_set(v___x_3818_, 1, v_a_3814_);
if (v_isShared_3817_ == 0)
{
lean_ctor_set(v___x_3816_, 0, v___x_3818_);
v___x_3820_ = v___x_3816_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v___x_3818_);
v___x_3820_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
lean_object* v___x_3821_; 
v___x_3821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3820_);
return v___x_3821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__1___boxed(lean_object* v_a_3824_, lean_object* v_x_3825_, lean_object* v___y_3826_){
_start:
{
lean_object* v_res_3827_; 
v_res_3827_ = l_Std_Async_EAsync_concurrently___redArg___lam__1(v_a_3824_, v_x_3825_);
return v_res_3827_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__0(lean_object* v_a_3828_, lean_object* v_x_3829_){
_start:
{
if (lean_obj_tag(v_x_3829_) == 0)
{
lean_object* v_a_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3839_; 
lean_dec_ref(v_a_3828_);
v_a_3831_ = lean_ctor_get(v_x_3829_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v_x_3829_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3833_ = v_x_3829_;
v_isShared_3834_ = v_isSharedCheck_3839_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_a_3831_);
lean_dec(v_x_3829_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3839_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v___x_3836_; 
if (v_isShared_3834_ == 0)
{
v___x_3836_ = v___x_3833_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3831_);
v___x_3836_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
lean_object* v___x_3837_; 
v___x_3837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3837_, 0, v___x_3836_);
return v___x_3837_;
}
}
}
else
{
lean_object* v_a_3840_; lean_object* v___f_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; uint8_t v___x_3844_; lean_object* v___x_3845_; 
v_a_3840_ = lean_ctor_get(v_x_3829_, 0);
lean_inc(v_a_3840_);
lean_dec_ref(v_x_3829_);
v___f_3841_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrently___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3841_, 0, v_a_3840_);
v___x_3842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3842_, 0, v_a_3828_);
v___x_3843_ = lean_unsigned_to_nat(0u);
v___x_3844_ = 0;
v___x_3845_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3843_, v___x_3844_, v___x_3842_, v___f_3841_);
return v___x_3845_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__0___boxed(lean_object* v_a_3846_, lean_object* v_x_3847_, lean_object* v___y_3848_){
_start:
{
lean_object* v_res_3849_; 
v_res_3849_ = l_Std_Async_EAsync_concurrently___redArg___lam__0(v_a_3846_, v_x_3847_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__2(lean_object* v_a_3850_, lean_object* v_x_3851_){
_start:
{
if (lean_obj_tag(v_x_3851_) == 0)
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3861_; 
lean_dec_ref(v_a_3850_);
v_a_3853_ = lean_ctor_get(v_x_3851_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v_x_3851_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3855_ = v_x_3851_;
v_isShared_3856_ = v_isSharedCheck_3861_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v_x_3851_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3861_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3858_; 
if (v_isShared_3856_ == 0)
{
v___x_3858_ = v___x_3855_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_a_3853_);
v___x_3858_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
lean_object* v___x_3859_; 
v___x_3859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3858_);
return v___x_3859_;
}
}
}
else
{
lean_object* v_a_3862_; lean_object* v___f_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; uint8_t v___x_3866_; lean_object* v___x_3867_; 
v_a_3862_ = lean_ctor_get(v_x_3851_, 0);
lean_inc(v_a_3862_);
lean_dec_ref(v_x_3851_);
v___f_3863_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrently___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3863_, 0, v_a_3862_);
v___x_3864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3864_, 0, v_a_3850_);
v___x_3865_ = lean_unsigned_to_nat(0u);
v___x_3866_ = 0;
v___x_3867_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3865_, v___x_3866_, v___x_3864_, v___f_3863_);
return v___x_3867_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__2___boxed(lean_object* v_a_3868_, lean_object* v_x_3869_, lean_object* v___y_3870_){
_start:
{
lean_object* v_res_3871_; 
v_res_3871_ = l_Std_Async_EAsync_concurrently___redArg___lam__2(v_a_3868_, v_x_3869_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__3(lean_object* v_y_3872_, lean_object* v_prio_3873_, lean_object* v___f_3874_, lean_object* v_x_3875_){
_start:
{
if (lean_obj_tag(v_x_3875_) == 0)
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3885_; 
lean_dec_ref(v___f_3874_);
lean_dec(v_prio_3873_);
lean_dec_ref(v_y_3872_);
v_a_3877_ = lean_ctor_get(v_x_3875_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v_x_3875_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3879_ = v_x_3875_;
v_isShared_3880_ = v_isSharedCheck_3885_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v_x_3875_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3885_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3877_);
v___x_3882_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
lean_object* v___x_3883_; 
v___x_3883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3882_);
return v___x_3883_;
}
}
}
else
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3902_; 
v_a_3886_ = lean_ctor_get(v_x_3875_, 0);
v_isSharedCheck_3902_ = !lean_is_exclusive(v_x_3875_);
if (v_isSharedCheck_3902_ == 0)
{
v___x_3888_ = v_x_3875_;
v_isShared_3889_ = v_isSharedCheck_3902_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v_x_3875_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3902_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___f_3892_; lean_object* v___x_3893_; uint8_t v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3897_; 
v___x_3890_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_3890_, 0, lean_box(0));
lean_closure_set(v___x_3890_, 1, v_y_3872_);
v___x_3891_ = lean_io_as_task(v___x_3890_, v_prio_3873_);
v___f_3892_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrently___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3892_, 0, v_a_3886_);
v___x_3893_ = lean_unsigned_to_nat(0u);
v___x_3894_ = 1;
v___x_3895_ = lean_task_bind(v___x_3891_, v___f_3874_, v___x_3893_, v___x_3894_);
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 0, v___x_3895_);
v___x_3897_ = v___x_3888_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v___x_3895_);
v___x_3897_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
lean_object* v___x_3898_; uint8_t v___x_3899_; lean_object* v___x_3900_; 
v___x_3898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3897_);
v___x_3899_ = 0;
v___x_3900_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3893_, v___x_3899_, v___x_3898_, v___f_3892_);
return v___x_3900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__3___boxed(lean_object* v_y_3903_, lean_object* v_prio_3904_, lean_object* v___f_3905_, lean_object* v_x_3906_, lean_object* v___y_3907_){
_start:
{
lean_object* v_res_3908_; 
v_res_3908_ = l_Std_Async_EAsync_concurrently___redArg___lam__3(v_y_3903_, v_prio_3904_, v___f_3905_, v_x_3906_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg(lean_object* v_x_3909_, lean_object* v_y_3910_, lean_object* v_prio_3911_){
_start:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___f_3915_; lean_object* v___f_3916_; lean_object* v___x_3917_; uint8_t v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; uint8_t v___x_3922_; lean_object* v___x_3923_; 
v___x_3913_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_3913_, 0, lean_box(0));
lean_closure_set(v___x_3913_, 1, v_x_3909_);
lean_inc(v_prio_3911_);
v___x_3914_ = lean_io_as_task(v___x_3913_, v_prio_3911_);
v___f_3915_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___f_3916_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrently___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3916_, 0, v_y_3910_);
lean_closure_set(v___f_3916_, 1, v_prio_3911_);
lean_closure_set(v___f_3916_, 2, v___f_3915_);
v___x_3917_ = lean_unsigned_to_nat(0u);
v___x_3918_ = 1;
v___x_3919_ = lean_task_bind(v___x_3914_, v___f_3915_, v___x_3917_, v___x_3918_);
v___x_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3919_);
v___x_3921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3920_);
v___x_3922_ = 0;
v___x_3923_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3917_, v___x_3922_, v___x_3921_, v___f_3916_);
return v___x_3923_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___boxed(lean_object* v_x_3924_, lean_object* v_y_3925_, lean_object* v_prio_3926_, lean_object* v_a_3927_){
_start:
{
lean_object* v_res_3928_; 
v_res_3928_ = l_Std_Async_EAsync_concurrently___redArg(v_x_3924_, v_y_3925_, v_prio_3926_);
return v_res_3928_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently(lean_object* v_00_u03b5_3929_, lean_object* v_00_u03b1_3930_, lean_object* v_00_u03b2_3931_, lean_object* v_x_3932_, lean_object* v_y_3933_, lean_object* v_prio_3934_){
_start:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___f_3938_; lean_object* v___f_3939_; lean_object* v___x_3940_; uint8_t v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; uint8_t v___x_3945_; lean_object* v___x_3946_; 
v___x_3936_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_3936_, 0, lean_box(0));
lean_closure_set(v___x_3936_, 1, v_x_3932_);
lean_inc(v_prio_3934_);
v___x_3937_ = lean_io_as_task(v___x_3936_, v_prio_3934_);
v___f_3938_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___f_3939_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrently___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3939_, 0, v_y_3933_);
lean_closure_set(v___f_3939_, 1, v_prio_3934_);
lean_closure_set(v___f_3939_, 2, v___f_3938_);
v___x_3940_ = lean_unsigned_to_nat(0u);
v___x_3941_ = 1;
v___x_3942_ = lean_task_bind(v___x_3937_, v___f_3938_, v___x_3940_, v___x_3941_);
v___x_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3942_);
v___x_3944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3943_);
v___x_3945_ = 0;
v___x_3946_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3940_, v___x_3945_, v___x_3944_, v___f_3939_);
return v___x_3946_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___boxed(lean_object* v_00_u03b5_3947_, lean_object* v_00_u03b1_3948_, lean_object* v_00_u03b2_3949_, lean_object* v_x_3950_, lean_object* v_y_3951_, lean_object* v_prio_3952_, lean_object* v_a_3953_){
_start:
{
lean_object* v_res_3954_; 
v_res_3954_ = l_Std_Async_EAsync_concurrently(v_00_u03b5_3947_, v_00_u03b1_3948_, v_00_u03b2_3949_, v_x_3950_, v_y_3951_, v_prio_3952_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__1(lean_object* v_x_3955_){
_start:
{
if (lean_obj_tag(v_x_3955_) == 0)
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3965_; 
v_a_3957_ = lean_ctor_get(v_x_3955_, 0);
v_isSharedCheck_3965_ = !lean_is_exclusive(v_x_3955_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3959_ = v_x_3955_;
v_isShared_3960_ = v_isSharedCheck_3965_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v_x_3955_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3965_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3962_; 
if (v_isShared_3960_ == 0)
{
v___x_3962_ = v___x_3959_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_a_3957_);
v___x_3962_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
lean_object* v___x_3963_; 
v___x_3963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3962_);
return v___x_3963_;
}
}
}
else
{
lean_object* v_a_3966_; lean_object* v___x_3967_; 
v_a_3966_ = lean_ctor_get(v_x_3955_, 0);
lean_inc(v_a_3966_);
lean_dec_ref(v_x_3955_);
v___x_3967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3967_, 0, v_a_3966_);
return v___x_3967_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__1___boxed(lean_object* v_x_3968_, lean_object* v___y_3969_){
_start:
{
lean_object* v_res_3970_; 
v_res_3970_ = l_Std_Async_EAsync_race___redArg___lam__1(v_x_3968_);
return v_res_3970_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__0(lean_object* v_a_3971_){
_start:
{
lean_object* v___x_3972_; 
v___x_3972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3972_, 0, v_a_3971_);
return v___x_3972_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__3(lean_object* v_a_3973_, lean_object* v_value_3974_){
_start:
{
lean_object* v___x_3976_; 
v___x_3976_ = lean_io_promise_resolve(v_value_3974_, v_a_3973_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__3___boxed(lean_object* v_a_3977_, lean_object* v_value_3978_, lean_object* v___y_3979_){
_start:
{
lean_object* v_res_3980_; 
v_res_3980_ = l_Std_Async_EAsync_race___redArg___lam__3(v_a_3977_, v_value_3978_);
lean_dec(v_a_3977_);
return v_res_3980_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__2(lean_object* v_a_3981_, lean_object* v___f_3982_, lean_object* v___f_3983_, lean_object* v_x_3984_){
_start:
{
if (lean_obj_tag(v_x_3984_) == 0)
{
lean_object* v_a_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3994_; 
lean_dec_ref(v___f_3983_);
lean_dec_ref(v___f_3982_);
v_a_3986_ = lean_ctor_get(v_x_3984_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v_x_3984_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3988_ = v_x_3984_;
v_isShared_3989_ = v_isSharedCheck_3994_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_a_3986_);
lean_dec(v_x_3984_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3994_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3991_; 
if (v_isShared_3989_ == 0)
{
v___x_3991_ = v___x_3988_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_a_3986_);
v___x_3991_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
lean_object* v___x_3992_; 
v___x_3992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3991_);
return v___x_3992_;
}
}
}
else
{
lean_object* v___x_3995_; lean_object* v___x_3996_; uint8_t v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
lean_dec_ref(v_x_3984_);
v___x_3995_ = l_IO_Promise_result_x21___redArg(v_a_3981_);
v___x_3996_ = lean_unsigned_to_nat(0u);
v___x_3997_ = 0;
v___x_3998_ = lean_task_map(v___f_3982_, v___x_3995_, v___x_3996_, v___x_3997_);
v___x_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3998_);
v___x_4000_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3996_, v___x_3997_, v___x_3999_, v___f_3983_);
return v___x_4000_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__2___boxed(lean_object* v_a_4001_, lean_object* v___f_4002_, lean_object* v___f_4003_, lean_object* v_x_4004_, lean_object* v___y_4005_){
_start:
{
lean_object* v_res_4006_; 
v_res_4006_ = l_Std_Async_EAsync_race___redArg___lam__2(v_a_4001_, v___f_4002_, v___f_4003_, v_x_4004_);
lean_dec(v_a_4001_);
return v_res_4006_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__4(lean_object* v_a_4007_, lean_object* v___x_4008_, lean_object* v___x_4009_, uint8_t v___x_4010_, lean_object* v___f_4011_, lean_object* v_x_4012_){
_start:
{
if (lean_obj_tag(v_x_4012_) == 0)
{
lean_object* v_a_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4022_; 
lean_dec_ref(v___f_4011_);
lean_dec(v___x_4009_);
lean_dec_ref(v___x_4008_);
lean_dec_ref(v_a_4007_);
v_a_4014_ = lean_ctor_get(v_x_4012_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v_x_4012_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4016_ = v_x_4012_;
v_isShared_4017_ = v_isSharedCheck_4022_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_a_4014_);
lean_dec(v_x_4012_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4022_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4019_; 
if (v_isShared_4017_ == 0)
{
v___x_4019_ = v___x_4016_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_a_4014_);
v___x_4019_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
lean_object* v___x_4020_; 
v___x_4020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4020_, 0, v___x_4019_);
return v___x_4020_;
}
}
}
else
{
lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4032_; 
v_isSharedCheck_4032_ = !lean_is_exclusive(v_x_4012_);
if (v_isSharedCheck_4032_ == 0)
{
lean_object* v_unused_4033_; 
v_unused_4033_ = lean_ctor_get(v_x_4012_, 0);
lean_dec(v_unused_4033_);
v___x_4024_ = v_x_4012_;
v_isShared_4025_ = v_isSharedCheck_4032_;
goto v_resetjp_4023_;
}
else
{
lean_dec(v_x_4012_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4032_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4026_; lean_object* v___x_4028_; 
lean_inc(v___x_4009_);
v___x_4026_ = l_BaseIO_chainTask___redArg(v_a_4007_, v___x_4008_, v___x_4009_, v___x_4010_);
if (v_isShared_4025_ == 0)
{
lean_ctor_set(v___x_4024_, 0, v___x_4026_);
v___x_4028_ = v___x_4024_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_4026_);
v___x_4028_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4029_, 0, v___x_4028_);
v___x_4030_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4009_, v___x_4010_, v___x_4029_, v___f_4011_);
return v___x_4030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__4___boxed(lean_object* v_a_4034_, lean_object* v___x_4035_, lean_object* v___x_4036_, lean_object* v___x_4037_, lean_object* v___f_4038_, lean_object* v_x_4039_, lean_object* v___y_4040_){
_start:
{
uint8_t v___x_1425__boxed_4041_; lean_object* v_res_4042_; 
v___x_1425__boxed_4041_ = lean_unbox(v___x_4037_);
v_res_4042_ = l_Std_Async_EAsync_race___redArg___lam__4(v_a_4034_, v___x_4035_, v___x_4036_, v___x_1425__boxed_4041_, v___f_4038_, v_x_4039_);
return v_res_4042_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__5(lean_object* v___f_4043_, lean_object* v___f_4044_, lean_object* v_a_4045_, lean_object* v___f_4046_, lean_object* v_x_4047_){
_start:
{
if (lean_obj_tag(v_x_4047_) == 0)
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4057_; 
lean_dec_ref(v___f_4046_);
lean_dec_ref(v_a_4045_);
lean_dec_ref(v___f_4044_);
lean_dec(v___f_4043_);
v_a_4049_ = lean_ctor_get(v_x_4047_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v_x_4047_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4051_ = v_x_4047_;
v_isShared_4052_ = v_isSharedCheck_4057_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v_x_4047_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4057_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4054_; 
if (v_isShared_4052_ == 0)
{
v___x_4054_ = v___x_4051_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_a_4049_);
v___x_4054_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
lean_object* v___x_4055_; 
v___x_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4054_);
return v___x_4055_;
}
}
}
else
{
lean_object* v_a_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4074_; 
v_a_4058_ = lean_ctor_get(v_x_4047_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v_x_4047_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4060_ = v_x_4047_;
v_isShared_4061_ = v_isSharedCheck_4074_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_a_4058_);
lean_dec(v_x_4047_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4074_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; uint8_t v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___f_4068_; lean_object* v___x_4070_; 
v___x_4062_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_4062_, 0, lean_box(0));
lean_closure_set(v___x_4062_, 1, lean_box(0));
lean_closure_set(v___x_4062_, 2, v___f_4043_);
lean_closure_set(v___x_4062_, 3, lean_box(0));
v___x_4063_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4063_, 0, lean_box(0));
lean_closure_set(v___x_4063_, 1, lean_box(0));
lean_closure_set(v___x_4063_, 2, lean_box(0));
lean_closure_set(v___x_4063_, 3, v___x_4062_);
lean_closure_set(v___x_4063_, 4, v___f_4044_);
v___x_4064_ = lean_unsigned_to_nat(0u);
v___x_4065_ = 0;
lean_inc_ref(v___x_4063_);
v___x_4066_ = l_BaseIO_chainTask___redArg(v_a_4045_, v___x_4063_, v___x_4064_, v___x_4065_);
v___x_4067_ = lean_box(v___x_4065_);
v___f_4068_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__4___boxed), 7, 5);
lean_closure_set(v___f_4068_, 0, v_a_4058_);
lean_closure_set(v___f_4068_, 1, v___x_4063_);
lean_closure_set(v___f_4068_, 2, v___x_4064_);
lean_closure_set(v___f_4068_, 3, v___x_4067_);
lean_closure_set(v___f_4068_, 4, v___f_4046_);
if (v_isShared_4061_ == 0)
{
lean_ctor_set(v___x_4060_, 0, v___x_4066_);
v___x_4070_ = v___x_4060_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v___x_4066_);
v___x_4070_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4071_, 0, v___x_4070_);
v___x_4072_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4064_, v___x_4065_, v___x_4071_, v___f_4068_);
return v___x_4072_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__5___boxed(lean_object* v___f_4075_, lean_object* v___f_4076_, lean_object* v_a_4077_, lean_object* v___f_4078_, lean_object* v_x_4079_, lean_object* v___y_4080_){
_start:
{
lean_object* v_res_4081_; 
v_res_4081_ = l_Std_Async_EAsync_race___redArg___lam__5(v___f_4075_, v___f_4076_, v_a_4077_, v___f_4078_, v_x_4079_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__6(lean_object* v_y_4082_, lean_object* v_prio_4083_, lean_object* v___f_4084_, lean_object* v___f_4085_, lean_object* v___f_4086_, lean_object* v___f_4087_, lean_object* v_x_4088_){
_start:
{
if (lean_obj_tag(v_x_4088_) == 0)
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4098_; 
lean_dec_ref(v___f_4087_);
lean_dec_ref(v___f_4086_);
lean_dec_ref(v___f_4085_);
lean_dec(v___f_4084_);
lean_dec(v_prio_4083_);
lean_dec_ref(v_y_4082_);
v_a_4090_ = lean_ctor_get(v_x_4088_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v_x_4088_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4092_ = v_x_4088_;
v_isShared_4093_ = v_isSharedCheck_4098_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v_x_4088_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4098_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4095_; 
if (v_isShared_4093_ == 0)
{
v___x_4095_ = v___x_4092_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_a_4090_);
v___x_4095_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
lean_object* v___x_4096_; 
v___x_4096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4095_);
return v___x_4096_;
}
}
}
else
{
lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4115_; 
v_a_4099_ = lean_ctor_get(v_x_4088_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v_x_4088_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4101_ = v_x_4088_;
v_isShared_4102_ = v_isSharedCheck_4115_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v_x_4088_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4115_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___f_4105_; lean_object* v___x_4106_; uint8_t v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4110_; 
v___x_4103_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4103_, 0, lean_box(0));
lean_closure_set(v___x_4103_, 1, v_y_4082_);
v___x_4104_ = lean_io_as_task(v___x_4103_, v_prio_4083_);
v___f_4105_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__5___boxed), 6, 4);
lean_closure_set(v___f_4105_, 0, v___f_4084_);
lean_closure_set(v___f_4105_, 1, v___f_4085_);
lean_closure_set(v___f_4105_, 2, v_a_4099_);
lean_closure_set(v___f_4105_, 3, v___f_4086_);
v___x_4106_ = lean_unsigned_to_nat(0u);
v___x_4107_ = 1;
v___x_4108_ = lean_task_bind(v___x_4104_, v___f_4087_, v___x_4106_, v___x_4107_);
if (v_isShared_4102_ == 0)
{
lean_ctor_set(v___x_4101_, 0, v___x_4108_);
v___x_4110_ = v___x_4101_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v___x_4108_);
v___x_4110_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
lean_object* v___x_4111_; uint8_t v___x_4112_; lean_object* v___x_4113_; 
v___x_4111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4111_, 0, v___x_4110_);
v___x_4112_ = 0;
v___x_4113_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4106_, v___x_4112_, v___x_4111_, v___f_4105_);
return v___x_4113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__6___boxed(lean_object* v_y_4116_, lean_object* v_prio_4117_, lean_object* v___f_4118_, lean_object* v___f_4119_, lean_object* v___f_4120_, lean_object* v___f_4121_, lean_object* v_x_4122_, lean_object* v___y_4123_){
_start:
{
lean_object* v_res_4124_; 
v_res_4124_ = l_Std_Async_EAsync_race___redArg___lam__6(v_y_4116_, v_prio_4117_, v___f_4118_, v___f_4119_, v___f_4120_, v___f_4121_, v_x_4122_);
return v_res_4124_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__7(lean_object* v_x_4125_, lean_object* v_prio_4126_, lean_object* v___f_4127_, lean_object* v___f_4128_, lean_object* v_y_4129_, lean_object* v___f_4130_, lean_object* v___f_4131_, lean_object* v___f_4132_, lean_object* v_x_4133_){
_start:
{
if (lean_obj_tag(v_x_4133_) == 0)
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4143_; 
lean_dec_ref(v___f_4132_);
lean_dec_ref(v___f_4131_);
lean_dec(v___f_4130_);
lean_dec_ref(v_y_4129_);
lean_dec_ref(v___f_4128_);
lean_dec_ref(v___f_4127_);
lean_dec(v_prio_4126_);
lean_dec_ref(v_x_4125_);
v_a_4135_ = lean_ctor_get(v_x_4133_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v_x_4133_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4137_ = v_x_4133_;
v_isShared_4138_ = v_isSharedCheck_4143_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v_x_4133_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4143_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4138_ == 0)
{
v___x_4140_ = v___x_4137_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4135_);
v___x_4140_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
lean_object* v___x_4141_; 
v___x_4141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4141_, 0, v___x_4140_);
return v___x_4141_;
}
}
}
else
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4162_; 
v_a_4144_ = lean_ctor_get(v_x_4133_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v_x_4133_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4146_ = v_x_4133_;
v_isShared_4147_ = v_isSharedCheck_4162_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v_x_4133_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4162_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___f_4150_; lean_object* v___f_4151_; lean_object* v___f_4152_; lean_object* v___x_4153_; uint8_t v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4157_; 
v___x_4148_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4148_, 0, lean_box(0));
lean_closure_set(v___x_4148_, 1, v_x_4125_);
lean_inc(v_prio_4126_);
v___x_4149_ = lean_io_as_task(v___x_4148_, v_prio_4126_);
lean_inc(v_a_4144_);
v___f_4150_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4150_, 0, v_a_4144_);
v___f_4151_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_4151_, 0, v_a_4144_);
lean_closure_set(v___f_4151_, 1, v___f_4127_);
lean_closure_set(v___f_4151_, 2, v___f_4128_);
v___f_4152_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__6___boxed), 8, 6);
lean_closure_set(v___f_4152_, 0, v_y_4129_);
lean_closure_set(v___f_4152_, 1, v_prio_4126_);
lean_closure_set(v___f_4152_, 2, v___f_4130_);
lean_closure_set(v___f_4152_, 3, v___f_4150_);
lean_closure_set(v___f_4152_, 4, v___f_4151_);
lean_closure_set(v___f_4152_, 5, v___f_4131_);
v___x_4153_ = lean_unsigned_to_nat(0u);
v___x_4154_ = 1;
v___x_4155_ = lean_task_bind(v___x_4149_, v___f_4132_, v___x_4153_, v___x_4154_);
if (v_isShared_4147_ == 0)
{
lean_ctor_set(v___x_4146_, 0, v___x_4155_);
v___x_4157_ = v___x_4146_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v___x_4155_);
v___x_4157_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
lean_object* v___x_4158_; uint8_t v___x_4159_; lean_object* v___x_4160_; 
v___x_4158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4157_);
v___x_4159_ = 0;
v___x_4160_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4153_, v___x_4159_, v___x_4158_, v___f_4152_);
return v___x_4160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__7___boxed(lean_object* v_x_4163_, lean_object* v_prio_4164_, lean_object* v___f_4165_, lean_object* v___f_4166_, lean_object* v_y_4167_, lean_object* v___f_4168_, lean_object* v___f_4169_, lean_object* v___f_4170_, lean_object* v_x_4171_, lean_object* v___y_4172_){
_start:
{
lean_object* v_res_4173_; 
v_res_4173_ = l_Std_Async_EAsync_race___redArg___lam__7(v_x_4163_, v_prio_4164_, v___f_4165_, v___f_4166_, v_y_4167_, v___f_4168_, v___f_4169_, v___f_4170_, v_x_4171_);
return v_res_4173_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg(lean_object* v_x_4176_, lean_object* v_y_4177_, lean_object* v_prio_4178_){
_start:
{
lean_object* v___x_4180_; lean_object* v___f_4181_; lean_object* v___f_4182_; lean_object* v___f_4183_; lean_object* v___f_4184_; lean_object* v___f_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; uint8_t v___x_4189_; lean_object* v___x_4190_; 
v___x_4180_ = lean_io_promise_new();
v___f_4181_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___f_4182_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__0));
v___f_4183_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__1));
v___f_4184_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_4185_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_4185_, 0, v_x_4176_);
lean_closure_set(v___f_4185_, 1, v_prio_4178_);
lean_closure_set(v___f_4185_, 2, v___f_4183_);
lean_closure_set(v___f_4185_, 3, v___f_4182_);
lean_closure_set(v___f_4185_, 4, v_y_4177_);
lean_closure_set(v___f_4185_, 5, v___f_4184_);
lean_closure_set(v___f_4185_, 6, v___f_4181_);
lean_closure_set(v___f_4185_, 7, v___f_4181_);
v___x_4186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4186_, 0, v___x_4180_);
v___x_4187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4186_);
v___x_4188_ = lean_unsigned_to_nat(0u);
v___x_4189_ = 0;
v___x_4190_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4188_, v___x_4189_, v___x_4187_, v___f_4185_);
return v___x_4190_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___boxed(lean_object* v_x_4191_, lean_object* v_y_4192_, lean_object* v_prio_4193_, lean_object* v_a_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l_Std_Async_EAsync_race___redArg(v_x_4191_, v_y_4192_, v_prio_4193_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race(lean_object* v_00_u03b1_4196_, lean_object* v_00_u03b5_4197_, lean_object* v_inst_4198_, lean_object* v_x_4199_, lean_object* v_y_4200_, lean_object* v_prio_4201_){
_start:
{
lean_object* v___x_4203_; lean_object* v___f_4204_; lean_object* v___f_4205_; lean_object* v___f_4206_; lean_object* v___f_4207_; lean_object* v___f_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; uint8_t v___x_4212_; lean_object* v___x_4213_; 
v___x_4203_ = lean_io_promise_new();
v___f_4204_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___f_4205_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__0));
v___f_4206_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__1));
v___f_4207_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_4208_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_4208_, 0, v_x_4199_);
lean_closure_set(v___f_4208_, 1, v_prio_4201_);
lean_closure_set(v___f_4208_, 2, v___f_4206_);
lean_closure_set(v___f_4208_, 3, v___f_4205_);
lean_closure_set(v___f_4208_, 4, v_y_4200_);
lean_closure_set(v___f_4208_, 5, v___f_4207_);
lean_closure_set(v___f_4208_, 6, v___f_4204_);
lean_closure_set(v___f_4208_, 7, v___f_4204_);
v___x_4209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4203_);
v___x_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4210_, 0, v___x_4209_);
v___x_4211_ = lean_unsigned_to_nat(0u);
v___x_4212_ = 0;
v___x_4213_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4211_, v___x_4212_, v___x_4210_, v___f_4208_);
return v___x_4213_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___boxed(lean_object* v_00_u03b1_4214_, lean_object* v_00_u03b5_4215_, lean_object* v_inst_4216_, lean_object* v_x_4217_, lean_object* v_y_4218_, lean_object* v_prio_4219_, lean_object* v_a_4220_){
_start:
{
lean_object* v_res_4221_; 
v_res_4221_ = l_Std_Async_EAsync_race(v_00_u03b1_4214_, v_00_u03b5_4215_, v_inst_4216_, v_x_4217_, v_y_4218_, v_prio_4219_);
lean_dec(v_inst_4216_);
return v_res_4221_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1(lean_object* v_prio_4222_, lean_object* v___f_4223_, lean_object* v_x_4224_){
_start:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; uint8_t v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; 
v___x_4226_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4226_, 0, lean_box(0));
lean_closure_set(v___x_4226_, 1, v_x_4224_);
v___x_4227_ = lean_io_as_task(v___x_4226_, v_prio_4222_);
v___x_4228_ = lean_unsigned_to_nat(0u);
v___x_4229_ = 1;
v___x_4230_ = lean_task_bind(v___x_4227_, v___f_4223_, v___x_4228_, v___x_4229_);
v___x_4231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4231_, 0, v___x_4230_);
v___x_4232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4231_);
return v___x_4232_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1___boxed(lean_object* v_prio_4233_, lean_object* v___f_4234_, lean_object* v_x_4235_, lean_object* v___y_4236_){
_start:
{
lean_object* v_res_4237_; 
v_res_4237_ = l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1(v_prio_4233_, v___f_4234_, v_x_4235_);
return v_res_4237_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__0(lean_object* v___y_4238_){
_start:
{
lean_object* v___x_4240_; 
v___x_4240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4240_, 0, v___y_4238_);
return v___x_4240_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__0___boxed(lean_object* v___y_4241_, lean_object* v___y_4242_){
_start:
{
lean_object* v_res_4243_; 
v_res_4243_ = l_Std_Async_EAsync_concurrentlyAll___redArg___lam__0(v___y_4241_);
return v_res_4243_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__2(lean_object* v___x_4244_, lean_object* v___f_4245_, lean_object* v_x_4246_){
_start:
{
if (lean_obj_tag(v_x_4246_) == 0)
{
lean_object* v_a_4248_; lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4256_; 
lean_dec_ref(v___f_4245_);
lean_dec_ref(v___x_4244_);
v_a_4248_ = lean_ctor_get(v_x_4246_, 0);
v_isSharedCheck_4256_ = !lean_is_exclusive(v_x_4246_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4250_ = v_x_4246_;
v_isShared_4251_ = v_isSharedCheck_4256_;
goto v_resetjp_4249_;
}
else
{
lean_inc(v_a_4248_);
lean_dec(v_x_4246_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4256_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v___x_4253_; 
if (v_isShared_4251_ == 0)
{
v___x_4253_ = v___x_4250_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v_a_4248_);
v___x_4253_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
lean_object* v___x_4254_; 
v___x_4254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4254_, 0, v___x_4253_);
return v___x_4254_;
}
}
}
else
{
lean_object* v_a_4257_; size_t v_sz_4258_; size_t v___x_4259_; lean_object* v___x_290__overap_4260_; lean_object* v___x_4261_; 
v_a_4257_ = lean_ctor_get(v_x_4246_, 0);
lean_inc(v_a_4257_);
lean_dec_ref(v_x_4246_);
v_sz_4258_ = lean_array_size(v_a_4257_);
v___x_4259_ = ((size_t)0ULL);
v___x_290__overap_4260_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_4244_, v___f_4245_, v_sz_4258_, v___x_4259_, v_a_4257_);
v___x_4261_ = lean_apply_1(v___x_290__overap_4260_, lean_box(0));
return v___x_4261_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__2___boxed(lean_object* v___x_4262_, lean_object* v___f_4263_, lean_object* v_x_4264_, lean_object* v___y_4265_){
_start:
{
lean_object* v_res_4266_; 
v_res_4266_ = l_Std_Async_EAsync_concurrentlyAll___redArg___lam__2(v___x_4262_, v___f_4263_, v_x_4264_);
return v_res_4266_;
}
}
static lean_object* _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0(void){
_start:
{
lean_object* v___x_4267_; 
v___x_4267_ = l_Std_Async_EAsync_instMonad(lean_box(0));
return v___x_4267_;
}
}
static lean_object* _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__2(void){
_start:
{
lean_object* v___f_4269_; lean_object* v___x_4270_; lean_object* v___f_4271_; 
v___f_4269_ = ((lean_object*)(l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1));
v___x_4270_ = lean_obj_once(&l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0, &l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0_once, _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0);
v___f_4271_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrentlyAll___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4271_, 0, v___x_4270_);
lean_closure_set(v___f_4271_, 1, v___f_4269_);
return v___f_4271_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg(lean_object* v_xs_4272_, lean_object* v_prio_4273_){
_start:
{
lean_object* v___f_4275_; lean_object* v___f_4276_; lean_object* v___x_4277_; size_t v_sz_4278_; size_t v___x_4279_; lean_object* v___x_217__overap_4280_; lean_object* v___x_4281_; lean_object* v___f_4282_; lean_object* v___x_4283_; uint8_t v___x_4284_; lean_object* v___x_4285_; 
v___f_4275_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___f_4276_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4276_, 0, v_prio_4273_);
lean_closure_set(v___f_4276_, 1, v___f_4275_);
v___x_4277_ = lean_obj_once(&l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0, &l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0_once, _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0);
v_sz_4278_ = lean_array_size(v_xs_4272_);
v___x_4279_ = ((size_t)0ULL);
v___x_217__overap_4280_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_4277_, v___f_4276_, v_sz_4278_, v___x_4279_, v_xs_4272_);
v___x_4281_ = lean_apply_1(v___x_217__overap_4280_, lean_box(0));
v___f_4282_ = lean_obj_once(&l_Std_Async_EAsync_concurrentlyAll___redArg___closed__2, &l_Std_Async_EAsync_concurrentlyAll___redArg___closed__2_once, _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__2);
v___x_4283_ = lean_unsigned_to_nat(0u);
v___x_4284_ = 0;
v___x_4285_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4283_, v___x_4284_, v___x_4281_, v___f_4282_);
return v___x_4285_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___boxed(lean_object* v_xs_4286_, lean_object* v_prio_4287_, lean_object* v_a_4288_){
_start:
{
lean_object* v_res_4289_; 
v_res_4289_ = l_Std_Async_EAsync_concurrentlyAll___redArg(v_xs_4286_, v_prio_4287_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll(lean_object* v_00_u03b5_4290_, lean_object* v_00_u03b1_4291_, lean_object* v_xs_4292_, lean_object* v_prio_4293_){
_start:
{
lean_object* v___f_4295_; lean_object* v___f_4296_; lean_object* v___x_4297_; size_t v_sz_4298_; size_t v___x_4299_; lean_object* v___x_239__overap_4300_; lean_object* v___x_4301_; lean_object* v___f_4302_; lean_object* v___x_4303_; uint8_t v___x_4304_; lean_object* v___x_4305_; 
v___f_4295_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___f_4296_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4296_, 0, v_prio_4293_);
lean_closure_set(v___f_4296_, 1, v___f_4295_);
v___x_4297_ = lean_obj_once(&l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0, &l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0_once, _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0);
v_sz_4298_ = lean_array_size(v_xs_4292_);
v___x_4299_ = ((size_t)0ULL);
v___x_239__overap_4300_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_4297_, v___f_4296_, v_sz_4298_, v___x_4299_, v_xs_4292_);
v___x_4301_ = lean_apply_1(v___x_239__overap_4300_, lean_box(0));
v___f_4302_ = lean_obj_once(&l_Std_Async_EAsync_concurrentlyAll___redArg___closed__2, &l_Std_Async_EAsync_concurrentlyAll___redArg___closed__2_once, _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__2);
v___x_4303_ = lean_unsigned_to_nat(0u);
v___x_4304_ = 0;
v___x_4305_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4303_, v___x_4304_, v___x_4301_, v___f_4302_);
return v___x_4305_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___boxed(lean_object* v_00_u03b5_4306_, lean_object* v_00_u03b1_4307_, lean_object* v_xs_4308_, lean_object* v_prio_4309_, lean_object* v_a_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l_Std_Async_EAsync_concurrentlyAll(v_00_u03b5_4306_, v_00_u03b1_4307_, v_xs_4308_, v_prio_4309_);
return v_res_4311_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__4(lean_object* v___f_4312_, lean_object* v___f_4313_, lean_object* v_x_4314_){
_start:
{
if (lean_obj_tag(v_x_4314_) == 0)
{
lean_object* v_a_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4324_; 
lean_dec_ref(v___f_4313_);
lean_dec(v___f_4312_);
v_a_4316_ = lean_ctor_get(v_x_4314_, 0);
v_isSharedCheck_4324_ = !lean_is_exclusive(v_x_4314_);
if (v_isSharedCheck_4324_ == 0)
{
v___x_4318_ = v_x_4314_;
v_isShared_4319_ = v_isSharedCheck_4324_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_a_4316_);
lean_dec(v_x_4314_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4324_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v___x_4321_; 
if (v_isShared_4319_ == 0)
{
v___x_4321_ = v___x_4318_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4323_; 
v_reuseFailAlloc_4323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4323_, 0, v_a_4316_);
v___x_4321_ = v_reuseFailAlloc_4323_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
lean_object* v___x_4322_; 
v___x_4322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4322_, 0, v___x_4321_);
return v___x_4322_;
}
}
}
else
{
lean_object* v_a_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4338_; 
v_a_4325_ = lean_ctor_get(v_x_4314_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v_x_4314_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4327_ = v_x_4314_;
v_isShared_4328_ = v_isSharedCheck_4338_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_a_4325_);
lean_dec(v_x_4314_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4338_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; uint8_t v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4335_; 
v___x_4329_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_4329_, 0, lean_box(0));
lean_closure_set(v___x_4329_, 1, lean_box(0));
lean_closure_set(v___x_4329_, 2, v___f_4312_);
lean_closure_set(v___x_4329_, 3, lean_box(0));
v___x_4330_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4330_, 0, lean_box(0));
lean_closure_set(v___x_4330_, 1, lean_box(0));
lean_closure_set(v___x_4330_, 2, lean_box(0));
lean_closure_set(v___x_4330_, 3, v___x_4329_);
lean_closure_set(v___x_4330_, 4, v___f_4313_);
v___x_4331_ = lean_unsigned_to_nat(0u);
v___x_4332_ = 0;
v___x_4333_ = l_BaseIO_chainTask___redArg(v_a_4325_, v___x_4330_, v___x_4331_, v___x_4332_);
if (v_isShared_4328_ == 0)
{
lean_ctor_set(v___x_4327_, 0, v___x_4333_);
v___x_4335_ = v___x_4327_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v___x_4333_);
v___x_4335_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
lean_object* v___x_4336_; 
v___x_4336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4336_, 0, v___x_4335_);
return v___x_4336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__4___boxed(lean_object* v___f_4339_, lean_object* v___f_4340_, lean_object* v_x_4341_, lean_object* v___y_4342_){
_start:
{
lean_object* v_res_4343_; 
v_res_4343_ = l_Std_Async_EAsync_raceAll___redArg___lam__4(v___f_4339_, v___f_4340_, v_x_4341_);
return v_res_4343_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__0(lean_object* v_prio_4344_, lean_object* v___f_4345_, lean_object* v___f_4346_, lean_object* v_x_4347_){
_start:
{
lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; uint8_t v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; uint8_t v___x_4356_; lean_object* v___x_4357_; 
v___x_4349_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4349_, 0, lean_box(0));
lean_closure_set(v___x_4349_, 1, v_x_4347_);
v___x_4350_ = lean_io_as_task(v___x_4349_, v_prio_4344_);
v___x_4351_ = lean_unsigned_to_nat(0u);
v___x_4352_ = 1;
v___x_4353_ = lean_task_bind(v___x_4350_, v___f_4345_, v___x_4351_, v___x_4352_);
v___x_4354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4354_, 0, v___x_4353_);
v___x_4355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4355_, 0, v___x_4354_);
v___x_4356_ = 0;
v___x_4357_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4351_, v___x_4356_, v___x_4355_, v___f_4346_);
return v___x_4357_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__0___boxed(lean_object* v_prio_4358_, lean_object* v___f_4359_, lean_object* v___f_4360_, lean_object* v_x_4361_, lean_object* v___y_4362_){
_start:
{
lean_object* v_res_4363_; 
v_res_4363_ = l_Std_Async_EAsync_raceAll___redArg___lam__0(v_prio_4358_, v___f_4359_, v___f_4360_, v_x_4361_);
return v_res_4363_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__2(lean_object* v___f_4364_, lean_object* v_prio_4365_, lean_object* v___f_4366_, lean_object* v_inst_4367_, lean_object* v_xs_4368_, lean_object* v___f_4369_, lean_object* v___f_4370_, lean_object* v_x_4371_){
_start:
{
if (lean_obj_tag(v_x_4371_) == 0)
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4381_; 
lean_dec_ref(v___f_4370_);
lean_dec_ref(v___f_4369_);
lean_dec(v_xs_4368_);
lean_dec_ref(v_inst_4367_);
lean_dec_ref(v___f_4366_);
lean_dec(v_prio_4365_);
lean_dec(v___f_4364_);
v_a_4373_ = lean_ctor_get(v_x_4371_, 0);
v_isSharedCheck_4381_ = !lean_is_exclusive(v_x_4371_);
if (v_isSharedCheck_4381_ == 0)
{
v___x_4375_ = v_x_4371_;
v_isShared_4376_ = v_isSharedCheck_4381_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v_x_4371_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4381_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4378_; 
if (v_isShared_4376_ == 0)
{
v___x_4378_ = v___x_4375_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v_a_4373_);
v___x_4378_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
lean_object* v___x_4379_; 
v___x_4379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4379_, 0, v___x_4378_);
return v___x_4379_;
}
}
}
else
{
lean_object* v_a_4382_; lean_object* v___f_4383_; lean_object* v___f_4384_; lean_object* v___f_4385_; lean_object* v___x_4386_; lean_object* v___f_4387_; lean_object* v___x_4388_; uint8_t v___x_4389_; lean_object* v___x_4390_; 
v_a_4382_ = lean_ctor_get(v_x_4371_, 0);
lean_inc_n(v_a_4382_, 2);
lean_dec_ref(v_x_4371_);
v___f_4383_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4383_, 0, v_a_4382_);
v___f_4384_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_raceAll___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_4384_, 0, v___f_4364_);
lean_closure_set(v___f_4384_, 1, v___f_4383_);
v___f_4385_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_raceAll___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4385_, 0, v_prio_4365_);
lean_closure_set(v___f_4385_, 1, v___f_4366_);
lean_closure_set(v___f_4385_, 2, v___f_4384_);
v___x_4386_ = lean_apply_3(v_inst_4367_, v_xs_4368_, v___f_4385_, lean_box(0));
v___f_4387_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_4387_, 0, v_a_4382_);
lean_closure_set(v___f_4387_, 1, v___f_4369_);
lean_closure_set(v___f_4387_, 2, v___f_4370_);
v___x_4388_ = lean_unsigned_to_nat(0u);
v___x_4389_ = 0;
v___x_4390_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4388_, v___x_4389_, v___x_4386_, v___f_4387_);
return v___x_4390_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__2___boxed(lean_object* v___f_4391_, lean_object* v_prio_4392_, lean_object* v___f_4393_, lean_object* v_inst_4394_, lean_object* v_xs_4395_, lean_object* v___f_4396_, lean_object* v___f_4397_, lean_object* v_x_4398_, lean_object* v___y_4399_){
_start:
{
lean_object* v_res_4400_; 
v_res_4400_ = l_Std_Async_EAsync_raceAll___redArg___lam__2(v___f_4391_, v_prio_4392_, v___f_4393_, v_inst_4394_, v_xs_4395_, v___f_4396_, v___f_4397_, v_x_4398_);
return v_res_4400_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg(lean_object* v_inst_4401_, lean_object* v_xs_4402_, lean_object* v_prio_4403_){
_start:
{
lean_object* v___x_4405_; lean_object* v___f_4406_; lean_object* v___f_4407_; lean_object* v___f_4408_; lean_object* v___f_4409_; lean_object* v___f_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; uint8_t v___x_4414_; lean_object* v___x_4415_; 
v___x_4405_ = lean_io_promise_new();
v___f_4406_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__1));
v___f_4407_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__0));
v___f_4408_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___f_4409_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_4410_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_raceAll___redArg___lam__2___boxed), 9, 7);
lean_closure_set(v___f_4410_, 0, v___f_4409_);
lean_closure_set(v___f_4410_, 1, v_prio_4403_);
lean_closure_set(v___f_4410_, 2, v___f_4408_);
lean_closure_set(v___f_4410_, 3, v_inst_4401_);
lean_closure_set(v___f_4410_, 4, v_xs_4402_);
lean_closure_set(v___f_4410_, 5, v___f_4406_);
lean_closure_set(v___f_4410_, 6, v___f_4407_);
v___x_4411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4411_, 0, v___x_4405_);
v___x_4412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4412_, 0, v___x_4411_);
v___x_4413_ = lean_unsigned_to_nat(0u);
v___x_4414_ = 0;
v___x_4415_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4413_, v___x_4414_, v___x_4412_, v___f_4410_);
return v___x_4415_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___boxed(lean_object* v_inst_4416_, lean_object* v_xs_4417_, lean_object* v_prio_4418_, lean_object* v_a_4419_){
_start:
{
lean_object* v_res_4420_; 
v_res_4420_ = l_Std_Async_EAsync_raceAll___redArg(v_inst_4416_, v_xs_4417_, v_prio_4418_);
return v_res_4420_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll(lean_object* v_00_u03b1_4421_, lean_object* v_00_u03b5_4422_, lean_object* v_c_4423_, lean_object* v_inst_4424_, lean_object* v_inst_4425_, lean_object* v_xs_4426_, lean_object* v_prio_4427_){
_start:
{
lean_object* v___x_4429_; lean_object* v___f_4430_; lean_object* v___f_4431_; lean_object* v___f_4432_; lean_object* v___f_4433_; lean_object* v___f_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; uint8_t v___x_4438_; lean_object* v___x_4439_; 
v___x_4429_ = lean_io_promise_new();
v___f_4430_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__1));
v___f_4431_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__0));
v___f_4432_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___f_4433_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_4434_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_raceAll___redArg___lam__2___boxed), 9, 7);
lean_closure_set(v___f_4434_, 0, v___f_4433_);
lean_closure_set(v___f_4434_, 1, v_prio_4427_);
lean_closure_set(v___f_4434_, 2, v___f_4432_);
lean_closure_set(v___f_4434_, 3, v_inst_4425_);
lean_closure_set(v___f_4434_, 4, v_xs_4426_);
lean_closure_set(v___f_4434_, 5, v___f_4430_);
lean_closure_set(v___f_4434_, 6, v___f_4431_);
v___x_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4435_, 0, v___x_4429_);
v___x_4436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4436_, 0, v___x_4435_);
v___x_4437_ = lean_unsigned_to_nat(0u);
v___x_4438_ = 0;
v___x_4439_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4437_, v___x_4438_, v___x_4436_, v___f_4434_);
return v___x_4439_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___boxed(lean_object* v_00_u03b1_4440_, lean_object* v_00_u03b5_4441_, lean_object* v_c_4442_, lean_object* v_inst_4443_, lean_object* v_inst_4444_, lean_object* v_xs_4445_, lean_object* v_prio_4446_, lean_object* v_a_4447_){
_start:
{
lean_object* v_res_4448_; 
v_res_4448_ = l_Std_Async_EAsync_raceAll(v_00_u03b1_4440_, v_00_u03b5_4441_, v_c_4442_, v_inst_4443_, v_inst_4444_, v_xs_4445_, v_prio_4446_);
lean_dec(v_inst_4443_);
return v_res_4448_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_toIO___redArg(lean_object* v_x_4449_){
_start:
{
lean_object* v___x_4451_; 
v___x_4451_ = lean_apply_1(v_x_4449_, lean_box(0));
if (lean_obj_tag(v___x_4451_) == 0)
{
lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4460_; 
v_a_4452_ = lean_ctor_get(v___x_4451_, 0);
v_isSharedCheck_4460_ = !lean_is_exclusive(v___x_4451_);
if (v_isSharedCheck_4460_ == 0)
{
v___x_4454_ = v___x_4451_;
v_isShared_4455_ = v_isSharedCheck_4460_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v___x_4451_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4460_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4456_; lean_object* v___x_4458_; 
v___x_4456_ = lean_task_pure(v_a_4452_);
if (v_isShared_4455_ == 0)
{
lean_ctor_set(v___x_4454_, 0, v___x_4456_);
v___x_4458_ = v___x_4454_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v___x_4456_);
v___x_4458_ = v_reuseFailAlloc_4459_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
return v___x_4458_;
}
}
}
else
{
lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4468_; 
v_a_4461_ = lean_ctor_get(v___x_4451_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4451_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4463_ = v___x_4451_;
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v___x_4451_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4466_; 
if (v_isShared_4464_ == 0)
{
lean_ctor_set_tag(v___x_4463_, 0);
v___x_4466_ = v___x_4463_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v_a_4461_);
v___x_4466_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
return v___x_4466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_toIO___redArg___boxed(lean_object* v_x_4469_, lean_object* v_a_4470_){
_start:
{
lean_object* v_res_4471_; 
v_res_4471_ = l_Std_Async_Async_toIO___redArg(v_x_4469_);
return v_res_4471_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_toIO(lean_object* v_00_u03b1_4472_, lean_object* v_x_4473_){
_start:
{
lean_object* v___x_4475_; 
v___x_4475_ = lean_apply_1(v_x_4473_, lean_box(0));
if (lean_obj_tag(v___x_4475_) == 0)
{
lean_object* v_a_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4484_; 
v_a_4476_ = lean_ctor_get(v___x_4475_, 0);
v_isSharedCheck_4484_ = !lean_is_exclusive(v___x_4475_);
if (v_isSharedCheck_4484_ == 0)
{
v___x_4478_ = v___x_4475_;
v_isShared_4479_ = v_isSharedCheck_4484_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_a_4476_);
lean_dec(v___x_4475_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4484_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4480_; lean_object* v___x_4482_; 
v___x_4480_ = lean_task_pure(v_a_4476_);
if (v_isShared_4479_ == 0)
{
lean_ctor_set(v___x_4478_, 0, v___x_4480_);
v___x_4482_ = v___x_4478_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v___x_4480_);
v___x_4482_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
return v___x_4482_;
}
}
}
else
{
lean_object* v_a_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4492_; 
v_a_4485_ = lean_ctor_get(v___x_4475_, 0);
v_isSharedCheck_4492_ = !lean_is_exclusive(v___x_4475_);
if (v_isSharedCheck_4492_ == 0)
{
v___x_4487_ = v___x_4475_;
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_a_4485_);
lean_dec(v___x_4475_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v___x_4490_; 
if (v_isShared_4488_ == 0)
{
lean_ctor_set_tag(v___x_4487_, 0);
v___x_4490_ = v___x_4487_;
goto v_reusejp_4489_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v_a_4485_);
v___x_4490_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4489_;
}
v_reusejp_4489_:
{
return v___x_4490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_toIO___boxed(lean_object* v_00_u03b1_4493_, lean_object* v_x_4494_, lean_object* v_a_4495_){
_start:
{
lean_object* v_res_4496_; 
v_res_4496_ = l_Std_Async_Async_toIO(v_00_u03b1_4493_, v_x_4494_);
return v_res_4496_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_block___redArg(lean_object* v_x_4497_, lean_object* v_prio_4498_){
_start:
{
lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___f_4502_; lean_object* v___x_4503_; uint8_t v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; 
v___x_4500_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4500_, 0, lean_box(0));
lean_closure_set(v___x_4500_, 1, v_x_4497_);
v___x_4501_ = lean_io_as_task(v___x_4500_, v_prio_4498_);
v___f_4502_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___x_4503_ = lean_unsigned_to_nat(0u);
v___x_4504_ = 1;
v___x_4505_ = lean_task_bind(v___x_4501_, v___f_4502_, v___x_4503_, v___x_4504_);
v___x_4506_ = lean_task_get_own(v___x_4505_);
if (lean_obj_tag(v___x_4506_) == 0)
{
lean_object* v_a_4507_; lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4514_; 
v_a_4507_ = lean_ctor_get(v___x_4506_, 0);
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4506_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4509_ = v___x_4506_;
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
else
{
lean_inc(v_a_4507_);
lean_dec(v___x_4506_);
v___x_4509_ = lean_box(0);
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
v_resetjp_4508_:
{
lean_object* v___x_4512_; 
if (v_isShared_4510_ == 0)
{
lean_ctor_set_tag(v___x_4509_, 1);
v___x_4512_ = v___x_4509_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_a_4507_);
v___x_4512_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
return v___x_4512_;
}
}
}
else
{
lean_object* v_a_4515_; lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4522_; 
v_a_4515_ = lean_ctor_get(v___x_4506_, 0);
v_isSharedCheck_4522_ = !lean_is_exclusive(v___x_4506_);
if (v_isSharedCheck_4522_ == 0)
{
v___x_4517_ = v___x_4506_;
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
else
{
lean_inc(v_a_4515_);
lean_dec(v___x_4506_);
v___x_4517_ = lean_box(0);
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
v_resetjp_4516_:
{
lean_object* v___x_4520_; 
if (v_isShared_4518_ == 0)
{
lean_ctor_set_tag(v___x_4517_, 0);
v___x_4520_ = v___x_4517_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_a_4515_);
v___x_4520_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
return v___x_4520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_block___redArg___boxed(lean_object* v_x_4523_, lean_object* v_prio_4524_, lean_object* v_a_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l_Std_Async_Async_block___redArg(v_x_4523_, v_prio_4524_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_block(lean_object* v_00_u03b1_4527_, lean_object* v_x_4528_, lean_object* v_prio_4529_){
_start:
{
lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___f_4533_; lean_object* v___x_4534_; uint8_t v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___x_4531_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4531_, 0, lean_box(0));
lean_closure_set(v___x_4531_, 1, v_x_4528_);
v___x_4532_ = lean_io_as_task(v___x_4531_, v_prio_4529_);
v___f_4533_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___x_4534_ = lean_unsigned_to_nat(0u);
v___x_4535_ = 1;
v___x_4536_ = lean_task_bind(v___x_4532_, v___f_4533_, v___x_4534_, v___x_4535_);
v___x_4537_ = lean_task_get_own(v___x_4536_);
if (lean_obj_tag(v___x_4537_) == 0)
{
lean_object* v_a_4538_; lean_object* v___x_4540_; uint8_t v_isShared_4541_; uint8_t v_isSharedCheck_4545_; 
v_a_4538_ = lean_ctor_get(v___x_4537_, 0);
v_isSharedCheck_4545_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4545_ == 0)
{
v___x_4540_ = v___x_4537_;
v_isShared_4541_ = v_isSharedCheck_4545_;
goto v_resetjp_4539_;
}
else
{
lean_inc(v_a_4538_);
lean_dec(v___x_4537_);
v___x_4540_ = lean_box(0);
v_isShared_4541_ = v_isSharedCheck_4545_;
goto v_resetjp_4539_;
}
v_resetjp_4539_:
{
lean_object* v___x_4543_; 
if (v_isShared_4541_ == 0)
{
lean_ctor_set_tag(v___x_4540_, 1);
v___x_4543_ = v___x_4540_;
goto v_reusejp_4542_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_a_4538_);
v___x_4543_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4542_;
}
v_reusejp_4542_:
{
return v___x_4543_;
}
}
}
else
{
lean_object* v_a_4546_; lean_object* v___x_4548_; uint8_t v_isShared_4549_; uint8_t v_isSharedCheck_4553_; 
v_a_4546_ = lean_ctor_get(v___x_4537_, 0);
v_isSharedCheck_4553_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4553_ == 0)
{
v___x_4548_ = v___x_4537_;
v_isShared_4549_ = v_isSharedCheck_4553_;
goto v_resetjp_4547_;
}
else
{
lean_inc(v_a_4546_);
lean_dec(v___x_4537_);
v___x_4548_ = lean_box(0);
v_isShared_4549_ = v_isSharedCheck_4553_;
goto v_resetjp_4547_;
}
v_resetjp_4547_:
{
lean_object* v___x_4551_; 
if (v_isShared_4549_ == 0)
{
lean_ctor_set_tag(v___x_4548_, 0);
v___x_4551_ = v___x_4548_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v_a_4546_);
v___x_4551_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
return v___x_4551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_block___boxed(lean_object* v_00_u03b1_4554_, lean_object* v_x_4555_, lean_object* v_prio_4556_, lean_object* v_a_4557_){
_start:
{
lean_object* v_res_4558_; 
v_res_4558_ = l_Std_Async_Async_block(v_00_u03b1_4554_, v_x_4555_, v_prio_4556_);
return v_res_4558_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise___redArg___lam__1(lean_object* v___f_4559_, lean_object* v_x_4560_){
_start:
{
if (lean_obj_tag(v_x_4560_) == 0)
{
lean_object* v_a_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4570_; 
lean_dec_ref(v___f_4559_);
v_a_4562_ = lean_ctor_get(v_x_4560_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v_x_4560_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4564_ = v_x_4560_;
v_isShared_4565_ = v_isSharedCheck_4570_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_a_4562_);
lean_dec(v_x_4560_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4570_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4567_; 
if (v_isShared_4565_ == 0)
{
v___x_4567_ = v___x_4564_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_a_4562_);
v___x_4567_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
lean_object* v___x_4568_; 
v___x_4568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4568_, 0, v___x_4567_);
return v___x_4568_;
}
}
}
else
{
lean_object* v_a_4571_; 
v_a_4571_ = lean_ctor_get(v_x_4560_, 0);
lean_inc(v_a_4571_);
lean_dec_ref(v_x_4560_);
if (lean_obj_tag(v_a_4571_) == 0)
{
lean_object* v_a_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4580_; 
lean_dec_ref(v___f_4559_);
v_a_4572_ = lean_ctor_get(v_a_4571_, 0);
v_isSharedCheck_4580_ = !lean_is_exclusive(v_a_4571_);
if (v_isSharedCheck_4580_ == 0)
{
v___x_4574_ = v_a_4571_;
v_isShared_4575_ = v_isSharedCheck_4580_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_a_4572_);
lean_dec(v_a_4571_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4580_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v___x_4577_; 
if (v_isShared_4575_ == 0)
{
v___x_4577_ = v___x_4574_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4579_; 
v_reuseFailAlloc_4579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4579_, 0, v_a_4572_);
v___x_4577_ = v_reuseFailAlloc_4579_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
lean_object* v___x_4578_; 
v___x_4578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4577_);
return v___x_4578_;
}
}
}
else
{
lean_object* v_a_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; uint8_t v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; 
v_a_4581_ = lean_ctor_get(v_a_4571_, 0);
lean_inc(v_a_4581_);
lean_dec_ref(v_a_4571_);
v___x_4582_ = lean_io_promise_result_opt(v_a_4581_);
lean_dec(v_a_4581_);
v___x_4583_ = lean_unsigned_to_nat(0u);
v___x_4584_ = 0;
v___x_4585_ = lean_task_map(v___f_4559_, v___x_4582_, v___x_4583_, v___x_4584_);
v___x_4586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4586_, 0, v___x_4585_);
return v___x_4586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise___redArg___lam__1___boxed(lean_object* v___f_4587_, lean_object* v_x_4588_, lean_object* v___y_4589_){
_start:
{
lean_object* v_res_4590_; 
v_res_4590_ = l_Std_Async_Async_ofPromise___redArg___lam__1(v___f_4587_, v_x_4588_);
return v_res_4590_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise___redArg(lean_object* v_task_4591_, lean_object* v_error_4592_){
_start:
{
lean_object* v___f_4594_; lean_object* v___f_4595_; lean_object* v_val_4597_; lean_object* v___x_4603_; 
v___f_4594_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPromise___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4594_, 0, v_error_4592_);
v___f_4595_ = lean_alloc_closure((void*)(l_Std_Async_Async_ofPromise___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4595_, 0, v___f_4594_);
v___x_4603_ = lean_apply_1(v_task_4591_, lean_box(0));
if (lean_obj_tag(v___x_4603_) == 0)
{
lean_object* v_a_4604_; lean_object* v___x_4606_; uint8_t v_isShared_4607_; uint8_t v_isSharedCheck_4611_; 
v_a_4604_ = lean_ctor_get(v___x_4603_, 0);
v_isSharedCheck_4611_ = !lean_is_exclusive(v___x_4603_);
if (v_isSharedCheck_4611_ == 0)
{
v___x_4606_ = v___x_4603_;
v_isShared_4607_ = v_isSharedCheck_4611_;
goto v_resetjp_4605_;
}
else
{
lean_inc(v_a_4604_);
lean_dec(v___x_4603_);
v___x_4606_ = lean_box(0);
v_isShared_4607_ = v_isSharedCheck_4611_;
goto v_resetjp_4605_;
}
v_resetjp_4605_:
{
lean_object* v___x_4609_; 
if (v_isShared_4607_ == 0)
{
lean_ctor_set_tag(v___x_4606_, 1);
v___x_4609_ = v___x_4606_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v_a_4604_);
v___x_4609_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
v_val_4597_ = v___x_4609_;
goto v___jp_4596_;
}
}
}
else
{
lean_object* v_a_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4619_; 
v_a_4612_ = lean_ctor_get(v___x_4603_, 0);
v_isSharedCheck_4619_ = !lean_is_exclusive(v___x_4603_);
if (v_isSharedCheck_4619_ == 0)
{
v___x_4614_ = v___x_4603_;
v_isShared_4615_ = v_isSharedCheck_4619_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_a_4612_);
lean_dec(v___x_4603_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4619_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
lean_object* v___x_4617_; 
if (v_isShared_4615_ == 0)
{
lean_ctor_set_tag(v___x_4614_, 0);
v___x_4617_ = v___x_4614_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v_a_4612_);
v___x_4617_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
v_val_4597_ = v___x_4617_;
goto v___jp_4596_;
}
}
}
v___jp_4596_:
{
lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; uint8_t v___x_4601_; lean_object* v___x_4602_; 
v___x_4598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4598_, 0, v_val_4597_);
v___x_4599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4599_, 0, v___x_4598_);
v___x_4600_ = lean_unsigned_to_nat(0u);
v___x_4601_ = 0;
v___x_4602_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4600_, v___x_4601_, v___x_4599_, v___f_4595_);
return v___x_4602_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise___redArg___boxed(lean_object* v_task_4620_, lean_object* v_error_4621_, lean_object* v_a_4622_){
_start:
{
lean_object* v_res_4623_; 
v_res_4623_ = l_Std_Async_Async_ofPromise___redArg(v_task_4620_, v_error_4621_);
return v_res_4623_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise(lean_object* v_00_u03b1_4624_, lean_object* v_task_4625_, lean_object* v_error_4626_){
_start:
{
lean_object* v___f_4628_; lean_object* v___f_4629_; lean_object* v_val_4631_; lean_object* v___x_4637_; 
v___f_4628_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPromise___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4628_, 0, v_error_4626_);
v___f_4629_ = lean_alloc_closure((void*)(l_Std_Async_Async_ofPromise___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4629_, 0, v___f_4628_);
v___x_4637_ = lean_apply_1(v_task_4625_, lean_box(0));
if (lean_obj_tag(v___x_4637_) == 0)
{
lean_object* v_a_4638_; lean_object* v___x_4640_; uint8_t v_isShared_4641_; uint8_t v_isSharedCheck_4645_; 
v_a_4638_ = lean_ctor_get(v___x_4637_, 0);
v_isSharedCheck_4645_ = !lean_is_exclusive(v___x_4637_);
if (v_isSharedCheck_4645_ == 0)
{
v___x_4640_ = v___x_4637_;
v_isShared_4641_ = v_isSharedCheck_4645_;
goto v_resetjp_4639_;
}
else
{
lean_inc(v_a_4638_);
lean_dec(v___x_4637_);
v___x_4640_ = lean_box(0);
v_isShared_4641_ = v_isSharedCheck_4645_;
goto v_resetjp_4639_;
}
v_resetjp_4639_:
{
lean_object* v___x_4643_; 
if (v_isShared_4641_ == 0)
{
lean_ctor_set_tag(v___x_4640_, 1);
v___x_4643_ = v___x_4640_;
goto v_reusejp_4642_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v_a_4638_);
v___x_4643_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4642_;
}
v_reusejp_4642_:
{
v_val_4631_ = v___x_4643_;
goto v___jp_4630_;
}
}
}
else
{
lean_object* v_a_4646_; lean_object* v___x_4648_; uint8_t v_isShared_4649_; uint8_t v_isSharedCheck_4653_; 
v_a_4646_ = lean_ctor_get(v___x_4637_, 0);
v_isSharedCheck_4653_ = !lean_is_exclusive(v___x_4637_);
if (v_isSharedCheck_4653_ == 0)
{
v___x_4648_ = v___x_4637_;
v_isShared_4649_ = v_isSharedCheck_4653_;
goto v_resetjp_4647_;
}
else
{
lean_inc(v_a_4646_);
lean_dec(v___x_4637_);
v___x_4648_ = lean_box(0);
v_isShared_4649_ = v_isSharedCheck_4653_;
goto v_resetjp_4647_;
}
v_resetjp_4647_:
{
lean_object* v___x_4651_; 
if (v_isShared_4649_ == 0)
{
lean_ctor_set_tag(v___x_4648_, 0);
v___x_4651_ = v___x_4648_;
goto v_reusejp_4650_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v_a_4646_);
v___x_4651_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4650_;
}
v_reusejp_4650_:
{
v_val_4631_ = v___x_4651_;
goto v___jp_4630_;
}
}
}
v___jp_4630_:
{
lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; uint8_t v___x_4635_; lean_object* v___x_4636_; 
v___x_4632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4632_, 0, v_val_4631_);
v___x_4633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4633_, 0, v___x_4632_);
v___x_4634_ = lean_unsigned_to_nat(0u);
v___x_4635_ = 0;
v___x_4636_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4634_, v___x_4635_, v___x_4633_, v___f_4629_);
return v___x_4636_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise___boxed(lean_object* v_00_u03b1_4654_, lean_object* v_task_4655_, lean_object* v_error_4656_, lean_object* v_a_4657_){
_start:
{
lean_object* v_res_4658_; 
v_res_4658_ = l_Std_Async_Async_ofPromise(v_00_u03b1_4654_, v_task_4655_, v_error_4656_);
return v_res_4658_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofAsyncTask___redArg(lean_object* v_task_4659_){
_start:
{
lean_object* v___x_4661_; 
v___x_4661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4661_, 0, v_task_4659_);
return v___x_4661_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofAsyncTask___redArg___boxed(lean_object* v_task_4662_, lean_object* v_a_4663_){
_start:
{
lean_object* v_res_4664_; 
v_res_4664_ = l_Std_Async_Async_ofAsyncTask___redArg(v_task_4662_);
return v_res_4664_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofAsyncTask(lean_object* v_00_u03b1_4665_, lean_object* v_task_4666_){
_start:
{
lean_object* v___x_4668_; 
v___x_4668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4668_, 0, v_task_4666_);
return v___x_4668_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofAsyncTask___boxed(lean_object* v_00_u03b1_4669_, lean_object* v_task_4670_, lean_object* v_a_4671_){
_start:
{
lean_object* v_res_4672_; 
v_res_4672_ = l_Std_Async_Async_ofAsyncTask(v_00_u03b1_4669_, v_task_4670_);
return v_res_4672_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___redArg___lam__0(lean_object* v_a_4673_){
_start:
{
lean_object* v___x_4674_; 
v___x_4674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4674_, 0, v_a_4673_);
return v___x_4674_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___redArg___lam__1(lean_object* v___f_4675_, lean_object* v_x_4676_){
_start:
{
if (lean_obj_tag(v_x_4676_) == 0)
{
lean_object* v_a_4678_; lean_object* v___x_4680_; uint8_t v_isShared_4681_; uint8_t v_isSharedCheck_4686_; 
lean_dec_ref(v___f_4675_);
v_a_4678_ = lean_ctor_get(v_x_4676_, 0);
v_isSharedCheck_4686_ = !lean_is_exclusive(v_x_4676_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4680_ = v_x_4676_;
v_isShared_4681_ = v_isSharedCheck_4686_;
goto v_resetjp_4679_;
}
else
{
lean_inc(v_a_4678_);
lean_dec(v_x_4676_);
v___x_4680_ = lean_box(0);
v_isShared_4681_ = v_isSharedCheck_4686_;
goto v_resetjp_4679_;
}
v_resetjp_4679_:
{
lean_object* v___x_4683_; 
if (v_isShared_4681_ == 0)
{
v___x_4683_ = v___x_4680_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_a_4678_);
v___x_4683_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
lean_object* v___x_4684_; 
v___x_4684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4684_, 0, v___x_4683_);
return v___x_4684_;
}
}
}
else
{
lean_object* v_a_4687_; 
v_a_4687_ = lean_ctor_get(v_x_4676_, 0);
lean_inc(v_a_4687_);
lean_dec_ref(v_x_4676_);
if (lean_obj_tag(v_a_4687_) == 0)
{
lean_object* v_a_4688_; lean_object* v___x_4690_; uint8_t v_isShared_4691_; uint8_t v_isSharedCheck_4696_; 
lean_dec_ref(v___f_4675_);
v_a_4688_ = lean_ctor_get(v_a_4687_, 0);
v_isSharedCheck_4696_ = !lean_is_exclusive(v_a_4687_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4690_ = v_a_4687_;
v_isShared_4691_ = v_isSharedCheck_4696_;
goto v_resetjp_4689_;
}
else
{
lean_inc(v_a_4688_);
lean_dec(v_a_4687_);
v___x_4690_ = lean_box(0);
v_isShared_4691_ = v_isSharedCheck_4696_;
goto v_resetjp_4689_;
}
v_resetjp_4689_:
{
lean_object* v___x_4693_; 
if (v_isShared_4691_ == 0)
{
v___x_4693_ = v___x_4690_;
goto v_reusejp_4692_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v_a_4688_);
v___x_4693_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4692_;
}
v_reusejp_4692_:
{
lean_object* v___x_4694_; 
v___x_4694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4694_, 0, v___x_4693_);
return v___x_4694_;
}
}
}
else
{
lean_object* v_a_4697_; lean_object* v___x_4698_; uint8_t v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; 
v_a_4697_ = lean_ctor_get(v_a_4687_, 0);
lean_inc(v_a_4697_);
lean_dec_ref(v_a_4687_);
v___x_4698_ = lean_unsigned_to_nat(0u);
v___x_4699_ = 0;
v___x_4700_ = lean_task_map(v___f_4675_, v_a_4697_, v___x_4698_, v___x_4699_);
v___x_4701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4701_, 0, v___x_4700_);
return v___x_4701_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___redArg___lam__1___boxed(lean_object* v___f_4702_, lean_object* v_x_4703_, lean_object* v___y_4704_){
_start:
{
lean_object* v_res_4705_; 
v_res_4705_ = l_Std_Async_Async_ofIOTask___redArg___lam__1(v___f_4702_, v_x_4703_);
return v_res_4705_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___redArg(lean_object* v_task_4709_){
_start:
{
lean_object* v___f_4711_; lean_object* v_val_4713_; lean_object* v___x_4719_; 
v___f_4711_ = ((lean_object*)(l_Std_Async_Async_ofIOTask___redArg___closed__1));
v___x_4719_ = lean_apply_1(v_task_4709_, lean_box(0));
if (lean_obj_tag(v___x_4719_) == 0)
{
lean_object* v_a_4720_; lean_object* v___x_4722_; uint8_t v_isShared_4723_; uint8_t v_isSharedCheck_4727_; 
v_a_4720_ = lean_ctor_get(v___x_4719_, 0);
v_isSharedCheck_4727_ = !lean_is_exclusive(v___x_4719_);
if (v_isSharedCheck_4727_ == 0)
{
v___x_4722_ = v___x_4719_;
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
else
{
lean_inc(v_a_4720_);
lean_dec(v___x_4719_);
v___x_4722_ = lean_box(0);
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
v_resetjp_4721_:
{
lean_object* v___x_4725_; 
if (v_isShared_4723_ == 0)
{
lean_ctor_set_tag(v___x_4722_, 1);
v___x_4725_ = v___x_4722_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v_a_4720_);
v___x_4725_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
v_val_4713_ = v___x_4725_;
goto v___jp_4712_;
}
}
}
else
{
lean_object* v_a_4728_; lean_object* v___x_4730_; uint8_t v_isShared_4731_; uint8_t v_isSharedCheck_4735_; 
v_a_4728_ = lean_ctor_get(v___x_4719_, 0);
v_isSharedCheck_4735_ = !lean_is_exclusive(v___x_4719_);
if (v_isSharedCheck_4735_ == 0)
{
v___x_4730_ = v___x_4719_;
v_isShared_4731_ = v_isSharedCheck_4735_;
goto v_resetjp_4729_;
}
else
{
lean_inc(v_a_4728_);
lean_dec(v___x_4719_);
v___x_4730_ = lean_box(0);
v_isShared_4731_ = v_isSharedCheck_4735_;
goto v_resetjp_4729_;
}
v_resetjp_4729_:
{
lean_object* v___x_4733_; 
if (v_isShared_4731_ == 0)
{
lean_ctor_set_tag(v___x_4730_, 0);
v___x_4733_ = v___x_4730_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4734_; 
v_reuseFailAlloc_4734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4734_, 0, v_a_4728_);
v___x_4733_ = v_reuseFailAlloc_4734_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
v_val_4713_ = v___x_4733_;
goto v___jp_4712_;
}
}
}
v___jp_4712_:
{
lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; uint8_t v___x_4717_; lean_object* v___x_4718_; 
v___x_4714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4714_, 0, v_val_4713_);
v___x_4715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4715_, 0, v___x_4714_);
v___x_4716_ = lean_unsigned_to_nat(0u);
v___x_4717_ = 0;
v___x_4718_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4716_, v___x_4717_, v___x_4715_, v___f_4711_);
return v___x_4718_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___redArg___boxed(lean_object* v_task_4736_, lean_object* v_a_4737_){
_start:
{
lean_object* v_res_4738_; 
v_res_4738_ = l_Std_Async_Async_ofIOTask___redArg(v_task_4736_);
return v_res_4738_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask(lean_object* v_00_u03b1_4739_, lean_object* v_task_4740_){
_start:
{
lean_object* v___f_4742_; lean_object* v_val_4744_; lean_object* v___x_4750_; 
v___f_4742_ = ((lean_object*)(l_Std_Async_Async_ofIOTask___redArg___closed__1));
v___x_4750_ = lean_apply_1(v_task_4740_, lean_box(0));
if (lean_obj_tag(v___x_4750_) == 0)
{
lean_object* v_a_4751_; lean_object* v___x_4753_; uint8_t v_isShared_4754_; uint8_t v_isSharedCheck_4758_; 
v_a_4751_ = lean_ctor_get(v___x_4750_, 0);
v_isSharedCheck_4758_ = !lean_is_exclusive(v___x_4750_);
if (v_isSharedCheck_4758_ == 0)
{
v___x_4753_ = v___x_4750_;
v_isShared_4754_ = v_isSharedCheck_4758_;
goto v_resetjp_4752_;
}
else
{
lean_inc(v_a_4751_);
lean_dec(v___x_4750_);
v___x_4753_ = lean_box(0);
v_isShared_4754_ = v_isSharedCheck_4758_;
goto v_resetjp_4752_;
}
v_resetjp_4752_:
{
lean_object* v___x_4756_; 
if (v_isShared_4754_ == 0)
{
lean_ctor_set_tag(v___x_4753_, 1);
v___x_4756_ = v___x_4753_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v_a_4751_);
v___x_4756_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4755_;
}
v_reusejp_4755_:
{
v_val_4744_ = v___x_4756_;
goto v___jp_4743_;
}
}
}
else
{
lean_object* v_a_4759_; lean_object* v___x_4761_; uint8_t v_isShared_4762_; uint8_t v_isSharedCheck_4766_; 
v_a_4759_ = lean_ctor_get(v___x_4750_, 0);
v_isSharedCheck_4766_ = !lean_is_exclusive(v___x_4750_);
if (v_isSharedCheck_4766_ == 0)
{
v___x_4761_ = v___x_4750_;
v_isShared_4762_ = v_isSharedCheck_4766_;
goto v_resetjp_4760_;
}
else
{
lean_inc(v_a_4759_);
lean_dec(v___x_4750_);
v___x_4761_ = lean_box(0);
v_isShared_4762_ = v_isSharedCheck_4766_;
goto v_resetjp_4760_;
}
v_resetjp_4760_:
{
lean_object* v___x_4764_; 
if (v_isShared_4762_ == 0)
{
lean_ctor_set_tag(v___x_4761_, 0);
v___x_4764_ = v___x_4761_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v_a_4759_);
v___x_4764_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
v_val_4744_ = v___x_4764_;
goto v___jp_4743_;
}
}
}
v___jp_4743_:
{
lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; uint8_t v___x_4748_; lean_object* v___x_4749_; 
v___x_4745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4745_, 0, v_val_4744_);
v___x_4746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4746_, 0, v___x_4745_);
v___x_4747_ = lean_unsigned_to_nat(0u);
v___x_4748_ = 0;
v___x_4749_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4747_, v___x_4748_, v___x_4746_, v___f_4742_);
return v___x_4749_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___boxed(lean_object* v_00_u03b1_4767_, lean_object* v_task_4768_, lean_object* v_a_4769_){
_start:
{
lean_object* v_res_4770_; 
v_res_4770_ = l_Std_Async_Async_ofIOTask(v_00_u03b1_4767_, v_task_4768_);
return v_res_4770_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofExcept___redArg(lean_object* v_except_4771_){
_start:
{
lean_object* v___x_4773_; 
v___x_4773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4773_, 0, v_except_4771_);
return v___x_4773_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofExcept___redArg___boxed(lean_object* v_except_4774_, lean_object* v_a_4775_){
_start:
{
lean_object* v_res_4776_; 
v_res_4776_ = l_Std_Async_Async_ofExcept___redArg(v_except_4774_);
return v_res_4776_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofExcept(lean_object* v_00_u03b1_4777_, lean_object* v_except_4778_){
_start:
{
lean_object* v___x_4780_; 
v___x_4780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4780_, 0, v_except_4778_);
return v___x_4780_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofExcept___boxed(lean_object* v_00_u03b1_4781_, lean_object* v_except_4782_, lean_object* v_a_4783_){
_start:
{
lean_object* v_res_4784_; 
v_res_4784_ = l_Std_Async_Async_ofExcept(v_00_u03b1_4781_, v_except_4782_);
return v_res_4784_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofTask___redArg(lean_object* v_task_4785_){
_start:
{
lean_object* v___f_4787_; lean_object* v___x_4788_; uint8_t v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; 
v___f_4787_ = ((lean_object*)(l_Std_Async_Async_ofIOTask___redArg___closed__0));
v___x_4788_ = lean_unsigned_to_nat(0u);
v___x_4789_ = 0;
v___x_4790_ = lean_task_map(v___f_4787_, v_task_4785_, v___x_4788_, v___x_4789_);
v___x_4791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4791_, 0, v___x_4790_);
return v___x_4791_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofTask___redArg___boxed(lean_object* v_task_4792_, lean_object* v_a_4793_){
_start:
{
lean_object* v_res_4794_; 
v_res_4794_ = l_Std_Async_Async_ofTask___redArg(v_task_4792_);
return v_res_4794_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofTask(lean_object* v_00_u03b1_4795_, lean_object* v_task_4796_){
_start:
{
lean_object* v___f_4798_; lean_object* v___x_4799_; uint8_t v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; 
v___f_4798_ = ((lean_object*)(l_Std_Async_Async_ofIOTask___redArg___closed__0));
v___x_4799_ = lean_unsigned_to_nat(0u);
v___x_4800_ = 0;
v___x_4801_ = lean_task_map(v___f_4798_, v_task_4796_, v___x_4799_, v___x_4800_);
v___x_4802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4802_, 0, v___x_4801_);
return v___x_4802_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofTask___boxed(lean_object* v_00_u03b1_4803_, lean_object* v_task_4804_, lean_object* v_a_4805_){
_start:
{
lean_object* v_res_4806_; 
v_res_4806_ = l_Std_Async_Async_ofTask(v_00_u03b1_4803_, v_task_4804_);
return v_res_4806_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPurePromise___redArg(lean_object* v_task_4807_, lean_object* v_error_4808_){
_start:
{
lean_object* v___x_4810_; 
v___x_4810_ = lean_apply_1(v_task_4807_, lean_box(0));
if (lean_obj_tag(v___x_4810_) == 0)
{
lean_object* v_a_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4823_; 
v_a_4811_ = lean_ctor_get(v___x_4810_, 0);
v_isSharedCheck_4823_ = !lean_is_exclusive(v___x_4810_);
if (v_isSharedCheck_4823_ == 0)
{
v___x_4813_ = v___x_4810_;
v_isShared_4814_ = v_isSharedCheck_4823_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_a_4811_);
lean_dec(v___x_4810_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4823_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v___f_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; uint8_t v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4821_; 
v___f_4815_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPurePromise___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4815_, 0, v_error_4808_);
v___x_4816_ = lean_io_promise_result_opt(v_a_4811_);
lean_dec(v_a_4811_);
v___x_4817_ = lean_unsigned_to_nat(0u);
v___x_4818_ = 0;
v___x_4819_ = lean_task_map(v___f_4815_, v___x_4816_, v___x_4817_, v___x_4818_);
if (v_isShared_4814_ == 0)
{
lean_ctor_set_tag(v___x_4813_, 1);
lean_ctor_set(v___x_4813_, 0, v___x_4819_);
v___x_4821_ = v___x_4813_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v___x_4819_);
v___x_4821_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4820_;
}
v_reusejp_4820_:
{
return v___x_4821_;
}
}
}
else
{
lean_object* v_a_4824_; lean_object* v___x_4826_; uint8_t v_isShared_4827_; uint8_t v_isSharedCheck_4832_; 
lean_dec_ref(v_error_4808_);
v_a_4824_ = lean_ctor_get(v___x_4810_, 0);
v_isSharedCheck_4832_ = !lean_is_exclusive(v___x_4810_);
if (v_isSharedCheck_4832_ == 0)
{
v___x_4826_ = v___x_4810_;
v_isShared_4827_ = v_isSharedCheck_4832_;
goto v_resetjp_4825_;
}
else
{
lean_inc(v_a_4824_);
lean_dec(v___x_4810_);
v___x_4826_ = lean_box(0);
v_isShared_4827_ = v_isSharedCheck_4832_;
goto v_resetjp_4825_;
}
v_resetjp_4825_:
{
lean_object* v___x_4829_; 
if (v_isShared_4827_ == 0)
{
lean_ctor_set_tag(v___x_4826_, 0);
v___x_4829_ = v___x_4826_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4831_; 
v_reuseFailAlloc_4831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4831_, 0, v_a_4824_);
v___x_4829_ = v_reuseFailAlloc_4831_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
lean_object* v___x_4830_; 
v___x_4830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4830_, 0, v___x_4829_);
return v___x_4830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPurePromise___redArg___boxed(lean_object* v_task_4833_, lean_object* v_error_4834_, lean_object* v_a_4835_){
_start:
{
lean_object* v_res_4836_; 
v_res_4836_ = l_Std_Async_Async_ofPurePromise___redArg(v_task_4833_, v_error_4834_);
return v_res_4836_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPurePromise(lean_object* v_00_u03b1_4837_, lean_object* v_task_4838_, lean_object* v_error_4839_){
_start:
{
lean_object* v___x_4841_; 
v___x_4841_ = lean_apply_1(v_task_4838_, lean_box(0));
if (lean_obj_tag(v___x_4841_) == 0)
{
lean_object* v_a_4842_; lean_object* v___x_4844_; uint8_t v_isShared_4845_; uint8_t v_isSharedCheck_4854_; 
v_a_4842_ = lean_ctor_get(v___x_4841_, 0);
v_isSharedCheck_4854_ = !lean_is_exclusive(v___x_4841_);
if (v_isSharedCheck_4854_ == 0)
{
v___x_4844_ = v___x_4841_;
v_isShared_4845_ = v_isSharedCheck_4854_;
goto v_resetjp_4843_;
}
else
{
lean_inc(v_a_4842_);
lean_dec(v___x_4841_);
v___x_4844_ = lean_box(0);
v_isShared_4845_ = v_isSharedCheck_4854_;
goto v_resetjp_4843_;
}
v_resetjp_4843_:
{
lean_object* v___f_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; uint8_t v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4852_; 
v___f_4846_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPurePromise___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4846_, 0, v_error_4839_);
v___x_4847_ = lean_io_promise_result_opt(v_a_4842_);
lean_dec(v_a_4842_);
v___x_4848_ = lean_unsigned_to_nat(0u);
v___x_4849_ = 0;
v___x_4850_ = lean_task_map(v___f_4846_, v___x_4847_, v___x_4848_, v___x_4849_);
if (v_isShared_4845_ == 0)
{
lean_ctor_set_tag(v___x_4844_, 1);
lean_ctor_set(v___x_4844_, 0, v___x_4850_);
v___x_4852_ = v___x_4844_;
goto v_reusejp_4851_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v___x_4850_);
v___x_4852_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4851_;
}
v_reusejp_4851_:
{
return v___x_4852_;
}
}
}
else
{
lean_object* v_a_4855_; lean_object* v___x_4857_; uint8_t v_isShared_4858_; uint8_t v_isSharedCheck_4863_; 
lean_dec_ref(v_error_4839_);
v_a_4855_ = lean_ctor_get(v___x_4841_, 0);
v_isSharedCheck_4863_ = !lean_is_exclusive(v___x_4841_);
if (v_isSharedCheck_4863_ == 0)
{
v___x_4857_ = v___x_4841_;
v_isShared_4858_ = v_isSharedCheck_4863_;
goto v_resetjp_4856_;
}
else
{
lean_inc(v_a_4855_);
lean_dec(v___x_4841_);
v___x_4857_ = lean_box(0);
v_isShared_4858_ = v_isSharedCheck_4863_;
goto v_resetjp_4856_;
}
v_resetjp_4856_:
{
lean_object* v___x_4860_; 
if (v_isShared_4858_ == 0)
{
lean_ctor_set_tag(v___x_4857_, 0);
v___x_4860_ = v___x_4857_;
goto v_reusejp_4859_;
}
else
{
lean_object* v_reuseFailAlloc_4862_; 
v_reuseFailAlloc_4862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4862_, 0, v_a_4855_);
v___x_4860_ = v_reuseFailAlloc_4862_;
goto v_reusejp_4859_;
}
v_reusejp_4859_:
{
lean_object* v___x_4861_; 
v___x_4861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4861_, 0, v___x_4860_);
return v___x_4861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPurePromise___boxed(lean_object* v_00_u03b1_4864_, lean_object* v_task_4865_, lean_object* v_error_4866_, lean_object* v_a_4867_){
_start:
{
lean_object* v_res_4868_; 
v_res_4868_ = l_Std_Async_Async_ofPurePromise(v_00_u03b1_4864_, v_task_4865_, v_error_4866_);
return v_res_4868_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___redArg(lean_object* v_t_4870_){
_start:
{
lean_object* v___x_4872_; 
v___x_4872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4872_, 0, v_t_4870_);
return v___x_4872_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___redArg___boxed(lean_object* v_t_4873_, lean_object* v_a_4874_){
_start:
{
lean_object* v_res_4875_; 
v_res_4875_ = l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___redArg(v_t_4873_);
return v_res_4875_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1(lean_object* v_00_u03b1_4876_, lean_object* v_t_4877_){
_start:
{
lean_object* v___x_4879_; 
v___x_4879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4879_, 0, v_t_4877_);
return v___x_4879_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___boxed(lean_object* v_00_u03b1_4880_, lean_object* v_t_4881_, lean_object* v_a_4882_){
_start:
{
lean_object* v_res_4883_; 
v_res_4883_ = l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1(v_00_u03b1_4880_, v_t_4881_);
return v_res_4883_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitPromise___aux__1___redArg(lean_object* v_t_4886_){
_start:
{
lean_object* v___f_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; uint8_t v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; 
v___f_4888_ = ((lean_object*)(l_Std_Async_Async_ofIOTask___redArg___closed__0));
v___x_4889_ = l_IO_Promise_result_x21___redArg(v_t_4886_);
v___x_4890_ = lean_unsigned_to_nat(0u);
v___x_4891_ = 0;
v___x_4892_ = lean_task_map(v___f_4888_, v___x_4889_, v___x_4890_, v___x_4891_);
v___x_4893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4893_, 0, v___x_4892_);
return v___x_4893_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitPromise___aux__1___redArg___boxed(lean_object* v_t_4894_, lean_object* v_a_4895_){
_start:
{
lean_object* v_res_4896_; 
v_res_4896_ = l_Std_Async_Async_instMonadAwaitPromise___aux__1___redArg(v_t_4894_);
lean_dec(v_t_4894_);
return v_res_4896_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitPromise___aux__1(lean_object* v_00_u03b1_4897_, lean_object* v_t_4898_){
_start:
{
lean_object* v___f_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; uint8_t v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; 
v___f_4900_ = ((lean_object*)(l_Std_Async_Async_ofIOTask___redArg___closed__0));
v___x_4901_ = l_IO_Promise_result_x21___redArg(v_t_4898_);
v___x_4902_ = lean_unsigned_to_nat(0u);
v___x_4903_ = 0;
v___x_4904_ = lean_task_map(v___f_4900_, v___x_4901_, v___x_4902_, v___x_4903_);
v___x_4905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4905_, 0, v___x_4904_);
return v___x_4905_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitPromise___aux__1___boxed(lean_object* v_00_u03b1_4906_, lean_object* v_t_4907_, lean_object* v_a_4908_){
_start:
{
lean_object* v_res_4909_; 
v_res_4909_ = l_Std_Async_Async_instMonadAwaitPromise___aux__1(v_00_u03b1_4906_, v_t_4907_);
lean_dec(v_t_4907_);
return v_res_4909_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__1(lean_object* v_a_4912_, lean_object* v_x_4913_){
_start:
{
if (lean_obj_tag(v_x_4913_) == 0)
{
lean_object* v_a_4915_; lean_object* v___x_4917_; uint8_t v_isShared_4918_; uint8_t v_isSharedCheck_4923_; 
lean_dec(v_a_4912_);
v_a_4915_ = lean_ctor_get(v_x_4913_, 0);
v_isSharedCheck_4923_ = !lean_is_exclusive(v_x_4913_);
if (v_isSharedCheck_4923_ == 0)
{
v___x_4917_ = v_x_4913_;
v_isShared_4918_ = v_isSharedCheck_4923_;
goto v_resetjp_4916_;
}
else
{
lean_inc(v_a_4915_);
lean_dec(v_x_4913_);
v___x_4917_ = lean_box(0);
v_isShared_4918_ = v_isSharedCheck_4923_;
goto v_resetjp_4916_;
}
v_resetjp_4916_:
{
lean_object* v___x_4920_; 
if (v_isShared_4918_ == 0)
{
v___x_4920_ = v___x_4917_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_a_4915_);
v___x_4920_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
lean_object* v___x_4921_; 
v___x_4921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4921_, 0, v___x_4920_);
return v___x_4921_;
}
}
}
else
{
lean_object* v_a_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4933_; 
v_a_4924_ = lean_ctor_get(v_x_4913_, 0);
v_isSharedCheck_4933_ = !lean_is_exclusive(v_x_4913_);
if (v_isSharedCheck_4933_ == 0)
{
v___x_4926_ = v_x_4913_;
v_isShared_4927_ = v_isSharedCheck_4933_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_a_4924_);
lean_dec(v_x_4913_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4933_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
lean_object* v___x_4928_; lean_object* v___x_4930_; 
v___x_4928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4928_, 0, v_a_4912_);
lean_ctor_set(v___x_4928_, 1, v_a_4924_);
if (v_isShared_4927_ == 0)
{
lean_ctor_set(v___x_4926_, 0, v___x_4928_);
v___x_4930_ = v___x_4926_;
goto v_reusejp_4929_;
}
else
{
lean_object* v_reuseFailAlloc_4932_; 
v_reuseFailAlloc_4932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4932_, 0, v___x_4928_);
v___x_4930_ = v_reuseFailAlloc_4932_;
goto v_reusejp_4929_;
}
v_reusejp_4929_:
{
lean_object* v___x_4931_; 
v___x_4931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4931_, 0, v___x_4930_);
return v___x_4931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__1___boxed(lean_object* v_a_4934_, lean_object* v_x_4935_, lean_object* v___y_4936_){
_start:
{
lean_object* v_res_4937_; 
v_res_4937_ = l_Std_Async_Async_concurrently___redArg___lam__1(v_a_4934_, v_x_4935_);
return v_res_4937_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__0(lean_object* v_a_4938_, lean_object* v_x_4939_){
_start:
{
if (lean_obj_tag(v_x_4939_) == 0)
{
lean_object* v_a_4941_; lean_object* v___x_4943_; uint8_t v_isShared_4944_; uint8_t v_isSharedCheck_4949_; 
lean_dec_ref(v_a_4938_);
v_a_4941_ = lean_ctor_get(v_x_4939_, 0);
v_isSharedCheck_4949_ = !lean_is_exclusive(v_x_4939_);
if (v_isSharedCheck_4949_ == 0)
{
v___x_4943_ = v_x_4939_;
v_isShared_4944_ = v_isSharedCheck_4949_;
goto v_resetjp_4942_;
}
else
{
lean_inc(v_a_4941_);
lean_dec(v_x_4939_);
v___x_4943_ = lean_box(0);
v_isShared_4944_ = v_isSharedCheck_4949_;
goto v_resetjp_4942_;
}
v_resetjp_4942_:
{
lean_object* v___x_4946_; 
if (v_isShared_4944_ == 0)
{
v___x_4946_ = v___x_4943_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4948_; 
v_reuseFailAlloc_4948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4948_, 0, v_a_4941_);
v___x_4946_ = v_reuseFailAlloc_4948_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
lean_object* v___x_4947_; 
v___x_4947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4947_, 0, v___x_4946_);
return v___x_4947_;
}
}
}
else
{
lean_object* v_a_4950_; lean_object* v___f_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; uint8_t v___x_4954_; lean_object* v___x_4955_; 
v_a_4950_ = lean_ctor_get(v_x_4939_, 0);
lean_inc(v_a_4950_);
lean_dec_ref(v_x_4939_);
v___f_4951_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrently___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4951_, 0, v_a_4950_);
v___x_4952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4952_, 0, v_a_4938_);
v___x_4953_ = lean_unsigned_to_nat(0u);
v___x_4954_ = 0;
v___x_4955_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4953_, v___x_4954_, v___x_4952_, v___f_4951_);
return v___x_4955_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__0___boxed(lean_object* v_a_4956_, lean_object* v_x_4957_, lean_object* v___y_4958_){
_start:
{
lean_object* v_res_4959_; 
v_res_4959_ = l_Std_Async_Async_concurrently___redArg___lam__0(v_a_4956_, v_x_4957_);
return v_res_4959_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__2(lean_object* v_a_4960_, lean_object* v_x_4961_){
_start:
{
if (lean_obj_tag(v_x_4961_) == 0)
{
lean_object* v_a_4963_; lean_object* v___x_4965_; uint8_t v_isShared_4966_; uint8_t v_isSharedCheck_4971_; 
lean_dec_ref(v_a_4960_);
v_a_4963_ = lean_ctor_get(v_x_4961_, 0);
v_isSharedCheck_4971_ = !lean_is_exclusive(v_x_4961_);
if (v_isSharedCheck_4971_ == 0)
{
v___x_4965_ = v_x_4961_;
v_isShared_4966_ = v_isSharedCheck_4971_;
goto v_resetjp_4964_;
}
else
{
lean_inc(v_a_4963_);
lean_dec(v_x_4961_);
v___x_4965_ = lean_box(0);
v_isShared_4966_ = v_isSharedCheck_4971_;
goto v_resetjp_4964_;
}
v_resetjp_4964_:
{
lean_object* v___x_4968_; 
if (v_isShared_4966_ == 0)
{
v___x_4968_ = v___x_4965_;
goto v_reusejp_4967_;
}
else
{
lean_object* v_reuseFailAlloc_4970_; 
v_reuseFailAlloc_4970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4970_, 0, v_a_4963_);
v___x_4968_ = v_reuseFailAlloc_4970_;
goto v_reusejp_4967_;
}
v_reusejp_4967_:
{
lean_object* v___x_4969_; 
v___x_4969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4969_, 0, v___x_4968_);
return v___x_4969_;
}
}
}
else
{
lean_object* v_a_4972_; lean_object* v___f_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; uint8_t v___x_4976_; lean_object* v___x_4977_; 
v_a_4972_ = lean_ctor_get(v_x_4961_, 0);
lean_inc(v_a_4972_);
lean_dec_ref(v_x_4961_);
v___f_4973_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrently___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4973_, 0, v_a_4972_);
v___x_4974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4974_, 0, v_a_4960_);
v___x_4975_ = lean_unsigned_to_nat(0u);
v___x_4976_ = 0;
v___x_4977_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4975_, v___x_4976_, v___x_4974_, v___f_4973_);
return v___x_4977_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__2___boxed(lean_object* v_a_4978_, lean_object* v_x_4979_, lean_object* v___y_4980_){
_start:
{
lean_object* v_res_4981_; 
v_res_4981_ = l_Std_Async_Async_concurrently___redArg___lam__2(v_a_4978_, v_x_4979_);
return v_res_4981_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__3(lean_object* v_y_4982_, lean_object* v_prio_4983_, lean_object* v___f_4984_, lean_object* v_x_4985_){
_start:
{
if (lean_obj_tag(v_x_4985_) == 0)
{
lean_object* v_a_4987_; lean_object* v___x_4989_; uint8_t v_isShared_4990_; uint8_t v_isSharedCheck_4995_; 
lean_dec_ref(v___f_4984_);
lean_dec(v_prio_4983_);
lean_dec_ref(v_y_4982_);
v_a_4987_ = lean_ctor_get(v_x_4985_, 0);
v_isSharedCheck_4995_ = !lean_is_exclusive(v_x_4985_);
if (v_isSharedCheck_4995_ == 0)
{
v___x_4989_ = v_x_4985_;
v_isShared_4990_ = v_isSharedCheck_4995_;
goto v_resetjp_4988_;
}
else
{
lean_inc(v_a_4987_);
lean_dec(v_x_4985_);
v___x_4989_ = lean_box(0);
v_isShared_4990_ = v_isSharedCheck_4995_;
goto v_resetjp_4988_;
}
v_resetjp_4988_:
{
lean_object* v___x_4992_; 
if (v_isShared_4990_ == 0)
{
v___x_4992_ = v___x_4989_;
goto v_reusejp_4991_;
}
else
{
lean_object* v_reuseFailAlloc_4994_; 
v_reuseFailAlloc_4994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4994_, 0, v_a_4987_);
v___x_4992_ = v_reuseFailAlloc_4994_;
goto v_reusejp_4991_;
}
v_reusejp_4991_:
{
lean_object* v___x_4993_; 
v___x_4993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4993_, 0, v___x_4992_);
return v___x_4993_;
}
}
}
else
{
lean_object* v_a_4996_; lean_object* v___x_4998_; uint8_t v_isShared_4999_; uint8_t v_isSharedCheck_5012_; 
v_a_4996_ = lean_ctor_get(v_x_4985_, 0);
v_isSharedCheck_5012_ = !lean_is_exclusive(v_x_4985_);
if (v_isSharedCheck_5012_ == 0)
{
v___x_4998_ = v_x_4985_;
v_isShared_4999_ = v_isSharedCheck_5012_;
goto v_resetjp_4997_;
}
else
{
lean_inc(v_a_4996_);
lean_dec(v_x_4985_);
v___x_4998_ = lean_box(0);
v_isShared_4999_ = v_isSharedCheck_5012_;
goto v_resetjp_4997_;
}
v_resetjp_4997_:
{
lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___f_5002_; lean_object* v___x_5003_; uint8_t v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5007_; 
v___x_5000_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5000_, 0, lean_box(0));
lean_closure_set(v___x_5000_, 1, v_y_4982_);
v___x_5001_ = lean_io_as_task(v___x_5000_, v_prio_4983_);
v___f_5002_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrently___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_5002_, 0, v_a_4996_);
v___x_5003_ = lean_unsigned_to_nat(0u);
v___x_5004_ = 1;
v___x_5005_ = lean_task_bind(v___x_5001_, v___f_4984_, v___x_5003_, v___x_5004_);
if (v_isShared_4999_ == 0)
{
lean_ctor_set(v___x_4998_, 0, v___x_5005_);
v___x_5007_ = v___x_4998_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5011_; 
v_reuseFailAlloc_5011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5011_, 0, v___x_5005_);
v___x_5007_ = v_reuseFailAlloc_5011_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
lean_object* v___x_5008_; uint8_t v___x_5009_; lean_object* v___x_5010_; 
v___x_5008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5008_, 0, v___x_5007_);
v___x_5009_ = 0;
v___x_5010_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5003_, v___x_5009_, v___x_5008_, v___f_5002_);
return v___x_5010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__3___boxed(lean_object* v_y_5013_, lean_object* v_prio_5014_, lean_object* v___f_5015_, lean_object* v_x_5016_, lean_object* v___y_5017_){
_start:
{
lean_object* v_res_5018_; 
v_res_5018_ = l_Std_Async_Async_concurrently___redArg___lam__3(v_y_5013_, v_prio_5014_, v___f_5015_, v_x_5016_);
return v_res_5018_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg(lean_object* v_x_5019_, lean_object* v_y_5020_, lean_object* v_prio_5021_){
_start:
{
lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___f_5025_; lean_object* v___f_5026_; lean_object* v___x_5027_; uint8_t v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; uint8_t v___x_5032_; lean_object* v___x_5033_; 
v___x_5023_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5023_, 0, lean_box(0));
lean_closure_set(v___x_5023_, 1, v_x_5019_);
lean_inc(v_prio_5021_);
v___x_5024_ = lean_io_as_task(v___x_5023_, v_prio_5021_);
v___f_5025_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___f_5026_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrently___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_5026_, 0, v_y_5020_);
lean_closure_set(v___f_5026_, 1, v_prio_5021_);
lean_closure_set(v___f_5026_, 2, v___f_5025_);
v___x_5027_ = lean_unsigned_to_nat(0u);
v___x_5028_ = 1;
v___x_5029_ = lean_task_bind(v___x_5024_, v___f_5025_, v___x_5027_, v___x_5028_);
v___x_5030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5030_, 0, v___x_5029_);
v___x_5031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5031_, 0, v___x_5030_);
v___x_5032_ = 0;
v___x_5033_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5027_, v___x_5032_, v___x_5031_, v___f_5026_);
return v___x_5033_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___boxed(lean_object* v_x_5034_, lean_object* v_y_5035_, lean_object* v_prio_5036_, lean_object* v_a_5037_){
_start:
{
lean_object* v_res_5038_; 
v_res_5038_ = l_Std_Async_Async_concurrently___redArg(v_x_5034_, v_y_5035_, v_prio_5036_);
return v_res_5038_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently(lean_object* v_00_u03b1_5039_, lean_object* v_00_u03b2_5040_, lean_object* v_x_5041_, lean_object* v_y_5042_, lean_object* v_prio_5043_){
_start:
{
lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___f_5047_; lean_object* v___f_5048_; lean_object* v___x_5049_; uint8_t v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; uint8_t v___x_5054_; lean_object* v___x_5055_; 
v___x_5045_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5045_, 0, lean_box(0));
lean_closure_set(v___x_5045_, 1, v_x_5041_);
lean_inc(v_prio_5043_);
v___x_5046_ = lean_io_as_task(v___x_5045_, v_prio_5043_);
v___f_5047_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___f_5048_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrently___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_5048_, 0, v_y_5042_);
lean_closure_set(v___f_5048_, 1, v_prio_5043_);
lean_closure_set(v___f_5048_, 2, v___f_5047_);
v___x_5049_ = lean_unsigned_to_nat(0u);
v___x_5050_ = 1;
v___x_5051_ = lean_task_bind(v___x_5046_, v___f_5047_, v___x_5049_, v___x_5050_);
v___x_5052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5052_, 0, v___x_5051_);
v___x_5053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5053_, 0, v___x_5052_);
v___x_5054_ = 0;
v___x_5055_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5049_, v___x_5054_, v___x_5053_, v___f_5048_);
return v___x_5055_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___boxed(lean_object* v_00_u03b1_5056_, lean_object* v_00_u03b2_5057_, lean_object* v_x_5058_, lean_object* v_y_5059_, lean_object* v_prio_5060_, lean_object* v_a_5061_){
_start:
{
lean_object* v_res_5062_; 
v_res_5062_ = l_Std_Async_Async_concurrently(v_00_u03b1_5056_, v_00_u03b2_5057_, v_x_5058_, v_y_5059_, v_prio_5060_);
return v_res_5062_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__1(lean_object* v_x_5063_){
_start:
{
if (lean_obj_tag(v_x_5063_) == 0)
{
lean_object* v_a_5065_; lean_object* v___x_5067_; uint8_t v_isShared_5068_; uint8_t v_isSharedCheck_5073_; 
v_a_5065_ = lean_ctor_get(v_x_5063_, 0);
v_isSharedCheck_5073_ = !lean_is_exclusive(v_x_5063_);
if (v_isSharedCheck_5073_ == 0)
{
v___x_5067_ = v_x_5063_;
v_isShared_5068_ = v_isSharedCheck_5073_;
goto v_resetjp_5066_;
}
else
{
lean_inc(v_a_5065_);
lean_dec(v_x_5063_);
v___x_5067_ = lean_box(0);
v_isShared_5068_ = v_isSharedCheck_5073_;
goto v_resetjp_5066_;
}
v_resetjp_5066_:
{
lean_object* v___x_5070_; 
if (v_isShared_5068_ == 0)
{
v___x_5070_ = v___x_5067_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5072_; 
v_reuseFailAlloc_5072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5072_, 0, v_a_5065_);
v___x_5070_ = v_reuseFailAlloc_5072_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
lean_object* v___x_5071_; 
v___x_5071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5071_, 0, v___x_5070_);
return v___x_5071_;
}
}
}
else
{
lean_object* v_a_5074_; lean_object* v___x_5075_; 
v_a_5074_ = lean_ctor_get(v_x_5063_, 0);
lean_inc(v_a_5074_);
lean_dec_ref(v_x_5063_);
v___x_5075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5075_, 0, v_a_5074_);
return v___x_5075_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__1___boxed(lean_object* v_x_5076_, lean_object* v___y_5077_){
_start:
{
lean_object* v_res_5078_; 
v_res_5078_ = l_Std_Async_Async_race___redArg___lam__1(v_x_5076_);
return v_res_5078_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__0(lean_object* v_a_5079_){
_start:
{
lean_object* v___x_5080_; 
v___x_5080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5080_, 0, v_a_5079_);
return v___x_5080_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__3(lean_object* v_a_5081_, lean_object* v_value_5082_){
_start:
{
lean_object* v___x_5084_; 
v___x_5084_ = lean_io_promise_resolve(v_value_5082_, v_a_5081_);
return v___x_5084_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__3___boxed(lean_object* v_a_5085_, lean_object* v_value_5086_, lean_object* v___y_5087_){
_start:
{
lean_object* v_res_5088_; 
v_res_5088_ = l_Std_Async_Async_race___redArg___lam__3(v_a_5085_, v_value_5086_);
lean_dec(v_a_5085_);
return v_res_5088_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__2(lean_object* v_a_5089_, lean_object* v___f_5090_, lean_object* v___f_5091_, lean_object* v_x_5092_){
_start:
{
if (lean_obj_tag(v_x_5092_) == 0)
{
lean_object* v_a_5094_; lean_object* v___x_5096_; uint8_t v_isShared_5097_; uint8_t v_isSharedCheck_5102_; 
lean_dec_ref(v___f_5091_);
lean_dec_ref(v___f_5090_);
v_a_5094_ = lean_ctor_get(v_x_5092_, 0);
v_isSharedCheck_5102_ = !lean_is_exclusive(v_x_5092_);
if (v_isSharedCheck_5102_ == 0)
{
v___x_5096_ = v_x_5092_;
v_isShared_5097_ = v_isSharedCheck_5102_;
goto v_resetjp_5095_;
}
else
{
lean_inc(v_a_5094_);
lean_dec(v_x_5092_);
v___x_5096_ = lean_box(0);
v_isShared_5097_ = v_isSharedCheck_5102_;
goto v_resetjp_5095_;
}
v_resetjp_5095_:
{
lean_object* v___x_5099_; 
if (v_isShared_5097_ == 0)
{
v___x_5099_ = v___x_5096_;
goto v_reusejp_5098_;
}
else
{
lean_object* v_reuseFailAlloc_5101_; 
v_reuseFailAlloc_5101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5101_, 0, v_a_5094_);
v___x_5099_ = v_reuseFailAlloc_5101_;
goto v_reusejp_5098_;
}
v_reusejp_5098_:
{
lean_object* v___x_5100_; 
v___x_5100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5100_, 0, v___x_5099_);
return v___x_5100_;
}
}
}
else
{
lean_object* v___x_5103_; lean_object* v___x_5104_; uint8_t v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; 
lean_dec_ref(v_x_5092_);
v___x_5103_ = l_IO_Promise_result_x21___redArg(v_a_5089_);
v___x_5104_ = lean_unsigned_to_nat(0u);
v___x_5105_ = 0;
v___x_5106_ = lean_task_map(v___f_5090_, v___x_5103_, v___x_5104_, v___x_5105_);
v___x_5107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5107_, 0, v___x_5106_);
v___x_5108_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5104_, v___x_5105_, v___x_5107_, v___f_5091_);
return v___x_5108_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__2___boxed(lean_object* v_a_5109_, lean_object* v___f_5110_, lean_object* v___f_5111_, lean_object* v_x_5112_, lean_object* v___y_5113_){
_start:
{
lean_object* v_res_5114_; 
v_res_5114_ = l_Std_Async_Async_race___redArg___lam__2(v_a_5109_, v___f_5110_, v___f_5111_, v_x_5112_);
lean_dec(v_a_5109_);
return v_res_5114_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__4(lean_object* v_a_5115_, lean_object* v___x_5116_, lean_object* v___x_5117_, uint8_t v___x_5118_, lean_object* v___f_5119_, lean_object* v_x_5120_){
_start:
{
if (lean_obj_tag(v_x_5120_) == 0)
{
lean_object* v_a_5122_; lean_object* v___x_5124_; uint8_t v_isShared_5125_; uint8_t v_isSharedCheck_5130_; 
lean_dec_ref(v___f_5119_);
lean_dec(v___x_5117_);
lean_dec_ref(v___x_5116_);
lean_dec_ref(v_a_5115_);
v_a_5122_ = lean_ctor_get(v_x_5120_, 0);
v_isSharedCheck_5130_ = !lean_is_exclusive(v_x_5120_);
if (v_isSharedCheck_5130_ == 0)
{
v___x_5124_ = v_x_5120_;
v_isShared_5125_ = v_isSharedCheck_5130_;
goto v_resetjp_5123_;
}
else
{
lean_inc(v_a_5122_);
lean_dec(v_x_5120_);
v___x_5124_ = lean_box(0);
v_isShared_5125_ = v_isSharedCheck_5130_;
goto v_resetjp_5123_;
}
v_resetjp_5123_:
{
lean_object* v___x_5127_; 
if (v_isShared_5125_ == 0)
{
v___x_5127_ = v___x_5124_;
goto v_reusejp_5126_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v_a_5122_);
v___x_5127_ = v_reuseFailAlloc_5129_;
goto v_reusejp_5126_;
}
v_reusejp_5126_:
{
lean_object* v___x_5128_; 
v___x_5128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5128_, 0, v___x_5127_);
return v___x_5128_;
}
}
}
else
{
lean_object* v___x_5132_; uint8_t v_isShared_5133_; uint8_t v_isSharedCheck_5140_; 
v_isSharedCheck_5140_ = !lean_is_exclusive(v_x_5120_);
if (v_isSharedCheck_5140_ == 0)
{
lean_object* v_unused_5141_; 
v_unused_5141_ = lean_ctor_get(v_x_5120_, 0);
lean_dec(v_unused_5141_);
v___x_5132_ = v_x_5120_;
v_isShared_5133_ = v_isSharedCheck_5140_;
goto v_resetjp_5131_;
}
else
{
lean_dec(v_x_5120_);
v___x_5132_ = lean_box(0);
v_isShared_5133_ = v_isSharedCheck_5140_;
goto v_resetjp_5131_;
}
v_resetjp_5131_:
{
lean_object* v___x_5134_; lean_object* v___x_5136_; 
lean_inc(v___x_5117_);
v___x_5134_ = l_BaseIO_chainTask___redArg(v_a_5115_, v___x_5116_, v___x_5117_, v___x_5118_);
if (v_isShared_5133_ == 0)
{
lean_ctor_set(v___x_5132_, 0, v___x_5134_);
v___x_5136_ = v___x_5132_;
goto v_reusejp_5135_;
}
else
{
lean_object* v_reuseFailAlloc_5139_; 
v_reuseFailAlloc_5139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5139_, 0, v___x_5134_);
v___x_5136_ = v_reuseFailAlloc_5139_;
goto v_reusejp_5135_;
}
v_reusejp_5135_:
{
lean_object* v___x_5137_; lean_object* v___x_5138_; 
v___x_5137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5137_, 0, v___x_5136_);
v___x_5138_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5117_, v___x_5118_, v___x_5137_, v___f_5119_);
return v___x_5138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__4___boxed(lean_object* v_a_5142_, lean_object* v___x_5143_, lean_object* v___x_5144_, lean_object* v___x_5145_, lean_object* v___f_5146_, lean_object* v_x_5147_, lean_object* v___y_5148_){
_start:
{
uint8_t v___x_1405__boxed_5149_; lean_object* v_res_5150_; 
v___x_1405__boxed_5149_ = lean_unbox(v___x_5145_);
v_res_5150_ = l_Std_Async_Async_race___redArg___lam__4(v_a_5142_, v___x_5143_, v___x_5144_, v___x_1405__boxed_5149_, v___f_5146_, v_x_5147_);
return v_res_5150_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__5(lean_object* v___f_5151_, lean_object* v___f_5152_, lean_object* v_a_5153_, lean_object* v___f_5154_, lean_object* v_x_5155_){
_start:
{
if (lean_obj_tag(v_x_5155_) == 0)
{
lean_object* v_a_5157_; lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5165_; 
lean_dec_ref(v___f_5154_);
lean_dec_ref(v_a_5153_);
lean_dec_ref(v___f_5152_);
lean_dec(v___f_5151_);
v_a_5157_ = lean_ctor_get(v_x_5155_, 0);
v_isSharedCheck_5165_ = !lean_is_exclusive(v_x_5155_);
if (v_isSharedCheck_5165_ == 0)
{
v___x_5159_ = v_x_5155_;
v_isShared_5160_ = v_isSharedCheck_5165_;
goto v_resetjp_5158_;
}
else
{
lean_inc(v_a_5157_);
lean_dec(v_x_5155_);
v___x_5159_ = lean_box(0);
v_isShared_5160_ = v_isSharedCheck_5165_;
goto v_resetjp_5158_;
}
v_resetjp_5158_:
{
lean_object* v___x_5162_; 
if (v_isShared_5160_ == 0)
{
v___x_5162_ = v___x_5159_;
goto v_reusejp_5161_;
}
else
{
lean_object* v_reuseFailAlloc_5164_; 
v_reuseFailAlloc_5164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5164_, 0, v_a_5157_);
v___x_5162_ = v_reuseFailAlloc_5164_;
goto v_reusejp_5161_;
}
v_reusejp_5161_:
{
lean_object* v___x_5163_; 
v___x_5163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5163_, 0, v___x_5162_);
return v___x_5163_;
}
}
}
else
{
lean_object* v_a_5166_; lean_object* v___x_5168_; uint8_t v_isShared_5169_; uint8_t v_isSharedCheck_5182_; 
v_a_5166_ = lean_ctor_get(v_x_5155_, 0);
v_isSharedCheck_5182_ = !lean_is_exclusive(v_x_5155_);
if (v_isSharedCheck_5182_ == 0)
{
v___x_5168_ = v_x_5155_;
v_isShared_5169_ = v_isSharedCheck_5182_;
goto v_resetjp_5167_;
}
else
{
lean_inc(v_a_5166_);
lean_dec(v_x_5155_);
v___x_5168_ = lean_box(0);
v_isShared_5169_ = v_isSharedCheck_5182_;
goto v_resetjp_5167_;
}
v_resetjp_5167_:
{
lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; uint8_t v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___f_5176_; lean_object* v___x_5178_; 
v___x_5170_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_5170_, 0, lean_box(0));
lean_closure_set(v___x_5170_, 1, lean_box(0));
lean_closure_set(v___x_5170_, 2, v___f_5151_);
lean_closure_set(v___x_5170_, 3, lean_box(0));
v___x_5171_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_5171_, 0, lean_box(0));
lean_closure_set(v___x_5171_, 1, lean_box(0));
lean_closure_set(v___x_5171_, 2, lean_box(0));
lean_closure_set(v___x_5171_, 3, v___x_5170_);
lean_closure_set(v___x_5171_, 4, v___f_5152_);
v___x_5172_ = lean_unsigned_to_nat(0u);
v___x_5173_ = 0;
lean_inc_ref(v___x_5171_);
v___x_5174_ = l_BaseIO_chainTask___redArg(v_a_5153_, v___x_5171_, v___x_5172_, v___x_5173_);
v___x_5175_ = lean_box(v___x_5173_);
v___f_5176_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__4___boxed), 7, 5);
lean_closure_set(v___f_5176_, 0, v_a_5166_);
lean_closure_set(v___f_5176_, 1, v___x_5171_);
lean_closure_set(v___f_5176_, 2, v___x_5172_);
lean_closure_set(v___f_5176_, 3, v___x_5175_);
lean_closure_set(v___f_5176_, 4, v___f_5154_);
if (v_isShared_5169_ == 0)
{
lean_ctor_set(v___x_5168_, 0, v___x_5174_);
v___x_5178_ = v___x_5168_;
goto v_reusejp_5177_;
}
else
{
lean_object* v_reuseFailAlloc_5181_; 
v_reuseFailAlloc_5181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5181_, 0, v___x_5174_);
v___x_5178_ = v_reuseFailAlloc_5181_;
goto v_reusejp_5177_;
}
v_reusejp_5177_:
{
lean_object* v___x_5179_; lean_object* v___x_5180_; 
v___x_5179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5179_, 0, v___x_5178_);
v___x_5180_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5172_, v___x_5173_, v___x_5179_, v___f_5176_);
return v___x_5180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__5___boxed(lean_object* v___f_5183_, lean_object* v___f_5184_, lean_object* v_a_5185_, lean_object* v___f_5186_, lean_object* v_x_5187_, lean_object* v___y_5188_){
_start:
{
lean_object* v_res_5189_; 
v_res_5189_ = l_Std_Async_Async_race___redArg___lam__5(v___f_5183_, v___f_5184_, v_a_5185_, v___f_5186_, v_x_5187_);
return v_res_5189_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__6(lean_object* v_y_5190_, lean_object* v_prio_5191_, lean_object* v___f_5192_, lean_object* v___f_5193_, lean_object* v___f_5194_, lean_object* v___f_5195_, lean_object* v_x_5196_){
_start:
{
if (lean_obj_tag(v_x_5196_) == 0)
{
lean_object* v_a_5198_; lean_object* v___x_5200_; uint8_t v_isShared_5201_; uint8_t v_isSharedCheck_5206_; 
lean_dec_ref(v___f_5195_);
lean_dec_ref(v___f_5194_);
lean_dec_ref(v___f_5193_);
lean_dec(v___f_5192_);
lean_dec(v_prio_5191_);
lean_dec_ref(v_y_5190_);
v_a_5198_ = lean_ctor_get(v_x_5196_, 0);
v_isSharedCheck_5206_ = !lean_is_exclusive(v_x_5196_);
if (v_isSharedCheck_5206_ == 0)
{
v___x_5200_ = v_x_5196_;
v_isShared_5201_ = v_isSharedCheck_5206_;
goto v_resetjp_5199_;
}
else
{
lean_inc(v_a_5198_);
lean_dec(v_x_5196_);
v___x_5200_ = lean_box(0);
v_isShared_5201_ = v_isSharedCheck_5206_;
goto v_resetjp_5199_;
}
v_resetjp_5199_:
{
lean_object* v___x_5203_; 
if (v_isShared_5201_ == 0)
{
v___x_5203_ = v___x_5200_;
goto v_reusejp_5202_;
}
else
{
lean_object* v_reuseFailAlloc_5205_; 
v_reuseFailAlloc_5205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5205_, 0, v_a_5198_);
v___x_5203_ = v_reuseFailAlloc_5205_;
goto v_reusejp_5202_;
}
v_reusejp_5202_:
{
lean_object* v___x_5204_; 
v___x_5204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5204_, 0, v___x_5203_);
return v___x_5204_;
}
}
}
else
{
lean_object* v_a_5207_; lean_object* v___x_5209_; uint8_t v_isShared_5210_; uint8_t v_isSharedCheck_5223_; 
v_a_5207_ = lean_ctor_get(v_x_5196_, 0);
v_isSharedCheck_5223_ = !lean_is_exclusive(v_x_5196_);
if (v_isSharedCheck_5223_ == 0)
{
v___x_5209_ = v_x_5196_;
v_isShared_5210_ = v_isSharedCheck_5223_;
goto v_resetjp_5208_;
}
else
{
lean_inc(v_a_5207_);
lean_dec(v_x_5196_);
v___x_5209_ = lean_box(0);
v_isShared_5210_ = v_isSharedCheck_5223_;
goto v_resetjp_5208_;
}
v_resetjp_5208_:
{
lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___f_5213_; lean_object* v___x_5214_; uint8_t v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5218_; 
v___x_5211_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5211_, 0, lean_box(0));
lean_closure_set(v___x_5211_, 1, v_y_5190_);
v___x_5212_ = lean_io_as_task(v___x_5211_, v_prio_5191_);
v___f_5213_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__5___boxed), 6, 4);
lean_closure_set(v___f_5213_, 0, v___f_5192_);
lean_closure_set(v___f_5213_, 1, v___f_5193_);
lean_closure_set(v___f_5213_, 2, v_a_5207_);
lean_closure_set(v___f_5213_, 3, v___f_5194_);
v___x_5214_ = lean_unsigned_to_nat(0u);
v___x_5215_ = 1;
v___x_5216_ = lean_task_bind(v___x_5212_, v___f_5195_, v___x_5214_, v___x_5215_);
if (v_isShared_5210_ == 0)
{
lean_ctor_set(v___x_5209_, 0, v___x_5216_);
v___x_5218_ = v___x_5209_;
goto v_reusejp_5217_;
}
else
{
lean_object* v_reuseFailAlloc_5222_; 
v_reuseFailAlloc_5222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5222_, 0, v___x_5216_);
v___x_5218_ = v_reuseFailAlloc_5222_;
goto v_reusejp_5217_;
}
v_reusejp_5217_:
{
lean_object* v___x_5219_; uint8_t v___x_5220_; lean_object* v___x_5221_; 
v___x_5219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5219_, 0, v___x_5218_);
v___x_5220_ = 0;
v___x_5221_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5214_, v___x_5220_, v___x_5219_, v___f_5213_);
return v___x_5221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__6___boxed(lean_object* v_y_5224_, lean_object* v_prio_5225_, lean_object* v___f_5226_, lean_object* v___f_5227_, lean_object* v___f_5228_, lean_object* v___f_5229_, lean_object* v_x_5230_, lean_object* v___y_5231_){
_start:
{
lean_object* v_res_5232_; 
v_res_5232_ = l_Std_Async_Async_race___redArg___lam__6(v_y_5224_, v_prio_5225_, v___f_5226_, v___f_5227_, v___f_5228_, v___f_5229_, v_x_5230_);
return v_res_5232_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__7(lean_object* v_x_5233_, lean_object* v_prio_5234_, lean_object* v___f_5235_, lean_object* v___f_5236_, lean_object* v_y_5237_, lean_object* v___f_5238_, lean_object* v___f_5239_, lean_object* v___f_5240_, lean_object* v_x_5241_){
_start:
{
if (lean_obj_tag(v_x_5241_) == 0)
{
lean_object* v_a_5243_; lean_object* v___x_5245_; uint8_t v_isShared_5246_; uint8_t v_isSharedCheck_5251_; 
lean_dec_ref(v___f_5240_);
lean_dec_ref(v___f_5239_);
lean_dec(v___f_5238_);
lean_dec_ref(v_y_5237_);
lean_dec_ref(v___f_5236_);
lean_dec_ref(v___f_5235_);
lean_dec(v_prio_5234_);
lean_dec_ref(v_x_5233_);
v_a_5243_ = lean_ctor_get(v_x_5241_, 0);
v_isSharedCheck_5251_ = !lean_is_exclusive(v_x_5241_);
if (v_isSharedCheck_5251_ == 0)
{
v___x_5245_ = v_x_5241_;
v_isShared_5246_ = v_isSharedCheck_5251_;
goto v_resetjp_5244_;
}
else
{
lean_inc(v_a_5243_);
lean_dec(v_x_5241_);
v___x_5245_ = lean_box(0);
v_isShared_5246_ = v_isSharedCheck_5251_;
goto v_resetjp_5244_;
}
v_resetjp_5244_:
{
lean_object* v___x_5248_; 
if (v_isShared_5246_ == 0)
{
v___x_5248_ = v___x_5245_;
goto v_reusejp_5247_;
}
else
{
lean_object* v_reuseFailAlloc_5250_; 
v_reuseFailAlloc_5250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5250_, 0, v_a_5243_);
v___x_5248_ = v_reuseFailAlloc_5250_;
goto v_reusejp_5247_;
}
v_reusejp_5247_:
{
lean_object* v___x_5249_; 
v___x_5249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5249_, 0, v___x_5248_);
return v___x_5249_;
}
}
}
else
{
lean_object* v_a_5252_; lean_object* v___x_5254_; uint8_t v_isShared_5255_; uint8_t v_isSharedCheck_5270_; 
v_a_5252_ = lean_ctor_get(v_x_5241_, 0);
v_isSharedCheck_5270_ = !lean_is_exclusive(v_x_5241_);
if (v_isSharedCheck_5270_ == 0)
{
v___x_5254_ = v_x_5241_;
v_isShared_5255_ = v_isSharedCheck_5270_;
goto v_resetjp_5253_;
}
else
{
lean_inc(v_a_5252_);
lean_dec(v_x_5241_);
v___x_5254_ = lean_box(0);
v_isShared_5255_ = v_isSharedCheck_5270_;
goto v_resetjp_5253_;
}
v_resetjp_5253_:
{
lean_object* v___x_5256_; lean_object* v___x_5257_; lean_object* v___f_5258_; lean_object* v___f_5259_; lean_object* v___f_5260_; lean_object* v___x_5261_; uint8_t v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5265_; 
v___x_5256_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5256_, 0, lean_box(0));
lean_closure_set(v___x_5256_, 1, v_x_5233_);
lean_inc(v_prio_5234_);
v___x_5257_ = lean_io_as_task(v___x_5256_, v_prio_5234_);
lean_inc(v_a_5252_);
v___f_5258_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_5258_, 0, v_a_5252_);
v___f_5259_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_5259_, 0, v_a_5252_);
lean_closure_set(v___f_5259_, 1, v___f_5235_);
lean_closure_set(v___f_5259_, 2, v___f_5236_);
v___f_5260_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__6___boxed), 8, 6);
lean_closure_set(v___f_5260_, 0, v_y_5237_);
lean_closure_set(v___f_5260_, 1, v_prio_5234_);
lean_closure_set(v___f_5260_, 2, v___f_5238_);
lean_closure_set(v___f_5260_, 3, v___f_5258_);
lean_closure_set(v___f_5260_, 4, v___f_5259_);
lean_closure_set(v___f_5260_, 5, v___f_5239_);
v___x_5261_ = lean_unsigned_to_nat(0u);
v___x_5262_ = 1;
v___x_5263_ = lean_task_bind(v___x_5257_, v___f_5240_, v___x_5261_, v___x_5262_);
if (v_isShared_5255_ == 0)
{
lean_ctor_set(v___x_5254_, 0, v___x_5263_);
v___x_5265_ = v___x_5254_;
goto v_reusejp_5264_;
}
else
{
lean_object* v_reuseFailAlloc_5269_; 
v_reuseFailAlloc_5269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5269_, 0, v___x_5263_);
v___x_5265_ = v_reuseFailAlloc_5269_;
goto v_reusejp_5264_;
}
v_reusejp_5264_:
{
lean_object* v___x_5266_; uint8_t v___x_5267_; lean_object* v___x_5268_; 
v___x_5266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5266_, 0, v___x_5265_);
v___x_5267_ = 0;
v___x_5268_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5261_, v___x_5267_, v___x_5266_, v___f_5260_);
return v___x_5268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__7___boxed(lean_object* v_x_5271_, lean_object* v_prio_5272_, lean_object* v___f_5273_, lean_object* v___f_5274_, lean_object* v_y_5275_, lean_object* v___f_5276_, lean_object* v___f_5277_, lean_object* v___f_5278_, lean_object* v_x_5279_, lean_object* v___y_5280_){
_start:
{
lean_object* v_res_5281_; 
v_res_5281_ = l_Std_Async_Async_race___redArg___lam__7(v_x_5271_, v_prio_5272_, v___f_5273_, v___f_5274_, v_y_5275_, v___f_5276_, v___f_5277_, v___f_5278_, v_x_5279_);
return v_res_5281_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg(lean_object* v_x_5284_, lean_object* v_y_5285_, lean_object* v_prio_5286_){
_start:
{
lean_object* v___x_5288_; lean_object* v___f_5289_; lean_object* v___f_5290_; lean_object* v___f_5291_; lean_object* v___f_5292_; lean_object* v___f_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; uint8_t v___x_5297_; lean_object* v___x_5298_; 
v___x_5288_ = lean_io_promise_new();
v___f_5289_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___f_5290_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__0));
v___f_5291_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__1));
v___f_5292_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_5293_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_5293_, 0, v_x_5284_);
lean_closure_set(v___f_5293_, 1, v_prio_5286_);
lean_closure_set(v___f_5293_, 2, v___f_5291_);
lean_closure_set(v___f_5293_, 3, v___f_5290_);
lean_closure_set(v___f_5293_, 4, v_y_5285_);
lean_closure_set(v___f_5293_, 5, v___f_5292_);
lean_closure_set(v___f_5293_, 6, v___f_5289_);
lean_closure_set(v___f_5293_, 7, v___f_5289_);
v___x_5294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5294_, 0, v___x_5288_);
v___x_5295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5295_, 0, v___x_5294_);
v___x_5296_ = lean_unsigned_to_nat(0u);
v___x_5297_ = 0;
v___x_5298_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5296_, v___x_5297_, v___x_5295_, v___f_5293_);
return v___x_5298_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___boxed(lean_object* v_x_5299_, lean_object* v_y_5300_, lean_object* v_prio_5301_, lean_object* v_a_5302_){
_start:
{
lean_object* v_res_5303_; 
v_res_5303_ = l_Std_Async_Async_race___redArg(v_x_5299_, v_y_5300_, v_prio_5301_);
return v_res_5303_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race(lean_object* v_00_u03b1_5304_, lean_object* v_inst_5305_, lean_object* v_x_5306_, lean_object* v_y_5307_, lean_object* v_prio_5308_){
_start:
{
lean_object* v___x_5310_; lean_object* v___f_5311_; lean_object* v___f_5312_; lean_object* v___f_5313_; lean_object* v___f_5314_; lean_object* v___f_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; uint8_t v___x_5319_; lean_object* v___x_5320_; 
v___x_5310_ = lean_io_promise_new();
v___f_5311_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___f_5312_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__0));
v___f_5313_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__1));
v___f_5314_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_5315_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_5315_, 0, v_x_5306_);
lean_closure_set(v___f_5315_, 1, v_prio_5308_);
lean_closure_set(v___f_5315_, 2, v___f_5313_);
lean_closure_set(v___f_5315_, 3, v___f_5312_);
lean_closure_set(v___f_5315_, 4, v_y_5307_);
lean_closure_set(v___f_5315_, 5, v___f_5314_);
lean_closure_set(v___f_5315_, 6, v___f_5311_);
lean_closure_set(v___f_5315_, 7, v___f_5311_);
v___x_5316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5316_, 0, v___x_5310_);
v___x_5317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5317_, 0, v___x_5316_);
v___x_5318_ = lean_unsigned_to_nat(0u);
v___x_5319_ = 0;
v___x_5320_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5318_, v___x_5319_, v___x_5317_, v___f_5315_);
return v___x_5320_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___boxed(lean_object* v_00_u03b1_5321_, lean_object* v_inst_5322_, lean_object* v_x_5323_, lean_object* v_y_5324_, lean_object* v_prio_5325_, lean_object* v_a_5326_){
_start:
{
lean_object* v_res_5327_; 
v_res_5327_ = l_Std_Async_Async_race(v_00_u03b1_5321_, v_inst_5322_, v_x_5323_, v_y_5324_, v_prio_5325_);
lean_dec(v_inst_5322_);
return v_res_5327_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg___lam__1(lean_object* v_prio_5328_, lean_object* v___f_5329_, lean_object* v_x_5330_){
_start:
{
lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; uint8_t v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; 
v___x_5332_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5332_, 0, lean_box(0));
lean_closure_set(v___x_5332_, 1, v_x_5330_);
v___x_5333_ = lean_io_as_task(v___x_5332_, v_prio_5328_);
v___x_5334_ = lean_unsigned_to_nat(0u);
v___x_5335_ = 1;
v___x_5336_ = lean_task_bind(v___x_5333_, v___f_5329_, v___x_5334_, v___x_5335_);
v___x_5337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5337_, 0, v___x_5336_);
v___x_5338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5338_, 0, v___x_5337_);
return v___x_5338_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg___lam__1___boxed(lean_object* v_prio_5339_, lean_object* v___f_5340_, lean_object* v_x_5341_, lean_object* v___y_5342_){
_start:
{
lean_object* v_res_5343_; 
v_res_5343_ = l_Std_Async_Async_concurrentlyAll___redArg___lam__1(v_prio_5339_, v___f_5340_, v_x_5341_);
return v_res_5343_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg___lam__0(lean_object* v___x_5345_, lean_object* v_x_5346_){
_start:
{
if (lean_obj_tag(v_x_5346_) == 0)
{
lean_object* v_a_5348_; lean_object* v___x_5350_; uint8_t v_isShared_5351_; uint8_t v_isSharedCheck_5356_; 
lean_dec_ref(v___x_5345_);
v_a_5348_ = lean_ctor_get(v_x_5346_, 0);
v_isSharedCheck_5356_ = !lean_is_exclusive(v_x_5346_);
if (v_isSharedCheck_5356_ == 0)
{
v___x_5350_ = v_x_5346_;
v_isShared_5351_ = v_isSharedCheck_5356_;
goto v_resetjp_5349_;
}
else
{
lean_inc(v_a_5348_);
lean_dec(v_x_5346_);
v___x_5350_ = lean_box(0);
v_isShared_5351_ = v_isSharedCheck_5356_;
goto v_resetjp_5349_;
}
v_resetjp_5349_:
{
lean_object* v___x_5353_; 
if (v_isShared_5351_ == 0)
{
v___x_5353_ = v___x_5350_;
goto v_reusejp_5352_;
}
else
{
lean_object* v_reuseFailAlloc_5355_; 
v_reuseFailAlloc_5355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5355_, 0, v_a_5348_);
v___x_5353_ = v_reuseFailAlloc_5355_;
goto v_reusejp_5352_;
}
v_reusejp_5352_:
{
lean_object* v___x_5354_; 
v___x_5354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5354_, 0, v___x_5353_);
return v___x_5354_;
}
}
}
else
{
lean_object* v_a_5357_; lean_object* v___x_5358_; size_t v_sz_5359_; size_t v___x_5360_; lean_object* v___x_269__overap_5361_; lean_object* v___x_5362_; 
v_a_5357_ = lean_ctor_get(v_x_5346_, 0);
lean_inc(v_a_5357_);
lean_dec_ref(v_x_5346_);
v___x_5358_ = ((lean_object*)(l_Std_Async_Async_concurrentlyAll___redArg___lam__0___closed__0));
v_sz_5359_ = lean_array_size(v_a_5357_);
v___x_5360_ = ((size_t)0ULL);
v___x_269__overap_5361_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_5345_, v___x_5358_, v_sz_5359_, v___x_5360_, v_a_5357_);
v___x_5362_ = lean_apply_1(v___x_269__overap_5361_, lean_box(0));
return v___x_5362_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg___lam__0___boxed(lean_object* v___x_5363_, lean_object* v_x_5364_, lean_object* v___y_5365_){
_start:
{
lean_object* v_res_5366_; 
v_res_5366_ = l_Std_Async_Async_concurrentlyAll___redArg___lam__0(v___x_5363_, v_x_5364_);
return v_res_5366_;
}
}
static lean_object* _init_l_Std_Async_Async_concurrentlyAll___redArg___closed__0(void){
_start:
{
lean_object* v___x_5367_; lean_object* v___f_5368_; 
v___x_5367_ = lean_obj_once(&l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0, &l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0_once, _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0);
v___f_5368_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrentlyAll___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5368_, 0, v___x_5367_);
return v___f_5368_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg(lean_object* v_xs_5369_, lean_object* v_prio_5370_){
_start:
{
lean_object* v___f_5372_; lean_object* v___f_5373_; lean_object* v___x_5374_; size_t v_sz_5375_; size_t v___x_5376_; lean_object* v___x_204__overap_5377_; lean_object* v___x_5378_; lean_object* v___f_5379_; lean_object* v___x_5380_; uint8_t v___x_5381_; lean_object* v___x_5382_; 
v___f_5372_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___f_5373_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrentlyAll___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_5373_, 0, v_prio_5370_);
lean_closure_set(v___f_5373_, 1, v___f_5372_);
v___x_5374_ = lean_obj_once(&l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0, &l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0_once, _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0);
v_sz_5375_ = lean_array_size(v_xs_5369_);
v___x_5376_ = ((size_t)0ULL);
v___x_204__overap_5377_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_5374_, v___f_5373_, v_sz_5375_, v___x_5376_, v_xs_5369_);
v___x_5378_ = lean_apply_1(v___x_204__overap_5377_, lean_box(0));
v___f_5379_ = lean_obj_once(&l_Std_Async_Async_concurrentlyAll___redArg___closed__0, &l_Std_Async_Async_concurrentlyAll___redArg___closed__0_once, _init_l_Std_Async_Async_concurrentlyAll___redArg___closed__0);
v___x_5380_ = lean_unsigned_to_nat(0u);
v___x_5381_ = 0;
v___x_5382_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5380_, v___x_5381_, v___x_5378_, v___f_5379_);
return v___x_5382_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg___boxed(lean_object* v_xs_5383_, lean_object* v_prio_5384_, lean_object* v_a_5385_){
_start:
{
lean_object* v_res_5386_; 
v_res_5386_ = l_Std_Async_Async_concurrentlyAll___redArg(v_xs_5383_, v_prio_5384_);
return v_res_5386_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll(lean_object* v_00_u03b1_5387_, lean_object* v_xs_5388_, lean_object* v_prio_5389_){
_start:
{
lean_object* v___f_5391_; lean_object* v___f_5392_; lean_object* v___x_5393_; size_t v_sz_5394_; size_t v___x_5395_; lean_object* v___x_226__overap_5396_; lean_object* v___x_5397_; lean_object* v___f_5398_; lean_object* v___x_5399_; uint8_t v___x_5400_; lean_object* v___x_5401_; 
v___f_5391_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___f_5392_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrentlyAll___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_5392_, 0, v_prio_5389_);
lean_closure_set(v___f_5392_, 1, v___f_5391_);
v___x_5393_ = lean_obj_once(&l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0, &l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0_once, _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0);
v_sz_5394_ = lean_array_size(v_xs_5388_);
v___x_5395_ = ((size_t)0ULL);
v___x_226__overap_5396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_5393_, v___f_5392_, v_sz_5394_, v___x_5395_, v_xs_5388_);
v___x_5397_ = lean_apply_1(v___x_226__overap_5396_, lean_box(0));
v___f_5398_ = lean_obj_once(&l_Std_Async_Async_concurrentlyAll___redArg___closed__0, &l_Std_Async_Async_concurrentlyAll___redArg___closed__0_once, _init_l_Std_Async_Async_concurrentlyAll___redArg___closed__0);
v___x_5399_ = lean_unsigned_to_nat(0u);
v___x_5400_ = 0;
v___x_5401_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5399_, v___x_5400_, v___x_5397_, v___f_5398_);
return v___x_5401_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___boxed(lean_object* v_00_u03b1_5402_, lean_object* v_xs_5403_, lean_object* v_prio_5404_, lean_object* v_a_5405_){
_start:
{
lean_object* v_res_5406_; 
v_res_5406_ = l_Std_Async_Async_concurrentlyAll(v_00_u03b1_5402_, v_xs_5403_, v_prio_5404_);
return v_res_5406_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__4(lean_object* v___f_5407_, lean_object* v___f_5408_, lean_object* v_x_5409_){
_start:
{
if (lean_obj_tag(v_x_5409_) == 0)
{
lean_object* v_a_5411_; lean_object* v___x_5413_; uint8_t v_isShared_5414_; uint8_t v_isSharedCheck_5419_; 
lean_dec_ref(v___f_5408_);
lean_dec(v___f_5407_);
v_a_5411_ = lean_ctor_get(v_x_5409_, 0);
v_isSharedCheck_5419_ = !lean_is_exclusive(v_x_5409_);
if (v_isSharedCheck_5419_ == 0)
{
v___x_5413_ = v_x_5409_;
v_isShared_5414_ = v_isSharedCheck_5419_;
goto v_resetjp_5412_;
}
else
{
lean_inc(v_a_5411_);
lean_dec(v_x_5409_);
v___x_5413_ = lean_box(0);
v_isShared_5414_ = v_isSharedCheck_5419_;
goto v_resetjp_5412_;
}
v_resetjp_5412_:
{
lean_object* v___x_5416_; 
if (v_isShared_5414_ == 0)
{
v___x_5416_ = v___x_5413_;
goto v_reusejp_5415_;
}
else
{
lean_object* v_reuseFailAlloc_5418_; 
v_reuseFailAlloc_5418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5418_, 0, v_a_5411_);
v___x_5416_ = v_reuseFailAlloc_5418_;
goto v_reusejp_5415_;
}
v_reusejp_5415_:
{
lean_object* v___x_5417_; 
v___x_5417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5417_, 0, v___x_5416_);
return v___x_5417_;
}
}
}
else
{
lean_object* v_a_5420_; lean_object* v___x_5422_; uint8_t v_isShared_5423_; uint8_t v_isSharedCheck_5433_; 
v_a_5420_ = lean_ctor_get(v_x_5409_, 0);
v_isSharedCheck_5433_ = !lean_is_exclusive(v_x_5409_);
if (v_isSharedCheck_5433_ == 0)
{
v___x_5422_ = v_x_5409_;
v_isShared_5423_ = v_isSharedCheck_5433_;
goto v_resetjp_5421_;
}
else
{
lean_inc(v_a_5420_);
lean_dec(v_x_5409_);
v___x_5422_ = lean_box(0);
v_isShared_5423_ = v_isSharedCheck_5433_;
goto v_resetjp_5421_;
}
v_resetjp_5421_:
{
lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; uint8_t v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5430_; 
v___x_5424_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_5424_, 0, lean_box(0));
lean_closure_set(v___x_5424_, 1, lean_box(0));
lean_closure_set(v___x_5424_, 2, v___f_5407_);
lean_closure_set(v___x_5424_, 3, lean_box(0));
v___x_5425_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_5425_, 0, lean_box(0));
lean_closure_set(v___x_5425_, 1, lean_box(0));
lean_closure_set(v___x_5425_, 2, lean_box(0));
lean_closure_set(v___x_5425_, 3, v___x_5424_);
lean_closure_set(v___x_5425_, 4, v___f_5408_);
v___x_5426_ = lean_unsigned_to_nat(0u);
v___x_5427_ = 0;
v___x_5428_ = l_BaseIO_chainTask___redArg(v_a_5420_, v___x_5425_, v___x_5426_, v___x_5427_);
if (v_isShared_5423_ == 0)
{
lean_ctor_set(v___x_5422_, 0, v___x_5428_);
v___x_5430_ = v___x_5422_;
goto v_reusejp_5429_;
}
else
{
lean_object* v_reuseFailAlloc_5432_; 
v_reuseFailAlloc_5432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5432_, 0, v___x_5428_);
v___x_5430_ = v_reuseFailAlloc_5432_;
goto v_reusejp_5429_;
}
v_reusejp_5429_:
{
lean_object* v___x_5431_; 
v___x_5431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5431_, 0, v___x_5430_);
return v___x_5431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__4___boxed(lean_object* v___f_5434_, lean_object* v___f_5435_, lean_object* v_x_5436_, lean_object* v___y_5437_){
_start:
{
lean_object* v_res_5438_; 
v_res_5438_ = l_Std_Async_Async_raceAll___redArg___lam__4(v___f_5434_, v___f_5435_, v_x_5436_);
return v_res_5438_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__0(lean_object* v_prio_5439_, lean_object* v___f_5440_, lean_object* v___f_5441_, lean_object* v_x_5442_){
_start:
{
lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; uint8_t v___x_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; uint8_t v___x_5451_; lean_object* v___x_5452_; 
v___x_5444_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5444_, 0, lean_box(0));
lean_closure_set(v___x_5444_, 1, v_x_5442_);
v___x_5445_ = lean_io_as_task(v___x_5444_, v_prio_5439_);
v___x_5446_ = lean_unsigned_to_nat(0u);
v___x_5447_ = 1;
v___x_5448_ = lean_task_bind(v___x_5445_, v___f_5440_, v___x_5446_, v___x_5447_);
v___x_5449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5449_, 0, v___x_5448_);
v___x_5450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5450_, 0, v___x_5449_);
v___x_5451_ = 0;
v___x_5452_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5446_, v___x_5451_, v___x_5450_, v___f_5441_);
return v___x_5452_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__0___boxed(lean_object* v_prio_5453_, lean_object* v___f_5454_, lean_object* v___f_5455_, lean_object* v_x_5456_, lean_object* v___y_5457_){
_start:
{
lean_object* v_res_5458_; 
v_res_5458_ = l_Std_Async_Async_raceAll___redArg___lam__0(v_prio_5453_, v___f_5454_, v___f_5455_, v_x_5456_);
return v_res_5458_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__2(lean_object* v___f_5459_, lean_object* v_prio_5460_, lean_object* v___f_5461_, lean_object* v_inst_5462_, lean_object* v_xs_5463_, lean_object* v___f_5464_, lean_object* v___f_5465_, lean_object* v_x_5466_){
_start:
{
if (lean_obj_tag(v_x_5466_) == 0)
{
lean_object* v_a_5468_; lean_object* v___x_5470_; uint8_t v_isShared_5471_; uint8_t v_isSharedCheck_5476_; 
lean_dec_ref(v___f_5465_);
lean_dec_ref(v___f_5464_);
lean_dec(v_xs_5463_);
lean_dec_ref(v_inst_5462_);
lean_dec_ref(v___f_5461_);
lean_dec(v_prio_5460_);
lean_dec(v___f_5459_);
v_a_5468_ = lean_ctor_get(v_x_5466_, 0);
v_isSharedCheck_5476_ = !lean_is_exclusive(v_x_5466_);
if (v_isSharedCheck_5476_ == 0)
{
v___x_5470_ = v_x_5466_;
v_isShared_5471_ = v_isSharedCheck_5476_;
goto v_resetjp_5469_;
}
else
{
lean_inc(v_a_5468_);
lean_dec(v_x_5466_);
v___x_5470_ = lean_box(0);
v_isShared_5471_ = v_isSharedCheck_5476_;
goto v_resetjp_5469_;
}
v_resetjp_5469_:
{
lean_object* v___x_5473_; 
if (v_isShared_5471_ == 0)
{
v___x_5473_ = v___x_5470_;
goto v_reusejp_5472_;
}
else
{
lean_object* v_reuseFailAlloc_5475_; 
v_reuseFailAlloc_5475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5475_, 0, v_a_5468_);
v___x_5473_ = v_reuseFailAlloc_5475_;
goto v_reusejp_5472_;
}
v_reusejp_5472_:
{
lean_object* v___x_5474_; 
v___x_5474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5474_, 0, v___x_5473_);
return v___x_5474_;
}
}
}
else
{
lean_object* v_a_5477_; lean_object* v___f_5478_; lean_object* v___f_5479_; lean_object* v___f_5480_; lean_object* v___x_5481_; lean_object* v___f_5482_; lean_object* v___x_5483_; uint8_t v___x_5484_; lean_object* v___x_5485_; 
v_a_5477_ = lean_ctor_get(v_x_5466_, 0);
lean_inc_n(v_a_5477_, 2);
lean_dec_ref(v_x_5466_);
v___f_5478_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_5478_, 0, v_a_5477_);
v___f_5479_ = lean_alloc_closure((void*)(l_Std_Async_Async_raceAll___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_5479_, 0, v___f_5459_);
lean_closure_set(v___f_5479_, 1, v___f_5478_);
v___f_5480_ = lean_alloc_closure((void*)(l_Std_Async_Async_raceAll___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_5480_, 0, v_prio_5460_);
lean_closure_set(v___f_5480_, 1, v___f_5461_);
lean_closure_set(v___f_5480_, 2, v___f_5479_);
v___x_5481_ = lean_apply_3(v_inst_5462_, v_xs_5463_, v___f_5480_, lean_box(0));
v___f_5482_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_5482_, 0, v_a_5477_);
lean_closure_set(v___f_5482_, 1, v___f_5464_);
lean_closure_set(v___f_5482_, 2, v___f_5465_);
v___x_5483_ = lean_unsigned_to_nat(0u);
v___x_5484_ = 0;
v___x_5485_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5483_, v___x_5484_, v___x_5481_, v___f_5482_);
return v___x_5485_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__2___boxed(lean_object* v___f_5486_, lean_object* v_prio_5487_, lean_object* v___f_5488_, lean_object* v_inst_5489_, lean_object* v_xs_5490_, lean_object* v___f_5491_, lean_object* v___f_5492_, lean_object* v_x_5493_, lean_object* v___y_5494_){
_start:
{
lean_object* v_res_5495_; 
v_res_5495_ = l_Std_Async_Async_raceAll___redArg___lam__2(v___f_5486_, v_prio_5487_, v___f_5488_, v_inst_5489_, v_xs_5490_, v___f_5491_, v___f_5492_, v_x_5493_);
return v_res_5495_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg(lean_object* v_inst_5496_, lean_object* v_xs_5497_, lean_object* v_prio_5498_){
_start:
{
lean_object* v___x_5500_; lean_object* v___f_5501_; lean_object* v___f_5502_; lean_object* v___f_5503_; lean_object* v___f_5504_; lean_object* v___f_5505_; lean_object* v___x_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; uint8_t v___x_5509_; lean_object* v___x_5510_; 
v___x_5500_ = lean_io_promise_new();
v___f_5501_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__1));
v___f_5502_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__0));
v___f_5503_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___f_5504_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_5505_ = lean_alloc_closure((void*)(l_Std_Async_Async_raceAll___redArg___lam__2___boxed), 9, 7);
lean_closure_set(v___f_5505_, 0, v___f_5504_);
lean_closure_set(v___f_5505_, 1, v_prio_5498_);
lean_closure_set(v___f_5505_, 2, v___f_5503_);
lean_closure_set(v___f_5505_, 3, v_inst_5496_);
lean_closure_set(v___f_5505_, 4, v_xs_5497_);
lean_closure_set(v___f_5505_, 5, v___f_5501_);
lean_closure_set(v___f_5505_, 6, v___f_5502_);
v___x_5506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5506_, 0, v___x_5500_);
v___x_5507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5507_, 0, v___x_5506_);
v___x_5508_ = lean_unsigned_to_nat(0u);
v___x_5509_ = 0;
v___x_5510_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5508_, v___x_5509_, v___x_5507_, v___f_5505_);
return v___x_5510_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___boxed(lean_object* v_inst_5511_, lean_object* v_xs_5512_, lean_object* v_prio_5513_, lean_object* v_a_5514_){
_start:
{
lean_object* v_res_5515_; 
v_res_5515_ = l_Std_Async_Async_raceAll___redArg(v_inst_5511_, v_xs_5512_, v_prio_5513_);
return v_res_5515_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll(lean_object* v_c_5516_, lean_object* v_00_u03b1_5517_, lean_object* v_inst_5518_, lean_object* v_xs_5519_, lean_object* v_prio_5520_){
_start:
{
lean_object* v___x_5522_; lean_object* v___f_5523_; lean_object* v___f_5524_; lean_object* v___f_5525_; lean_object* v___f_5526_; lean_object* v___f_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; uint8_t v___x_5531_; lean_object* v___x_5532_; 
v___x_5522_ = lean_io_promise_new();
v___f_5523_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__1));
v___f_5524_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__0));
v___f_5525_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___f_5526_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_5527_ = lean_alloc_closure((void*)(l_Std_Async_Async_raceAll___redArg___lam__2___boxed), 9, 7);
lean_closure_set(v___f_5527_, 0, v___f_5526_);
lean_closure_set(v___f_5527_, 1, v_prio_5520_);
lean_closure_set(v___f_5527_, 2, v___f_5525_);
lean_closure_set(v___f_5527_, 3, v_inst_5518_);
lean_closure_set(v___f_5527_, 4, v_xs_5519_);
lean_closure_set(v___f_5527_, 5, v___f_5523_);
lean_closure_set(v___f_5527_, 6, v___f_5524_);
v___x_5528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5528_, 0, v___x_5522_);
v___x_5529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5529_, 0, v___x_5528_);
v___x_5530_ = lean_unsigned_to_nat(0u);
v___x_5531_ = 0;
v___x_5532_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5530_, v___x_5531_, v___x_5529_, v___f_5527_);
return v___x_5532_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___boxed(lean_object* v_c_5533_, lean_object* v_00_u03b1_5534_, lean_object* v_inst_5535_, lean_object* v_xs_5536_, lean_object* v_prio_5537_, lean_object* v_a_5538_){
_start:
{
lean_object* v_res_5539_; 
v_res_5539_ = l_Std_Async_Async_raceAll(v_c_5533_, v_00_u03b1_5534_, v_inst_5535_, v_xs_5536_, v_prio_5537_);
return v_res_5539_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_background___redArg(lean_object* v_inst_5540_, lean_object* v_inst_5541_, lean_object* v_action_5542_, lean_object* v_prio_5543_){
_start:
{
lean_object* v_toApplicative_5544_; lean_object* v_toFunctor_5545_; lean_object* v_mapConst_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; 
v_toApplicative_5544_ = lean_ctor_get(v_inst_5540_, 0);
lean_inc_ref(v_toApplicative_5544_);
lean_dec_ref(v_inst_5540_);
v_toFunctor_5545_ = lean_ctor_get(v_toApplicative_5544_, 0);
lean_inc_ref(v_toFunctor_5545_);
lean_dec_ref(v_toApplicative_5544_);
v_mapConst_5546_ = lean_ctor_get(v_toFunctor_5545_, 1);
lean_inc(v_mapConst_5546_);
lean_dec_ref(v_toFunctor_5545_);
v___x_5547_ = lean_apply_3(v_inst_5541_, lean_box(0), v_action_5542_, v_prio_5543_);
v___x_5548_ = lean_box(0);
v___x_5549_ = lean_apply_4(v_mapConst_5546_, lean_box(0), lean_box(0), v___x_5548_, v___x_5547_);
return v___x_5549_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_background(lean_object* v_m_5550_, lean_object* v_t_5551_, lean_object* v_00_u03b1_5552_, lean_object* v_inst_5553_, lean_object* v_inst_5554_, lean_object* v_action_5555_, lean_object* v_prio_5556_){
_start:
{
lean_object* v_toApplicative_5557_; lean_object* v_toFunctor_5558_; lean_object* v_mapConst_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; 
v_toApplicative_5557_ = lean_ctor_get(v_inst_5553_, 0);
lean_inc_ref(v_toApplicative_5557_);
lean_dec_ref(v_inst_5553_);
v_toFunctor_5558_ = lean_ctor_get(v_toApplicative_5557_, 0);
lean_inc_ref(v_toFunctor_5558_);
lean_dec_ref(v_toApplicative_5557_);
v_mapConst_5559_ = lean_ctor_get(v_toFunctor_5558_, 1);
lean_inc(v_mapConst_5559_);
lean_dec_ref(v_toFunctor_5558_);
v___x_5560_ = lean_apply_3(v_inst_5554_, lean_box(0), v_action_5555_, v_prio_5556_);
v___x_5561_ = lean_box(0);
v___x_5562_ = lean_apply_4(v_mapConst_5559_, lean_box(0), lean_box(0), v___x_5561_, v___x_5560_);
return v___x_5562_;
}
}
lean_object* runtime_initialize_Init_System_Promise(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Async_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_System_Promise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Async_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_Promise(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Async_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_Promise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Async_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Async_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
