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
lean_object* lean_task_pure(lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_instMonadBaseIO___aux__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* l_liftM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Function_const___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* l_MonadExcept_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_io_get_task_state(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_io_promise_new();
lean_object* l_instMonadLiftT___redArg___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Async_ETask_instFunctor___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_instFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ETask_instFunctor___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ETask_instFunctor___redArg___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ETask_instFunctor___redArg___closed__0 = (const lean_object*)&l_Std_Async_ETask_instFunctor___redArg___closed__0_value;
static const lean_closure_object l_Std_Async_ETask_instFunctor___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ETask_instFunctor___redArg___lam__0, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_ETask_instFunctor___redArg___closed__0_value)} };
static const lean_object* l_Std_Async_ETask_instFunctor___redArg___closed__1 = (const lean_object*)&l_Std_Async_ETask_instFunctor___redArg___closed__1_value;
static const lean_ctor_object l_Std_Async_ETask_instFunctor___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_ETask_instFunctor___redArg___closed__0_value),((lean_object*)&l_Std_Async_ETask_instFunctor___redArg___closed__1_value)}};
static const lean_object* l_Std_Async_ETask_instFunctor___redArg___closed__2 = (const lean_object*)&l_Std_Async_ETask_instFunctor___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Async_ETask_instFunctor___redArg();
LEAN_EXPORT lean_object* l_Std_Async_ETask_instFunctor___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Async_ETask_instFunctor___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_ETask_instFunctor___closed__0;
LEAN_EXPORT lean_object* l_Std_Async_ETask_instFunctor(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_ETask_instMonad___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ETask_instMonad___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ETask_instMonad___redArg___closed__0 = (const lean_object*)&l_Std_Async_ETask_instMonad___redArg___closed__0_value;
static const lean_closure_object l_Std_Async_ETask_instMonad___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ETask_instMonad___redArg___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ETask_instMonad___redArg___closed__1 = (const lean_object*)&l_Std_Async_ETask_instMonad___redArg___closed__1_value;
static const lean_closure_object l_Std_Async_ETask_instMonad___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ETask_instMonad___redArg___lam__5, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ETask_instMonad___redArg___closed__2 = (const lean_object*)&l_Std_Async_ETask_instMonad___redArg___closed__2_value;
static const lean_closure_object l_Std_Async_ETask_instMonad___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ETask_instMonad___redArg___lam__7, .m_arity = 6, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Async_ETask_instMonad___redArg___closed__0_value),((lean_object*)&l_Std_Async_ETask_instMonad___redArg___closed__2_value)} };
static const lean_object* l_Std_Async_ETask_instMonad___redArg___closed__3 = (const lean_object*)&l_Std_Async_ETask_instMonad___redArg___closed__3_value;
static const lean_closure_object l_Std_Async_ETask_instMonad___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ETask_instMonad___redArg___lam__9, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_ETask_instMonad___redArg___closed__4 = (const lean_object*)&l_Std_Async_ETask_instMonad___redArg___closed__4_value;
static lean_once_cell_t l_Std_Async_ETask_instMonad___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_ETask_instMonad___redArg___closed__5;
static lean_once_cell_t l_Std_Async_ETask_instMonad___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_ETask_instMonad___redArg___closed__6;
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg();
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Async_ETask_instMonad___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_ETask_instMonad___closed__0;
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
static const lean_closure_object l_Std_Async_BaseAsync_race___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instFunctor___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instFunctor___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_instFunctor___redArg___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instFunctor___redArg___closed__0_value;
static const lean_closure_object l_Std_Async_EAsync_instFunctor___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instFunctor___redArg___lam__1___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_EAsync_instFunctor___redArg___closed__0_value)} };
static const lean_object* l_Std_Async_EAsync_instFunctor___redArg___closed__1 = (const lean_object*)&l_Std_Async_EAsync_instFunctor___redArg___closed__1_value;
static const lean_ctor_object l_Std_Async_EAsync_instFunctor___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_EAsync_instFunctor___redArg___closed__0_value),((lean_object*)&l_Std_Async_EAsync_instFunctor___redArg___closed__1_value)}};
static const lean_object* l_Std_Async_EAsync_instFunctor___redArg___closed__2 = (const lean_object*)&l_Std_Async_EAsync_instFunctor___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___redArg();
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Async_EAsync_instFunctor___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_EAsync_instFunctor___closed__0;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instMonad___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonad___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_instMonad___redArg___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonad___redArg___closed__0_value;
static const lean_closure_object l_Std_Async_EAsync_instMonad___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonad___redArg___lam__2___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_instMonad___redArg___closed__1 = (const lean_object*)&l_Std_Async_EAsync_instMonad___redArg___closed__1_value;
static const lean_closure_object l_Std_Async_EAsync_instMonad___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonad___redArg___lam__5___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_EAsync_instMonad___redArg___closed__0_value)} };
static const lean_object* l_Std_Async_EAsync_instMonad___redArg___closed__2 = (const lean_object*)&l_Std_Async_EAsync_instMonad___redArg___closed__2_value;
static const lean_closure_object l_Std_Async_EAsync_instMonad___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonad___redArg___lam__7___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_instMonad___redArg___closed__3 = (const lean_object*)&l_Std_Async_EAsync_instMonad___redArg___closed__3_value;
static lean_once_cell_t l_Std_Async_EAsync_instMonad___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_EAsync_instMonad___redArg___closed__4;
static const lean_closure_object l_Std_Async_EAsync_instMonad___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_bind___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Async_EAsync_instMonad___redArg___closed__5 = (const lean_object*)&l_Std_Async_EAsync_instMonad___redArg___closed__5_value;
static lean_once_cell_t l_Std_Async_EAsync_instMonad___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_EAsync_instMonad___redArg___closed__6;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg();
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Async_EAsync_instMonad___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_EAsync_instMonad___closed__0;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad(lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instMonadLiftEIO___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_lift___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Async_EAsync_instMonadLiftEIO___redArg___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonadLiftEIO___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO___redArg();
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExcept___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExcept___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instMonadExcept___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadExcept___redArg___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_instMonadExcept___redArg___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonadExcept___redArg___closed__0_value;
static const lean_closure_object l_Std_Async_EAsync_instMonadExcept___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_throw___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Async_EAsync_instMonadExcept___redArg___closed__1 = (const lean_object*)&l_Std_Async_EAsync_instMonadExcept___redArg___closed__1_value;
static const lean_ctor_object l_Std_Async_EAsync_instMonadExcept___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_EAsync_instMonadExcept___redArg___closed__1_value),((lean_object*)&l_Std_Async_EAsync_instMonadExcept___redArg___closed__0_value)}};
static const lean_object* l_Std_Async_EAsync_instMonadExcept___redArg___closed__2 = (const lean_object*)&l_Std_Async_EAsync_instMonadExcept___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExcept___redArg();
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExcept___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Async_EAsync_instMonadExcept___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_EAsync_instMonadExcept___closed__0;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExcept(lean_object*);
static const lean_ctor_object l_Std_Async_EAsync_instMonadExceptOf___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_EAsync_instMonadExcept___redArg___closed__1_value),((lean_object*)&l_Std_Async_EAsync_instMonadExcept___redArg___closed__0_value)}};
static const lean_object* l_Std_Async_EAsync_instMonadExceptOf___redArg___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonadExceptOf___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExceptOf___redArg();
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExceptOf___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Async_EAsync_instMonadExceptOf___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_EAsync_instMonadExceptOf___closed__0;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExceptOf(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadFinally___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadFinally___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instMonadFinally___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadFinally___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_instMonadFinally___redArg___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonadFinally___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadFinally___redArg();
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadFinally___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadFinally(lean_object*);
static lean_once_cell_t l_Std_Async_EAsync_instOrElse___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_EAsync_instOrElse___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instOrElse___redArg();
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instOrElse___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Async_EAsync_instOrElse___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_EAsync_instOrElse___closed__0;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instOrElse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instInhabited___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instInhabited(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitETask___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitETask___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instMonadAwaitETask___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadAwaitETask___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_instMonadAwaitETask___redArg___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonadAwaitETask___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitETask___redArg();
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitETask___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitETask(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitTask___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitTask___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instMonadAwaitTask___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadAwaitTask___redArg___lam__1___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___closed__0_value)} };
static const lean_object* l_Std_Async_EAsync_instMonadAwaitTask___redArg___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonadAwaitTask___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitTask___redArg();
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitTask___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Async_EAsync_instMonadAwaitTask___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_EAsync_instMonadAwaitTask___closed__0;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitTask(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_EAsync_instMonadAwaitAsyncTaskError = (const lean_object*)&l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitPromise___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitPromise___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instMonadAwaitPromise___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadAwaitPromise___redArg___lam__1___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___closed__0_value)} };
static const lean_object* l_Std_Async_EAsync_instMonadAwaitPromise___redArg___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonadAwaitPromise___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitPromise___redArg();
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitPromise___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Async_EAsync_instMonadAwaitPromise___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_EAsync_instMonadAwaitPromise___closed__0;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitPromise(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncETask___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncETask___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instMonadAsyncETask___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadAsyncETask___redArg___lam__1___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_EAsync_asTask___redArg___closed__0_value)} };
static const lean_object* l_Std_Async_EAsync_instMonadAsyncETask___redArg___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonadAsyncETask___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncETask___redArg();
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncETask___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Async_EAsync_instMonadAsyncETask___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_EAsync_instMonadAsyncETask___closed__0;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncETask(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0_value;
static const lean_closure_object l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__1___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0_value)} };
static const lean_object* l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__1 = (const lean_object*)&l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Async_EAsync_instMonadAsyncAsyncTaskError = (const lean_object*)&l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO___redArg();
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1___redArg();
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg___lam__1___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___closed__0_value)} };
static const lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Async_EAsync_instMonadLiftBaseAsync___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___closed__0;
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
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_EAsync_instForInLoopUnit___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_instForInLoopUnit___redArg___closed__0 = (const lean_object*)&l_Std_Async_EAsync_instForInLoopUnit___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___redArg();
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___redArg___boxed(lean_object*);
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
static const lean_closure_object l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_concurrentlyAll___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0 = (const lean_object*)&l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0_value;
static lean_once_cell_t l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1;
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
lean_dec_ref_known(v_x_211_, 1);
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
lean_dec_ref_known(v_a_254_, 1);
v_a_257_ = v_a_260_;
goto v___jp_256_;
}
else
{
lean_object* v_a_261_; lean_object* v___x_262_; 
v_a_261_ = lean_ctor_get(v_a_254_, 0);
lean_inc(v_a_261_);
lean_dec_ref_known(v_a_254_, 1);
v___x_262_ = lean_apply_2(v_f_253_, v_a_261_, lean_box(0));
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_a_263_);
lean_dec_ref_known(v___x_262_, 1);
return v_a_263_;
}
else
{
lean_object* v_a_264_; 
v_a_264_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_a_264_);
lean_dec_ref_known(v___x_262_, 1);
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
lean_dec_ref_known(v_a_306_, 1);
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
lean_dec_ref_known(v___x_316_, 1);
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
lean_dec_ref_known(v___x_316_, 1);
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
LEAN_EXPORT lean_object* l_Std_Async_ETask_instFunctor___redArg___lam__1(lean_object* v_00_u03b1_460_, lean_object* v_00_u03b2_461_, lean_object* v_f_462_, lean_object* v_x_463_){
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
LEAN_EXPORT lean_object* l_Std_Async_ETask_instFunctor___redArg___lam__0(lean_object* v___f_468_, lean_object* v_00_u03b1_469_, lean_object* v_00_u03b2_470_, lean_object* v___y_471_, lean_object* v___y_472_){
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
LEAN_EXPORT lean_object* l_Std_Async_ETask_instFunctor___redArg(){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = ((lean_object*)(l_Std_Async_ETask_instFunctor___redArg___closed__2));
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instFunctor___redArg___boxed(lean_object* v___dummy_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Std_Async_ETask_instFunctor___redArg();
return v_res_484_;
}
}
static lean_object* _init_l_Std_Async_ETask_instFunctor___closed__0(void){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Std_Async_ETask_instFunctor___redArg();
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instFunctor(lean_object* v_00_u03b5_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = lean_obj_once(&l_Std_Async_ETask_instFunctor___closed__0, &l_Std_Async_ETask_instFunctor___closed__0_once, _init_l_Std_Async_ETask_instFunctor___closed__0);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__0(lean_object* v_00_u03b1_488_, lean_object* v___y_489_){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v___y_489_);
v___x_491_ = lean_task_pure(v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__1(lean_object* v_a_492_, lean_object* v_x_493_){
_start:
{
if (lean_obj_tag(v_x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_dec(v_a_492_);
v_a_494_ = lean_ctor_get(v_x_493_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v_x_493_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v_x_493_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v_x_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
else
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_510_; 
v_a_502_ = lean_ctor_get(v_x_493_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v_x_493_);
if (v_isSharedCheck_510_ == 0)
{
v___x_504_ = v_x_493_;
v_isShared_505_ = v_isSharedCheck_510_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v_x_493_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_510_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_506_; lean_object* v___x_508_; 
v___x_506_ = lean_apply_1(v_a_492_, v_a_502_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_506_);
v___x_508_ = v___x_504_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__2(lean_object* v_x_511_, lean_object* v_x_512_){
_start:
{
if (lean_obj_tag(v_x_512_) == 0)
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_521_; 
lean_dec_ref(v_x_511_);
v_a_513_ = lean_ctor_get(v_x_512_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v_x_512_);
if (v_isSharedCheck_521_ == 0)
{
v___x_515_ = v_x_512_;
v_isShared_516_ = v_isSharedCheck_521_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v_x_512_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_521_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_520_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_519_; 
v___x_519_ = lean_task_pure(v___x_518_);
return v___x_519_;
}
}
}
else
{
lean_object* v_a_522_; lean_object* v___f_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; lean_object* v___x_528_; 
v_a_522_ = lean_ctor_get(v_x_512_, 0);
lean_inc(v_a_522_);
lean_dec_ref_known(v_x_512_, 1);
v___f_523_ = lean_alloc_closure((void*)(l_Std_Async_ETask_instMonad___redArg___lam__1), 2, 1);
lean_closure_set(v___f_523_, 0, v_a_522_);
v___x_524_ = lean_box(0);
v___x_525_ = lean_apply_1(v_x_511_, v___x_524_);
v___x_526_ = lean_unsigned_to_nat(0u);
v___x_527_ = 0;
v___x_528_ = lean_task_map(v___f_523_, v___x_525_, v___x_526_, v___x_527_);
return v___x_528_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__3(lean_object* v_00_u03b1_529_, lean_object* v_00_u03b2_530_, lean_object* v_f_531_, lean_object* v_x_532_){
_start:
{
lean_object* v___f_533_; lean_object* v___x_534_; uint8_t v___x_535_; lean_object* v___x_536_; 
v___f_533_ = lean_alloc_closure((void*)(l_Std_Async_ETask_instMonad___redArg___lam__2), 2, 1);
lean_closure_set(v___f_533_, 0, v_x_532_);
v___x_534_ = lean_unsigned_to_nat(0u);
v___x_535_ = 0;
v___x_536_ = lean_task_bind(v_f_531_, v___f_533_, v___x_534_, v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__5(lean_object* v_00_u03b1_537_, lean_object* v_00_u03b2_538_, lean_object* v_x_539_, lean_object* v_f_540_){
_start:
{
lean_object* v___f_541_; lean_object* v___x_542_; uint8_t v___x_543_; lean_object* v___x_544_; 
v___f_541_ = lean_alloc_closure((void*)(l_Std_Async_ETask_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_541_, 0, v_f_540_);
v___x_542_ = lean_unsigned_to_nat(0u);
v___x_543_ = 0;
v___x_544_ = lean_task_bind(v_x_539_, v___f_541_, v___x_542_, v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__4(lean_object* v___f_545_, lean_object* v_a_546_, lean_object* v_x_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = lean_apply_2(v___f_545_, lean_box(0), v_a_546_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__4___boxed(lean_object* v___f_549_, lean_object* v_a_550_, lean_object* v_x_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Std_Async_ETask_instMonad___redArg___lam__4(v___f_549_, v_a_550_, v_x_551_);
lean_dec(v_x_551_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__6(lean_object* v___f_553_, lean_object* v_y_554_, lean_object* v___f_555_, lean_object* v_a_556_){
_start:
{
lean_object* v___f_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___f_557_ = lean_alloc_closure((void*)(l_Std_Async_ETask_instMonad___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_557_, 0, v___f_553_);
lean_closure_set(v___f_557_, 1, v_a_556_);
v___x_558_ = lean_box(0);
v___x_559_ = lean_apply_1(v_y_554_, v___x_558_);
v___x_560_ = lean_apply_4(v___f_555_, lean_box(0), lean_box(0), v___x_559_, v___f_557_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__7(lean_object* v___f_561_, lean_object* v___f_562_, lean_object* v_00_u03b1_563_, lean_object* v_00_u03b2_564_, lean_object* v_x_565_, lean_object* v_y_566_){
_start:
{
lean_object* v___f_567_; lean_object* v___x_568_; 
lean_inc_ref(v___f_562_);
v___f_567_ = lean_alloc_closure((void*)(l_Std_Async_ETask_instMonad___redArg___lam__6), 4, 3);
lean_closure_set(v___f_567_, 0, v___f_561_);
lean_closure_set(v___f_567_, 1, v_y_566_);
lean_closure_set(v___f_567_, 2, v___f_562_);
v___x_568_ = lean_apply_4(v___f_562_, lean_box(0), lean_box(0), v_x_565_, v___f_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__8(lean_object* v_y_569_, lean_object* v_x_570_){
_start:
{
if (lean_obj_tag(v_x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_579_; 
lean_dec_ref(v_y_569_);
v_a_571_ = lean_ctor_get(v_x_570_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v_x_570_);
if (v_isSharedCheck_579_ == 0)
{
v___x_573_ = v_x_570_;
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v_x_570_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_578_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_577_; 
v___x_577_ = lean_task_pure(v___x_576_);
return v___x_577_;
}
}
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec_ref_known(v_x_570_, 1);
v___x_580_ = lean_box(0);
v___x_581_ = lean_apply_1(v_y_569_, v___x_580_);
return v___x_581_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__9(lean_object* v_00_u03b1_582_, lean_object* v_00_u03b2_583_, lean_object* v_x_584_, lean_object* v_y_585_){
_start:
{
lean_object* v___f_586_; lean_object* v___x_587_; uint8_t v___x_588_; lean_object* v___x_589_; 
v___f_586_ = lean_alloc_closure((void*)(l_Std_Async_ETask_instMonad___redArg___lam__8), 2, 1);
lean_closure_set(v___f_586_, 0, v_y_585_);
v___x_587_ = lean_unsigned_to_nat(0u);
v___x_588_ = 0;
v___x_589_ = lean_task_bind(v_x_584_, v___f_586_, v___x_587_, v___x_588_);
return v___x_589_;
}
}
static lean_object* _init_l_Std_Async_ETask_instMonad___redArg___closed__5(void){
_start:
{
lean_object* v___f_597_; lean_object* v___f_598_; lean_object* v___f_599_; lean_object* v___f_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___f_597_ = ((lean_object*)(l_Std_Async_ETask_instMonad___redArg___closed__4));
v___f_598_ = ((lean_object*)(l_Std_Async_ETask_instMonad___redArg___closed__3));
v___f_599_ = ((lean_object*)(l_Std_Async_ETask_instMonad___redArg___closed__1));
v___f_600_ = ((lean_object*)(l_Std_Async_ETask_instMonad___redArg___closed__0));
v___x_601_ = lean_obj_once(&l_Std_Async_ETask_instFunctor___closed__0, &l_Std_Async_ETask_instFunctor___closed__0_once, _init_l_Std_Async_ETask_instFunctor___closed__0);
v___x_602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v___f_600_);
lean_ctor_set(v___x_602_, 2, v___f_599_);
lean_ctor_set(v___x_602_, 3, v___f_598_);
lean_ctor_set(v___x_602_, 4, v___f_597_);
return v___x_602_;
}
}
static lean_object* _init_l_Std_Async_ETask_instMonad___redArg___closed__6(void){
_start:
{
lean_object* v___f_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___f_603_ = ((lean_object*)(l_Std_Async_ETask_instMonad___redArg___closed__2));
v___x_604_ = lean_obj_once(&l_Std_Async_ETask_instMonad___redArg___closed__5, &l_Std_Async_ETask_instMonad___redArg___closed__5_once, _init_l_Std_Async_ETask_instMonad___redArg___closed__5);
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v___f_603_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg(){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = lean_obj_once(&l_Std_Async_ETask_instMonad___redArg___closed__6, &l_Std_Async_ETask_instMonad___redArg___closed__6_once, _init_l_Std_Async_ETask_instMonad___redArg___closed__6);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___boxed(lean_object* v___dummy_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Std_Async_ETask_instMonad___redArg();
return v_res_609_;
}
}
static lean_object* _init_l_Std_Async_ETask_instMonad___closed__0(void){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Std_Async_ETask_instMonad___redArg();
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad(lean_object* v_00_u03b5_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = lean_obj_once(&l_Std_Async_ETask_instMonad___closed__0, &l_Std_Async_ETask_instMonad___closed__0_once, _init_l_Std_Async_ETask_instMonad___closed__0);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapIO___redArg___lam__0(lean_object* v_f_613_, lean_object* v_a_614_){
_start:
{
lean_object* v_a_617_; 
if (lean_obj_tag(v_a_614_) == 0)
{
lean_object* v_a_619_; 
lean_dec_ref(v_f_613_);
v_a_619_ = lean_ctor_get(v_a_614_, 0);
lean_inc(v_a_619_);
lean_dec_ref_known(v_a_614_, 1);
v_a_617_ = v_a_619_;
goto v___jp_616_;
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_630_; 
v_a_620_ = lean_ctor_get(v_a_614_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v_a_614_);
if (v_isSharedCheck_630_ == 0)
{
v___x_622_ = v_a_614_;
v_isShared_623_ = v_isSharedCheck_630_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v_a_614_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_630_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_624_; 
v___x_624_ = lean_apply_2(v_f_613_, v_a_620_, lean_box(0));
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v___x_627_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref_known(v___x_624_, 1);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v_a_625_);
v___x_627_ = v___x_622_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
else
{
lean_object* v_a_629_; 
lean_del_object(v___x_622_);
v_a_629_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_629_);
lean_dec_ref_known(v___x_624_, 1);
v_a_617_ = v_a_629_;
goto v___jp_616_;
}
}
}
v___jp_616_:
{
lean_object* v___x_618_; 
v___x_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_618_, 0, v_a_617_);
return v___x_618_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapIO___redArg___lam__0___boxed(lean_object* v_f_631_, lean_object* v_a_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Std_Async_AsyncTask_mapIO___redArg___lam__0(v_f_631_, v_a_632_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapIO___redArg(lean_object* v_f_635_, lean_object* v_x_636_, lean_object* v_prio_637_, uint8_t v_sync_638_){
_start:
{
lean_object* v___f_640_; lean_object* v___x_641_; 
v___f_640_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_mapIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_640_, 0, v_f_635_);
v___x_641_ = lean_io_map_task(v___f_640_, v_x_636_, v_prio_637_, v_sync_638_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapIO___redArg___boxed(lean_object* v_f_642_, lean_object* v_x_643_, lean_object* v_prio_644_, lean_object* v_sync_645_, lean_object* v_a_646_){
_start:
{
uint8_t v_sync_boxed_647_; lean_object* v_res_648_; 
v_sync_boxed_647_ = lean_unbox(v_sync_645_);
v_res_648_ = l_Std_Async_AsyncTask_mapIO___redArg(v_f_642_, v_x_643_, v_prio_644_, v_sync_boxed_647_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapIO(lean_object* v_00_u03b1_649_, lean_object* v_00_u03b2_650_, lean_object* v_f_651_, lean_object* v_x_652_, lean_object* v_prio_653_, uint8_t v_sync_654_){
_start:
{
lean_object* v___f_656_; lean_object* v___x_657_; 
v___f_656_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_mapIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_656_, 0, v_f_651_);
v___x_657_ = lean_io_map_task(v___f_656_, v_x_652_, v_prio_653_, v_sync_654_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapIO___boxed(lean_object* v_00_u03b1_658_, lean_object* v_00_u03b2_659_, lean_object* v_f_660_, lean_object* v_x_661_, lean_object* v_prio_662_, lean_object* v_sync_663_, lean_object* v_a_664_){
_start:
{
uint8_t v_sync_boxed_665_; lean_object* v_res_666_; 
v_sync_boxed_665_ = lean_unbox(v_sync_663_);
v_res_666_ = l_Std_Async_AsyncTask_mapIO(v_00_u03b1_658_, v_00_u03b2_659_, v_f_660_, v_x_661_, v_prio_662_, v_sync_boxed_665_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_pure___redArg(lean_object* v_x_667_){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_668_, 0, v_x_667_);
v___x_669_ = lean_task_pure(v___x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_pure(lean_object* v_00_u03b1_670_, lean_object* v_x_671_){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_672_, 0, v_x_671_);
v___x_673_ = lean_task_pure(v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bind___redArg___lam__0(lean_object* v_f_674_, lean_object* v_x_675_){
_start:
{
if (lean_obj_tag(v_x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_684_; 
lean_dec_ref(v_f_674_);
v_a_676_ = lean_ctor_get(v_x_675_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v_x_675_);
if (v_isSharedCheck_684_ == 0)
{
v___x_678_ = v_x_675_;
v_isShared_679_ = v_isSharedCheck_684_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v_x_675_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_684_;
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
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_683_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_682_; 
v___x_682_ = lean_task_pure(v___x_681_);
return v___x_682_;
}
}
}
else
{
lean_object* v_a_685_; lean_object* v___x_686_; 
v_a_685_ = lean_ctor_get(v_x_675_, 0);
lean_inc(v_a_685_);
lean_dec_ref_known(v_x_675_, 1);
v___x_686_ = lean_apply_1(v_f_674_, v_a_685_);
return v___x_686_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bind___redArg(lean_object* v_x_687_, lean_object* v_f_688_, lean_object* v_prio_689_, uint8_t v_sync_690_){
_start:
{
lean_object* v___f_691_; lean_object* v___x_692_; 
v___f_691_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_691_, 0, v_f_688_);
v___x_692_ = lean_task_bind(v_x_687_, v___f_691_, v_prio_689_, v_sync_690_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bind___redArg___boxed(lean_object* v_x_693_, lean_object* v_f_694_, lean_object* v_prio_695_, lean_object* v_sync_696_){
_start:
{
uint8_t v_sync_boxed_697_; lean_object* v_res_698_; 
v_sync_boxed_697_ = lean_unbox(v_sync_696_);
v_res_698_ = l_Std_Async_AsyncTask_bind___redArg(v_x_693_, v_f_694_, v_prio_695_, v_sync_boxed_697_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bind(lean_object* v_00_u03b1_699_, lean_object* v_00_u03b2_700_, lean_object* v_x_701_, lean_object* v_f_702_, lean_object* v_prio_703_, uint8_t v_sync_704_){
_start:
{
lean_object* v___f_705_; lean_object* v___x_706_; 
v___f_705_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_705_, 0, v_f_702_);
v___x_706_ = lean_task_bind(v_x_701_, v___f_705_, v_prio_703_, v_sync_704_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bind___boxed(lean_object* v_00_u03b1_707_, lean_object* v_00_u03b2_708_, lean_object* v_x_709_, lean_object* v_f_710_, lean_object* v_prio_711_, lean_object* v_sync_712_){
_start:
{
uint8_t v_sync_boxed_713_; lean_object* v_res_714_; 
v_sync_boxed_713_ = lean_unbox(v_sync_712_);
v_res_714_ = l_Std_Async_AsyncTask_bind(v_00_u03b1_707_, v_00_u03b2_708_, v_x_709_, v_f_710_, v_prio_711_, v_sync_boxed_713_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_map___redArg___lam__0(lean_object* v_f_715_, lean_object* v_x_716_){
_start:
{
if (lean_obj_tag(v_x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
lean_dec(v_f_715_);
v_a_717_ = lean_ctor_get(v_x_716_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v_x_716_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v_x_716_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v_x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_733_; 
v_a_725_ = lean_ctor_get(v_x_716_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v_x_716_);
if (v_isSharedCheck_733_ == 0)
{
v___x_727_ = v_x_716_;
v_isShared_728_ = v_isSharedCheck_733_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v_x_716_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_733_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_729_ = lean_apply_1(v_f_715_, v_a_725_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___x_729_);
v___x_731_ = v___x_727_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_map___redArg(lean_object* v_f_734_, lean_object* v_x_735_, lean_object* v_prio_736_, uint8_t v_sync_737_){
_start:
{
lean_object* v___f_738_; lean_object* v___x_739_; 
v___f_738_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_738_, 0, v_f_734_);
v___x_739_ = lean_task_map(v___f_738_, v_x_735_, v_prio_736_, v_sync_737_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_map___redArg___boxed(lean_object* v_f_740_, lean_object* v_x_741_, lean_object* v_prio_742_, lean_object* v_sync_743_){
_start:
{
uint8_t v_sync_boxed_744_; lean_object* v_res_745_; 
v_sync_boxed_744_ = lean_unbox(v_sync_743_);
v_res_745_ = l_Std_Async_AsyncTask_map___redArg(v_f_740_, v_x_741_, v_prio_742_, v_sync_boxed_744_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_map(lean_object* v_00_u03b1_746_, lean_object* v_00_u03b2_747_, lean_object* v_f_748_, lean_object* v_x_749_, lean_object* v_prio_750_, uint8_t v_sync_751_){
_start:
{
lean_object* v___f_752_; lean_object* v___x_753_; 
v___f_752_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_752_, 0, v_f_748_);
v___x_753_ = lean_task_map(v___f_752_, v_x_749_, v_prio_750_, v_sync_751_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_map___boxed(lean_object* v_00_u03b1_754_, lean_object* v_00_u03b2_755_, lean_object* v_f_756_, lean_object* v_x_757_, lean_object* v_prio_758_, lean_object* v_sync_759_){
_start:
{
uint8_t v_sync_boxed_760_; lean_object* v_res_761_; 
v_sync_boxed_760_ = lean_unbox(v_sync_759_);
v_res_761_ = l_Std_Async_AsyncTask_map(v_00_u03b1_754_, v_00_u03b2_755_, v_f_756_, v_x_757_, v_prio_758_, v_sync_boxed_760_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bindIO___redArg___lam__0(lean_object* v_f_762_, lean_object* v_a_763_){
_start:
{
lean_object* v_a_766_; 
if (lean_obj_tag(v_a_763_) == 0)
{
lean_object* v_a_769_; 
lean_dec_ref(v_f_762_);
v_a_769_ = lean_ctor_get(v_a_763_, 0);
lean_inc(v_a_769_);
lean_dec_ref_known(v_a_763_, 1);
v_a_766_ = v_a_769_;
goto v___jp_765_;
}
else
{
lean_object* v_a_770_; lean_object* v___x_771_; 
v_a_770_ = lean_ctor_get(v_a_763_, 0);
lean_inc(v_a_770_);
lean_dec_ref_known(v_a_763_, 1);
v___x_771_ = lean_apply_2(v_f_762_, v_a_770_, lean_box(0));
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_a_772_);
lean_dec_ref_known(v___x_771_, 1);
return v_a_772_;
}
else
{
lean_object* v_a_773_; 
v_a_773_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_a_773_);
lean_dec_ref_known(v___x_771_, 1);
v_a_766_ = v_a_773_;
goto v___jp_765_;
}
}
v___jp_765_:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_767_, 0, v_a_766_);
v___x_768_ = lean_task_pure(v___x_767_);
return v___x_768_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bindIO___redArg___lam__0___boxed(lean_object* v_f_774_, lean_object* v_a_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Std_Async_AsyncTask_bindIO___redArg___lam__0(v_f_774_, v_a_775_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bindIO___redArg(lean_object* v_x_778_, lean_object* v_f_779_, lean_object* v_prio_780_, uint8_t v_sync_781_){
_start:
{
lean_object* v___f_783_; lean_object* v___x_784_; 
v___f_783_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_bindIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_783_, 0, v_f_779_);
v___x_784_ = lean_io_bind_task(v_x_778_, v___f_783_, v_prio_780_, v_sync_781_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bindIO___redArg___boxed(lean_object* v_x_785_, lean_object* v_f_786_, lean_object* v_prio_787_, lean_object* v_sync_788_, lean_object* v_a_789_){
_start:
{
uint8_t v_sync_boxed_790_; lean_object* v_res_791_; 
v_sync_boxed_790_ = lean_unbox(v_sync_788_);
v_res_791_ = l_Std_Async_AsyncTask_bindIO___redArg(v_x_785_, v_f_786_, v_prio_787_, v_sync_boxed_790_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bindIO(lean_object* v_00_u03b1_792_, lean_object* v_00_u03b2_793_, lean_object* v_x_794_, lean_object* v_f_795_, lean_object* v_prio_796_, uint8_t v_sync_797_){
_start:
{
lean_object* v___f_799_; lean_object* v___x_800_; 
v___f_799_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_bindIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_799_, 0, v_f_795_);
v___x_800_ = lean_io_bind_task(v_x_794_, v___f_799_, v_prio_796_, v_sync_797_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bindIO___boxed(lean_object* v_00_u03b1_801_, lean_object* v_00_u03b2_802_, lean_object* v_x_803_, lean_object* v_f_804_, lean_object* v_prio_805_, lean_object* v_sync_806_, lean_object* v_a_807_){
_start:
{
uint8_t v_sync_boxed_808_; lean_object* v_res_809_; 
v_sync_boxed_808_ = lean_unbox(v_sync_806_);
v_res_809_ = l_Std_Async_AsyncTask_bindIO(v_00_u03b1_801_, v_00_u03b2_802_, v_x_803_, v_f_804_, v_prio_805_, v_sync_boxed_808_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapTaskIO___redArg(lean_object* v_f_810_, lean_object* v_x_811_, lean_object* v_prio_812_, uint8_t v_sync_813_){
_start:
{
lean_object* v___f_815_; lean_object* v___x_816_; 
v___f_815_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_mapIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_815_, 0, v_f_810_);
v___x_816_ = lean_io_map_task(v___f_815_, v_x_811_, v_prio_812_, v_sync_813_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapTaskIO___redArg___boxed(lean_object* v_f_817_, lean_object* v_x_818_, lean_object* v_prio_819_, lean_object* v_sync_820_, lean_object* v_a_821_){
_start:
{
uint8_t v_sync_boxed_822_; lean_object* v_res_823_; 
v_sync_boxed_822_ = lean_unbox(v_sync_820_);
v_res_823_ = l_Std_Async_AsyncTask_mapTaskIO___redArg(v_f_817_, v_x_818_, v_prio_819_, v_sync_boxed_822_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapTaskIO(lean_object* v_00_u03b1_824_, lean_object* v_00_u03b2_825_, lean_object* v_f_826_, lean_object* v_x_827_, lean_object* v_prio_828_, uint8_t v_sync_829_){
_start:
{
lean_object* v___f_831_; lean_object* v___x_832_; 
v___f_831_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_mapIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_831_, 0, v_f_826_);
v___x_832_ = lean_io_map_task(v___f_831_, v_x_827_, v_prio_828_, v_sync_829_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapTaskIO___boxed(lean_object* v_00_u03b1_833_, lean_object* v_00_u03b2_834_, lean_object* v_f_835_, lean_object* v_x_836_, lean_object* v_prio_837_, lean_object* v_sync_838_, lean_object* v_a_839_){
_start:
{
uint8_t v_sync_boxed_840_; lean_object* v_res_841_; 
v_sync_boxed_840_ = lean_unbox(v_sync_838_);
v_res_841_ = l_Std_Async_AsyncTask_mapTaskIO(v_00_u03b1_833_, v_00_u03b2_834_, v_f_835_, v_x_836_, v_prio_837_, v_sync_boxed_840_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_block___redArg(lean_object* v_x_842_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = lean_task_get_own(v_x_842_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_844_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_844_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set_tag(v___x_847_, 1);
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
v_a_853_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_844_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_844_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
lean_ctor_set_tag(v___x_855_, 0);
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_block___redArg___boxed(lean_object* v_x_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Std_Async_AsyncTask_block___redArg(v_x_861_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_block(lean_object* v_00_u03b1_864_, lean_object* v_x_865_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Std_Async_AsyncTask_block___redArg(v_x_865_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_block___boxed(lean_object* v_00_u03b1_868_, lean_object* v_x_869_, lean_object* v_a_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Std_Async_AsyncTask_block(v_00_u03b1_868_, v_x_869_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPromise___redArg___lam__0(lean_object* v_error_872_, lean_object* v_x_873_){
_start:
{
if (lean_obj_tag(v_x_873_) == 0)
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = lean_mk_io_user_error(v_error_872_);
v___x_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
return v___x_875_;
}
else
{
lean_object* v_val_876_; 
lean_dec_ref(v_error_872_);
v_val_876_ = lean_ctor_get(v_x_873_, 0);
lean_inc(v_val_876_);
return v_val_876_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPromise___redArg___lam__0___boxed(lean_object* v_error_877_, lean_object* v_x_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Std_Async_AsyncTask_ofPromise___redArg___lam__0(v_error_877_, v_x_878_);
lean_dec(v_x_878_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPromise___redArg(lean_object* v_x_880_, lean_object* v_error_881_){
_start:
{
lean_object* v___f_882_; lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; lean_object* v___x_886_; 
v___f_882_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPromise___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_882_, 0, v_error_881_);
v___x_883_ = lean_io_promise_result_opt(v_x_880_);
v___x_884_ = lean_unsigned_to_nat(0u);
v___x_885_ = 0;
v___x_886_ = lean_task_map(v___f_882_, v___x_883_, v___x_884_, v___x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPromise___redArg___boxed(lean_object* v_x_887_, lean_object* v_error_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Std_Async_AsyncTask_ofPromise___redArg(v_x_887_, v_error_888_);
lean_dec(v_x_887_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPromise(lean_object* v_00_u03b1_890_, lean_object* v_x_891_, lean_object* v_error_892_){
_start:
{
lean_object* v___f_893_; lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; lean_object* v___x_897_; 
v___f_893_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPromise___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_893_, 0, v_error_892_);
v___x_894_ = lean_io_promise_result_opt(v_x_891_);
v___x_895_ = lean_unsigned_to_nat(0u);
v___x_896_ = 0;
v___x_897_ = lean_task_map(v___f_893_, v___x_894_, v___x_895_, v___x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPromise___boxed(lean_object* v_00_u03b1_898_, lean_object* v_x_899_, lean_object* v_error_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Std_Async_AsyncTask_ofPromise(v_00_u03b1_898_, v_x_899_, v_error_900_);
lean_dec(v_x_899_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPurePromise___redArg___lam__0(lean_object* v_error_902_, lean_object* v_x_903_){
_start:
{
if (lean_obj_tag(v_x_903_) == 0)
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_mk_io_user_error(v_error_902_);
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
return v___x_905_;
}
else
{
lean_object* v_val_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
lean_dec_ref(v_error_902_);
v_val_906_ = lean_ctor_get(v_x_903_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v_x_903_);
if (v_isSharedCheck_913_ == 0)
{
v___x_908_ = v_x_903_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_val_906_);
lean_dec(v_x_903_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_val_906_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPurePromise___redArg(lean_object* v_x_914_, lean_object* v_error_915_){
_start:
{
lean_object* v___f_916_; lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; lean_object* v___x_920_; 
v___f_916_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPurePromise___redArg___lam__0), 2, 1);
lean_closure_set(v___f_916_, 0, v_error_915_);
v___x_917_ = lean_io_promise_result_opt(v_x_914_);
v___x_918_ = lean_unsigned_to_nat(0u);
v___x_919_ = 1;
v___x_920_ = lean_task_map(v___f_916_, v___x_917_, v___x_918_, v___x_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPurePromise___redArg___boxed(lean_object* v_x_921_, lean_object* v_error_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Std_Async_AsyncTask_ofPurePromise___redArg(v_x_921_, v_error_922_);
lean_dec(v_x_921_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPurePromise(lean_object* v_00_u03b1_924_, lean_object* v_x_925_, lean_object* v_error_926_){
_start:
{
lean_object* v___f_927_; lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; lean_object* v___x_931_; 
v___f_927_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPurePromise___redArg___lam__0), 2, 1);
lean_closure_set(v___f_927_, 0, v_error_926_);
v___x_928_ = lean_io_promise_result_opt(v_x_925_);
v___x_929_ = lean_unsigned_to_nat(0u);
v___x_930_ = 1;
v___x_931_ = lean_task_map(v___f_927_, v___x_928_, v___x_929_, v___x_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPurePromise___boxed(lean_object* v_00_u03b1_932_, lean_object* v_x_933_, lean_object* v_error_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Std_Async_AsyncTask_ofPurePromise(v_00_u03b1_932_, v_x_933_, v_error_934_);
lean_dec(v_x_933_);
return v_res_935_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_AsyncTask_getState___redArg(lean_object* v_x_936_){
_start:
{
uint8_t v___x_938_; 
v___x_938_ = lean_io_get_task_state(v_x_936_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_getState___redArg___boxed(lean_object* v_x_939_, lean_object* v_a_940_){
_start:
{
uint8_t v_res_941_; lean_object* v_r_942_; 
v_res_941_ = l_Std_Async_AsyncTask_getState___redArg(v_x_939_);
lean_dec_ref(v_x_939_);
v_r_942_ = lean_box(v_res_941_);
return v_r_942_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_AsyncTask_getState(lean_object* v_00_u03b1_943_, lean_object* v_x_944_){
_start:
{
uint8_t v___x_946_; 
v___x_946_ = lean_io_get_task_state(v_x_944_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_getState___boxed(lean_object* v_00_u03b1_947_, lean_object* v_x_948_, lean_object* v_a_949_){
_start:
{
uint8_t v_res_950_; lean_object* v_r_951_; 
v_res_950_ = l_Std_Async_AsyncTask_getState(v_00_u03b1_947_, v_x_948_);
lean_dec_ref(v_x_948_);
v_r_951_ = lean_box(v_res_950_);
return v_r_951_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorIdx___redArg(lean_object* v_x_952_){
_start:
{
if (lean_obj_tag(v_x_952_) == 0)
{
lean_object* v___x_953_; 
v___x_953_ = lean_unsigned_to_nat(0u);
return v___x_953_;
}
else
{
lean_object* v___x_954_; 
v___x_954_ = lean_unsigned_to_nat(1u);
return v___x_954_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorIdx___redArg___boxed(lean_object* v_x_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Std_Async_MaybeTask_ctorIdx___redArg(v_x_955_);
lean_dec_ref(v_x_955_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorIdx(lean_object* v_00_u03b1_957_, lean_object* v_x_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Std_Async_MaybeTask_ctorIdx___redArg(v_x_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorIdx___boxed(lean_object* v_00_u03b1_960_, lean_object* v_x_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Std_Async_MaybeTask_ctorIdx(v_00_u03b1_960_, v_x_961_);
lean_dec_ref(v_x_961_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorElim___redArg(lean_object* v_t_963_, lean_object* v_k_964_){
_start:
{
if (lean_obj_tag(v_t_963_) == 0)
{
lean_object* v_a_965_; lean_object* v___x_966_; 
v_a_965_ = lean_ctor_get(v_t_963_, 0);
lean_inc(v_a_965_);
lean_dec_ref_known(v_t_963_, 1);
v___x_966_ = lean_apply_1(v_k_964_, v_a_965_);
return v___x_966_;
}
else
{
lean_object* v_a_967_; lean_object* v___x_968_; 
v_a_967_ = lean_ctor_get(v_t_963_, 0);
lean_inc_ref(v_a_967_);
lean_dec_ref_known(v_t_963_, 1);
v___x_968_ = lean_apply_1(v_k_964_, v_a_967_);
return v___x_968_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorElim(lean_object* v_00_u03b1_969_, lean_object* v_motive_970_, lean_object* v_ctorIdx_971_, lean_object* v_t_972_, lean_object* v_h_973_, lean_object* v_k_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Std_Async_MaybeTask_ctorElim___redArg(v_t_972_, v_k_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorElim___boxed(lean_object* v_00_u03b1_976_, lean_object* v_motive_977_, lean_object* v_ctorIdx_978_, lean_object* v_t_979_, lean_object* v_h_980_, lean_object* v_k_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Std_Async_MaybeTask_ctorElim(v_00_u03b1_976_, v_motive_977_, v_ctorIdx_978_, v_t_979_, v_h_980_, v_k_981_);
lean_dec(v_ctorIdx_978_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_pure_elim___redArg(lean_object* v_t_983_, lean_object* v_pure_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Std_Async_MaybeTask_ctorElim___redArg(v_t_983_, v_pure_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_pure_elim(lean_object* v_00_u03b1_986_, lean_object* v_motive_987_, lean_object* v_t_988_, lean_object* v_h_989_, lean_object* v_pure_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Std_Async_MaybeTask_ctorElim___redArg(v_t_988_, v_pure_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ofTask_elim___redArg(lean_object* v_t_992_, lean_object* v_ofTask_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_Std_Async_MaybeTask_ctorElim___redArg(v_t_992_, v_ofTask_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ofTask_elim(lean_object* v_00_u03b1_995_, lean_object* v_motive_996_, lean_object* v_t_997_, lean_object* v_h_998_, lean_object* v_ofTask_999_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Std_Async_MaybeTask_ctorElim___redArg(v_t_997_, v_ofTask_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_toTask___redArg(lean_object* v_x_1001_){
_start:
{
if (lean_obj_tag(v_x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1003_; 
v_a_1002_ = lean_ctor_get(v_x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v_x_1001_, 1);
v___x_1003_ = lean_task_pure(v_a_1002_);
return v___x_1003_;
}
else
{
lean_object* v_a_1004_; 
v_a_1004_ = lean_ctor_get(v_x_1001_, 0);
lean_inc_ref(v_a_1004_);
lean_dec_ref_known(v_x_1001_, 1);
return v_a_1004_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_toTask(lean_object* v_00_u03b1_1005_, lean_object* v_x_1006_){
_start:
{
if (lean_obj_tag(v_x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1008_; 
v_a_1007_ = lean_ctor_get(v_x_1006_, 0);
lean_inc(v_a_1007_);
lean_dec_ref_known(v_x_1006_, 1);
v___x_1008_ = lean_task_pure(v_a_1007_);
return v___x_1008_;
}
else
{
lean_object* v_a_1009_; 
v_a_1009_ = lean_ctor_get(v_x_1006_, 0);
lean_inc_ref(v_a_1009_);
lean_dec_ref_known(v_x_1006_, 1);
return v_a_1009_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_get___redArg(lean_object* v_x_1010_){
_start:
{
if (lean_obj_tag(v_x_1010_) == 0)
{
lean_object* v_a_1011_; 
v_a_1011_ = lean_ctor_get(v_x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref_known(v_x_1010_, 1);
return v_a_1011_;
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1013_; 
v_a_1012_ = lean_ctor_get(v_x_1010_, 0);
lean_inc_ref(v_a_1012_);
lean_dec_ref_known(v_x_1010_, 1);
v___x_1013_ = lean_task_get_own(v_a_1012_);
return v___x_1013_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_get(lean_object* v_00_u03b1_1014_, lean_object* v_x_1015_){
_start:
{
if (lean_obj_tag(v_x_1015_) == 0)
{
lean_object* v_a_1016_; 
v_a_1016_ = lean_ctor_get(v_x_1015_, 0);
lean_inc(v_a_1016_);
lean_dec_ref_known(v_x_1015_, 1);
return v_a_1016_;
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1018_; 
v_a_1017_ = lean_ctor_get(v_x_1015_, 0);
lean_inc_ref(v_a_1017_);
lean_dec_ref_known(v_x_1015_, 1);
v___x_1018_ = lean_task_get_own(v_a_1017_);
return v___x_1018_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_map___redArg(lean_object* v_f_1019_, lean_object* v_prio_1020_, uint8_t v_sync_1021_, lean_object* v_x_1022_){
_start:
{
if (lean_obj_tag(v_x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1031_; 
lean_dec(v_prio_1020_);
v_a_1023_ = lean_ctor_get(v_x_1022_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_x_1022_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1025_ = v_x_1022_;
v_isShared_1026_ = v_isSharedCheck_1031_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v_x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1031_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1027_ = lean_apply_1(v_f_1019_, v_a_1023_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1027_);
v___x_1029_ = v___x_1025_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1040_; 
v_a_1032_ = lean_ctor_get(v_x_1022_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_x_1022_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1034_ = v_x_1022_;
v_isShared_1035_ = v_isSharedCheck_1040_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v_x_1022_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1040_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1036_ = lean_task_map(v_f_1019_, v_a_1032_, v_prio_1020_, v_sync_1021_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 0, v___x_1036_);
v___x_1038_ = v___x_1034_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_map___redArg___boxed(lean_object* v_f_1041_, lean_object* v_prio_1042_, lean_object* v_sync_1043_, lean_object* v_x_1044_){
_start:
{
uint8_t v_sync_boxed_1045_; lean_object* v_res_1046_; 
v_sync_boxed_1045_ = lean_unbox(v_sync_1043_);
v_res_1046_ = l_Std_Async_MaybeTask_map___redArg(v_f_1041_, v_prio_1042_, v_sync_boxed_1045_, v_x_1044_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_map(lean_object* v_00_u03b1_1047_, lean_object* v_00_u03b2_1048_, lean_object* v_f_1049_, lean_object* v_prio_1050_, uint8_t v_sync_1051_, lean_object* v_x_1052_){
_start:
{
if (lean_obj_tag(v_x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1061_; 
lean_dec(v_prio_1050_);
v_a_1053_ = lean_ctor_get(v_x_1052_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_x_1052_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1055_ = v_x_1052_;
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v_x_1052_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1057_ = lean_apply_1(v_f_1049_, v_a_1053_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1057_);
v___x_1059_ = v___x_1055_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1070_; 
v_a_1062_ = lean_ctor_get(v_x_1052_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_x_1052_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1064_ = v_x_1052_;
v_isShared_1065_ = v_isSharedCheck_1070_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v_x_1052_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1070_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1066_ = lean_task_map(v_f_1049_, v_a_1062_, v_prio_1050_, v_sync_1051_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v___x_1066_);
v___x_1068_ = v___x_1064_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_map___boxed(lean_object* v_00_u03b1_1071_, lean_object* v_00_u03b2_1072_, lean_object* v_f_1073_, lean_object* v_prio_1074_, lean_object* v_sync_1075_, lean_object* v_x_1076_){
_start:
{
uint8_t v_sync_boxed_1077_; lean_object* v_res_1078_; 
v_sync_boxed_1077_ = lean_unbox(v_sync_1075_);
v_res_1078_ = l_Std_Async_MaybeTask_map(v_00_u03b1_1071_, v_00_u03b2_1072_, v_f_1073_, v_prio_1074_, v_sync_boxed_1077_, v_x_1076_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_bind___redArg___lam__0(lean_object* v_f_1079_, lean_object* v_x_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_apply_1(v_f_1079_, v_x_1080_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1083_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1082_);
lean_dec_ref_known(v___x_1081_, 1);
v___x_1083_ = lean_task_pure(v_a_1082_);
return v___x_1083_;
}
else
{
lean_object* v_a_1084_; 
v_a_1084_ = lean_ctor_get(v___x_1081_, 0);
lean_inc_ref(v_a_1084_);
lean_dec_ref_known(v___x_1081_, 1);
return v_a_1084_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_bind___redArg(lean_object* v_t_1085_, lean_object* v_f_1086_, lean_object* v_prio_1087_, uint8_t v_sync_1088_){
_start:
{
if (lean_obj_tag(v_t_1085_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1090_; 
lean_dec(v_prio_1087_);
v_a_1089_ = lean_ctor_get(v_t_1085_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v_t_1085_, 1);
v___x_1090_ = lean_apply_1(v_f_1086_, v_a_1089_);
return v___x_1090_;
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1100_; 
v_a_1091_ = lean_ctor_get(v_t_1085_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_t_1085_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1093_ = v_t_1085_;
v_isShared_1094_ = v_isSharedCheck_1100_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v_t_1085_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1100_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___f_1095_; lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___f_1095_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1095_, 0, v_f_1086_);
v___x_1096_ = lean_task_bind(v_a_1091_, v___f_1095_, v_prio_1087_, v_sync_1088_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 0, v___x_1096_);
v___x_1098_ = v___x_1093_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_bind___redArg___boxed(lean_object* v_t_1101_, lean_object* v_f_1102_, lean_object* v_prio_1103_, lean_object* v_sync_1104_){
_start:
{
uint8_t v_sync_boxed_1105_; lean_object* v_res_1106_; 
v_sync_boxed_1105_ = lean_unbox(v_sync_1104_);
v_res_1106_ = l_Std_Async_MaybeTask_bind___redArg(v_t_1101_, v_f_1102_, v_prio_1103_, v_sync_boxed_1105_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_bind(lean_object* v_00_u03b1_1107_, lean_object* v_00_u03b2_1108_, lean_object* v_t_1109_, lean_object* v_f_1110_, lean_object* v_prio_1111_, uint8_t v_sync_1112_){
_start:
{
if (lean_obj_tag(v_t_1109_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1114_; 
lean_dec(v_prio_1111_);
v_a_1113_ = lean_ctor_get(v_t_1109_, 0);
lean_inc(v_a_1113_);
lean_dec_ref_known(v_t_1109_, 1);
v___x_1114_ = lean_apply_1(v_f_1110_, v_a_1113_);
return v___x_1114_;
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1124_; 
v_a_1115_ = lean_ctor_get(v_t_1109_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_t_1109_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1117_ = v_t_1109_;
v_isShared_1118_ = v_isSharedCheck_1124_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v_t_1109_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1124_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___f_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___f_1119_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1119_, 0, v_f_1110_);
v___x_1120_ = lean_task_bind(v_a_1115_, v___f_1119_, v_prio_1111_, v_sync_1112_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1120_);
v___x_1122_ = v___x_1117_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_bind___boxed(lean_object* v_00_u03b1_1125_, lean_object* v_00_u03b2_1126_, lean_object* v_t_1127_, lean_object* v_f_1128_, lean_object* v_prio_1129_, lean_object* v_sync_1130_){
_start:
{
uint8_t v_sync_boxed_1131_; lean_object* v_res_1132_; 
v_sync_boxed_1131_ = lean_unbox(v_sync_1130_);
v_res_1132_ = l_Std_Async_MaybeTask_bind(v_00_u03b1_1125_, v_00_u03b2_1126_, v_t_1127_, v_f_1128_, v_prio_1129_, v_sync_boxed_1131_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_joinTask___redArg___lam__0(lean_object* v_x_1133_){
_start:
{
if (lean_obj_tag(v_x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1135_; 
v_a_1134_ = lean_ctor_get(v_x_1133_, 0);
lean_inc(v_a_1134_);
lean_dec_ref_known(v_x_1133_, 1);
v___x_1135_ = lean_task_pure(v_a_1134_);
return v___x_1135_;
}
else
{
lean_object* v_a_1136_; 
v_a_1136_ = lean_ctor_get(v_x_1133_, 0);
lean_inc_ref(v_a_1136_);
lean_dec_ref_known(v_x_1133_, 1);
return v_a_1136_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_joinTask___redArg(lean_object* v_t_1138_){
_start:
{
lean_object* v___f_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; lean_object* v___x_1142_; 
v___f_1139_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___x_1140_ = lean_unsigned_to_nat(0u);
v___x_1141_ = 1;
v___x_1142_ = lean_task_bind(v_t_1138_, v___f_1139_, v___x_1140_, v___x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_joinTask(lean_object* v_00_u03b1_1143_, lean_object* v_t_1144_){
_start:
{
lean_object* v___f_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; lean_object* v___x_1148_; 
v___f_1145_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___x_1146_ = lean_unsigned_to_nat(0u);
v___x_1147_ = 1;
v___x_1148_ = lean_task_bind(v_t_1144_, v___f_1145_, v___x_1146_, v___x_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instFunctor___lam__0(lean_object* v_00_u03b1_1149_, lean_object* v_00_u03b2_1150_, lean_object* v_f_1151_, lean_object* v___y_1152_){
_start:
{
if (lean_obj_tag(v___y_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1161_; 
v_a_1153_ = lean_ctor_get(v___y_1152_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___y_1152_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1155_ = v___y_1152_;
v_isShared_1156_ = v_isSharedCheck_1161_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___y_1152_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1161_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1157_; lean_object* v___x_1159_; 
v___x_1157_ = lean_apply_1(v_f_1151_, v_a_1153_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 0, v___x_1157_);
v___x_1159_ = v___x_1155_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1157_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
else
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1172_; 
v_a_1162_ = lean_ctor_get(v___y_1152_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___y_1152_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1164_ = v___y_1152_;
v_isShared_1165_ = v_isSharedCheck_1172_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___y_1152_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1172_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; uint8_t v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1170_; 
v___x_1166_ = lean_unsigned_to_nat(0u);
v___x_1167_ = 0;
v___x_1168_ = lean_task_map(v_f_1151_, v_a_1162_, v___x_1166_, v___x_1167_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v___x_1168_);
v___x_1170_ = v___x_1164_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instFunctor___lam__1(lean_object* v___f_1173_, lean_object* v_00_u03b1_1174_, lean_object* v_00_u03b2_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_1178_, 0, lean_box(0));
lean_closure_set(v___x_1178_, 1, lean_box(0));
lean_closure_set(v___x_1178_, 2, v___y_1176_);
v___x_1179_ = lean_apply_4(v___f_1173_, lean_box(0), lean_box(0), v___x_1178_, v___y_1177_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__0(lean_object* v_00_u03b1_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___y_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__1(lean_object* v_x_1190_, lean_object* v_y_1191_){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = lean_box(0);
v___x_1193_ = lean_apply_1(v_x_1190_, v___x_1192_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1202_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1196_ = v___x_1193_;
v_isShared_1197_ = v_isSharedCheck_1202_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1193_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1202_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1198_ = lean_apply_1(v_y_1191_, v_a_1194_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1198_);
v___x_1200_ = v___x_1196_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1213_; 
v_a_1203_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1205_ = v___x_1193_;
v_isShared_1206_ = v_isSharedCheck_1213_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1193_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1213_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; uint8_t v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = 0;
v___x_1209_ = lean_task_map(v_y_1191_, v_a_1203_, v___x_1207_, v___x_1208_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v___x_1209_);
v___x_1211_ = v___x_1205_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1209_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__2(lean_object* v___f_1214_, lean_object* v_x_1215_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = lean_apply_1(v___f_1214_, v_x_1215_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1218_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_a_1217_);
lean_dec_ref_known(v___x_1216_, 1);
v___x_1218_ = lean_task_pure(v_a_1217_);
return v___x_1218_;
}
else
{
lean_object* v_a_1219_; 
v_a_1219_ = lean_ctor_get(v___x_1216_, 0);
lean_inc_ref(v_a_1219_);
lean_dec_ref_known(v___x_1216_, 1);
return v_a_1219_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__3(lean_object* v_00_u03b1_1220_, lean_object* v_00_u03b2_1221_, lean_object* v_f_1222_, lean_object* v_x_1223_){
_start:
{
lean_object* v___f_1224_; 
lean_inc_ref(v_x_1223_);
v___f_1224_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_instMonad___lam__1), 2, 1);
lean_closure_set(v___f_1224_, 0, v_x_1223_);
if (lean_obj_tag(v_f_1222_) == 0)
{
lean_object* v_a_1225_; lean_object* v___x_1226_; 
lean_dec_ref(v___f_1224_);
v_a_1225_ = lean_ctor_get(v_f_1222_, 0);
lean_inc(v_a_1225_);
lean_dec_ref_known(v_f_1222_, 1);
v___x_1226_ = l_Std_Async_MaybeTask_instMonad___lam__1(v_x_1223_, v_a_1225_);
return v___x_1226_;
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1238_; 
lean_dec_ref(v_x_1223_);
v_a_1227_ = lean_ctor_get(v_f_1222_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_f_1222_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1229_ = v_f_1222_;
v_isShared_1230_ = v_isSharedCheck_1238_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v_f_1222_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1238_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___f_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1236_; 
v___f_1231_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_instMonad___lam__2), 2, 1);
lean_closure_set(v___f_1231_, 0, v___f_1224_);
v___x_1232_ = lean_unsigned_to_nat(0u);
v___x_1233_ = 0;
v___x_1234_ = lean_task_bind(v_a_1227_, v___f_1231_, v___x_1232_, v___x_1233_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v___x_1234_);
v___x_1236_ = v___x_1229_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1234_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__5(lean_object* v_00_u03b1_1239_, lean_object* v_00_u03b2_1240_, lean_object* v_t_1241_, lean_object* v_f_1242_){
_start:
{
if (lean_obj_tag(v_t_1241_) == 0)
{
lean_object* v_a_1243_; lean_object* v___x_1244_; 
v_a_1243_ = lean_ctor_get(v_t_1241_, 0);
lean_inc(v_a_1243_);
lean_dec_ref_known(v_t_1241_, 1);
v___x_1244_ = lean_apply_1(v_f_1242_, v_a_1243_);
return v___x_1244_;
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1256_; 
v_a_1245_ = lean_ctor_get(v_t_1241_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_t_1241_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1247_ = v_t_1241_;
v_isShared_1248_ = v_isSharedCheck_1256_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v_t_1241_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1256_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___f_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___f_1249_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1249_, 0, v_f_1242_);
v___x_1250_ = lean_unsigned_to_nat(0u);
v___x_1251_ = 0;
v___x_1252_ = lean_task_bind(v_a_1245_, v___f_1249_, v___x_1250_, v___x_1251_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1252_);
v___x_1254_ = v___x_1247_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__4(lean_object* v_a_1257_, lean_object* v_x_1258_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1259_, 0, v_a_1257_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__4___boxed(lean_object* v_a_1260_, lean_object* v_x_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Std_Async_MaybeTask_instMonad___lam__4(v_a_1260_, v_x_1261_);
lean_dec(v_x_1261_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__6(lean_object* v_y_1263_, lean_object* v___f_1264_, lean_object* v_a_1265_){
_start:
{
lean_object* v___f_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___f_1266_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_instMonad___lam__4___boxed), 2, 1);
lean_closure_set(v___f_1266_, 0, v_a_1265_);
v___x_1267_ = lean_box(0);
v___x_1268_ = lean_apply_1(v_y_1263_, v___x_1267_);
v___x_1269_ = lean_apply_4(v___f_1264_, lean_box(0), lean_box(0), v___x_1268_, v___f_1266_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__7(lean_object* v___f_1270_, lean_object* v_00_u03b1_1271_, lean_object* v_00_u03b2_1272_, lean_object* v_x_1273_, lean_object* v_y_1274_){
_start:
{
lean_object* v___f_1275_; lean_object* v___x_1276_; 
lean_inc_ref(v___f_1270_);
v___f_1275_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_instMonad___lam__6), 3, 2);
lean_closure_set(v___f_1275_, 0, v_y_1274_);
lean_closure_set(v___f_1275_, 1, v___f_1270_);
v___x_1276_ = lean_apply_4(v___f_1270_, lean_box(0), lean_box(0), v_x_1273_, v___f_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__8(lean_object* v_y_1277_, lean_object* v_x_1278_){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = lean_box(0);
v___x_1280_ = lean_apply_1(v_y_1277_, v___x_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__8___boxed(lean_object* v_y_1281_, lean_object* v_x_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Std_Async_MaybeTask_instMonad___lam__8(v_y_1281_, v_x_1282_);
lean_dec(v_x_1282_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__9(lean_object* v___f_1284_, lean_object* v_x_1285_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_apply_1(v___f_1284_, v_x_1285_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v___x_1288_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___x_1286_, 1);
v___x_1288_ = lean_task_pure(v_a_1287_);
return v___x_1288_;
}
else
{
lean_object* v_a_1289_; 
v_a_1289_ = lean_ctor_get(v___x_1286_, 0);
lean_inc_ref(v_a_1289_);
lean_dec_ref_known(v___x_1286_, 1);
return v_a_1289_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__10(lean_object* v_00_u03b1_1290_, lean_object* v_00_u03b2_1291_, lean_object* v_x_1292_, lean_object* v_y_1293_){
_start:
{
lean_object* v___f_1294_; 
lean_inc_ref(v_y_1293_);
v___f_1294_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_instMonad___lam__8___boxed), 2, 1);
lean_closure_set(v___f_1294_, 0, v_y_1293_);
if (lean_obj_tag(v_x_1292_) == 0)
{
lean_object* v_a_1295_; lean_object* v___x_1296_; 
lean_dec_ref(v___f_1294_);
v_a_1295_ = lean_ctor_get(v_x_1292_, 0);
lean_inc(v_a_1295_);
lean_dec_ref_known(v_x_1292_, 1);
v___x_1296_ = l_Std_Async_MaybeTask_instMonad___lam__8(v_y_1293_, v_a_1295_);
lean_dec(v_a_1295_);
return v___x_1296_;
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1308_; 
lean_dec_ref(v_y_1293_);
v_a_1297_ = lean_ctor_get(v_x_1292_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v_x_1292_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1299_ = v_x_1292_;
v_isShared_1300_ = v_isSharedCheck_1308_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v_x_1292_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1308_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___f_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1306_; 
v___f_1301_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_instMonad___lam__9), 2, 1);
lean_closure_set(v___f_1301_, 0, v___f_1294_);
v___x_1302_ = lean_unsigned_to_nat(0u);
v___x_1303_ = 0;
v___x_1304_ = lean_task_bind(v_a_1297_, v___f_1301_, v___x_1302_, v___x_1303_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v___x_1304_);
v___x_1306_ = v___x_1299_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_mk___redArg(lean_object* v_x_1325_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_apply_1(v_x_1325_, lean_box(0));
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_mk___redArg___boxed(lean_object* v_x_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Std_Async_BaseAsync_mk___redArg(v_x_1328_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_mk(lean_object* v_00_u03b1_1331_, lean_object* v_x_1332_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_apply_1(v_x_1332_, lean_box(0));
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_mk___boxed(lean_object* v_00_u03b1_1335_, lean_object* v_x_1336_, lean_object* v_a_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Std_Async_BaseAsync_mk(v_00_u03b1_1335_, v_x_1336_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toRawBaseIO___redArg(lean_object* v_x_1339_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_apply_1(v_x_1339_, lean_box(0));
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toRawBaseIO___redArg___boxed(lean_object* v_x_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Std_Async_BaseAsync_toRawBaseIO___redArg(v_x_1342_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toRawBaseIO(lean_object* v_00_u03b1_1345_, lean_object* v_x_1346_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = lean_apply_1(v_x_1346_, lean_box(0));
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toRawBaseIO___boxed(lean_object* v_00_u03b1_1349_, lean_object* v_x_1350_, lean_object* v_a_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Std_Async_BaseAsync_toRawBaseIO(v_00_u03b1_1349_, v_x_1350_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toBaseIO___redArg(lean_object* v_x_1353_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_apply_1(v_x_1353_, lean_box(0));
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v___x_1357_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_a_1356_);
lean_dec_ref_known(v___x_1355_, 1);
v___x_1357_ = lean_task_pure(v_a_1356_);
return v___x_1357_;
}
else
{
lean_object* v_a_1358_; 
v_a_1358_ = lean_ctor_get(v___x_1355_, 0);
lean_inc_ref(v_a_1358_);
lean_dec_ref_known(v___x_1355_, 1);
return v_a_1358_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toBaseIO___redArg___boxed(lean_object* v_x_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Std_Async_BaseAsync_toBaseIO___redArg(v_x_1359_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toBaseIO(lean_object* v_00_u03b1_1362_, lean_object* v_x_1363_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = lean_apply_1(v_x_1363_, lean_box(0));
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1367_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1366_);
lean_dec_ref_known(v___x_1365_, 1);
v___x_1367_ = lean_task_pure(v_a_1366_);
return v___x_1367_;
}
else
{
lean_object* v_a_1368_; 
v_a_1368_ = lean_ctor_get(v___x_1365_, 0);
lean_inc_ref(v_a_1368_);
lean_dec_ref_known(v___x_1365_, 1);
return v_a_1368_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toBaseIO___boxed(lean_object* v_00_u03b1_1369_, lean_object* v_x_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Std_Async_BaseAsync_toBaseIO(v_00_u03b1_1369_, v_x_1370_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofTask___redArg(lean_object* v_x_1373_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1375_, 0, v_x_1373_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofTask___redArg___boxed(lean_object* v_x_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_Std_Async_BaseAsync_ofTask___redArg(v_x_1376_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofTask(lean_object* v_00_u03b1_1379_, lean_object* v_x_1380_){
_start:
{
lean_object* v___x_1382_; 
v___x_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1382_, 0, v_x_1380_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofTask___boxed(lean_object* v_00_u03b1_1383_, lean_object* v_x_1384_, lean_object* v_a_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_Std_Async_BaseAsync_ofTask(v_00_u03b1_1383_, v_x_1384_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_pure___redArg(lean_object* v_a_1387_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v_a_1387_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_pure___redArg___boxed(lean_object* v_a_1390_, lean_object* v_a_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Std_Async_BaseAsync_pure___redArg(v_a_1390_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_pure(lean_object* v_00_u03b1_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1396_, 0, v_a_1394_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_pure___boxed(lean_object* v_00_u03b1_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Std_Async_BaseAsync_pure(v_00_u03b1_1397_, v_a_1398_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_map___redArg(lean_object* v_f_1401_, lean_object* v_self_1402_, lean_object* v_prio_1403_, uint8_t v_sync_1404_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = lean_apply_1(v_self_1402_, lean_box(0));
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1415_; 
lean_dec(v_prio_1403_);
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1415_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1415_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1411_ = lean_apply_1(v_f_1401_, v_a_1407_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1411_);
v___x_1413_ = v___x_1409_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1424_; 
v_a_1416_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1418_ = v___x_1406_;
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1406_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1420_ = lean_task_map(v_f_1401_, v_a_1416_, v_prio_1403_, v_sync_1404_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1420_);
v___x_1422_ = v___x_1418_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_map___redArg___boxed(lean_object* v_f_1425_, lean_object* v_self_1426_, lean_object* v_prio_1427_, lean_object* v_sync_1428_, lean_object* v_a_1429_){
_start:
{
uint8_t v_sync_boxed_1430_; lean_object* v_res_1431_; 
v_sync_boxed_1430_ = lean_unbox(v_sync_1428_);
v_res_1431_ = l_Std_Async_BaseAsync_map___redArg(v_f_1425_, v_self_1426_, v_prio_1427_, v_sync_boxed_1430_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_map(lean_object* v_00_u03b1_1432_, lean_object* v_00_u03b2_1433_, lean_object* v_f_1434_, lean_object* v_self_1435_, lean_object* v_prio_1436_, uint8_t v_sync_1437_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = lean_apply_1(v_self_1435_, lean_box(0));
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1448_; 
lean_dec(v_prio_1436_);
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1442_ = v___x_1439_;
v_isShared_1443_ = v_isSharedCheck_1448_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1439_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1448_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1444_ = lean_apply_1(v_f_1434_, v_a_1440_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 0, v___x_1444_);
v___x_1446_ = v___x_1442_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1457_; 
v_a_1449_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1451_ = v___x_1439_;
v_isShared_1452_ = v_isSharedCheck_1457_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1439_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1457_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v___x_1455_; 
v___x_1453_ = lean_task_map(v_f_1434_, v_a_1449_, v_prio_1436_, v_sync_1437_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___x_1453_);
v___x_1455_ = v___x_1451_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1453_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_map___boxed(lean_object* v_00_u03b1_1458_, lean_object* v_00_u03b2_1459_, lean_object* v_f_1460_, lean_object* v_self_1461_, lean_object* v_prio_1462_, lean_object* v_sync_1463_, lean_object* v_a_1464_){
_start:
{
uint8_t v_sync_boxed_1465_; lean_object* v_res_1466_; 
v_sync_boxed_1465_ = lean_unbox(v_sync_1463_);
v_res_1466_ = l_Std_Async_BaseAsync_map(v_00_u03b1_1458_, v_00_u03b2_1459_, v_f_1460_, v_self_1461_, v_prio_1462_, v_sync_boxed_1465_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___lam__0(lean_object* v_f_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = lean_apply_2(v_f_1467_, v_a_1468_, lean_box(0));
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1472_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___x_1470_, 1);
v___x_1472_ = lean_task_pure(v_a_1471_);
return v___x_1472_;
}
else
{
lean_object* v_a_1473_; 
v_a_1473_ = lean_ctor_get(v___x_1470_, 0);
lean_inc_ref(v_a_1473_);
lean_dec_ref_known(v___x_1470_, 1);
return v_a_1473_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___lam__0___boxed(lean_object* v_f_1474_, lean_object* v_a_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___lam__0(v_f_1474_, v_a_1475_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(lean_object* v_prio_1478_, uint8_t v_sync_1479_, lean_object* v_t_1480_, lean_object* v_f_1481_){
_start:
{
if (lean_obj_tag(v_t_1480_) == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1484_; 
lean_dec(v_prio_1478_);
v_a_1483_ = lean_ctor_get(v_t_1480_, 0);
lean_inc(v_a_1483_);
lean_dec_ref_known(v_t_1480_, 1);
v___x_1484_ = lean_apply_2(v_f_1481_, v_a_1483_, lean_box(0));
return v___x_1484_;
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1494_; 
v_a_1485_ = lean_ctor_get(v_t_1480_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v_t_1480_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1487_ = v_t_1480_;
v_isShared_1488_ = v_isSharedCheck_1494_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v_t_1480_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1494_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___f_1489_; lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___f_1489_ = lean_alloc_closure((void*)(l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1489_, 0, v_f_1481_);
v___x_1490_ = lean_io_bind_task(v_a_1485_, v___f_1489_, v_prio_1478_, v_sync_1479_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 0, v___x_1490_);
v___x_1492_ = v___x_1487_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___boxed(lean_object* v_prio_1495_, lean_object* v_sync_1496_, lean_object* v_t_1497_, lean_object* v_f_1498_, lean_object* v_a_1499_){
_start:
{
uint8_t v_sync_boxed_1500_; lean_object* v_res_1501_; 
v_sync_boxed_1500_ = lean_unbox(v_sync_1496_);
v_res_1501_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_1495_, v_sync_boxed_1500_, v_t_1497_, v_f_1498_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object* v_00_u03b1_1502_, lean_object* v_00_u03b2_1503_, lean_object* v_prio_1504_, uint8_t v_sync_1505_, lean_object* v_t_1506_, lean_object* v_f_1507_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_1504_, v_sync_1505_, v_t_1506_, v_f_1507_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___boxed(lean_object* v_00_u03b1_1510_, lean_object* v_00_u03b2_1511_, lean_object* v_prio_1512_, lean_object* v_sync_1513_, lean_object* v_t_1514_, lean_object* v_f_1515_, lean_object* v_a_1516_){
_start:
{
uint8_t v_sync_boxed_1517_; lean_object* v_res_1518_; 
v_sync_boxed_1517_ = lean_unbox(v_sync_1513_);
v_res_1518_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(v_00_u03b1_1510_, v_00_u03b2_1511_, v_prio_1512_, v_sync_boxed_1517_, v_t_1514_, v_f_1515_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_bind___redArg(lean_object* v_self_1519_, lean_object* v_f_1520_, lean_object* v_prio_1521_, uint8_t v_sync_1522_){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1524_ = lean_apply_1(v_self_1519_, lean_box(0));
v___x_1525_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_1521_, v_sync_1522_, v___x_1524_, v_f_1520_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_bind___redArg___boxed(lean_object* v_self_1526_, lean_object* v_f_1527_, lean_object* v_prio_1528_, lean_object* v_sync_1529_, lean_object* v_a_1530_){
_start:
{
uint8_t v_sync_boxed_1531_; lean_object* v_res_1532_; 
v_sync_boxed_1531_ = lean_unbox(v_sync_1529_);
v_res_1532_ = l_Std_Async_BaseAsync_bind___redArg(v_self_1526_, v_f_1527_, v_prio_1528_, v_sync_boxed_1531_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_bind(lean_object* v_00_u03b1_1533_, lean_object* v_00_u03b2_1534_, lean_object* v_self_1535_, lean_object* v_f_1536_, lean_object* v_prio_1537_, uint8_t v_sync_1538_){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = lean_apply_1(v_self_1535_, lean_box(0));
v___x_1541_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_1537_, v_sync_1538_, v___x_1540_, v_f_1536_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_bind___boxed(lean_object* v_00_u03b1_1542_, lean_object* v_00_u03b2_1543_, lean_object* v_self_1544_, lean_object* v_f_1545_, lean_object* v_prio_1546_, lean_object* v_sync_1547_, lean_object* v_a_1548_){
_start:
{
uint8_t v_sync_boxed_1549_; lean_object* v_res_1550_; 
v_sync_boxed_1549_ = lean_unbox(v_sync_1547_);
v_res_1550_ = l_Std_Async_BaseAsync_bind(v_00_u03b1_1542_, v_00_u03b2_1543_, v_self_1544_, v_f_1545_, v_prio_1546_, v_sync_boxed_1549_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_lift___redArg(lean_object* v_x_1551_){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = lean_apply_1(v_x_1551_, lean_box(0));
v___x_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_lift___redArg___boxed(lean_object* v_x_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Std_Async_BaseAsync_lift___redArg(v_x_1555_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_lift(lean_object* v_00_u03b1_1558_, lean_object* v_x_1559_){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = lean_apply_1(v_x_1559_, lean_box(0));
v___x_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_lift___boxed(lean_object* v_00_u03b1_1563_, lean_object* v_x_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Std_Async_BaseAsync_lift(v_00_u03b1_1563_, v_x_1564_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_wait___redArg(lean_object* v_self_1567_){
_start:
{
lean_object* v_val_1570_; lean_object* v___x_1572_; 
v___x_1572_ = lean_apply_1(v_self_1567_, lean_box(0));
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1574_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_a_1573_);
lean_dec_ref_known(v___x_1572_, 1);
v___x_1574_ = lean_task_pure(v_a_1573_);
v_val_1570_ = v___x_1574_;
goto v___jp_1569_;
}
else
{
lean_object* v_a_1575_; 
v_a_1575_ = lean_ctor_get(v___x_1572_, 0);
lean_inc_ref(v_a_1575_);
lean_dec_ref_known(v___x_1572_, 1);
v_val_1570_ = v_a_1575_;
goto v___jp_1569_;
}
v___jp_1569_:
{
lean_object* v___x_1571_; 
v___x_1571_ = lean_task_get_own(v_val_1570_);
return v___x_1571_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_wait___redArg___boxed(lean_object* v_self_1576_, lean_object* v_a_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Std_Async_BaseAsync_wait___redArg(v_self_1576_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_wait(lean_object* v_00_u03b1_1579_, lean_object* v_self_1580_){
_start:
{
lean_object* v_val_1583_; lean_object* v___x_1585_; 
v___x_1585_ = lean_apply_1(v_self_1580_, lean_box(0));
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1587_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref_known(v___x_1585_, 1);
v___x_1587_ = lean_task_pure(v_a_1586_);
v_val_1583_ = v___x_1587_;
goto v___jp_1582_;
}
else
{
lean_object* v_a_1588_; 
v_a_1588_ = lean_ctor_get(v___x_1585_, 0);
lean_inc_ref(v_a_1588_);
lean_dec_ref_known(v___x_1585_, 1);
v_val_1583_ = v_a_1588_;
goto v___jp_1582_;
}
v___jp_1582_:
{
lean_object* v___x_1584_; 
v___x_1584_ = lean_task_get_own(v_val_1583_);
return v___x_1584_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_wait___boxed(lean_object* v_00_u03b1_1589_, lean_object* v_self_1590_, lean_object* v_a_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Std_Async_BaseAsync_wait(v_00_u03b1_1589_, v_self_1590_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_asTask___redArg(lean_object* v_x_1593_, lean_object* v_prio_1594_){
_start:
{
lean_object* v___f_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; uint8_t v___x_1600_; lean_object* v___x_1601_; 
v___f_1596_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___x_1597_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1597_, 0, lean_box(0));
lean_closure_set(v___x_1597_, 1, v_x_1593_);
v___x_1598_ = lean_io_as_task(v___x_1597_, v_prio_1594_);
v___x_1599_ = lean_unsigned_to_nat(0u);
v___x_1600_ = 1;
v___x_1601_ = lean_task_bind(v___x_1598_, v___f_1596_, v___x_1599_, v___x_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_asTask___redArg___boxed(lean_object* v_x_1602_, lean_object* v_prio_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Std_Async_BaseAsync_asTask___redArg(v_x_1602_, v_prio_1603_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_asTask(lean_object* v_00_u03b1_1606_, lean_object* v_x_1607_, lean_object* v_prio_1608_){
_start:
{
lean_object* v___f_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; lean_object* v___x_1615_; 
v___f_1610_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___x_1611_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1611_, 0, lean_box(0));
lean_closure_set(v___x_1611_, 1, v_x_1607_);
v___x_1612_ = lean_io_as_task(v___x_1611_, v_prio_1608_);
v___x_1613_ = lean_unsigned_to_nat(0u);
v___x_1614_ = 1;
v___x_1615_ = lean_task_bind(v___x_1612_, v___f_1610_, v___x_1613_, v___x_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_asTask___boxed(lean_object* v_00_u03b1_1616_, lean_object* v_x_1617_, lean_object* v_prio_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Std_Async_BaseAsync_asTask(v_00_u03b1_1616_, v_x_1617_, v_prio_1618_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_await___redArg(lean_object* v_t_1621_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1623_, 0, v_t_1621_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_await___redArg___boxed(lean_object* v_t_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Std_Async_BaseAsync_await___redArg(v_t_1624_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_await(lean_object* v_00_u03b1_1627_, lean_object* v_t_1628_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1630_, 0, v_t_1628_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_await___boxed(lean_object* v_00_u03b1_1631_, lean_object* v_t_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Std_Async_BaseAsync_await(v_00_u03b1_1631_, v_t_1632_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_async___redArg(lean_object* v_self_1635_, lean_object* v_prio_1636_){
_start:
{
lean_object* v___f_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; uint8_t v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___f_1638_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___x_1639_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1639_, 0, lean_box(0));
lean_closure_set(v___x_1639_, 1, v_self_1635_);
v___x_1640_ = lean_io_as_task(v___x_1639_, v_prio_1636_);
v___x_1641_ = lean_unsigned_to_nat(0u);
v___x_1642_ = 1;
v___x_1643_ = lean_task_bind(v___x_1640_, v___f_1638_, v___x_1641_, v___x_1642_);
v___x_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_async___redArg___boxed(lean_object* v_self_1645_, lean_object* v_prio_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Std_Async_BaseAsync_async___redArg(v_self_1645_, v_prio_1646_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_async(lean_object* v_00_u03b1_1649_, lean_object* v_self_1650_, lean_object* v_prio_1651_){
_start:
{
lean_object* v___f_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; uint8_t v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___f_1653_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___x_1654_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1654_, 0, lean_box(0));
lean_closure_set(v___x_1654_, 1, v_self_1650_);
v___x_1655_ = lean_io_as_task(v___x_1654_, v_prio_1651_);
v___x_1656_ = lean_unsigned_to_nat(0u);
v___x_1657_ = 1;
v___x_1658_ = lean_task_bind(v___x_1655_, v___f_1653_, v___x_1656_, v___x_1657_);
v___x_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_async___boxed(lean_object* v_00_u03b1_1660_, lean_object* v_self_1661_, lean_object* v_prio_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Std_Async_BaseAsync_async(v_00_u03b1_1660_, v_self_1661_, v_prio_1662_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instFunctor___lam__0(lean_object* v_00_u03b1_1665_, lean_object* v_00_u03b2_1666_, lean_object* v_f_1667_, lean_object* v_self_1668_){
_start:
{
lean_object* v___x_1670_; uint8_t v___x_1671_; lean_object* v___x_1672_; 
v___x_1670_ = lean_unsigned_to_nat(0u);
v___x_1671_ = 0;
v___x_1672_ = lean_apply_1(v_self_1668_, lean_box(0));
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1681_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1675_ = v___x_1672_;
v_isShared_1676_ = v_isSharedCheck_1681_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1672_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1681_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1677_ = lean_apply_1(v_f_1667_, v_a_1673_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 0, v___x_1677_);
v___x_1679_ = v___x_1675_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1690_; 
v_a_1682_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1684_ = v___x_1672_;
v_isShared_1685_ = v_isSharedCheck_1690_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1672_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1690_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1686_ = lean_task_map(v_f_1667_, v_a_1682_, v___x_1670_, v___x_1671_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 0, v___x_1686_);
v___x_1688_ = v___x_1684_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instFunctor___lam__0___boxed(lean_object* v_00_u03b1_1691_, lean_object* v_00_u03b2_1692_, lean_object* v_f_1693_, lean_object* v_self_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Std_Async_BaseAsync_instFunctor___lam__0(v_00_u03b1_1691_, v_00_u03b2_1692_, v_f_1693_, v_self_1694_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instFunctor___lam__1(lean_object* v___f_1697_, lean_object* v_00_u03b1_1698_, lean_object* v_00_u03b2_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_1703_, 0, lean_box(0));
lean_closure_set(v___x_1703_, 1, lean_box(0));
lean_closure_set(v___x_1703_, 2, v___y_1700_);
v___x_1704_ = lean_apply_5(v___f_1697_, lean_box(0), lean_box(0), v___x_1703_, v___y_1701_, lean_box(0));
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instFunctor___lam__1___boxed(lean_object* v___f_1705_, lean_object* v_00_u03b1_1706_, lean_object* v_00_u03b2_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Std_Async_BaseAsync_instFunctor___lam__1(v___f_1705_, v_00_u03b1_1706_, v_00_u03b2_1707_, v___y_1708_, v___y_1709_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__0(lean_object* v_x_1719_, lean_object* v_y_1720_){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; uint8_t v___x_1724_; lean_object* v___x_1725_; 
v___x_1722_ = lean_box(0);
v___x_1723_ = lean_unsigned_to_nat(0u);
v___x_1724_ = 0;
v___x_1725_ = lean_apply_2(v_x_1719_, v___x_1722_, lean_box(0));
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1734_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1728_ = v___x_1725_;
v_isShared_1729_ = v_isSharedCheck_1734_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1725_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1734_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; lean_object* v___x_1732_; 
v___x_1730_ = lean_apply_1(v_y_1720_, v_a_1726_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v___x_1730_);
v___x_1732_ = v___x_1728_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1743_; 
v_a_1735_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1737_ = v___x_1725_;
v_isShared_1738_ = v_isSharedCheck_1743_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1725_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1743_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1739_; lean_object* v___x_1741_; 
v___x_1739_ = lean_task_map(v_y_1720_, v_a_1735_, v___x_1723_, v___x_1724_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 0, v___x_1739_);
v___x_1741_ = v___x_1737_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1739_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__0___boxed(lean_object* v_x_1744_, lean_object* v_y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Std_Async_BaseAsync_instMonad___lam__0(v_x_1744_, v_y_1745_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__1(lean_object* v_00_u03b1_1748_, lean_object* v_00_u03b2_1749_, lean_object* v_f_1750_, lean_object* v_x_1751_){
_start:
{
lean_object* v___f_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___f_1753_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_instMonad___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1753_, 0, v_x_1751_);
v___x_1754_ = lean_unsigned_to_nat(0u);
v___x_1755_ = 0;
v___x_1756_ = lean_apply_1(v_f_1750_, lean_box(0));
v___x_1757_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_1754_, v___x_1755_, v___x_1756_, v___f_1753_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__1___boxed(lean_object* v_00_u03b1_1758_, lean_object* v_00_u03b2_1759_, lean_object* v_f_1760_, lean_object* v_x_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Std_Async_BaseAsync_instMonad___lam__1(v_00_u03b1_1758_, v_00_u03b2_1759_, v_f_1760_, v_x_1761_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__2(lean_object* v_00_u03b1_1764_, lean_object* v_00_u03b2_1765_, lean_object* v_self_1766_, lean_object* v_f_1767_){
_start:
{
lean_object* v___x_1769_; uint8_t v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1769_ = lean_unsigned_to_nat(0u);
v___x_1770_ = 0;
v___x_1771_ = lean_apply_1(v_self_1766_, lean_box(0));
v___x_1772_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_1769_, v___x_1770_, v___x_1771_, v_f_1767_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__2___boxed(lean_object* v_00_u03b1_1773_, lean_object* v_00_u03b2_1774_, lean_object* v_self_1775_, lean_object* v_f_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Std_Async_BaseAsync_instMonad___lam__2(v_00_u03b1_1773_, v_00_u03b2_1774_, v_self_1775_, v_f_1776_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__3(lean_object* v_a_1779_, lean_object* v_x_1780_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1782_, 0, v_a_1779_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__3___boxed(lean_object* v_a_1783_, lean_object* v_x_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Std_Async_BaseAsync_instMonad___lam__3(v_a_1783_, v_x_1784_);
lean_dec(v_x_1784_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__4(lean_object* v_y_1787_, lean_object* v___f_1788_, lean_object* v_a_1789_){
_start:
{
lean_object* v___f_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___f_1791_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_instMonad___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1791_, 0, v_a_1789_);
v___x_1792_ = lean_box(0);
v___x_1793_ = lean_apply_1(v_y_1787_, v___x_1792_);
v___x_1794_ = lean_apply_5(v___f_1788_, lean_box(0), lean_box(0), v___x_1793_, v___f_1791_, lean_box(0));
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__4___boxed(lean_object* v_y_1795_, lean_object* v___f_1796_, lean_object* v_a_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Std_Async_BaseAsync_instMonad___lam__4(v_y_1795_, v___f_1796_, v_a_1797_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__5(lean_object* v___f_1800_, lean_object* v_00_u03b1_1801_, lean_object* v_00_u03b2_1802_, lean_object* v_x_1803_, lean_object* v_y_1804_){
_start:
{
lean_object* v___f_1806_; lean_object* v___x_1807_; 
lean_inc_ref(v___f_1800_);
v___f_1806_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_instMonad___lam__4___boxed), 4, 2);
lean_closure_set(v___f_1806_, 0, v_y_1804_);
lean_closure_set(v___f_1806_, 1, v___f_1800_);
v___x_1807_ = lean_apply_5(v___f_1800_, lean_box(0), lean_box(0), v_x_1803_, v___f_1806_, lean_box(0));
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__5___boxed(lean_object* v___f_1808_, lean_object* v_00_u03b1_1809_, lean_object* v_00_u03b2_1810_, lean_object* v_x_1811_, lean_object* v_y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Std_Async_BaseAsync_instMonad___lam__5(v___f_1808_, v_00_u03b1_1809_, v_00_u03b2_1810_, v_x_1811_, v_y_1812_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__6(lean_object* v_y_1815_, lean_object* v_x_1816_){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1818_ = lean_box(0);
v___x_1819_ = lean_apply_2(v_y_1815_, v___x_1818_, lean_box(0));
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__6___boxed(lean_object* v_y_1820_, lean_object* v_x_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Std_Async_BaseAsync_instMonad___lam__6(v_y_1820_, v_x_1821_);
lean_dec(v_x_1821_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__7(lean_object* v_00_u03b1_1824_, lean_object* v_00_u03b2_1825_, lean_object* v_x_1826_, lean_object* v_y_1827_){
_start:
{
lean_object* v___f_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___f_1829_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_instMonad___lam__6___boxed), 3, 1);
lean_closure_set(v___f_1829_, 0, v_y_1827_);
v___x_1830_ = lean_unsigned_to_nat(0u);
v___x_1831_ = 0;
v___x_1832_ = lean_apply_1(v_x_1826_, lean_box(0));
v___x_1833_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_1830_, v___x_1831_, v___x_1832_, v___f_1829_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__7___boxed(lean_object* v_00_u03b1_1834_, lean_object* v_00_u03b2_1835_, lean_object* v_x_1836_, lean_object* v_y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Std_Async_BaseAsync_instMonad___lam__7(v_00_u03b1_1834_, v_00_u03b2_1835_, v_x_1836_, v_y_1837_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadAsyncTask___lam__1(lean_object* v___f_1860_, lean_object* v_00_u03b1_1861_, lean_object* v_t_1862_, lean_object* v_prio_1863_){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; uint8_t v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1865_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1865_, 0, lean_box(0));
lean_closure_set(v___x_1865_, 1, v_t_1862_);
v___x_1866_ = lean_io_as_task(v___x_1865_, v_prio_1863_);
v___x_1867_ = lean_unsigned_to_nat(0u);
v___x_1868_ = 1;
v___x_1869_ = lean_task_bind(v___x_1866_, v___f_1860_, v___x_1867_, v___x_1868_);
v___x_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadAsyncTask___lam__1___boxed(lean_object* v___f_1871_, lean_object* v_00_u03b1_1872_, lean_object* v_t_1873_, lean_object* v_prio_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Std_Async_BaseAsync_instMonadAsyncTask___lam__1(v___f_1871_, v_00_u03b1_1872_, v_t_1873_, v_prio_1874_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instInhabited___redArg(lean_object* v_inst_1880_){
_start:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1881_, 0, v_inst_1880_);
v___x_1882_ = lean_alloc_closure((void*)(l_instMonadBaseIO___aux__5___boxed), 3, 2);
lean_closure_set(v___x_1882_, 0, lean_box(0));
lean_closure_set(v___x_1882_, 1, v___x_1881_);
v___x_1883_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_mk___boxed), 3, 2);
lean_closure_set(v___x_1883_, 0, lean_box(0));
lean_closure_set(v___x_1883_, 1, v___x_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instInhabited(lean_object* v_00_u03b1_1884_, lean_object* v_inst_1885_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Std_Async_BaseAsync_instInhabited___redArg(v_inst_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadFinally___lam__0(lean_object* v_res_1887_, lean_object* v_snd_1888_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1889_, 0, v_res_1887_);
lean_ctor_set(v___x_1889_, 1, v_snd_1888_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadFinally___lam__1(lean_object* v_f_1890_, lean_object* v_res_1891_){
_start:
{
lean_object* v___f_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; uint8_t v___x_1896_; lean_object* v___x_1897_; 
lean_inc_n(v_res_1891_, 2);
v___f_1893_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_instMonadFinally___lam__0), 2, 1);
lean_closure_set(v___f_1893_, 0, v_res_1891_);
v___x_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1894_, 0, v_res_1891_);
v___x_1895_ = lean_unsigned_to_nat(0u);
v___x_1896_ = 0;
v___x_1897_ = lean_apply_2(v_f_1890_, v___x_1894_, lean_box(0));
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1906_; 
lean_dec_ref(v___f_1893_);
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1900_ = v___x_1897_;
v_isShared_1901_ = v_isSharedCheck_1906_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1897_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1906_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1902_; lean_object* v___x_1904_; 
v___x_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1902_, 0, v_res_1891_);
lean_ctor_set(v___x_1902_, 1, v_a_1898_);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 0, v___x_1902_);
v___x_1904_ = v___x_1900_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1915_; 
lean_dec(v_res_1891_);
v_a_1907_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1909_ = v___x_1897_;
v_isShared_1910_ = v_isSharedCheck_1915_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1897_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1915_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1911_; lean_object* v___x_1913_; 
v___x_1911_ = lean_task_map(v___f_1893_, v_a_1907_, v___x_1895_, v___x_1896_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v___x_1911_);
v___x_1913_ = v___x_1909_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadFinally___lam__1___boxed(lean_object* v_f_1916_, lean_object* v_res_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Std_Async_BaseAsync_instMonadFinally___lam__1(v_f_1916_, v_res_1917_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadFinally___lam__2(lean_object* v_00_u03b1_1920_, lean_object* v_00_u03b2_1921_, lean_object* v_x_1922_, lean_object* v_f_1923_){
_start:
{
lean_object* v___f_1925_; lean_object* v___x_1926_; uint8_t v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___f_1925_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_instMonadFinally___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1925_, 0, v_f_1923_);
v___x_1926_ = lean_unsigned_to_nat(0u);
v___x_1927_ = 0;
v___x_1928_ = lean_apply_1(v_x_1922_, lean_box(0));
v___x_1929_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_1926_, v___x_1927_, v___x_1928_, v___f_1925_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadFinally___lam__2___boxed(lean_object* v_00_u03b1_1930_, lean_object* v_00_u03b2_1931_, lean_object* v_x_1932_, lean_object* v_f_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Std_Async_BaseAsync_instMonadFinally___lam__2(v_00_u03b1_1930_, v_00_u03b2_1931_, v_x_1932_, v_f_1933_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofExcept___redArg(lean_object* v_except_1938_){
_start:
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
v_a_1940_ = lean_ctor_get(v_except_1938_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v_except_1938_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v_except_1938_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v_except_1938_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
lean_ctor_set_tag(v___x_1942_, 0);
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofExcept___redArg___boxed(lean_object* v_except_1948_, lean_object* v_a_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l_Std_Async_BaseAsync_ofExcept___redArg(v_except_1948_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofExcept(lean_object* v_00_u03b1_1951_, lean_object* v_except_1952_){
_start:
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
v_a_1954_ = lean_ctor_get(v_except_1952_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v_except_1952_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v_except_1952_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v_except_1952_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
lean_ctor_set_tag(v___x_1956_, 0);
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofExcept___boxed(lean_object* v_00_u03b1_1962_, lean_object* v_except_1963_, lean_object* v_a_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Std_Async_BaseAsync_ofExcept(v_00_u03b1_1962_, v_except_1963_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__1(lean_object* v_resultX_1966_, lean_object* v_resultY_1967_){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1969_, 0, v_resultX_1966_);
lean_ctor_set(v___x_1969_, 1, v_resultY_1967_);
v___x_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__1___boxed(lean_object* v_resultX_1971_, lean_object* v_resultY_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Std_Async_BaseAsync_concurrently___redArg___lam__1(v_resultX_1971_, v_resultY_1972_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__0(lean_object* v_taskY_1975_, lean_object* v_resultX_1976_){
_start:
{
lean_object* v___f_1978_; lean_object* v___x_1979_; uint8_t v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___f_1978_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrently___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1978_, 0, v_resultX_1976_);
v___x_1979_ = lean_unsigned_to_nat(0u);
v___x_1980_ = 0;
v___x_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1981_, 0, v_taskY_1975_);
v___x_1982_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_1979_, v___x_1980_, v___x_1981_, v___f_1978_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__0___boxed(lean_object* v_taskY_1983_, lean_object* v_resultX_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Std_Async_BaseAsync_concurrently___redArg___lam__0(v_taskY_1983_, v_resultX_1984_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__2(lean_object* v_taskX_1987_, lean_object* v_taskY_1988_){
_start:
{
lean_object* v___f_1990_; lean_object* v___x_1991_; uint8_t v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___f_1990_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrently___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1990_, 0, v_taskY_1988_);
v___x_1991_ = lean_unsigned_to_nat(0u);
v___x_1992_ = 0;
v___x_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1993_, 0, v_taskX_1987_);
v___x_1994_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_1991_, v___x_1992_, v___x_1993_, v___f_1990_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__2___boxed(lean_object* v_taskX_1995_, lean_object* v_taskY_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_Std_Async_BaseAsync_concurrently___redArg___lam__2(v_taskX_1995_, v_taskY_1996_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__3(lean_object* v_y_1999_, lean_object* v_prio_2000_, lean_object* v___f_2001_, lean_object* v_taskX_2002_){
_start:
{
lean_object* v___f_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; uint8_t v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___f_2004_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrently___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2004_, 0, v_taskX_2002_);
v___x_2005_ = lean_unsigned_to_nat(0u);
v___x_2006_ = 0;
v___x_2007_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2007_, 0, lean_box(0));
lean_closure_set(v___x_2007_, 1, v_y_1999_);
v___x_2008_ = lean_io_as_task(v___x_2007_, v_prio_2000_);
v___x_2009_ = 1;
v___x_2010_ = lean_task_bind(v___x_2008_, v___f_2001_, v___x_2005_, v___x_2009_);
v___x_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
v___x_2012_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2005_, v___x_2006_, v___x_2011_, v___f_2004_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__3___boxed(lean_object* v_y_2013_, lean_object* v_prio_2014_, lean_object* v___f_2015_, lean_object* v_taskX_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Std_Async_BaseAsync_concurrently___redArg___lam__3(v_y_2013_, v_prio_2014_, v___f_2015_, v_taskX_2016_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg(lean_object* v_x_2019_, lean_object* v_y_2020_, lean_object* v_prio_2021_){
_start:
{
lean_object* v___f_2023_; lean_object* v___f_2024_; lean_object* v___x_2025_; uint8_t v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; uint8_t v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___f_2023_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
lean_inc(v_prio_2021_);
v___f_2024_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrently___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2024_, 0, v_y_2020_);
lean_closure_set(v___f_2024_, 1, v_prio_2021_);
lean_closure_set(v___f_2024_, 2, v___f_2023_);
v___x_2025_ = lean_unsigned_to_nat(0u);
v___x_2026_ = 0;
v___x_2027_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2027_, 0, lean_box(0));
lean_closure_set(v___x_2027_, 1, v_x_2019_);
v___x_2028_ = lean_io_as_task(v___x_2027_, v_prio_2021_);
v___x_2029_ = 1;
v___x_2030_ = lean_task_bind(v___x_2028_, v___f_2023_, v___x_2025_, v___x_2029_);
v___x_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2030_);
v___x_2032_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2025_, v___x_2026_, v___x_2031_, v___f_2024_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___boxed(lean_object* v_x_2033_, lean_object* v_y_2034_, lean_object* v_prio_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Std_Async_BaseAsync_concurrently___redArg(v_x_2033_, v_y_2034_, v_prio_2035_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently(lean_object* v_00_u03b1_2038_, lean_object* v_00_u03b2_2039_, lean_object* v_x_2040_, lean_object* v_y_2041_, lean_object* v_prio_2042_){
_start:
{
lean_object* v___f_2044_; lean_object* v___f_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; uint8_t v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___f_2044_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
lean_inc(v_prio_2042_);
v___f_2045_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrently___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2045_, 0, v_y_2041_);
lean_closure_set(v___f_2045_, 1, v_prio_2042_);
lean_closure_set(v___f_2045_, 2, v___f_2044_);
v___x_2046_ = lean_unsigned_to_nat(0u);
v___x_2047_ = 0;
v___x_2048_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2048_, 0, lean_box(0));
lean_closure_set(v___x_2048_, 1, v_x_2040_);
v___x_2049_ = lean_io_as_task(v___x_2048_, v_prio_2042_);
v___x_2050_ = 1;
v___x_2051_ = lean_task_bind(v___x_2049_, v___f_2044_, v___x_2046_, v___x_2050_);
v___x_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
v___x_2053_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2046_, v___x_2047_, v___x_2052_, v___f_2045_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___boxed(lean_object* v_00_u03b1_2054_, lean_object* v_00_u03b2_2055_, lean_object* v_x_2056_, lean_object* v_y_2057_, lean_object* v_prio_2058_, lean_object* v_a_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Std_Async_BaseAsync_concurrently(v_00_u03b1_2054_, v_00_u03b2_2055_, v_x_2056_, v_y_2057_, v_prio_2058_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__2(lean_object* v_promise_2061_, lean_object* v_value_2062_){
_start:
{
lean_object* v___x_2064_; 
v___x_2064_ = lean_io_promise_resolve(v_value_2062_, v_promise_2061_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__2___boxed(lean_object* v_promise_2065_, lean_object* v_value_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Std_Async_BaseAsync_race___redArg___lam__2(v_promise_2065_, v_value_2066_);
lean_dec(v_promise_2065_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__0(lean_object* v_promise_2069_, lean_object* v_____r_2070_){
_start:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = l_IO_Promise_result_x21___redArg(v_promise_2069_);
v___x_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2072_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__0___boxed(lean_object* v_promise_2074_, lean_object* v_____r_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Std_Async_BaseAsync_race___redArg___lam__0(v_promise_2074_, v_____r_2075_);
lean_dec(v_promise_2074_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__1(lean_object* v_task_u2082_2078_, lean_object* v___x_2079_, lean_object* v___x_2080_, uint8_t v___x_2081_, lean_object* v___f_2082_, lean_object* v_____r_2083_){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
lean_inc(v___x_2080_);
v___x_2085_ = l_BaseIO_chainTask___redArg(v_task_u2082_2078_, v___x_2079_, v___x_2080_, v___x_2081_);
v___x_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
v___x_2087_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2080_, v___x_2081_, v___x_2086_, v___f_2082_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__1___boxed(lean_object* v_task_u2082_2088_, lean_object* v___x_2089_, lean_object* v___x_2090_, lean_object* v___x_2091_, lean_object* v___f_2092_, lean_object* v_____r_2093_, lean_object* v___y_2094_){
_start:
{
uint8_t v___x_624__boxed_2095_; lean_object* v_res_2096_; 
v___x_624__boxed_2095_ = lean_unbox(v___x_2091_);
v_res_2096_ = l_Std_Async_BaseAsync_race___redArg___lam__1(v_task_u2082_2088_, v___x_2089_, v___x_2090_, v___x_624__boxed_2095_, v___f_2092_, v_____r_2093_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__3(lean_object* v___f_2097_, lean_object* v___f_2098_, lean_object* v___f_2099_, lean_object* v_task_u2081_2100_, lean_object* v_task_u2082_2101_){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; lean_object* v___x_2107_; lean_object* v___f_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2103_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_2103_, 0, lean_box(0));
lean_closure_set(v___x_2103_, 1, lean_box(0));
lean_closure_set(v___x_2103_, 2, v___f_2097_);
lean_closure_set(v___x_2103_, 3, lean_box(0));
v___x_2104_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_2104_, 0, lean_box(0));
lean_closure_set(v___x_2104_, 1, lean_box(0));
lean_closure_set(v___x_2104_, 2, lean_box(0));
lean_closure_set(v___x_2104_, 3, v___x_2103_);
lean_closure_set(v___x_2104_, 4, v___f_2098_);
v___x_2105_ = lean_unsigned_to_nat(0u);
v___x_2106_ = 0;
v___x_2107_ = lean_box(v___x_2106_);
lean_inc_ref(v___x_2104_);
v___f_2108_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2108_, 0, v_task_u2082_2101_);
lean_closure_set(v___f_2108_, 1, v___x_2104_);
lean_closure_set(v___f_2108_, 2, v___x_2105_);
lean_closure_set(v___f_2108_, 3, v___x_2107_);
lean_closure_set(v___f_2108_, 4, v___f_2099_);
v___x_2109_ = l_BaseIO_chainTask___redArg(v_task_u2081_2100_, v___x_2104_, v___x_2105_, v___x_2106_);
v___x_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
v___x_2111_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2105_, v___x_2106_, v___x_2110_, v___f_2108_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__3___boxed(lean_object* v___f_2112_, lean_object* v___f_2113_, lean_object* v___f_2114_, lean_object* v_task_u2081_2115_, lean_object* v_task_u2082_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Std_Async_BaseAsync_race___redArg___lam__3(v___f_2112_, v___f_2113_, v___f_2114_, v_task_u2081_2115_, v_task_u2082_2116_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__4(lean_object* v___f_2119_, lean_object* v___f_2120_, lean_object* v___f_2121_, lean_object* v_y_2122_, lean_object* v_prio_2123_, lean_object* v___f_2124_, lean_object* v_task_u2081_2125_){
_start:
{
lean_object* v___f_2127_; lean_object* v___x_2128_; uint8_t v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; uint8_t v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___f_2127_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_2127_, 0, v___f_2119_);
lean_closure_set(v___f_2127_, 1, v___f_2120_);
lean_closure_set(v___f_2127_, 2, v___f_2121_);
lean_closure_set(v___f_2127_, 3, v_task_u2081_2125_);
v___x_2128_ = lean_unsigned_to_nat(0u);
v___x_2129_ = 0;
v___x_2130_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2130_, 0, lean_box(0));
lean_closure_set(v___x_2130_, 1, v_y_2122_);
v___x_2131_ = lean_io_as_task(v___x_2130_, v_prio_2123_);
v___x_2132_ = 1;
v___x_2133_ = lean_task_bind(v___x_2131_, v___f_2124_, v___x_2128_, v___x_2132_);
v___x_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
v___x_2135_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2128_, v___x_2129_, v___x_2134_, v___f_2127_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__4___boxed(lean_object* v___f_2136_, lean_object* v___f_2137_, lean_object* v___f_2138_, lean_object* v_y_2139_, lean_object* v_prio_2140_, lean_object* v___f_2141_, lean_object* v_task_u2081_2142_, lean_object* v___y_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Std_Async_BaseAsync_race___redArg___lam__4(v___f_2136_, v___f_2137_, v___f_2138_, v_y_2139_, v_prio_2140_, v___f_2141_, v_task_u2081_2142_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__5(lean_object* v___f_2145_, lean_object* v_y_2146_, lean_object* v_prio_2147_, lean_object* v___f_2148_, lean_object* v_x_2149_, lean_object* v___f_2150_, lean_object* v_promise_2151_){
_start:
{
lean_object* v___f_2153_; lean_object* v___f_2154_; lean_object* v___f_2155_; lean_object* v___x_2156_; uint8_t v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; uint8_t v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
lean_inc(v_promise_2151_);
v___f_2153_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2153_, 0, v_promise_2151_);
v___f_2154_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2154_, 0, v_promise_2151_);
lean_inc(v_prio_2147_);
v___f_2155_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__4___boxed), 8, 6);
lean_closure_set(v___f_2155_, 0, v___f_2145_);
lean_closure_set(v___f_2155_, 1, v___f_2153_);
lean_closure_set(v___f_2155_, 2, v___f_2154_);
lean_closure_set(v___f_2155_, 3, v_y_2146_);
lean_closure_set(v___f_2155_, 4, v_prio_2147_);
lean_closure_set(v___f_2155_, 5, v___f_2148_);
v___x_2156_ = lean_unsigned_to_nat(0u);
v___x_2157_ = 0;
v___x_2158_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2158_, 0, lean_box(0));
lean_closure_set(v___x_2158_, 1, v_x_2149_);
v___x_2159_ = lean_io_as_task(v___x_2158_, v_prio_2147_);
v___x_2160_ = 1;
v___x_2161_ = lean_task_bind(v___x_2159_, v___f_2150_, v___x_2156_, v___x_2160_);
v___x_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
v___x_2163_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2156_, v___x_2157_, v___x_2162_, v___f_2155_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__5___boxed(lean_object* v___f_2164_, lean_object* v_y_2165_, lean_object* v_prio_2166_, lean_object* v___f_2167_, lean_object* v_x_2168_, lean_object* v___f_2169_, lean_object* v_promise_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Std_Async_BaseAsync_race___redArg___lam__5(v___f_2164_, v_y_2165_, v_prio_2166_, v___f_2167_, v_x_2168_, v___f_2169_, v_promise_2170_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg(lean_object* v_x_2174_, lean_object* v_y_2175_, lean_object* v_prio_2176_){
_start:
{
lean_object* v___f_2178_; lean_object* v___f_2179_; lean_object* v___f_2180_; lean_object* v___x_2181_; uint8_t v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___f_2178_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___f_2179_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_2180_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__5___boxed), 8, 6);
lean_closure_set(v___f_2180_, 0, v___f_2179_);
lean_closure_set(v___f_2180_, 1, v_y_2175_);
lean_closure_set(v___f_2180_, 2, v_prio_2176_);
lean_closure_set(v___f_2180_, 3, v___f_2178_);
lean_closure_set(v___f_2180_, 4, v_x_2174_);
lean_closure_set(v___f_2180_, 5, v___f_2178_);
v___x_2181_ = lean_unsigned_to_nat(0u);
v___x_2182_ = 0;
v___x_2183_ = lean_io_promise_new();
v___x_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2183_);
v___x_2185_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2181_, v___x_2182_, v___x_2184_, v___f_2180_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___boxed(lean_object* v_x_2186_, lean_object* v_y_2187_, lean_object* v_prio_2188_, lean_object* v_a_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_Std_Async_BaseAsync_race___redArg(v_x_2186_, v_y_2187_, v_prio_2188_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race(lean_object* v_00_u03b1_2191_, lean_object* v_inst_2192_, lean_object* v_x_2193_, lean_object* v_y_2194_, lean_object* v_prio_2195_){
_start:
{
lean_object* v___f_2197_; lean_object* v___f_2198_; lean_object* v___f_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___f_2197_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___f_2198_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_2199_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__5___boxed), 8, 6);
lean_closure_set(v___f_2199_, 0, v___f_2198_);
lean_closure_set(v___f_2199_, 1, v_y_2194_);
lean_closure_set(v___f_2199_, 2, v_prio_2195_);
lean_closure_set(v___f_2199_, 3, v___f_2197_);
lean_closure_set(v___f_2199_, 4, v_x_2193_);
lean_closure_set(v___f_2199_, 5, v___f_2197_);
v___x_2200_ = lean_unsigned_to_nat(0u);
v___x_2201_ = 0;
v___x_2202_ = lean_io_promise_new();
v___x_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
v___x_2204_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2200_, v___x_2201_, v___x_2203_, v___f_2199_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___boxed(lean_object* v_00_u03b1_2205_, lean_object* v_inst_2206_, lean_object* v_x_2207_, lean_object* v_y_2208_, lean_object* v_prio_2209_, lean_object* v_a_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Std_Async_BaseAsync_race(v_00_u03b1_2205_, v_inst_2206_, v_x_2207_, v_y_2208_, v_prio_2209_);
lean_dec(v_inst_2206_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1(lean_object* v_prio_2212_, lean_object* v___f_2213_, lean_object* v_x_2214_){
_start:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; uint8_t v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2216_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2216_, 0, lean_box(0));
lean_closure_set(v___x_2216_, 1, v_x_2214_);
v___x_2217_ = lean_io_as_task(v___x_2216_, v_prio_2212_);
v___x_2218_ = lean_unsigned_to_nat(0u);
v___x_2219_ = 1;
v___x_2220_ = lean_task_bind(v___x_2217_, v___f_2213_, v___x_2218_, v___x_2219_);
v___x_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1___boxed(lean_object* v_prio_2222_, lean_object* v___f_2223_, lean_object* v_x_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1(v_prio_2222_, v___f_2223_, v_x_2224_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0(lean_object* v___x_2228_, lean_object* v_tasks_2229_){
_start:
{
lean_object* v___x_2231_; size_t v_sz_2232_; size_t v___x_2233_; lean_object* v___x_219__overap_2234_; lean_object* v___x_2235_; 
v___x_2231_ = ((lean_object*)(l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0___closed__0));
v_sz_2232_ = lean_array_size(v_tasks_2229_);
v___x_2233_ = ((size_t)0ULL);
v___x_219__overap_2234_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2228_, v___x_2231_, v_sz_2232_, v___x_2233_, v_tasks_2229_);
v___x_2235_ = lean_apply_1(v___x_219__overap_2234_, lean_box(0));
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0___boxed(lean_object* v___x_2236_, lean_object* v_tasks_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0(v___x_2236_, v_tasks_2237_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg(lean_object* v_xs_2242_, lean_object* v_prio_2243_){
_start:
{
lean_object* v___f_2245_; lean_object* v___f_2246_; lean_object* v___x_2247_; lean_object* v___f_2248_; lean_object* v___x_2249_; uint8_t v___x_2250_; size_t v_sz_2251_; size_t v___x_2252_; lean_object* v___x_167__overap_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___f_2245_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___f_2246_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2246_, 0, v_prio_2243_);
lean_closure_set(v___f_2246_, 1, v___f_2245_);
v___x_2247_ = ((lean_object*)(l_Std_Async_BaseAsync_instMonad));
v___f_2248_ = ((lean_object*)(l_Std_Async_BaseAsync_concurrentlyAll___redArg___closed__0));
v___x_2249_ = lean_unsigned_to_nat(0u);
v___x_2250_ = 0;
v_sz_2251_ = lean_array_size(v_xs_2242_);
v___x_2252_ = ((size_t)0ULL);
v___x_167__overap_2253_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2247_, v___f_2246_, v_sz_2251_, v___x_2252_, v_xs_2242_);
v___x_2254_ = lean_apply_1(v___x_167__overap_2253_, lean_box(0));
v___x_2255_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2249_, v___x_2250_, v___x_2254_, v___f_2248_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___boxed(lean_object* v_xs_2256_, lean_object* v_prio_2257_, lean_object* v_a_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Std_Async_BaseAsync_concurrentlyAll___redArg(v_xs_2256_, v_prio_2257_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll(lean_object* v_00_u03b1_2260_, lean_object* v_xs_2261_, lean_object* v_prio_2262_){
_start:
{
lean_object* v___f_2264_; lean_object* v___f_2265_; lean_object* v___x_2266_; lean_object* v___f_2267_; lean_object* v___x_2268_; uint8_t v___x_2269_; size_t v_sz_2270_; size_t v___x_2271_; lean_object* v___x_196__overap_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___f_2264_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___f_2265_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2265_, 0, v_prio_2262_);
lean_closure_set(v___f_2265_, 1, v___f_2264_);
v___x_2266_ = ((lean_object*)(l_Std_Async_BaseAsync_instMonad));
v___f_2267_ = ((lean_object*)(l_Std_Async_BaseAsync_concurrentlyAll___redArg___closed__0));
v___x_2268_ = lean_unsigned_to_nat(0u);
v___x_2269_ = 0;
v_sz_2270_ = lean_array_size(v_xs_2261_);
v___x_2271_ = ((size_t)0ULL);
v___x_196__overap_2272_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2266_, v___f_2265_, v_sz_2270_, v___x_2271_, v_xs_2261_);
v___x_2273_ = lean_apply_1(v___x_196__overap_2272_, lean_box(0));
v___x_2274_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2268_, v___x_2269_, v___x_2273_, v___f_2267_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___boxed(lean_object* v_00_u03b1_2275_, lean_object* v_xs_2276_, lean_object* v_prio_2277_, lean_object* v_a_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Std_Async_BaseAsync_concurrentlyAll(v_00_u03b1_2275_, v_xs_2276_, v_prio_2277_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__2(lean_object* v___f_2280_, lean_object* v___f_2281_, lean_object* v_task_u2081_2282_){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; uint8_t v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2284_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_2284_, 0, lean_box(0));
lean_closure_set(v___x_2284_, 1, lean_box(0));
lean_closure_set(v___x_2284_, 2, v___f_2280_);
lean_closure_set(v___x_2284_, 3, lean_box(0));
v___x_2285_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_2285_, 0, lean_box(0));
lean_closure_set(v___x_2285_, 1, lean_box(0));
lean_closure_set(v___x_2285_, 2, lean_box(0));
lean_closure_set(v___x_2285_, 3, v___x_2284_);
lean_closure_set(v___x_2285_, 4, v___f_2281_);
v___x_2286_ = lean_unsigned_to_nat(0u);
v___x_2287_ = 0;
v___x_2288_ = l_BaseIO_chainTask___redArg(v_task_u2081_2282_, v___x_2285_, v___x_2286_, v___x_2287_);
v___x_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__2___boxed(lean_object* v___f_2290_, lean_object* v___f_2291_, lean_object* v_task_u2081_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Std_Async_BaseAsync_raceAll___redArg___lam__2(v___f_2290_, v___f_2291_, v_task_u2081_2292_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__0(lean_object* v_prio_2295_, lean_object* v___f_2296_, lean_object* v___f_2297_, lean_object* v_x_2298_){
_start:
{
lean_object* v___x_2300_; uint8_t v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; uint8_t v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2300_ = lean_unsigned_to_nat(0u);
v___x_2301_ = 0;
v___x_2302_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2302_, 0, lean_box(0));
lean_closure_set(v___x_2302_, 1, v_x_2298_);
v___x_2303_ = lean_io_as_task(v___x_2302_, v_prio_2295_);
v___x_2304_ = 1;
v___x_2305_ = lean_task_bind(v___x_2303_, v___f_2296_, v___x_2300_, v___x_2304_);
v___x_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
v___x_2307_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2300_, v___x_2301_, v___x_2306_, v___f_2297_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__0___boxed(lean_object* v_prio_2308_, lean_object* v___f_2309_, lean_object* v___f_2310_, lean_object* v_x_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Std_Async_BaseAsync_raceAll___redArg___lam__0(v_prio_2308_, v___f_2309_, v___f_2310_, v_x_2311_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__3(lean_object* v___f_2314_, lean_object* v_prio_2315_, lean_object* v___f_2316_, lean_object* v_inst_2317_, lean_object* v_xs_2318_, lean_object* v_promise_2319_){
_start:
{
lean_object* v___f_2321_; lean_object* v___f_2322_; lean_object* v___f_2323_; lean_object* v___f_2324_; lean_object* v___x_2325_; uint8_t v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
lean_inc(v_promise_2319_);
v___f_2321_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2321_, 0, v_promise_2319_);
v___f_2322_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_raceAll___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2322_, 0, v___f_2314_);
lean_closure_set(v___f_2322_, 1, v___f_2321_);
v___f_2323_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_raceAll___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2323_, 0, v_prio_2315_);
lean_closure_set(v___f_2323_, 1, v___f_2316_);
lean_closure_set(v___f_2323_, 2, v___f_2322_);
v___f_2324_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2324_, 0, v_promise_2319_);
v___x_2325_ = lean_unsigned_to_nat(0u);
v___x_2326_ = 0;
v___x_2327_ = lean_apply_3(v_inst_2317_, v_xs_2318_, v___f_2323_, lean_box(0));
v___x_2328_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2325_, v___x_2326_, v___x_2327_, v___f_2324_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__3___boxed(lean_object* v___f_2329_, lean_object* v_prio_2330_, lean_object* v___f_2331_, lean_object* v_inst_2332_, lean_object* v_xs_2333_, lean_object* v_promise_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v_res_2336_; 
v_res_2336_ = l_Std_Async_BaseAsync_raceAll___redArg___lam__3(v___f_2329_, v_prio_2330_, v___f_2331_, v_inst_2332_, v_xs_2333_, v_promise_2334_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg(lean_object* v_inst_2337_, lean_object* v_xs_2338_, lean_object* v_prio_2339_){
_start:
{
lean_object* v___f_2341_; lean_object* v___f_2342_; lean_object* v___f_2343_; lean_object* v___x_2344_; uint8_t v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___f_2341_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___f_2342_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_2343_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_raceAll___redArg___lam__3___boxed), 7, 5);
lean_closure_set(v___f_2343_, 0, v___f_2342_);
lean_closure_set(v___f_2343_, 1, v_prio_2339_);
lean_closure_set(v___f_2343_, 2, v___f_2341_);
lean_closure_set(v___f_2343_, 3, v_inst_2337_);
lean_closure_set(v___f_2343_, 4, v_xs_2338_);
v___x_2344_ = lean_unsigned_to_nat(0u);
v___x_2345_ = 0;
v___x_2346_ = lean_io_promise_new();
v___x_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2346_);
v___x_2348_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2344_, v___x_2345_, v___x_2347_, v___f_2343_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___boxed(lean_object* v_inst_2349_, lean_object* v_xs_2350_, lean_object* v_prio_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Std_Async_BaseAsync_raceAll___redArg(v_inst_2349_, v_xs_2350_, v_prio_2351_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll(lean_object* v_00_u03b1_2354_, lean_object* v_c_2355_, lean_object* v_inst_2356_, lean_object* v_inst_2357_, lean_object* v_xs_2358_, lean_object* v_prio_2359_){
_start:
{
lean_object* v___f_2361_; lean_object* v___f_2362_; lean_object* v___f_2363_; lean_object* v___x_2364_; uint8_t v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___f_2361_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___f_2362_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_2363_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_raceAll___redArg___lam__3___boxed), 7, 5);
lean_closure_set(v___f_2363_, 0, v___f_2362_);
lean_closure_set(v___f_2363_, 1, v_prio_2359_);
lean_closure_set(v___f_2363_, 2, v___f_2361_);
lean_closure_set(v___f_2363_, 3, v_inst_2357_);
lean_closure_set(v___f_2363_, 4, v_xs_2358_);
v___x_2364_ = lean_unsigned_to_nat(0u);
v___x_2365_ = 0;
v___x_2366_ = lean_io_promise_new();
v___x_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
v___x_2368_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2364_, v___x_2365_, v___x_2367_, v___f_2363_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___boxed(lean_object* v_00_u03b1_2369_, lean_object* v_c_2370_, lean_object* v_inst_2371_, lean_object* v_inst_2372_, lean_object* v_xs_2373_, lean_object* v_prio_2374_, lean_object* v_a_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Std_Async_BaseAsync_raceAll(v_00_u03b1_2369_, v_c_2370_, v_inst_2371_, v_inst_2372_, v_xs_2373_, v_prio_2374_);
lean_dec(v_inst_2371_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toBaseIO___redArg(lean_object* v_x_2377_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = lean_apply_1(v_x_2377_, lean_box(0));
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; lean_object* v___x_2381_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
lean_inc(v_a_2380_);
lean_dec_ref_known(v___x_2379_, 1);
v___x_2381_ = lean_task_pure(v_a_2380_);
return v___x_2381_;
}
else
{
lean_object* v_a_2382_; 
v_a_2382_ = lean_ctor_get(v___x_2379_, 0);
lean_inc_ref(v_a_2382_);
lean_dec_ref_known(v___x_2379_, 1);
return v_a_2382_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toBaseIO___redArg___boxed(lean_object* v_x_2383_, lean_object* v_a_2384_){
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l_Std_Async_EAsync_toBaseIO___redArg(v_x_2383_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toBaseIO(lean_object* v_00_u03b5_2386_, lean_object* v_00_u03b1_2387_, lean_object* v_x_2388_){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = lean_apply_1(v_x_2388_, lean_box(0));
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v___x_2392_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
lean_dec_ref_known(v___x_2390_, 1);
v___x_2392_ = lean_task_pure(v_a_2391_);
return v___x_2392_;
}
else
{
lean_object* v_a_2393_; 
v_a_2393_ = lean_ctor_get(v___x_2390_, 0);
lean_inc_ref(v_a_2393_);
lean_dec_ref_known(v___x_2390_, 1);
return v_a_2393_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toBaseIO___boxed(lean_object* v_00_u03b5_2394_, lean_object* v_00_u03b1_2395_, lean_object* v_x_2396_, lean_object* v_a_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l_Std_Async_EAsync_toBaseIO(v_00_u03b5_2394_, v_00_u03b1_2395_, v_x_2396_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofTask___redArg(lean_object* v_x_2399_){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2401_, 0, v_x_2399_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofTask___redArg___boxed(lean_object* v_x_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Std_Async_EAsync_ofTask___redArg(v_x_2402_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofTask(lean_object* v_00_u03b5_2405_, lean_object* v_00_u03b1_2406_, lean_object* v_x_2407_){
_start:
{
lean_object* v___x_2409_; 
v___x_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2409_, 0, v_x_2407_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofTask___boxed(lean_object* v_00_u03b5_2410_, lean_object* v_00_u03b1_2411_, lean_object* v_x_2412_, lean_object* v_a_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Std_Async_EAsync_ofTask(v_00_u03b5_2410_, v_00_u03b1_2411_, v_x_2412_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toEIO___redArg(lean_object* v_x_2415_){
_start:
{
lean_object* v___x_2417_; 
v___x_2417_ = lean_apply_1(v_x_2415_, lean_box(0));
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2426_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2420_ = v___x_2417_;
v_isShared_2421_ = v_isSharedCheck_2426_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2417_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2426_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2422_; lean_object* v___x_2424_; 
v___x_2422_ = lean_task_pure(v_a_2418_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 0, v___x_2422_);
v___x_2424_ = v___x_2420_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2422_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
else
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
v_a_2427_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2417_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2417_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
lean_ctor_set_tag(v___x_2429_, 0);
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2427_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toEIO___redArg___boxed(lean_object* v_x_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Std_Async_EAsync_toEIO___redArg(v_x_2435_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toEIO(lean_object* v_00_u03b5_2438_, lean_object* v_00_u03b1_2439_, lean_object* v_x_2440_){
_start:
{
lean_object* v___x_2442_; 
v___x_2442_ = lean_apply_1(v_x_2440_, lean_box(0));
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2451_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2451_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2451_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2447_; lean_object* v___x_2449_; 
v___x_2447_ = lean_task_pure(v_a_2443_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 0, v___x_2447_);
v___x_2449_ = v___x_2445_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2447_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
v_a_2452_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2442_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2442_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
lean_ctor_set_tag(v___x_2454_, 0);
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toEIO___boxed(lean_object* v_00_u03b5_2460_, lean_object* v_00_u03b1_2461_, lean_object* v_x_2462_, lean_object* v_a_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l_Std_Async_EAsync_toEIO(v_00_u03b5_2460_, v_00_u03b1_2461_, v_x_2462_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofETask___redArg(lean_object* v_x_2465_){
_start:
{
lean_object* v___x_2467_; 
v___x_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2467_, 0, v_x_2465_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofETask___redArg___boxed(lean_object* v_x_2468_, lean_object* v_a_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l_Std_Async_EAsync_ofETask___redArg(v_x_2468_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofETask(lean_object* v_00_u03b5_2471_, lean_object* v_00_u03b1_2472_, lean_object* v_x_2473_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2475_, 0, v_x_2473_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofETask___boxed(lean_object* v_00_u03b5_2476_, lean_object* v_00_u03b1_2477_, lean_object* v_x_2478_, lean_object* v_a_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Std_Async_EAsync_ofETask(v_00_u03b5_2476_, v_00_u03b1_2477_, v_x_2478_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_pure___redArg(lean_object* v_a_2481_){
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
LEAN_EXPORT lean_object* l_Std_Async_EAsync_pure___redArg___boxed(lean_object* v_a_2485_, lean_object* v_a_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_Std_Async_EAsync_pure___redArg(v_a_2485_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_pure(lean_object* v_00_u03b1_2488_, lean_object* v_00_u03b5_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2492_, 0, v_a_2490_);
v___x_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_pure___boxed(lean_object* v_00_u03b1_2494_, lean_object* v_00_u03b5_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l_Std_Async_EAsync_pure(v_00_u03b1_2494_, v_00_u03b5_2495_, v_a_2496_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_map___redArg(lean_object* v_f_2499_, lean_object* v_self_2500_){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; uint8_t v___x_2504_; lean_object* v___x_2505_; lean_object* v___y_2507_; 
lean_inc(v_f_2499_);
v___x_2502_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_2502_, 0, lean_box(0));
lean_closure_set(v___x_2502_, 1, lean_box(0));
lean_closure_set(v___x_2502_, 2, lean_box(0));
lean_closure_set(v___x_2502_, 3, v_f_2499_);
v___x_2503_ = lean_unsigned_to_nat(0u);
v___x_2504_ = 0;
v___x_2505_ = lean_apply_1(v_self_2500_, lean_box(0));
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2509_; 
lean_dec_ref(v___x_2502_);
v_a_2509_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2509_);
lean_dec_ref_known(v___x_2505_, 1);
if (lean_obj_tag(v_a_2509_) == 0)
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2517_; 
lean_dec(v_f_2499_);
v_a_2510_ = lean_ctor_get(v_a_2509_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v_a_2509_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2512_ = v_a_2509_;
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v_a_2509_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2513_ == 0)
{
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
v___y_2507_ = v___x_2515_;
goto v___jp_2506_;
}
}
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2526_; 
v_a_2518_ = lean_ctor_get(v_a_2509_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v_a_2509_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2520_ = v_a_2509_;
v_isShared_2521_ = v_isSharedCheck_2526_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v_a_2509_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2526_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2522_; lean_object* v___x_2524_; 
v___x_2522_ = lean_apply_1(v_f_2499_, v_a_2518_);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v___x_2522_);
v___x_2524_ = v___x_2520_;
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
v___y_2507_ = v___x_2524_;
goto v___jp_2506_;
}
}
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2535_; 
lean_dec(v_f_2499_);
v_a_2527_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2529_ = v___x_2505_;
v_isShared_2530_ = v_isSharedCheck_2535_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2505_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2535_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2531_; lean_object* v___x_2533_; 
v___x_2531_ = lean_task_map(v___x_2502_, v_a_2527_, v___x_2503_, v___x_2504_);
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 0, v___x_2531_);
v___x_2533_ = v___x_2529_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2531_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
v___jp_2506_:
{
lean_object* v___x_2508_; 
v___x_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2508_, 0, v___y_2507_);
return v___x_2508_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_map___redArg___boxed(lean_object* v_f_2536_, lean_object* v_self_2537_, lean_object* v_a_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l_Std_Async_EAsync_map___redArg(v_f_2536_, v_self_2537_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_map(lean_object* v_00_u03b1_2540_, lean_object* v_00_u03b2_2541_, lean_object* v_00_u03b5_2542_, lean_object* v_f_2543_, lean_object* v_self_2544_){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; uint8_t v___x_2548_; lean_object* v___x_2549_; lean_object* v___y_2551_; 
lean_inc(v_f_2543_);
v___x_2546_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_2546_, 0, lean_box(0));
lean_closure_set(v___x_2546_, 1, lean_box(0));
lean_closure_set(v___x_2546_, 2, lean_box(0));
lean_closure_set(v___x_2546_, 3, v_f_2543_);
v___x_2547_ = lean_unsigned_to_nat(0u);
v___x_2548_ = 0;
v___x_2549_ = lean_apply_1(v_self_2544_, lean_box(0));
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2553_; 
lean_dec_ref(v___x_2546_);
v_a_2553_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_a_2553_);
lean_dec_ref_known(v___x_2549_, 1);
if (lean_obj_tag(v_a_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
lean_dec(v_f_2543_);
v_a_2554_ = lean_ctor_get(v_a_2553_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v_a_2553_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v_a_2553_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v_a_2553_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2554_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
v___y_2551_ = v___x_2559_;
goto v___jp_2550_;
}
}
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2570_; 
v_a_2562_ = lean_ctor_get(v_a_2553_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v_a_2553_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2564_ = v_a_2553_;
v_isShared_2565_ = v_isSharedCheck_2570_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v_a_2553_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2570_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2566_; lean_object* v___x_2568_; 
v___x_2566_ = lean_apply_1(v_f_2543_, v_a_2562_);
if (v_isShared_2565_ == 0)
{
lean_ctor_set(v___x_2564_, 0, v___x_2566_);
v___x_2568_ = v___x_2564_;
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
v___y_2551_ = v___x_2568_;
goto v___jp_2550_;
}
}
}
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2579_; 
lean_dec(v_f_2543_);
v_a_2571_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2573_ = v___x_2549_;
v_isShared_2574_ = v_isSharedCheck_2579_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2549_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2579_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2575_ = lean_task_map(v___x_2546_, v_a_2571_, v___x_2547_, v___x_2548_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 0, v___x_2575_);
v___x_2577_ = v___x_2573_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2575_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
v___jp_2550_:
{
lean_object* v___x_2552_; 
v___x_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2552_, 0, v___y_2551_);
return v___x_2552_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_map___boxed(lean_object* v_00_u03b1_2580_, lean_object* v_00_u03b2_2581_, lean_object* v_00_u03b5_2582_, lean_object* v_f_2583_, lean_object* v_self_2584_, lean_object* v_a_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l_Std_Async_EAsync_map(v_00_u03b1_2580_, v_00_u03b2_2581_, v_00_u03b5_2582_, v_f_2583_, v_self_2584_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind___redArg___lam__0(lean_object* v_f_2587_, lean_object* v_x_2588_){
_start:
{
if (lean_obj_tag(v_x_2588_) == 0)
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2598_; 
lean_dec_ref(v_f_2587_);
v_a_2590_ = lean_ctor_get(v_x_2588_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v_x_2588_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2592_ = v_x_2588_;
v_isShared_2593_ = v_isSharedCheck_2598_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v_x_2588_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2598_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2590_);
v___x_2595_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
lean_object* v___x_2596_; 
v___x_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
return v___x_2596_;
}
}
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2600_; 
v_a_2599_ = lean_ctor_get(v_x_2588_, 0);
lean_inc(v_a_2599_);
lean_dec_ref_known(v_x_2588_, 1);
v___x_2600_ = lean_apply_2(v_f_2587_, v_a_2599_, lean_box(0));
return v___x_2600_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind___redArg___lam__0___boxed(lean_object* v_f_2601_, lean_object* v_x_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Std_Async_EAsync_bind___redArg___lam__0(v_f_2601_, v_x_2602_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind___redArg(lean_object* v_self_2605_, lean_object* v_f_2606_){
_start:
{
lean_object* v___f_2608_; lean_object* v___x_2609_; uint8_t v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___f_2608_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_bind___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2608_, 0, v_f_2606_);
v___x_2609_ = lean_unsigned_to_nat(0u);
v___x_2610_ = 0;
v___x_2611_ = lean_apply_1(v_self_2605_, lean_box(0));
v___x_2612_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2609_, v___x_2610_, v___x_2611_, v___f_2608_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind___redArg___boxed(lean_object* v_self_2613_, lean_object* v_f_2614_, lean_object* v_a_2615_){
_start:
{
lean_object* v_res_2616_; 
v_res_2616_ = l_Std_Async_EAsync_bind___redArg(v_self_2613_, v_f_2614_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind(lean_object* v_00_u03b5_2617_, lean_object* v_00_u03b1_2618_, lean_object* v_00_u03b2_2619_, lean_object* v_self_2620_, lean_object* v_f_2621_){
_start:
{
lean_object* v___f_2623_; lean_object* v___x_2624_; uint8_t v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___f_2623_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_bind___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2623_, 0, v_f_2621_);
v___x_2624_ = lean_unsigned_to_nat(0u);
v___x_2625_ = 0;
v___x_2626_ = lean_apply_1(v_self_2620_, lean_box(0));
v___x_2627_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2624_, v___x_2625_, v___x_2626_, v___f_2623_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind___boxed(lean_object* v_00_u03b5_2628_, lean_object* v_00_u03b1_2629_, lean_object* v_00_u03b2_2630_, lean_object* v_self_2631_, lean_object* v_f_2632_, lean_object* v_a_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l_Std_Async_EAsync_bind(v_00_u03b5_2628_, v_00_u03b1_2629_, v_00_u03b2_2630_, v_self_2631_, v_f_2632_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_lift___redArg(lean_object* v_x_2635_){
_start:
{
lean_object* v_val_2638_; lean_object* v___x_2640_; 
v___x_2640_ = lean_apply_1(v_x_2635_, lean_box(0));
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2640_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2640_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
lean_ctor_set_tag(v___x_2643_, 1);
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
v_val_2638_ = v___x_2646_;
goto v___jp_2637_;
}
}
}
else
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
v_a_2649_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v___x_2640_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2640_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
lean_ctor_set_tag(v___x_2651_, 0);
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2649_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
v_val_2638_ = v___x_2654_;
goto v___jp_2637_;
}
}
}
v___jp_2637_:
{
lean_object* v___x_2639_; 
v___x_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2639_, 0, v_val_2638_);
return v___x_2639_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_lift___redArg___boxed(lean_object* v_x_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_Std_Async_EAsync_lift___redArg(v_x_2657_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_lift(lean_object* v_00_u03b5_2660_, lean_object* v_00_u03b1_2661_, lean_object* v_x_2662_){
_start:
{
lean_object* v_val_2665_; lean_object* v___x_2667_; 
v___x_2667_ = lean_apply_1(v_x_2662_, lean_box(0));
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2667_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2667_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
lean_ctor_set_tag(v___x_2670_, 1);
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
v_val_2665_ = v___x_2673_;
goto v___jp_2664_;
}
}
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
v_a_2676_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2667_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2667_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
lean_ctor_set_tag(v___x_2678_, 0);
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
v_val_2665_ = v___x_2681_;
goto v___jp_2664_;
}
}
}
v___jp_2664_:
{
lean_object* v___x_2666_; 
v___x_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2666_, 0, v_val_2665_);
return v___x_2666_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_lift___boxed(lean_object* v_00_u03b5_2684_, lean_object* v_00_u03b1_2685_, lean_object* v_x_2686_, lean_object* v_a_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l_Std_Async_EAsync_lift(v_00_u03b5_2684_, v_00_u03b1_2685_, v_x_2686_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_wait___redArg(lean_object* v_self_2689_){
_start:
{
lean_object* v_val_2692_; lean_object* v___x_2710_; 
v___x_2710_ = lean_apply_1(v_self_2689_, lean_box(0));
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; lean_object* v___x_2712_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2711_);
lean_dec_ref_known(v___x_2710_, 1);
v___x_2712_ = lean_task_pure(v_a_2711_);
v_val_2692_ = v___x_2712_;
goto v___jp_2691_;
}
else
{
lean_object* v_a_2713_; 
v_a_2713_ = lean_ctor_get(v___x_2710_, 0);
lean_inc_ref(v_a_2713_);
lean_dec_ref_known(v___x_2710_, 1);
v_val_2692_ = v_a_2713_;
goto v___jp_2691_;
}
v___jp_2691_:
{
lean_object* v___x_2693_; 
v___x_2693_ = lean_task_get_own(v_val_2692_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2693_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2693_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
lean_ctor_set_tag(v___x_2696_, 1);
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
v_a_2702_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2693_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2693_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
lean_ctor_set_tag(v___x_2704_, 0);
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_wait___redArg___boxed(lean_object* v_self_2714_, lean_object* v_a_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_Std_Async_EAsync_wait___redArg(v_self_2714_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_wait(lean_object* v_00_u03b5_2717_, lean_object* v_00_u03b1_2718_, lean_object* v_self_2719_){
_start:
{
lean_object* v_val_2722_; lean_object* v___x_2740_; 
v___x_2740_ = lean_apply_1(v_self_2719_, lean_box(0));
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_a_2741_; lean_object* v___x_2742_; 
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2741_);
lean_dec_ref_known(v___x_2740_, 1);
v___x_2742_ = lean_task_pure(v_a_2741_);
v_val_2722_ = v___x_2742_;
goto v___jp_2721_;
}
else
{
lean_object* v_a_2743_; 
v_a_2743_ = lean_ctor_get(v___x_2740_, 0);
lean_inc_ref(v_a_2743_);
lean_dec_ref_known(v___x_2740_, 1);
v_val_2722_ = v_a_2743_;
goto v___jp_2721_;
}
v___jp_2721_:
{
lean_object* v___x_2723_; 
v___x_2723_ = lean_task_get_own(v_val_2722_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2726_ = v___x_2723_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2723_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
lean_ctor_set_tag(v___x_2726_, 1);
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_a_2724_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
else
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2739_; 
v_a_2732_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2734_ = v___x_2723_;
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2723_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2737_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set_tag(v___x_2734_, 0);
v___x_2737_ = v___x_2734_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2732_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_wait___boxed(lean_object* v_00_u03b5_2744_, lean_object* v_00_u03b1_2745_, lean_object* v_self_2746_, lean_object* v_a_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_Std_Async_EAsync_wait(v_00_u03b5_2744_, v_00_u03b1_2745_, v_self_2746_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_asTask___redArg___lam__0(lean_object* v_x_2749_){
_start:
{
if (lean_obj_tag(v_x_2749_) == 0)
{
lean_object* v_a_2750_; lean_object* v___x_2751_; 
v_a_2750_ = lean_ctor_get(v_x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref_known(v_x_2749_, 1);
v___x_2751_ = lean_task_pure(v_a_2750_);
return v___x_2751_;
}
else
{
lean_object* v_a_2752_; 
v_a_2752_ = lean_ctor_get(v_x_2749_, 0);
lean_inc_ref(v_a_2752_);
lean_dec_ref_known(v_x_2749_, 1);
return v_a_2752_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_asTask___redArg(lean_object* v_x_2754_, lean_object* v_prio_2755_){
_start:
{
lean_object* v___f_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; uint8_t v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___f_2757_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___x_2758_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2758_, 0, lean_box(0));
lean_closure_set(v___x_2758_, 1, v_x_2754_);
v___x_2759_ = lean_io_as_task(v___x_2758_, v_prio_2755_);
v___x_2760_ = lean_unsigned_to_nat(0u);
v___x_2761_ = 1;
v___x_2762_ = lean_task_bind(v___x_2759_, v___f_2757_, v___x_2760_, v___x_2761_);
v___x_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2762_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_asTask___redArg___boxed(lean_object* v_x_2764_, lean_object* v_prio_2765_, lean_object* v_a_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l_Std_Async_EAsync_asTask___redArg(v_x_2764_, v_prio_2765_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_asTask(lean_object* v_00_u03b5_2768_, lean_object* v_00_u03b1_2769_, lean_object* v_x_2770_, lean_object* v_prio_2771_){
_start:
{
lean_object* v___f_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; uint8_t v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___f_2773_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___x_2774_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2774_, 0, lean_box(0));
lean_closure_set(v___x_2774_, 1, v_x_2770_);
v___x_2775_ = lean_io_as_task(v___x_2774_, v_prio_2771_);
v___x_2776_ = lean_unsigned_to_nat(0u);
v___x_2777_ = 1;
v___x_2778_ = lean_task_bind(v___x_2775_, v___f_2773_, v___x_2776_, v___x_2777_);
v___x_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2778_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_asTask___boxed(lean_object* v_00_u03b5_2780_, lean_object* v_00_u03b1_2781_, lean_object* v_x_2782_, lean_object* v_prio_2783_, lean_object* v_a_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Std_Async_EAsync_asTask(v_00_u03b5_2780_, v_00_u03b1_2781_, v_x_2782_, v_prio_2783_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_block___redArg(lean_object* v_x_2786_, lean_object* v_prio_2787_){
_start:
{
lean_object* v___f_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; uint8_t v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___f_2789_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___x_2790_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2790_, 0, lean_box(0));
lean_closure_set(v___x_2790_, 1, v_x_2786_);
v___x_2791_ = lean_io_as_task(v___x_2790_, v_prio_2787_);
v___x_2792_ = lean_unsigned_to_nat(0u);
v___x_2793_ = 1;
v___x_2794_ = lean_task_bind(v___x_2791_, v___f_2789_, v___x_2792_, v___x_2793_);
v___x_2795_ = lean_task_get_own(v___x_2794_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2795_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2795_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
lean_ctor_set_tag(v___x_2798_, 1);
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
v_a_2804_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2795_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2795_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
lean_ctor_set_tag(v___x_2806_, 0);
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_block___redArg___boxed(lean_object* v_x_2812_, lean_object* v_prio_2813_, lean_object* v_a_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l_Std_Async_EAsync_block___redArg(v_x_2812_, v_prio_2813_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_block(lean_object* v_00_u03b5_2816_, lean_object* v_00_u03b1_2817_, lean_object* v_x_2818_, lean_object* v_prio_2819_){
_start:
{
lean_object* v___f_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; uint8_t v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___f_2821_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___x_2822_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2822_, 0, lean_box(0));
lean_closure_set(v___x_2822_, 1, v_x_2818_);
v___x_2823_ = lean_io_as_task(v___x_2822_, v_prio_2819_);
v___x_2824_ = lean_unsigned_to_nat(0u);
v___x_2825_ = 1;
v___x_2826_ = lean_task_bind(v___x_2823_, v___f_2821_, v___x_2824_, v___x_2825_);
v___x_2827_ = lean_task_get_own(v___x_2826_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2827_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2827_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
lean_ctor_set_tag(v___x_2830_, 1);
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
else
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
v_a_2836_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v___x_2827_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2827_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
if (v_isShared_2839_ == 0)
{
lean_ctor_set_tag(v___x_2838_, 0);
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2836_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_block___boxed(lean_object* v_00_u03b5_2844_, lean_object* v_00_u03b1_2845_, lean_object* v_x_2846_, lean_object* v_prio_2847_, lean_object* v_a_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l_Std_Async_EAsync_block(v_00_u03b5_2844_, v_00_u03b1_2845_, v_x_2846_, v_prio_2847_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_throw___redArg(lean_object* v_e_2850_){
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
LEAN_EXPORT lean_object* l_Std_Async_EAsync_throw___redArg___boxed(lean_object* v_e_2854_, lean_object* v_a_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_Std_Async_EAsync_throw___redArg(v_e_2854_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_throw(lean_object* v_00_u03b5_2857_, lean_object* v_00_u03b1_2858_, lean_object* v_e_2859_){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2861_, 0, v_e_2859_);
v___x_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2861_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_throw___boxed(lean_object* v_00_u03b5_2863_, lean_object* v_00_u03b1_2864_, lean_object* v_e_2865_, lean_object* v_a_2866_){
_start:
{
lean_object* v_res_2867_; 
v_res_2867_ = l_Std_Async_EAsync_throw(v_00_u03b5_2863_, v_00_u03b1_2864_, v_e_2865_);
return v_res_2867_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch___redArg___lam__0(lean_object* v_f_2868_, lean_object* v_x_2869_){
_start:
{
if (lean_obj_tag(v_x_2869_) == 0)
{
lean_object* v_a_2871_; lean_object* v___x_2872_; 
v_a_2871_ = lean_ctor_get(v_x_2869_, 0);
lean_inc(v_a_2871_);
lean_dec_ref_known(v_x_2869_, 1);
v___x_2872_ = lean_apply_2(v_f_2868_, v_a_2871_, lean_box(0));
return v___x_2872_;
}
else
{
lean_object* v___x_2873_; 
lean_dec_ref(v_f_2868_);
v___x_2873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2873_, 0, v_x_2869_);
return v___x_2873_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch___redArg___lam__0___boxed(lean_object* v_f_2874_, lean_object* v_x_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l_Std_Async_EAsync_tryCatch___redArg___lam__0(v_f_2874_, v_x_2875_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch___redArg(lean_object* v_x_2878_, lean_object* v_f_2879_, lean_object* v_prio_2880_, uint8_t v_sync_2881_){
_start:
{
lean_object* v___f_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___f_2883_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_tryCatch___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2883_, 0, v_f_2879_);
v___x_2884_ = lean_apply_1(v_x_2878_, lean_box(0));
v___x_2885_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_2880_, v_sync_2881_, v___x_2884_, v___f_2883_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch___redArg___boxed(lean_object* v_x_2886_, lean_object* v_f_2887_, lean_object* v_prio_2888_, lean_object* v_sync_2889_, lean_object* v_a_2890_){
_start:
{
uint8_t v_sync_boxed_2891_; lean_object* v_res_2892_; 
v_sync_boxed_2891_ = lean_unbox(v_sync_2889_);
v_res_2892_ = l_Std_Async_EAsync_tryCatch___redArg(v_x_2886_, v_f_2887_, v_prio_2888_, v_sync_boxed_2891_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch(lean_object* v_00_u03b5_2893_, lean_object* v_00_u03b1_2894_, lean_object* v_x_2895_, lean_object* v_f_2896_, lean_object* v_prio_2897_, uint8_t v_sync_2898_){
_start:
{
lean_object* v___f_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___f_2900_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_tryCatch___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2900_, 0, v_f_2896_);
v___x_2901_ = lean_apply_1(v_x_2895_, lean_box(0));
v___x_2902_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_2897_, v_sync_2898_, v___x_2901_, v___f_2900_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch___boxed(lean_object* v_00_u03b5_2903_, lean_object* v_00_u03b1_2904_, lean_object* v_x_2905_, lean_object* v_f_2906_, lean_object* v_prio_2907_, lean_object* v_sync_2908_, lean_object* v_a_2909_){
_start:
{
uint8_t v_sync_boxed_2910_; lean_object* v_res_2911_; 
v_sync_boxed_2910_ = lean_unbox(v_sync_2908_);
v_res_2911_ = l_Std_Async_EAsync_tryCatch(v_00_u03b5_2903_, v_00_u03b1_2904_, v_x_2905_, v_f_2906_, v_prio_2907_, v_sync_boxed_2910_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__0(lean_object* v_a_2912_, lean_object* v_____do__lift_2913_){
_start:
{
if (lean_obj_tag(v_____do__lift_2913_) == 0)
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2923_; 
lean_dec(v_a_2912_);
v_a_2915_ = lean_ctor_get(v_____do__lift_2913_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v_____do__lift_2913_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2917_ = v_____do__lift_2913_;
v_isShared_2918_ = v_isSharedCheck_2923_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v_____do__lift_2913_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2923_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2915_);
v___x_2920_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
lean_object* v___x_2921_; 
v___x_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
return v___x_2921_;
}
}
}
else
{
lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2931_; 
v_isSharedCheck_2931_ = !lean_is_exclusive(v_____do__lift_2913_);
if (v_isSharedCheck_2931_ == 0)
{
lean_object* v_unused_2932_; 
v_unused_2932_ = lean_ctor_get(v_____do__lift_2913_, 0);
lean_dec(v_unused_2932_);
v___x_2925_ = v_____do__lift_2913_;
v_isShared_2926_ = v_isSharedCheck_2931_;
goto v_resetjp_2924_;
}
else
{
lean_dec(v_____do__lift_2913_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2931_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
lean_ctor_set_tag(v___x_2925_, 0);
lean_ctor_set(v___x_2925_, 0, v_a_2912_);
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2912_);
v___x_2928_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
lean_object* v___x_2929_; 
v___x_2929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2928_);
return v___x_2929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__0___boxed(lean_object* v_a_2933_, lean_object* v_____do__lift_2934_, lean_object* v___y_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_Std_Async_EAsync_tryFinally_x27___redArg___lam__0(v_a_2933_, v_____do__lift_2934_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__1(lean_object* v_a_2937_, lean_object* v_____do__lift_2938_){
_start:
{
if (lean_obj_tag(v_____do__lift_2938_) == 0)
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2948_; 
lean_dec(v_a_2937_);
v_a_2940_ = lean_ctor_get(v_____do__lift_2938_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v_____do__lift_2938_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2942_ = v_____do__lift_2938_;
v_isShared_2943_ = v_isSharedCheck_2948_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v_____do__lift_2938_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2948_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2945_; 
if (v_isShared_2943_ == 0)
{
v___x_2945_ = v___x_2942_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2940_);
v___x_2945_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
lean_object* v___x_2946_; 
v___x_2946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2945_);
return v___x_2946_;
}
}
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2958_; 
v_a_2949_ = lean_ctor_get(v_____do__lift_2938_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v_____do__lift_2938_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2951_ = v_____do__lift_2938_;
v_isShared_2952_ = v_isSharedCheck_2958_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v_____do__lift_2938_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2958_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2953_; lean_object* v___x_2955_; 
v___x_2953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2953_, 0, v_a_2937_);
lean_ctor_set(v___x_2953_, 1, v_a_2949_);
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 0, v___x_2953_);
v___x_2955_ = v___x_2951_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v___x_2953_);
v___x_2955_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
lean_object* v___x_2956_; 
v___x_2956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2955_);
return v___x_2956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__1___boxed(lean_object* v_a_2959_, lean_object* v_____do__lift_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_Std_Async_EAsync_tryFinally_x27___redArg___lam__1(v_a_2959_, v_____do__lift_2960_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__2(lean_object* v_f_2963_, lean_object* v_x_2964_){
_start:
{
if (lean_obj_tag(v_x_2964_) == 0)
{
lean_object* v_a_2966_; lean_object* v___f_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; uint8_t v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
v_a_2966_ = lean_ctor_get(v_x_2964_, 0);
lean_inc(v_a_2966_);
lean_dec_ref_known(v_x_2964_, 1);
v___f_2967_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_tryFinally_x27___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2967_, 0, v_a_2966_);
v___x_2968_ = lean_box(0);
v___x_2969_ = lean_unsigned_to_nat(0u);
v___x_2970_ = 0;
v___x_2971_ = lean_apply_2(v_f_2963_, v___x_2968_, lean_box(0));
v___x_2972_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2969_, v___x_2970_, v___x_2971_, v___f_2967_);
return v___x_2972_;
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2985_; 
v_a_2973_ = lean_ctor_get(v_x_2964_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v_x_2964_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2975_ = v_x_2964_;
v_isShared_2976_ = v_isSharedCheck_2985_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v_x_2964_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2985_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___f_2977_; lean_object* v___x_2979_; 
lean_inc(v_a_2973_);
v___f_2977_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_tryFinally_x27___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2977_, 0, v_a_2973_);
if (v_isShared_2976_ == 0)
{
v___x_2979_ = v___x_2975_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_a_2973_);
v___x_2979_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
lean_object* v___x_2980_; uint8_t v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2980_ = lean_unsigned_to_nat(0u);
v___x_2981_ = 0;
v___x_2982_ = lean_apply_2(v_f_2963_, v___x_2979_, lean_box(0));
v___x_2983_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2980_, v___x_2981_, v___x_2982_, v___f_2977_);
return v___x_2983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__2___boxed(lean_object* v_f_2986_, lean_object* v_x_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l_Std_Async_EAsync_tryFinally_x27___redArg___lam__2(v_f_2986_, v_x_2987_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg(lean_object* v_x_2990_, lean_object* v_f_2991_, lean_object* v_prio_2992_, uint8_t v_sync_2993_){
_start:
{
lean_object* v___f_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___f_2995_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_tryFinally_x27___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2995_, 0, v_f_2991_);
v___x_2996_ = lean_apply_1(v_x_2990_, lean_box(0));
v___x_2997_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_2992_, v_sync_2993_, v___x_2996_, v___f_2995_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___boxed(lean_object* v_x_2998_, lean_object* v_f_2999_, lean_object* v_prio_3000_, lean_object* v_sync_3001_, lean_object* v_a_3002_){
_start:
{
uint8_t v_sync_boxed_3003_; lean_object* v_res_3004_; 
v_sync_boxed_3003_ = lean_unbox(v_sync_3001_);
v_res_3004_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v_x_2998_, v_f_2999_, v_prio_3000_, v_sync_boxed_3003_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27(lean_object* v_00_u03b5_3005_, lean_object* v_00_u03b1_3006_, lean_object* v_00_u03b2_3007_, lean_object* v_x_3008_, lean_object* v_f_3009_, lean_object* v_prio_3010_, uint8_t v_sync_3011_){
_start:
{
lean_object* v___x_3013_; 
v___x_3013_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v_x_3008_, v_f_3009_, v_prio_3010_, v_sync_3011_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___boxed(lean_object* v_00_u03b5_3014_, lean_object* v_00_u03b1_3015_, lean_object* v_00_u03b2_3016_, lean_object* v_x_3017_, lean_object* v_f_3018_, lean_object* v_prio_3019_, lean_object* v_sync_3020_, lean_object* v_a_3021_){
_start:
{
uint8_t v_sync_boxed_3022_; lean_object* v_res_3023_; 
v_sync_boxed_3022_ = lean_unbox(v_sync_3020_);
v_res_3023_ = l_Std_Async_EAsync_tryFinally_x27(v_00_u03b5_3014_, v_00_u03b1_3015_, v_00_u03b2_3016_, v_x_3017_, v_f_3018_, v_prio_3019_, v_sync_boxed_3022_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_await___redArg(lean_object* v_x_3024_){
_start:
{
lean_object* v___x_3026_; 
v___x_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3026_, 0, v_x_3024_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_await___redArg___boxed(lean_object* v_x_3027_, lean_object* v_a_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l_Std_Async_EAsync_await___redArg(v_x_3027_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_await(lean_object* v_00_u03b5_3030_, lean_object* v_00_u03b1_3031_, lean_object* v_x_3032_){
_start:
{
lean_object* v___x_3034_; 
v___x_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3034_, 0, v_x_3032_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_await___boxed(lean_object* v_00_u03b5_3035_, lean_object* v_00_u03b1_3036_, lean_object* v_x_3037_, lean_object* v_a_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l_Std_Async_EAsync_await(v_00_u03b5_3035_, v_00_u03b1_3036_, v_x_3037_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_async___redArg(lean_object* v_self_3040_, lean_object* v_prio_3041_){
_start:
{
lean_object* v___f_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; uint8_t v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___f_3043_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___x_3044_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_3044_, 0, lean_box(0));
lean_closure_set(v___x_3044_, 1, v_self_3040_);
v___x_3045_ = lean_io_as_task(v___x_3044_, v_prio_3041_);
v___x_3046_ = lean_unsigned_to_nat(0u);
v___x_3047_ = 1;
v___x_3048_ = lean_task_bind(v___x_3045_, v___f_3043_, v___x_3046_, v___x_3047_);
v___x_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
v___x_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3049_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_async___redArg___boxed(lean_object* v_self_3051_, lean_object* v_prio_3052_, lean_object* v_a_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Std_Async_EAsync_async___redArg(v_self_3051_, v_prio_3052_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_async(lean_object* v_00_u03b5_3055_, lean_object* v_00_u03b1_3056_, lean_object* v_self_3057_, lean_object* v_prio_3058_){
_start:
{
lean_object* v___f_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; uint8_t v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___f_3060_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___x_3061_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_3061_, 0, lean_box(0));
lean_closure_set(v___x_3061_, 1, v_self_3057_);
v___x_3062_ = lean_io_as_task(v___x_3061_, v_prio_3058_);
v___x_3063_ = lean_unsigned_to_nat(0u);
v___x_3064_ = 1;
v___x_3065_ = lean_task_bind(v___x_3062_, v___f_3060_, v___x_3063_, v___x_3064_);
v___x_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3065_);
v___x_3067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3066_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_async___boxed(lean_object* v_00_u03b5_3068_, lean_object* v_00_u03b1_3069_, lean_object* v_self_3070_, lean_object* v_prio_3071_, lean_object* v_a_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l_Std_Async_EAsync_async(v_00_u03b5_3068_, v_00_u03b1_3069_, v_self_3070_, v_prio_3071_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___redArg___lam__0(lean_object* v_00_u03b1_3074_, lean_object* v_00_u03b2_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; uint8_t v___x_3081_; lean_object* v___x_3082_; lean_object* v___y_3084_; 
lean_inc(v___y_3076_);
v___x_3079_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_3079_, 0, lean_box(0));
lean_closure_set(v___x_3079_, 1, lean_box(0));
lean_closure_set(v___x_3079_, 2, lean_box(0));
lean_closure_set(v___x_3079_, 3, v___y_3076_);
v___x_3080_ = lean_unsigned_to_nat(0u);
v___x_3081_ = 0;
v___x_3082_ = lean_apply_1(v___y_3077_, lean_box(0));
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v_a_3086_; 
lean_dec_ref(v___x_3079_);
v_a_3086_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_a_3086_);
lean_dec_ref_known(v___x_3082_, 1);
if (lean_obj_tag(v_a_3086_) == 0)
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
lean_dec(v___y_3076_);
v_a_3087_ = lean_ctor_get(v_a_3086_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v_a_3086_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v_a_3086_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v_a_3086_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
v___y_3084_ = v___x_3092_;
goto v___jp_3083_;
}
}
}
else
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3103_; 
v_a_3095_ = lean_ctor_get(v_a_3086_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v_a_3086_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3097_ = v_a_3086_;
v_isShared_3098_ = v_isSharedCheck_3103_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v_a_3086_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3103_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3099_; lean_object* v___x_3101_; 
v___x_3099_ = lean_apply_1(v___y_3076_, v_a_3095_);
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 0, v___x_3099_);
v___x_3101_ = v___x_3097_;
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
v___y_3084_ = v___x_3101_;
goto v___jp_3083_;
}
}
}
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3112_; 
lean_dec(v___y_3076_);
v_a_3104_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3106_ = v___x_3082_;
v_isShared_3107_ = v_isSharedCheck_3112_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3082_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3112_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3108_; lean_object* v___x_3110_; 
v___x_3108_ = lean_task_map(v___x_3079_, v_a_3104_, v___x_3080_, v___x_3081_);
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 0, v___x_3108_);
v___x_3110_ = v___x_3106_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3108_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
v___jp_3083_:
{
lean_object* v___x_3085_; 
v___x_3085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3085_, 0, v___y_3084_);
return v___x_3085_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___redArg___lam__0___boxed(lean_object* v_00_u03b1_3113_, lean_object* v_00_u03b2_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
lean_object* v_res_3118_; 
v_res_3118_ = l_Std_Async_EAsync_instFunctor___redArg___lam__0(v_00_u03b1_3113_, v_00_u03b2_3114_, v___y_3115_, v___y_3116_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___redArg___lam__1(lean_object* v___f_3119_, lean_object* v_00_u03b1_3120_, lean_object* v_00_u03b2_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3125_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_3125_, 0, lean_box(0));
lean_closure_set(v___x_3125_, 1, lean_box(0));
lean_closure_set(v___x_3125_, 2, v___y_3122_);
v___x_3126_ = lean_apply_5(v___f_3119_, lean_box(0), lean_box(0), v___x_3125_, v___y_3123_, lean_box(0));
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___redArg___lam__1___boxed(lean_object* v___f_3127_, lean_object* v_00_u03b1_3128_, lean_object* v_00_u03b2_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l_Std_Async_EAsync_instFunctor___redArg___lam__1(v___f_3127_, v_00_u03b1_3128_, v_00_u03b2_3129_, v___y_3130_, v___y_3131_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___redArg(){
_start:
{
lean_object* v___x_3141_; 
v___x_3141_ = ((lean_object*)(l_Std_Async_EAsync_instFunctor___redArg___closed__2));
return v___x_3141_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___redArg___boxed(lean_object* v___dummy_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l_Std_Async_EAsync_instFunctor___redArg();
return v_res_3143_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instFunctor___closed__0(void){
_start:
{
lean_object* v___x_3144_; 
v___x_3144_ = l_Std_Async_EAsync_instFunctor___redArg();
return v___x_3144_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor(lean_object* v_00_u03b5_3145_){
_start:
{
lean_object* v___x_3146_; 
v___x_3146_ = lean_obj_once(&l_Std_Async_EAsync_instFunctor___closed__0, &l_Std_Async_EAsync_instFunctor___closed__0_once, _init_l_Std_Async_EAsync_instFunctor___closed__0);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__0(lean_object* v_00_u03b1_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3150_, 0, v___y_3148_);
v___x_3151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3150_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__0___boxed(lean_object* v_00_u03b1_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l_Std_Async_EAsync_instMonad___redArg___lam__0(v_00_u03b1_3152_, v___y_3153_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__1(lean_object* v_x_3156_, lean_object* v_x_3157_){
_start:
{
if (lean_obj_tag(v_x_3157_) == 0)
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3167_; 
lean_dec_ref(v_x_3156_);
v_a_3159_ = lean_ctor_get(v_x_3157_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v_x_3157_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3161_ = v_x_3157_;
v_isShared_3162_ = v_isSharedCheck_3167_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v_x_3157_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3167_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
if (v_isShared_3162_ == 0)
{
v___x_3164_ = v___x_3161_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3159_);
v___x_3164_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
lean_object* v___x_3165_; 
v___x_3165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3164_);
return v___x_3165_;
}
}
}
else
{
lean_object* v_a_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; uint8_t v___x_3172_; lean_object* v___x_3173_; lean_object* v___y_3175_; 
v_a_3168_ = lean_ctor_get(v_x_3157_, 0);
lean_inc_n(v_a_3168_, 2);
lean_dec_ref_known(v_x_3157_, 1);
v___x_3169_ = lean_box(0);
v___x_3170_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_3170_, 0, lean_box(0));
lean_closure_set(v___x_3170_, 1, lean_box(0));
lean_closure_set(v___x_3170_, 2, lean_box(0));
lean_closure_set(v___x_3170_, 3, v_a_3168_);
v___x_3171_ = lean_unsigned_to_nat(0u);
v___x_3172_ = 0;
v___x_3173_ = lean_apply_2(v_x_3156_, v___x_3169_, lean_box(0));
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_object* v_a_3177_; 
lean_dec_ref(v___x_3170_);
v_a_3177_ = lean_ctor_get(v___x_3173_, 0);
lean_inc(v_a_3177_);
lean_dec_ref_known(v___x_3173_, 1);
if (lean_obj_tag(v_a_3177_) == 0)
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
lean_dec(v_a_3168_);
v_a_3178_ = lean_ctor_get(v_a_3177_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v_a_3177_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v_a_3177_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v_a_3177_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3183_; 
if (v_isShared_3181_ == 0)
{
v___x_3183_ = v___x_3180_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
v___y_3175_ = v___x_3183_;
goto v___jp_3174_;
}
}
}
else
{
lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3194_; 
v_a_3186_ = lean_ctor_get(v_a_3177_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v_a_3177_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3188_ = v_a_3177_;
v_isShared_3189_ = v_isSharedCheck_3194_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v_a_3177_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3194_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3190_; lean_object* v___x_3192_; 
v___x_3190_ = lean_apply_1(v_a_3168_, v_a_3186_);
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 0, v___x_3190_);
v___x_3192_ = v___x_3188_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3190_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
v___y_3175_ = v___x_3192_;
goto v___jp_3174_;
}
}
}
}
else
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3203_; 
lean_dec(v_a_3168_);
v_a_3195_ = lean_ctor_get(v___x_3173_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3197_ = v___x_3173_;
v_isShared_3198_ = v_isSharedCheck_3203_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3173_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3203_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3199_; lean_object* v___x_3201_; 
v___x_3199_ = lean_task_map(v___x_3170_, v_a_3195_, v___x_3171_, v___x_3172_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 0, v___x_3199_);
v___x_3201_ = v___x_3197_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3199_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
v___jp_3174_:
{
lean_object* v___x_3176_; 
v___x_3176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3176_, 0, v___y_3175_);
return v___x_3176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__1___boxed(lean_object* v_x_3204_, lean_object* v_x_3205_, lean_object* v___y_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l_Std_Async_EAsync_instMonad___redArg___lam__1(v_x_3204_, v_x_3205_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__2(lean_object* v_00_u03b1_3208_, lean_object* v_00_u03b2_3209_, lean_object* v_f_3210_, lean_object* v_x_3211_){
_start:
{
lean_object* v___f_3213_; lean_object* v___x_3214_; uint8_t v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___f_3213_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_instMonad___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3213_, 0, v_x_3211_);
v___x_3214_ = lean_unsigned_to_nat(0u);
v___x_3215_ = 0;
v___x_3216_ = lean_apply_1(v_f_3210_, lean_box(0));
v___x_3217_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3214_, v___x_3215_, v___x_3216_, v___f_3213_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__2___boxed(lean_object* v_00_u03b1_3218_, lean_object* v_00_u03b2_3219_, lean_object* v_f_3220_, lean_object* v_x_3221_, lean_object* v___y_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l_Std_Async_EAsync_instMonad___redArg___lam__2(v_00_u03b1_3218_, v_00_u03b2_3219_, v_f_3220_, v_x_3221_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__3(lean_object* v___f_3224_, lean_object* v_a_3225_, lean_object* v_x_3226_){
_start:
{
if (lean_obj_tag(v_x_3226_) == 0)
{
lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3236_; 
lean_dec(v_a_3225_);
lean_dec_ref(v___f_3224_);
v_a_3228_ = lean_ctor_get(v_x_3226_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v_x_3226_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3230_ = v_x_3226_;
v_isShared_3231_ = v_isSharedCheck_3236_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v_x_3226_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3236_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3233_; 
if (v_isShared_3231_ == 0)
{
v___x_3233_ = v___x_3230_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_a_3228_);
v___x_3233_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
lean_object* v___x_3234_; 
v___x_3234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3233_);
return v___x_3234_;
}
}
}
else
{
lean_object* v___x_3237_; 
lean_dec_ref_known(v_x_3226_, 1);
v___x_3237_ = lean_apply_3(v___f_3224_, lean_box(0), v_a_3225_, lean_box(0));
return v___x_3237_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__3___boxed(lean_object* v___f_3238_, lean_object* v_a_3239_, lean_object* v_x_3240_, lean_object* v___y_3241_){
_start:
{
lean_object* v_res_3242_; 
v_res_3242_ = l_Std_Async_EAsync_instMonad___redArg___lam__3(v___f_3238_, v_a_3239_, v_x_3240_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__4(lean_object* v___f_3243_, lean_object* v_y_3244_, lean_object* v_x_3245_){
_start:
{
if (lean_obj_tag(v_x_3245_) == 0)
{
lean_object* v___x_3247_; 
lean_dec_ref(v_y_3244_);
lean_dec_ref(v___f_3243_);
v___x_3247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3247_, 0, v_x_3245_);
return v___x_3247_;
}
else
{
lean_object* v_a_3248_; lean_object* v___f_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; uint8_t v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v_a_3248_ = lean_ctor_get(v_x_3245_, 0);
lean_inc(v_a_3248_);
lean_dec_ref_known(v_x_3245_, 1);
v___f_3249_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_instMonad___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_3249_, 0, v___f_3243_);
lean_closure_set(v___f_3249_, 1, v_a_3248_);
v___x_3250_ = lean_box(0);
v___x_3251_ = lean_unsigned_to_nat(0u);
v___x_3252_ = 0;
v___x_3253_ = lean_apply_2(v_y_3244_, v___x_3250_, lean_box(0));
v___x_3254_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3251_, v___x_3252_, v___x_3253_, v___f_3249_);
return v___x_3254_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__4___boxed(lean_object* v___f_3255_, lean_object* v_y_3256_, lean_object* v_x_3257_, lean_object* v___y_3258_){
_start:
{
lean_object* v_res_3259_; 
v_res_3259_ = l_Std_Async_EAsync_instMonad___redArg___lam__4(v___f_3255_, v_y_3256_, v_x_3257_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__5(lean_object* v___f_3260_, lean_object* v_00_u03b1_3261_, lean_object* v_00_u03b2_3262_, lean_object* v_x_3263_, lean_object* v_y_3264_){
_start:
{
lean_object* v___f_3266_; lean_object* v___x_3267_; uint8_t v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___f_3266_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_instMonad___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_3266_, 0, v___f_3260_);
lean_closure_set(v___f_3266_, 1, v_y_3264_);
v___x_3267_ = lean_unsigned_to_nat(0u);
v___x_3268_ = 0;
v___x_3269_ = lean_apply_1(v_x_3263_, lean_box(0));
v___x_3270_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3267_, v___x_3268_, v___x_3269_, v___f_3266_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__5___boxed(lean_object* v___f_3271_, lean_object* v_00_u03b1_3272_, lean_object* v_00_u03b2_3273_, lean_object* v_x_3274_, lean_object* v_y_3275_, lean_object* v___y_3276_){
_start:
{
lean_object* v_res_3277_; 
v_res_3277_ = l_Std_Async_EAsync_instMonad___redArg___lam__5(v___f_3271_, v_00_u03b1_3272_, v_00_u03b2_3273_, v_x_3274_, v_y_3275_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__6(lean_object* v_y_3278_, lean_object* v_x_3279_){
_start:
{
if (lean_obj_tag(v_x_3279_) == 0)
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3289_; 
lean_dec_ref(v_y_3278_);
v_a_3281_ = lean_ctor_get(v_x_3279_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v_x_3279_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3283_ = v_x_3279_;
v_isShared_3284_ = v_isSharedCheck_3289_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v_x_3279_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3289_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3286_; 
if (v_isShared_3284_ == 0)
{
v___x_3286_ = v___x_3283_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_a_3281_);
v___x_3286_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
lean_object* v___x_3287_; 
v___x_3287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3286_);
return v___x_3287_;
}
}
}
else
{
lean_object* v___x_3290_; lean_object* v___x_3291_; 
lean_dec_ref_known(v_x_3279_, 1);
v___x_3290_ = lean_box(0);
v___x_3291_ = lean_apply_2(v_y_3278_, v___x_3290_, lean_box(0));
return v___x_3291_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__6___boxed(lean_object* v_y_3292_, lean_object* v_x_3293_, lean_object* v___y_3294_){
_start:
{
lean_object* v_res_3295_; 
v_res_3295_ = l_Std_Async_EAsync_instMonad___redArg___lam__6(v_y_3292_, v_x_3293_);
return v_res_3295_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__7(lean_object* v_00_u03b1_3296_, lean_object* v_00_u03b2_3297_, lean_object* v_x_3298_, lean_object* v_y_3299_){
_start:
{
lean_object* v___f_3301_; lean_object* v___x_3302_; uint8_t v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___f_3301_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_instMonad___redArg___lam__6___boxed), 3, 1);
lean_closure_set(v___f_3301_, 0, v_y_3299_);
v___x_3302_ = lean_unsigned_to_nat(0u);
v___x_3303_ = 0;
v___x_3304_ = lean_apply_1(v_x_3298_, lean_box(0));
v___x_3305_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3302_, v___x_3303_, v___x_3304_, v___f_3301_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__7___boxed(lean_object* v_00_u03b1_3306_, lean_object* v_00_u03b2_3307_, lean_object* v_x_3308_, lean_object* v_y_3309_, lean_object* v___y_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l_Std_Async_EAsync_instMonad___redArg___lam__7(v_00_u03b1_3306_, v_00_u03b2_3307_, v_x_3308_, v_y_3309_);
return v_res_3311_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonad___redArg___closed__4(void){
_start:
{
lean_object* v___f_3317_; lean_object* v___f_3318_; lean_object* v___f_3319_; lean_object* v___f_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___f_3317_ = ((lean_object*)(l_Std_Async_EAsync_instMonad___redArg___closed__3));
v___f_3318_ = ((lean_object*)(l_Std_Async_EAsync_instMonad___redArg___closed__2));
v___f_3319_ = ((lean_object*)(l_Std_Async_EAsync_instMonad___redArg___closed__1));
v___f_3320_ = ((lean_object*)(l_Std_Async_EAsync_instMonad___redArg___closed__0));
v___x_3321_ = lean_obj_once(&l_Std_Async_EAsync_instFunctor___closed__0, &l_Std_Async_EAsync_instFunctor___closed__0_once, _init_l_Std_Async_EAsync_instFunctor___closed__0);
v___x_3322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3321_);
lean_ctor_set(v___x_3322_, 1, v___f_3320_);
lean_ctor_set(v___x_3322_, 2, v___f_3319_);
lean_ctor_set(v___x_3322_, 3, v___f_3318_);
lean_ctor_set(v___x_3322_, 4, v___f_3317_);
return v___x_3322_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonad___redArg___closed__6(void){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3324_ = ((lean_object*)(l_Std_Async_EAsync_instMonad___redArg___closed__5));
v___x_3325_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___redArg___closed__4, &l_Std_Async_EAsync_instMonad___redArg___closed__4_once, _init_l_Std_Async_EAsync_instMonad___redArg___closed__4);
v___x_3326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3325_);
lean_ctor_set(v___x_3326_, 1, v___x_3324_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg(){
_start:
{
lean_object* v___x_3328_; 
v___x_3328_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___redArg___closed__6, &l_Std_Async_EAsync_instMonad___redArg___closed__6_once, _init_l_Std_Async_EAsync_instMonad___redArg___closed__6);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___boxed(lean_object* v___dummy_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l_Std_Async_EAsync_instMonad___redArg();
return v_res_3330_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonad___closed__0(void){
_start:
{
lean_object* v___x_3331_; 
v___x_3331_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad(lean_object* v_00_u03b5_3332_){
_start:
{
lean_object* v___x_3333_; 
v___x_3333_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___closed__0, &l_Std_Async_EAsync_instMonad___closed__0_once, _init_l_Std_Async_EAsync_instMonad___closed__0);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO___redArg(){
_start:
{
lean_object* v___x_3336_; 
v___x_3336_ = ((lean_object*)(l_Std_Async_EAsync_instMonadLiftEIO___redArg___closed__0));
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO___redArg___boxed(lean_object* v___dummy_3337_){
_start:
{
lean_object* v_res_3338_; 
v_res_3338_ = l_Std_Async_EAsync_instMonadLiftEIO___redArg();
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO(lean_object* v_00_u03b5_3339_){
_start:
{
lean_object* v___x_3340_; 
v___x_3340_ = ((lean_object*)(l_Std_Async_EAsync_instMonadLiftEIO___redArg___closed__0));
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExcept___redArg___lam__1(lean_object* v_00_u03b1_3341_, lean_object* v_x_3342_, lean_object* v_f_3343_){
_start:
{
lean_object* v___f_3345_; lean_object* v___x_3346_; uint8_t v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___f_3345_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_tryCatch___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3345_, 0, v_f_3343_);
v___x_3346_ = lean_unsigned_to_nat(0u);
v___x_3347_ = 0;
v___x_3348_ = lean_apply_1(v_x_3342_, lean_box(0));
v___x_3349_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3346_, v___x_3347_, v___x_3348_, v___f_3345_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExcept___redArg___lam__1___boxed(lean_object* v_00_u03b1_3350_, lean_object* v_x_3351_, lean_object* v_f_3352_, lean_object* v___y_3353_){
_start:
{
lean_object* v_res_3354_; 
v_res_3354_ = l_Std_Async_EAsync_instMonadExcept___redArg___lam__1(v_00_u03b1_3350_, v_x_3351_, v_f_3352_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExcept___redArg(){
_start:
{
lean_object* v___x_3361_; 
v___x_3361_ = ((lean_object*)(l_Std_Async_EAsync_instMonadExcept___redArg___closed__2));
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExcept___redArg___boxed(lean_object* v___dummy_3362_){
_start:
{
lean_object* v_res_3363_; 
v_res_3363_ = l_Std_Async_EAsync_instMonadExcept___redArg();
return v_res_3363_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonadExcept___closed__0(void){
_start:
{
lean_object* v___x_3364_; 
v___x_3364_ = l_Std_Async_EAsync_instMonadExcept___redArg();
return v___x_3364_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExcept(lean_object* v_00_u03b5_3365_){
_start:
{
lean_object* v___x_3366_; 
v___x_3366_ = lean_obj_once(&l_Std_Async_EAsync_instMonadExcept___closed__0, &l_Std_Async_EAsync_instMonadExcept___closed__0_once, _init_l_Std_Async_EAsync_instMonadExcept___closed__0);
return v___x_3366_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExceptOf___redArg(){
_start:
{
lean_object* v___x_3371_; 
v___x_3371_ = ((lean_object*)(l_Std_Async_EAsync_instMonadExceptOf___redArg___closed__0));
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExceptOf___redArg___boxed(lean_object* v___dummy_3372_){
_start:
{
lean_object* v_res_3373_; 
v_res_3373_ = l_Std_Async_EAsync_instMonadExceptOf___redArg();
return v_res_3373_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonadExceptOf___closed__0(void){
_start:
{
lean_object* v___x_3374_; 
v___x_3374_ = l_Std_Async_EAsync_instMonadExceptOf___redArg();
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExceptOf(lean_object* v_00_u03b5_3375_){
_start:
{
lean_object* v___x_3376_; 
v___x_3376_ = lean_obj_once(&l_Std_Async_EAsync_instMonadExceptOf___closed__0, &l_Std_Async_EAsync_instMonadExceptOf___closed__0_once, _init_l_Std_Async_EAsync_instMonadExceptOf___closed__0);
return v___x_3376_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadFinally___redArg___lam__0(lean_object* v_00_u03b1_3377_, lean_object* v_00_u03b2_3378_, lean_object* v_x_3379_, lean_object* v_f_3380_){
_start:
{
lean_object* v___x_3382_; uint8_t v___x_3383_; lean_object* v___x_3384_; 
v___x_3382_ = lean_unsigned_to_nat(0u);
v___x_3383_ = 0;
v___x_3384_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v_x_3379_, v_f_3380_, v___x_3382_, v___x_3383_);
return v___x_3384_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadFinally___redArg___lam__0___boxed(lean_object* v_00_u03b1_3385_, lean_object* v_00_u03b2_3386_, lean_object* v_x_3387_, lean_object* v_f_3388_, lean_object* v___y_3389_){
_start:
{
lean_object* v_res_3390_; 
v_res_3390_ = l_Std_Async_EAsync_instMonadFinally___redArg___lam__0(v_00_u03b1_3385_, v_00_u03b2_3386_, v_x_3387_, v_f_3388_);
return v_res_3390_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadFinally___redArg(){
_start:
{
lean_object* v___f_3393_; 
v___f_3393_ = ((lean_object*)(l_Std_Async_EAsync_instMonadFinally___redArg___closed__0));
return v___f_3393_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadFinally___redArg___boxed(lean_object* v___dummy_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l_Std_Async_EAsync_instMonadFinally___redArg();
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadFinally(lean_object* v_00_u03b5_3396_){
_start:
{
lean_object* v___f_3397_; 
v___f_3397_ = ((lean_object*)(l_Std_Async_EAsync_instMonadFinally___redArg___closed__0));
return v___f_3397_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instOrElse___redArg___closed__0(void){
_start:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3398_ = lean_obj_once(&l_Std_Async_EAsync_instMonadExcept___closed__0, &l_Std_Async_EAsync_instMonadExcept___closed__0_once, _init_l_Std_Async_EAsync_instMonadExcept___closed__0);
v___x_3399_ = lean_alloc_closure((void*)(l_MonadExcept_orElse), 6, 4);
lean_closure_set(v___x_3399_, 0, lean_box(0));
lean_closure_set(v___x_3399_, 1, lean_box(0));
lean_closure_set(v___x_3399_, 2, v___x_3398_);
lean_closure_set(v___x_3399_, 3, lean_box(0));
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instOrElse___redArg(){
_start:
{
lean_object* v___x_3401_; 
v___x_3401_ = lean_obj_once(&l_Std_Async_EAsync_instOrElse___redArg___closed__0, &l_Std_Async_EAsync_instOrElse___redArg___closed__0_once, _init_l_Std_Async_EAsync_instOrElse___redArg___closed__0);
return v___x_3401_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instOrElse___redArg___boxed(lean_object* v___dummy_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l_Std_Async_EAsync_instOrElse___redArg();
return v_res_3403_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instOrElse___closed__0(void){
_start:
{
lean_object* v___x_3404_; 
v___x_3404_ = l_Std_Async_EAsync_instOrElse___redArg();
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instOrElse(lean_object* v_00_u03b5_3405_, lean_object* v_00_u03b1_3406_){
_start:
{
lean_object* v___x_3407_; 
v___x_3407_ = lean_obj_once(&l_Std_Async_EAsync_instOrElse___closed__0, &l_Std_Async_EAsync_instOrElse___closed__0_once, _init_l_Std_Async_EAsync_instOrElse___closed__0);
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instInhabited___redArg(lean_object* v_inst_3408_){
_start:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3409_, 0, v_inst_3408_);
v___x_3410_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_pure___boxed), 3, 2);
lean_closure_set(v___x_3410_, 0, lean_box(0));
lean_closure_set(v___x_3410_, 1, v___x_3409_);
v___x_3411_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_mk___boxed), 3, 2);
lean_closure_set(v___x_3411_, 0, lean_box(0));
lean_closure_set(v___x_3411_, 1, v___x_3410_);
return v___x_3411_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instInhabited(lean_object* v_00_u03b5_3412_, lean_object* v_00_u03b1_3413_, lean_object* v_inst_3414_){
_start:
{
lean_object* v___x_3415_; 
v___x_3415_ = l_Std_Async_EAsync_instInhabited___redArg(v_inst_3414_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitETask___redArg___lam__0(lean_object* v_00_u03b1_3416_, lean_object* v_t_3417_){
_start:
{
lean_object* v___x_3419_; 
v___x_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3419_, 0, v_t_3417_);
return v___x_3419_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitETask___redArg___lam__0___boxed(lean_object* v_00_u03b1_3420_, lean_object* v_t_3421_, lean_object* v___y_3422_){
_start:
{
lean_object* v_res_3423_; 
v_res_3423_ = l_Std_Async_EAsync_instMonadAwaitETask___redArg___lam__0(v_00_u03b1_3420_, v_t_3421_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitETask___redArg(){
_start:
{
lean_object* v___f_3426_; 
v___f_3426_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAwaitETask___redArg___closed__0));
return v___f_3426_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitETask___redArg___boxed(lean_object* v___dummy_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l_Std_Async_EAsync_instMonadAwaitETask___redArg();
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitETask(lean_object* v_00_u03b5_3429_){
_start:
{
lean_object* v___f_3430_; 
v___f_3430_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAwaitETask___redArg___closed__0));
return v___f_3430_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitTask___redArg___lam__1(lean_object* v___f_3431_, lean_object* v_00_u03b1_3432_, lean_object* v_t_3433_){
_start:
{
lean_object* v___x_3435_; uint8_t v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3435_ = lean_unsigned_to_nat(0u);
v___x_3436_ = 0;
v___x_3437_ = lean_task_map(v___f_3431_, v_t_3433_, v___x_3435_, v___x_3436_);
v___x_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3437_);
return v___x_3438_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitTask___redArg___lam__1___boxed(lean_object* v___f_3439_, lean_object* v_00_u03b1_3440_, lean_object* v_t_3441_, lean_object* v___y_3442_){
_start:
{
lean_object* v_res_3443_; 
v_res_3443_ = l_Std_Async_EAsync_instMonadAwaitTask___redArg___lam__1(v___f_3439_, v_00_u03b1_3440_, v_t_3441_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitTask___redArg(){
_start:
{
lean_object* v___f_3447_; 
v___f_3447_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAwaitTask___redArg___closed__0));
return v___f_3447_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitTask___redArg___boxed(lean_object* v___dummy_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l_Std_Async_EAsync_instMonadAwaitTask___redArg();
return v_res_3449_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonadAwaitTask___closed__0(void){
_start:
{
lean_object* v___x_3450_; 
v___x_3450_ = l_Std_Async_EAsync_instMonadAwaitTask___redArg();
return v___x_3450_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitTask(lean_object* v_00_u03b5_3451_){
_start:
{
lean_object* v___x_3452_; 
v___x_3452_ = lean_obj_once(&l_Std_Async_EAsync_instMonadAwaitTask___closed__0, &l_Std_Async_EAsync_instMonadAwaitTask___closed__0_once, _init_l_Std_Async_EAsync_instMonadAwaitTask___closed__0);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___lam__0(lean_object* v_00_u03b1_3453_, lean_object* v_t_3454_){
_start:
{
lean_object* v___x_3456_; 
v___x_3456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3456_, 0, v_t_3454_);
return v___x_3456_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___lam__0___boxed(lean_object* v_00_u03b1_3457_, lean_object* v_t_3458_, lean_object* v___y_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___lam__0(v_00_u03b1_3457_, v_t_3458_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitPromise___redArg___lam__1(lean_object* v___f_3463_, lean_object* v_00_u03b1_3464_, lean_object* v_t_3465_){
_start:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; uint8_t v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3467_ = l_IO_Promise_result_x21___redArg(v_t_3465_);
v___x_3468_ = lean_unsigned_to_nat(0u);
v___x_3469_ = 0;
v___x_3470_ = lean_task_map(v___f_3463_, v___x_3467_, v___x_3468_, v___x_3469_);
v___x_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
return v___x_3471_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitPromise___redArg___lam__1___boxed(lean_object* v___f_3472_, lean_object* v_00_u03b1_3473_, lean_object* v_t_3474_, lean_object* v___y_3475_){
_start:
{
lean_object* v_res_3476_; 
v_res_3476_ = l_Std_Async_EAsync_instMonadAwaitPromise___redArg___lam__1(v___f_3472_, v_00_u03b1_3473_, v_t_3474_);
lean_dec(v_t_3474_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitPromise___redArg(){
_start:
{
lean_object* v___f_3480_; 
v___f_3480_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAwaitPromise___redArg___closed__0));
return v___f_3480_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitPromise___redArg___boxed(lean_object* v___dummy_3481_){
_start:
{
lean_object* v_res_3482_; 
v_res_3482_ = l_Std_Async_EAsync_instMonadAwaitPromise___redArg();
return v_res_3482_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonadAwaitPromise___closed__0(void){
_start:
{
lean_object* v___x_3483_; 
v___x_3483_ = l_Std_Async_EAsync_instMonadAwaitPromise___redArg();
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitPromise(lean_object* v_00_u03b5_3484_){
_start:
{
lean_object* v___x_3485_; 
v___x_3485_ = lean_obj_once(&l_Std_Async_EAsync_instMonadAwaitPromise___closed__0, &l_Std_Async_EAsync_instMonadAwaitPromise___closed__0_once, _init_l_Std_Async_EAsync_instMonadAwaitPromise___closed__0);
return v___x_3485_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncETask___redArg___lam__1(lean_object* v___f_3486_, lean_object* v_00_u03b1_3487_, lean_object* v_t_3488_, lean_object* v_prio_3489_){
_start:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; uint8_t v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3491_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_3491_, 0, lean_box(0));
lean_closure_set(v___x_3491_, 1, v_t_3488_);
v___x_3492_ = lean_io_as_task(v___x_3491_, v_prio_3489_);
v___x_3493_ = lean_unsigned_to_nat(0u);
v___x_3494_ = 1;
v___x_3495_ = lean_task_bind(v___x_3492_, v___f_3486_, v___x_3493_, v___x_3494_);
v___x_3496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3495_);
v___x_3497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3496_);
return v___x_3497_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncETask___redArg___lam__1___boxed(lean_object* v___f_3498_, lean_object* v_00_u03b1_3499_, lean_object* v_t_3500_, lean_object* v_prio_3501_, lean_object* v___y_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l_Std_Async_EAsync_instMonadAsyncETask___redArg___lam__1(v___f_3498_, v_00_u03b1_3499_, v_t_3500_, v_prio_3501_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncETask___redArg(){
_start:
{
lean_object* v___f_3507_; 
v___f_3507_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncETask___redArg___closed__0));
return v___f_3507_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncETask___redArg___boxed(lean_object* v___dummy_3508_){
_start:
{
lean_object* v_res_3509_; 
v_res_3509_ = l_Std_Async_EAsync_instMonadAsyncETask___redArg();
return v_res_3509_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonadAsyncETask___closed__0(void){
_start:
{
lean_object* v___x_3510_; 
v___x_3510_ = l_Std_Async_EAsync_instMonadAsyncETask___redArg();
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncETask(lean_object* v_00_u03b5_3511_){
_start:
{
lean_object* v___x_3512_; 
v___x_3512_ = lean_obj_once(&l_Std_Async_EAsync_instMonadAsyncETask___closed__0, &l_Std_Async_EAsync_instMonadAsyncETask___closed__0_once, _init_l_Std_Async_EAsync_instMonadAsyncETask___closed__0);
return v___x_3512_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__0(lean_object* v_x_3513_){
_start:
{
if (lean_obj_tag(v_x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3515_; 
v_a_3514_ = lean_ctor_get(v_x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref_known(v_x_3513_, 1);
v___x_3515_ = lean_task_pure(v_a_3514_);
return v___x_3515_;
}
else
{
lean_object* v_a_3516_; 
v_a_3516_ = lean_ctor_get(v_x_3513_, 0);
lean_inc_ref(v_a_3516_);
lean_dec_ref_known(v_x_3513_, 1);
return v_a_3516_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__1(lean_object* v___f_3517_, lean_object* v_00_u03b1_3518_, lean_object* v_t_3519_, lean_object* v_prio_3520_){
_start:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; uint8_t v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3522_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_3522_, 0, lean_box(0));
lean_closure_set(v___x_3522_, 1, v_t_3519_);
v___x_3523_ = lean_io_as_task(v___x_3522_, v_prio_3520_);
v___x_3524_ = lean_unsigned_to_nat(0u);
v___x_3525_ = 1;
v___x_3526_ = lean_task_bind(v___x_3523_, v___f_3517_, v___x_3524_, v___x_3525_);
v___x_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3526_);
v___x_3528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3527_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__1___boxed(lean_object* v___f_3529_, lean_object* v_00_u03b1_3530_, lean_object* v_t_3531_, lean_object* v_prio_3532_, lean_object* v___y_3533_){
_start:
{
lean_object* v_res_3534_; 
v_res_3534_ = l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__1(v___f_3529_, v_00_u03b1_3530_, v_t_3531_, v_prio_3532_);
return v_res_3534_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___lam__0(lean_object* v_00_u03b1_3539_, lean_object* v_x_3540_){
_start:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3542_ = lean_apply_1(v_x_3540_, lean_box(0));
v___x_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3542_);
v___x_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3543_);
return v___x_3544_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___lam__0___boxed(lean_object* v_00_u03b1_3545_, lean_object* v_x_3546_, lean_object* v___y_3547_){
_start:
{
lean_object* v_res_3548_; 
v_res_3548_ = l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___lam__0(v_00_u03b1_3545_, v_x_3546_);
return v_res_3548_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO___redArg(){
_start:
{
lean_object* v___f_3551_; 
v___f_3551_ = ((lean_object*)(l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___closed__0));
return v___f_3551_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___boxed(lean_object* v___dummy_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_Std_Async_EAsync_instMonadLiftBaseIO___redArg();
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO(lean_object* v_00_u03b5_3554_){
_start:
{
lean_object* v___f_3555_; 
v___f_3555_ = ((lean_object*)(l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___closed__0));
return v___f_3555_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___lam__0(lean_object* v_00_u03b1_3556_, lean_object* v_x_3557_){
_start:
{
lean_object* v_val_3560_; lean_object* v___x_3562_; 
v___x_3562_ = lean_apply_1(v_x_3557_, lean_box(0));
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
v_a_3563_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3565_ = v___x_3562_;
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3562_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
lean_ctor_set_tag(v___x_3565_, 1);
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
v_val_3560_ = v___x_3568_;
goto v___jp_3559_;
}
}
}
else
{
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3578_; 
v_a_3571_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3573_ = v___x_3562_;
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_3562_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3576_; 
if (v_isShared_3574_ == 0)
{
lean_ctor_set_tag(v___x_3573_, 0);
v___x_3576_ = v___x_3573_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_a_3571_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
v_val_3560_ = v___x_3576_;
goto v___jp_3559_;
}
}
}
v___jp_3559_:
{
lean_object* v___x_3561_; 
v___x_3561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3561_, 0, v_val_3560_);
return v___x_3561_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___lam__0___boxed(lean_object* v_00_u03b1_3579_, lean_object* v_x_3580_, lean_object* v___y_3581_){
_start:
{
lean_object* v_res_3582_; 
v_res_3582_ = l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___lam__0(v_00_u03b1_3579_, v_x_3580_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1___redArg(){
_start:
{
lean_object* v___f_3585_; 
v___f_3585_ = ((lean_object*)(l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___closed__0));
return v___f_3585_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___boxed(lean_object* v___dummy_3586_){
_start:
{
lean_object* v_res_3587_; 
v_res_3587_ = l_Std_Async_EAsync_instMonadLiftEIO__1___redArg();
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1(lean_object* v_00_u03b5_3588_){
_start:
{
lean_object* v___f_3589_; 
v___f_3589_ = ((lean_object*)(l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___closed__0));
return v___f_3589_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg___lam__1(lean_object* v___f_3590_, lean_object* v_00_u03b1_3591_, lean_object* v_x_3592_){
_start:
{
lean_object* v___x_3594_; uint8_t v___x_3595_; lean_object* v___x_3596_; 
v___x_3594_ = lean_unsigned_to_nat(0u);
v___x_3595_ = 0;
v___x_3596_ = lean_apply_1(v_x_3592_, lean_box(0));
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3605_; 
lean_dec_ref(v___f_3590_);
v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3599_ = v___x_3596_;
v_isShared_3600_ = v_isSharedCheck_3605_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v___x_3596_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3605_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3601_; lean_object* v___x_3603_; 
v___x_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3601_, 0, v_a_3597_);
if (v_isShared_3600_ == 0)
{
lean_ctor_set(v___x_3599_, 0, v___x_3601_);
v___x_3603_ = v___x_3599_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v___x_3601_);
v___x_3603_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
return v___x_3603_;
}
}
}
else
{
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3614_; 
v_a_3606_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3608_ = v___x_3596_;
v_isShared_3609_ = v_isSharedCheck_3614_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v___x_3596_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3614_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3610_; lean_object* v___x_3612_; 
v___x_3610_ = lean_task_map(v___f_3590_, v_a_3606_, v___x_3594_, v___x_3595_);
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 0, v___x_3610_);
v___x_3612_ = v___x_3608_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___x_3610_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg___lam__1___boxed(lean_object* v___f_3615_, lean_object* v_00_u03b1_3616_, lean_object* v_x_3617_, lean_object* v___y_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg___lam__1(v___f_3615_, v_00_u03b1_3616_, v_x_3617_);
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg(){
_start:
{
lean_object* v___f_3623_; 
v___f_3623_ = ((lean_object*)(l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg___closed__0));
return v___f_3623_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg___boxed(lean_object* v___dummy_3624_){
_start:
{
lean_object* v_res_3625_; 
v_res_3625_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
return v_res_3625_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonadLiftBaseAsync___closed__0(void){
_start:
{
lean_object* v___x_3626_; 
v___x_3626_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync(lean_object* v_00_u03b5_3627_){
_start:
{
lean_object* v___x_3628_; 
v___x_3628_ = lean_obj_once(&l_Std_Async_EAsync_instMonadLiftBaseAsync___closed__0, &l_Std_Async_EAsync_instMonadLiftBaseAsync___closed__0_once, _init_l_Std_Async_EAsync_instMonadLiftBaseAsync___closed__0);
return v___x_3628_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___lam__0___boxed(lean_object* v_promise_3629_, lean_object* v_f_3630_, lean_object* v_prio_3631_, lean_object* v_x_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v_res_3634_; 
v_res_3634_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___lam__0(v_promise_3629_, v_f_3630_, v_prio_3631_, v_x_3632_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(lean_object* v_f_3635_, lean_object* v_prio_3636_, lean_object* v_promise_3637_, lean_object* v_b_3638_){
_start:
{
lean_object* v___f_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
lean_inc(v_prio_3636_);
lean_inc_ref_n(v_f_3635_, 2);
lean_inc(v_promise_3637_);
v___f_3640_ = lean_alloc_closure((void*)(l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3640_, 0, v_promise_3637_);
lean_closure_set(v___f_3640_, 1, v_f_3635_);
lean_closure_set(v___f_3640_, 2, v_prio_3636_);
v___x_3641_ = lean_box(0);
v___x_3642_ = lean_apply_3(v_f_3635_, v___x_3641_, v_b_3638_, lean_box(0));
if (lean_obj_tag(v___x_3642_) == 0)
{
lean_object* v_a_3643_; 
lean_dec_ref(v___f_3640_);
v_a_3643_ = lean_ctor_get(v___x_3642_, 0);
lean_inc(v_a_3643_);
lean_dec_ref_known(v___x_3642_, 1);
if (lean_obj_tag(v_a_3643_) == 0)
{
lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3652_; 
lean_dec(v_prio_3636_);
lean_dec_ref(v_f_3635_);
v_a_3644_ = lean_ctor_get(v_a_3643_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v_a_3643_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3646_ = v_a_3643_;
v_isShared_3647_ = v_isSharedCheck_3652_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v_a_3643_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3652_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3649_; 
if (v_isShared_3647_ == 0)
{
v___x_3649_ = v___x_3646_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3644_);
v___x_3649_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
lean_object* v___x_3650_; 
v___x_3650_ = lean_io_promise_resolve(v___x_3649_, v_promise_3637_);
lean_dec(v_promise_3637_);
return v___x_3650_;
}
}
}
else
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3664_; 
v_a_3653_ = lean_ctor_get(v_a_3643_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v_a_3643_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3655_ = v_a_3643_;
v_isShared_3656_ = v_isSharedCheck_3664_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v_a_3643_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3664_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
if (lean_obj_tag(v_a_3653_) == 0)
{
lean_object* v_a_3657_; lean_object* v___x_3659_; 
lean_dec(v_prio_3636_);
lean_dec_ref(v_f_3635_);
v_a_3657_ = lean_ctor_get(v_a_3653_, 0);
lean_inc(v_a_3657_);
lean_dec_ref_known(v_a_3653_, 1);
if (v_isShared_3656_ == 0)
{
lean_ctor_set(v___x_3655_, 0, v_a_3657_);
v___x_3659_ = v___x_3655_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_a_3657_);
v___x_3659_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
lean_object* v___x_3660_; 
v___x_3660_ = lean_io_promise_resolve(v___x_3659_, v_promise_3637_);
lean_dec(v_promise_3637_);
return v___x_3660_;
}
}
else
{
lean_object* v_a_3662_; 
lean_del_object(v___x_3655_);
v_a_3662_ = lean_ctor_get(v_a_3653_, 0);
lean_inc(v_a_3662_);
lean_dec_ref_known(v_a_3653_, 1);
v_b_3638_ = v_a_3662_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3665_; uint8_t v___x_3666_; lean_object* v___x_3667_; 
lean_dec(v_promise_3637_);
lean_dec_ref(v_f_3635_);
v_a_3665_ = lean_ctor_get(v___x_3642_, 0);
lean_inc_ref(v_a_3665_);
lean_dec_ref_known(v___x_3642_, 1);
v___x_3666_ = 0;
v___x_3667_ = l_BaseIO_chainTask___redArg(v_a_3665_, v___f_3640_, v_prio_3636_, v___x_3666_);
return v___x_3667_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___lam__0(lean_object* v_promise_3668_, lean_object* v_f_3669_, lean_object* v_prio_3670_, lean_object* v_x_3671_){
_start:
{
if (lean_obj_tag(v_x_3671_) == 0)
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3681_; 
lean_dec(v_prio_3670_);
lean_dec_ref(v_f_3669_);
v_a_3673_ = lean_ctor_get(v_x_3671_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v_x_3671_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3675_ = v_x_3671_;
v_isShared_3676_ = v_isSharedCheck_3681_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v_x_3671_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3681_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3678_; 
if (v_isShared_3676_ == 0)
{
v___x_3678_ = v___x_3675_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3673_);
v___x_3678_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
lean_object* v___x_3679_; 
v___x_3679_ = lean_io_promise_resolve(v___x_3678_, v_promise_3668_);
lean_dec(v_promise_3668_);
return v___x_3679_;
}
}
}
else
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3693_; 
v_a_3682_ = lean_ctor_get(v_x_3671_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v_x_3671_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3684_ = v_x_3671_;
v_isShared_3685_ = v_isSharedCheck_3693_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v_x_3671_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3693_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
if (lean_obj_tag(v_a_3682_) == 0)
{
lean_object* v_a_3686_; lean_object* v___x_3688_; 
lean_dec(v_prio_3670_);
lean_dec_ref(v_f_3669_);
v_a_3686_ = lean_ctor_get(v_a_3682_, 0);
lean_inc(v_a_3686_);
lean_dec_ref_known(v_a_3682_, 1);
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 0, v_a_3686_);
v___x_3688_ = v___x_3684_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3686_);
v___x_3688_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
lean_object* v___x_3689_; 
v___x_3689_ = lean_io_promise_resolve(v___x_3688_, v_promise_3668_);
lean_dec(v_promise_3668_);
return v___x_3689_;
}
}
else
{
lean_object* v_a_3691_; lean_object* v___x_3692_; 
lean_del_object(v___x_3684_);
v_a_3691_ = lean_ctor_get(v_a_3682_, 0);
lean_inc(v_a_3691_);
lean_dec_ref_known(v_a_3682_, 1);
v___x_3692_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(v_f_3669_, v_prio_3670_, v_promise_3668_, v_a_3691_);
return v___x_3692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___boxed(lean_object* v_f_3694_, lean_object* v_prio_3695_, lean_object* v_promise_3696_, lean_object* v_b_3697_, lean_object* v_a_3698_){
_start:
{
lean_object* v_res_3699_; 
v_res_3699_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(v_f_3694_, v_prio_3695_, v_promise_3696_, v_b_3697_);
return v_res_3699_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_object* v_00_u03b5_3700_, lean_object* v_00_u03b2_3701_, lean_object* v_f_3702_, lean_object* v_prio_3703_, lean_object* v_promise_3704_, lean_object* v_b_3705_){
_start:
{
lean_object* v___x_3707_; 
v___x_3707_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(v_f_3702_, v_prio_3703_, v_promise_3704_, v_b_3705_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___boxed(lean_object* v_00_u03b5_3708_, lean_object* v_00_u03b2_3709_, lean_object* v_f_3710_, lean_object* v_prio_3711_, lean_object* v_promise_3712_, lean_object* v_b_3713_, lean_object* v_a_3714_){
_start:
{
lean_object* v_res_3715_; 
v_res_3715_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(v_00_u03b5_3708_, v_00_u03b2_3709_, v_f_3710_, v_prio_3711_, v_promise_3712_, v_b_3713_);
return v_res_3715_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg___lam__0(lean_object* v_a_3716_, lean_object* v_x_3717_){
_start:
{
if (lean_obj_tag(v_x_3717_) == 0)
{
lean_object* v_a_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3727_; 
v_a_3719_ = lean_ctor_get(v_x_3717_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v_x_3717_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3721_ = v_x_3717_;
v_isShared_3722_ = v_isSharedCheck_3727_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_a_3719_);
lean_dec(v_x_3717_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3727_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
lean_object* v___x_3724_; 
if (v_isShared_3722_ == 0)
{
v___x_3724_ = v___x_3721_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3719_);
v___x_3724_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
lean_object* v___x_3725_; 
v___x_3725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3724_);
return v___x_3725_;
}
}
}
else
{
lean_object* v___x_3728_; lean_object* v___x_3729_; 
lean_dec_ref_known(v_x_3717_, 1);
v___x_3728_ = l_IO_Promise_result_x21___redArg(v_a_3716_);
v___x_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3728_);
return v___x_3729_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg___lam__0___boxed(lean_object* v_a_3730_, lean_object* v_x_3731_, lean_object* v___y_3732_){
_start:
{
lean_object* v_res_3733_; 
v_res_3733_ = l_Std_Async_EAsync_forIn___redArg___lam__0(v_a_3730_, v_x_3731_);
lean_dec(v_a_3730_);
return v_res_3733_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg___lam__1(lean_object* v_f_3734_, lean_object* v_prio_3735_, lean_object* v_init_3736_, lean_object* v_x_3737_){
_start:
{
if (lean_obj_tag(v_x_3737_) == 0)
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3747_; 
lean_dec(v_init_3736_);
lean_dec(v_prio_3735_);
lean_dec_ref(v_f_3734_);
v_a_3739_ = lean_ctor_get(v_x_3737_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v_x_3737_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3741_ = v_x_3737_;
v_isShared_3742_ = v_isSharedCheck_3747_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v_x_3737_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3747_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_a_3739_);
v___x_3744_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
lean_object* v___x_3745_; 
v___x_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3744_);
return v___x_3745_;
}
}
}
else
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3761_; 
v_a_3748_ = lean_ctor_get(v_x_3737_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v_x_3737_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3750_ = v_x_3737_;
v_isShared_3751_ = v_isSharedCheck_3761_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v_x_3737_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3761_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___f_3752_; lean_object* v___x_3753_; uint8_t v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3757_; 
lean_inc(v_a_3748_);
v___f_3752_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_forIn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3752_, 0, v_a_3748_);
v___x_3753_ = lean_unsigned_to_nat(0u);
v___x_3754_ = 0;
v___x_3755_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(v_f_3734_, v_prio_3735_, v_a_3748_, v_init_3736_);
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 0, v___x_3755_);
v___x_3757_ = v___x_3750_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3755_);
v___x_3757_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3758_, 0, v___x_3757_);
v___x_3759_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3753_, v___x_3754_, v___x_3758_, v___f_3752_);
return v___x_3759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg___lam__1___boxed(lean_object* v_f_3762_, lean_object* v_prio_3763_, lean_object* v_init_3764_, lean_object* v_x_3765_, lean_object* v___y_3766_){
_start:
{
lean_object* v_res_3767_; 
v_res_3767_ = l_Std_Async_EAsync_forIn___redArg___lam__1(v_f_3762_, v_prio_3763_, v_init_3764_, v_x_3765_);
return v_res_3767_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg(lean_object* v_init_3768_, lean_object* v_f_3769_, lean_object* v_prio_3770_){
_start:
{
lean_object* v___f_3772_; lean_object* v___x_3773_; uint8_t v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; 
v___f_3772_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_forIn___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_3772_, 0, v_f_3769_);
lean_closure_set(v___f_3772_, 1, v_prio_3770_);
lean_closure_set(v___f_3772_, 2, v_init_3768_);
v___x_3773_ = lean_unsigned_to_nat(0u);
v___x_3774_ = 0;
v___x_3775_ = lean_io_promise_new();
v___x_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3775_);
v___x_3777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3776_);
v___x_3778_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3773_, v___x_3774_, v___x_3777_, v___f_3772_);
return v___x_3778_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg___boxed(lean_object* v_init_3779_, lean_object* v_f_3780_, lean_object* v_prio_3781_, lean_object* v_a_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Std_Async_EAsync_forIn___redArg(v_init_3779_, v_f_3780_, v_prio_3781_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn(lean_object* v_00_u03b5_3784_, lean_object* v_00_u03b2_3785_, lean_object* v_init_3786_, lean_object* v_f_3787_, lean_object* v_prio_3788_){
_start:
{
lean_object* v___f_3790_; lean_object* v___x_3791_; uint8_t v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___f_3790_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_forIn___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_3790_, 0, v_f_3787_);
lean_closure_set(v___f_3790_, 1, v_prio_3788_);
lean_closure_set(v___f_3790_, 2, v_init_3786_);
v___x_3791_ = lean_unsigned_to_nat(0u);
v___x_3792_ = 0;
v___x_3793_ = lean_io_promise_new();
v___x_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3793_);
v___x_3795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3794_);
v___x_3796_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3791_, v___x_3792_, v___x_3795_, v___f_3790_);
return v___x_3796_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___boxed(lean_object* v_00_u03b5_3797_, lean_object* v_00_u03b2_3798_, lean_object* v_init_3799_, lean_object* v_f_3800_, lean_object* v_prio_3801_, lean_object* v_a_3802_){
_start:
{
lean_object* v_res_3803_; 
v_res_3803_ = l_Std_Async_EAsync_forIn(v_00_u03b5_3797_, v_00_u03b2_3798_, v_init_3799_, v_f_3800_, v_prio_3801_);
return v_res_3803_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__1(lean_object* v_f_3804_, lean_object* v___x_3805_, lean_object* v_init_3806_, lean_object* v_x_3807_){
_start:
{
if (lean_obj_tag(v_x_3807_) == 0)
{
lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3817_; 
lean_dec(v_init_3806_);
lean_dec(v___x_3805_);
lean_dec_ref(v_f_3804_);
v_a_3809_ = lean_ctor_get(v_x_3807_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v_x_3807_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3811_ = v_x_3807_;
v_isShared_3812_ = v_isSharedCheck_3817_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_dec(v_x_3807_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3817_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3814_; 
if (v_isShared_3812_ == 0)
{
v___x_3814_ = v___x_3811_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3809_);
v___x_3814_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
lean_object* v___x_3815_; 
v___x_3815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3814_);
return v___x_3815_;
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3830_; 
v_a_3818_ = lean_ctor_get(v_x_3807_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v_x_3807_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3820_ = v_x_3807_;
v_isShared_3821_ = v_isSharedCheck_3830_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v_x_3807_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3830_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___f_3822_; uint8_t v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3826_; 
lean_inc(v_a_3818_);
v___f_3822_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_forIn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3822_, 0, v_a_3818_);
v___x_3823_ = 0;
lean_inc(v___x_3805_);
v___x_3824_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(v_f_3804_, v___x_3805_, v_a_3818_, v_init_3806_);
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 0, v___x_3824_);
v___x_3826_ = v___x_3820_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v___x_3824_);
v___x_3826_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
lean_object* v___x_3827_; lean_object* v___x_3828_; 
v___x_3827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3826_);
v___x_3828_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3805_, v___x_3823_, v___x_3827_, v___f_3822_);
return v___x_3828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__1___boxed(lean_object* v_f_3831_, lean_object* v___x_3832_, lean_object* v_init_3833_, lean_object* v_x_3834_, lean_object* v___y_3835_){
_start:
{
lean_object* v_res_3836_; 
v_res_3836_ = l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__1(v_f_3831_, v___x_3832_, v_init_3833_, v_x_3834_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__0(lean_object* v_00_u03b2_3837_, lean_object* v_x_3838_, lean_object* v_init_3839_, lean_object* v_f_3840_){
_start:
{
lean_object* v___x_3842_; lean_object* v___f_3843_; uint8_t v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3842_ = lean_unsigned_to_nat(0u);
v___f_3843_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_3843_, 0, v_f_3840_);
lean_closure_set(v___f_3843_, 1, v___x_3842_);
lean_closure_set(v___f_3843_, 2, v_init_3839_);
v___x_3844_ = 0;
v___x_3845_ = lean_io_promise_new();
v___x_3846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3846_, 0, v___x_3845_);
v___x_3847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3846_);
v___x_3848_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3842_, v___x_3844_, v___x_3847_, v___f_3843_);
return v___x_3848_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__0___boxed(lean_object* v_00_u03b2_3849_, lean_object* v_x_3850_, lean_object* v_init_3851_, lean_object* v_f_3852_, lean_object* v___y_3853_){
_start:
{
lean_object* v_res_3854_; 
v_res_3854_ = l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__0(v_00_u03b2_3849_, v_x_3850_, v_init_3851_, v_f_3852_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___redArg(){
_start:
{
lean_object* v___f_3857_; 
v___f_3857_ = ((lean_object*)(l_Std_Async_EAsync_instForInLoopUnit___redArg___closed__0));
return v___f_3857_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___redArg___boxed(lean_object* v___dummy_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l_Std_Async_EAsync_instForInLoopUnit___redArg();
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit(lean_object* v_00_u03b5_3860_){
_start:
{
lean_object* v___f_3861_; 
v___f_3861_ = ((lean_object*)(l_Std_Async_EAsync_instForInLoopUnit___redArg___closed__0));
return v___f_3861_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofExcept___redArg(lean_object* v_except_3862_){
_start:
{
lean_object* v___x_3864_; 
v___x_3864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3864_, 0, v_except_3862_);
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofExcept___redArg___boxed(lean_object* v_except_3865_, lean_object* v_a_3866_){
_start:
{
lean_object* v_res_3867_; 
v_res_3867_ = l_Std_Async_EAsync_ofExcept___redArg(v_except_3865_);
return v_res_3867_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofExcept(lean_object* v_00_u03b5_3868_, lean_object* v_00_u03b1_3869_, lean_object* v_except_3870_){
_start:
{
lean_object* v___x_3872_; 
v___x_3872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3872_, 0, v_except_3870_);
return v___x_3872_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofExcept___boxed(lean_object* v_00_u03b5_3873_, lean_object* v_00_u03b1_3874_, lean_object* v_except_3875_, lean_object* v_a_3876_){
_start:
{
lean_object* v_res_3877_; 
v_res_3877_ = l_Std_Async_EAsync_ofExcept(v_00_u03b5_3873_, v_00_u03b1_3874_, v_except_3875_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__1(lean_object* v_a_3878_, lean_object* v_x_3879_){
_start:
{
if (lean_obj_tag(v_x_3879_) == 0)
{
lean_object* v_a_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3889_; 
lean_dec(v_a_3878_);
v_a_3881_ = lean_ctor_get(v_x_3879_, 0);
v_isSharedCheck_3889_ = !lean_is_exclusive(v_x_3879_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3883_ = v_x_3879_;
v_isShared_3884_ = v_isSharedCheck_3889_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_a_3881_);
lean_dec(v_x_3879_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3889_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3886_; 
if (v_isShared_3884_ == 0)
{
v___x_3886_ = v___x_3883_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_a_3881_);
v___x_3886_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
lean_object* v___x_3887_; 
v___x_3887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3886_);
return v___x_3887_;
}
}
}
else
{
lean_object* v_a_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3899_; 
v_a_3890_ = lean_ctor_get(v_x_3879_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v_x_3879_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3892_ = v_x_3879_;
v_isShared_3893_ = v_isSharedCheck_3899_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_a_3890_);
lean_dec(v_x_3879_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3899_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
lean_object* v___x_3894_; lean_object* v___x_3896_; 
v___x_3894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3894_, 0, v_a_3878_);
lean_ctor_set(v___x_3894_, 1, v_a_3890_);
if (v_isShared_3893_ == 0)
{
lean_ctor_set(v___x_3892_, 0, v___x_3894_);
v___x_3896_ = v___x_3892_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v___x_3894_);
v___x_3896_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
lean_object* v___x_3897_; 
v___x_3897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3896_);
return v___x_3897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__1___boxed(lean_object* v_a_3900_, lean_object* v_x_3901_, lean_object* v___y_3902_){
_start:
{
lean_object* v_res_3903_; 
v_res_3903_ = l_Std_Async_EAsync_concurrently___redArg___lam__1(v_a_3900_, v_x_3901_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__0(lean_object* v_a_3904_, lean_object* v_x_3905_){
_start:
{
if (lean_obj_tag(v_x_3905_) == 0)
{
lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3915_; 
lean_dec_ref(v_a_3904_);
v_a_3907_ = lean_ctor_get(v_x_3905_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v_x_3905_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3909_ = v_x_3905_;
v_isShared_3910_ = v_isSharedCheck_3915_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v_x_3905_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3915_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3912_; 
if (v_isShared_3910_ == 0)
{
v___x_3912_ = v___x_3909_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3907_);
v___x_3912_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
lean_object* v___x_3913_; 
v___x_3913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3912_);
return v___x_3913_;
}
}
}
else
{
lean_object* v_a_3916_; lean_object* v___f_3917_; lean_object* v___x_3918_; uint8_t v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
v_a_3916_ = lean_ctor_get(v_x_3905_, 0);
lean_inc(v_a_3916_);
lean_dec_ref_known(v_x_3905_, 1);
v___f_3917_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrently___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3917_, 0, v_a_3916_);
v___x_3918_ = lean_unsigned_to_nat(0u);
v___x_3919_ = 0;
v___x_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3920_, 0, v_a_3904_);
v___x_3921_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3918_, v___x_3919_, v___x_3920_, v___f_3917_);
return v___x_3921_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__0___boxed(lean_object* v_a_3922_, lean_object* v_x_3923_, lean_object* v___y_3924_){
_start:
{
lean_object* v_res_3925_; 
v_res_3925_ = l_Std_Async_EAsync_concurrently___redArg___lam__0(v_a_3922_, v_x_3923_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__2(lean_object* v_a_3926_, lean_object* v_x_3927_){
_start:
{
if (lean_obj_tag(v_x_3927_) == 0)
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3937_; 
lean_dec_ref(v_a_3926_);
v_a_3929_ = lean_ctor_get(v_x_3927_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v_x_3927_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3931_ = v_x_3927_;
v_isShared_3932_ = v_isSharedCheck_3937_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v_x_3927_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3937_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3934_; 
if (v_isShared_3932_ == 0)
{
v___x_3934_ = v___x_3931_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_a_3929_);
v___x_3934_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
lean_object* v___x_3935_; 
v___x_3935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3934_);
return v___x_3935_;
}
}
}
else
{
lean_object* v_a_3938_; lean_object* v___f_3939_; lean_object* v___x_3940_; uint8_t v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; 
v_a_3938_ = lean_ctor_get(v_x_3927_, 0);
lean_inc(v_a_3938_);
lean_dec_ref_known(v_x_3927_, 1);
v___f_3939_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrently___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3939_, 0, v_a_3938_);
v___x_3940_ = lean_unsigned_to_nat(0u);
v___x_3941_ = 0;
v___x_3942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3942_, 0, v_a_3926_);
v___x_3943_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3940_, v___x_3941_, v___x_3942_, v___f_3939_);
return v___x_3943_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__2___boxed(lean_object* v_a_3944_, lean_object* v_x_3945_, lean_object* v___y_3946_){
_start:
{
lean_object* v_res_3947_; 
v_res_3947_ = l_Std_Async_EAsync_concurrently___redArg___lam__2(v_a_3944_, v_x_3945_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__3(lean_object* v_y_3948_, lean_object* v_prio_3949_, lean_object* v___f_3950_, lean_object* v_x_3951_){
_start:
{
if (lean_obj_tag(v_x_3951_) == 0)
{
lean_object* v_a_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3961_; 
lean_dec_ref(v___f_3950_);
lean_dec(v_prio_3949_);
lean_dec_ref(v_y_3948_);
v_a_3953_ = lean_ctor_get(v_x_3951_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v_x_3951_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3955_ = v_x_3951_;
v_isShared_3956_ = v_isSharedCheck_3961_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_a_3953_);
lean_dec(v_x_3951_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3961_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3958_; 
if (v_isShared_3956_ == 0)
{
v___x_3958_ = v___x_3955_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_a_3953_);
v___x_3958_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
lean_object* v___x_3959_; 
v___x_3959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3958_);
return v___x_3959_;
}
}
}
else
{
lean_object* v_a_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3978_; 
v_a_3962_ = lean_ctor_get(v_x_3951_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v_x_3951_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3964_ = v_x_3951_;
v_isShared_3965_ = v_isSharedCheck_3978_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_a_3962_);
lean_dec(v_x_3951_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3978_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___f_3966_; lean_object* v___x_3967_; uint8_t v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; uint8_t v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3974_; 
v___f_3966_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrently___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3966_, 0, v_a_3962_);
v___x_3967_ = lean_unsigned_to_nat(0u);
v___x_3968_ = 0;
v___x_3969_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_3969_, 0, lean_box(0));
lean_closure_set(v___x_3969_, 1, v_y_3948_);
v___x_3970_ = lean_io_as_task(v___x_3969_, v_prio_3949_);
v___x_3971_ = 1;
v___x_3972_ = lean_task_bind(v___x_3970_, v___f_3950_, v___x_3967_, v___x_3971_);
if (v_isShared_3965_ == 0)
{
lean_ctor_set(v___x_3964_, 0, v___x_3972_);
v___x_3974_ = v___x_3964_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v___x_3972_);
v___x_3974_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3975_, 0, v___x_3974_);
v___x_3976_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3967_, v___x_3968_, v___x_3975_, v___f_3966_);
return v___x_3976_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__3___boxed(lean_object* v_y_3979_, lean_object* v_prio_3980_, lean_object* v___f_3981_, lean_object* v_x_3982_, lean_object* v___y_3983_){
_start:
{
lean_object* v_res_3984_; 
v_res_3984_ = l_Std_Async_EAsync_concurrently___redArg___lam__3(v_y_3979_, v_prio_3980_, v___f_3981_, v_x_3982_);
return v_res_3984_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg(lean_object* v_x_3985_, lean_object* v_y_3986_, lean_object* v_prio_3987_){
_start:
{
lean_object* v___f_3989_; lean_object* v___f_3990_; lean_object* v___x_3991_; uint8_t v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; uint8_t v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; 
v___f_3989_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
lean_inc(v_prio_3987_);
v___f_3990_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrently___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3990_, 0, v_y_3986_);
lean_closure_set(v___f_3990_, 1, v_prio_3987_);
lean_closure_set(v___f_3990_, 2, v___f_3989_);
v___x_3991_ = lean_unsigned_to_nat(0u);
v___x_3992_ = 0;
v___x_3993_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_3993_, 0, lean_box(0));
lean_closure_set(v___x_3993_, 1, v_x_3985_);
v___x_3994_ = lean_io_as_task(v___x_3993_, v_prio_3987_);
v___x_3995_ = 1;
v___x_3996_ = lean_task_bind(v___x_3994_, v___f_3989_, v___x_3991_, v___x_3995_);
v___x_3997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3997_, 0, v___x_3996_);
v___x_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3997_);
v___x_3999_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3991_, v___x_3992_, v___x_3998_, v___f_3990_);
return v___x_3999_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___boxed(lean_object* v_x_4000_, lean_object* v_y_4001_, lean_object* v_prio_4002_, lean_object* v_a_4003_){
_start:
{
lean_object* v_res_4004_; 
v_res_4004_ = l_Std_Async_EAsync_concurrently___redArg(v_x_4000_, v_y_4001_, v_prio_4002_);
return v_res_4004_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently(lean_object* v_00_u03b5_4005_, lean_object* v_00_u03b1_4006_, lean_object* v_00_u03b2_4007_, lean_object* v_x_4008_, lean_object* v_y_4009_, lean_object* v_prio_4010_){
_start:
{
lean_object* v___f_4012_; lean_object* v___f_4013_; lean_object* v___x_4014_; uint8_t v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; uint8_t v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
v___f_4012_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
lean_inc(v_prio_4010_);
v___f_4013_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrently___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_4013_, 0, v_y_4009_);
lean_closure_set(v___f_4013_, 1, v_prio_4010_);
lean_closure_set(v___f_4013_, 2, v___f_4012_);
v___x_4014_ = lean_unsigned_to_nat(0u);
v___x_4015_ = 0;
v___x_4016_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4016_, 0, lean_box(0));
lean_closure_set(v___x_4016_, 1, v_x_4008_);
v___x_4017_ = lean_io_as_task(v___x_4016_, v_prio_4010_);
v___x_4018_ = 1;
v___x_4019_ = lean_task_bind(v___x_4017_, v___f_4012_, v___x_4014_, v___x_4018_);
v___x_4020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4020_, 0, v___x_4019_);
v___x_4021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4021_, 0, v___x_4020_);
v___x_4022_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4014_, v___x_4015_, v___x_4021_, v___f_4013_);
return v___x_4022_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___boxed(lean_object* v_00_u03b5_4023_, lean_object* v_00_u03b1_4024_, lean_object* v_00_u03b2_4025_, lean_object* v_x_4026_, lean_object* v_y_4027_, lean_object* v_prio_4028_, lean_object* v_a_4029_){
_start:
{
lean_object* v_res_4030_; 
v_res_4030_ = l_Std_Async_EAsync_concurrently(v_00_u03b5_4023_, v_00_u03b1_4024_, v_00_u03b2_4025_, v_x_4026_, v_y_4027_, v_prio_4028_);
return v_res_4030_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__1(lean_object* v_x_4031_){
_start:
{
if (lean_obj_tag(v_x_4031_) == 0)
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4041_; 
v_a_4033_ = lean_ctor_get(v_x_4031_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v_x_4031_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4035_ = v_x_4031_;
v_isShared_4036_ = v_isSharedCheck_4041_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v_x_4031_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4041_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4038_; 
if (v_isShared_4036_ == 0)
{
v___x_4038_ = v___x_4035_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_a_4033_);
v___x_4038_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
lean_object* v___x_4039_; 
v___x_4039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4039_, 0, v___x_4038_);
return v___x_4039_;
}
}
}
else
{
lean_object* v_a_4042_; lean_object* v___x_4043_; 
v_a_4042_ = lean_ctor_get(v_x_4031_, 0);
lean_inc(v_a_4042_);
lean_dec_ref_known(v_x_4031_, 1);
v___x_4043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4043_, 0, v_a_4042_);
return v___x_4043_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__1___boxed(lean_object* v_x_4044_, lean_object* v___y_4045_){
_start:
{
lean_object* v_res_4046_; 
v_res_4046_ = l_Std_Async_EAsync_race___redArg___lam__1(v_x_4044_);
return v_res_4046_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__0(lean_object* v_a_4047_){
_start:
{
lean_object* v___x_4048_; 
v___x_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4048_, 0, v_a_4047_);
return v___x_4048_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__3(lean_object* v_a_4049_, lean_object* v_value_4050_){
_start:
{
lean_object* v___x_4052_; 
v___x_4052_ = lean_io_promise_resolve(v_value_4050_, v_a_4049_);
return v___x_4052_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__3___boxed(lean_object* v_a_4053_, lean_object* v_value_4054_, lean_object* v___y_4055_){
_start:
{
lean_object* v_res_4056_; 
v_res_4056_ = l_Std_Async_EAsync_race___redArg___lam__3(v_a_4053_, v_value_4054_);
lean_dec(v_a_4053_);
return v_res_4056_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__2(lean_object* v_a_4057_, lean_object* v___f_4058_, lean_object* v___f_4059_, lean_object* v_x_4060_){
_start:
{
if (lean_obj_tag(v_x_4060_) == 0)
{
lean_object* v_a_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4070_; 
lean_dec_ref(v___f_4059_);
lean_dec_ref(v___f_4058_);
v_a_4062_ = lean_ctor_get(v_x_4060_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v_x_4060_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4064_ = v_x_4060_;
v_isShared_4065_ = v_isSharedCheck_4070_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_a_4062_);
lean_dec(v_x_4060_);
v___x_4064_ = lean_box(0);
v_isShared_4065_ = v_isSharedCheck_4070_;
goto v_resetjp_4063_;
}
v_resetjp_4063_:
{
lean_object* v___x_4067_; 
if (v_isShared_4065_ == 0)
{
v___x_4067_ = v___x_4064_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_a_4062_);
v___x_4067_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
lean_object* v___x_4068_; 
v___x_4068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4067_);
return v___x_4068_;
}
}
}
else
{
lean_object* v___x_4071_; lean_object* v___x_4072_; uint8_t v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
lean_dec_ref_known(v_x_4060_, 1);
v___x_4071_ = l_IO_Promise_result_x21___redArg(v_a_4057_);
v___x_4072_ = lean_unsigned_to_nat(0u);
v___x_4073_ = 0;
v___x_4074_ = lean_task_map(v___f_4058_, v___x_4071_, v___x_4072_, v___x_4073_);
v___x_4075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4075_, 0, v___x_4074_);
v___x_4076_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4072_, v___x_4073_, v___x_4075_, v___f_4059_);
return v___x_4076_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__2___boxed(lean_object* v_a_4077_, lean_object* v___f_4078_, lean_object* v___f_4079_, lean_object* v_x_4080_, lean_object* v___y_4081_){
_start:
{
lean_object* v_res_4082_; 
v_res_4082_ = l_Std_Async_EAsync_race___redArg___lam__2(v_a_4077_, v___f_4078_, v___f_4079_, v_x_4080_);
lean_dec(v_a_4077_);
return v_res_4082_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__4(lean_object* v_a_4083_, lean_object* v___x_4084_, lean_object* v___x_4085_, uint8_t v___x_4086_, lean_object* v___f_4087_, lean_object* v_x_4088_){
_start:
{
if (lean_obj_tag(v_x_4088_) == 0)
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4098_; 
lean_dec_ref(v___f_4087_);
lean_dec(v___x_4085_);
lean_dec_ref(v___x_4084_);
lean_dec_ref(v_a_4083_);
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
lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4108_; 
v_isSharedCheck_4108_ = !lean_is_exclusive(v_x_4088_);
if (v_isSharedCheck_4108_ == 0)
{
lean_object* v_unused_4109_; 
v_unused_4109_ = lean_ctor_get(v_x_4088_, 0);
lean_dec(v_unused_4109_);
v___x_4100_ = v_x_4088_;
v_isShared_4101_ = v_isSharedCheck_4108_;
goto v_resetjp_4099_;
}
else
{
lean_dec(v_x_4088_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4108_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4102_; lean_object* v___x_4104_; 
lean_inc(v___x_4085_);
v___x_4102_ = l_BaseIO_chainTask___redArg(v_a_4083_, v___x_4084_, v___x_4085_, v___x_4086_);
if (v_isShared_4101_ == 0)
{
lean_ctor_set(v___x_4100_, 0, v___x_4102_);
v___x_4104_ = v___x_4100_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v___x_4102_);
v___x_4104_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
lean_object* v___x_4105_; lean_object* v___x_4106_; 
v___x_4105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4105_, 0, v___x_4104_);
v___x_4106_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4085_, v___x_4086_, v___x_4105_, v___f_4087_);
return v___x_4106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__4___boxed(lean_object* v_a_4110_, lean_object* v___x_4111_, lean_object* v___x_4112_, lean_object* v___x_4113_, lean_object* v___f_4114_, lean_object* v_x_4115_, lean_object* v___y_4116_){
_start:
{
uint8_t v___x_1434__boxed_4117_; lean_object* v_res_4118_; 
v___x_1434__boxed_4117_ = lean_unbox(v___x_4113_);
v_res_4118_ = l_Std_Async_EAsync_race___redArg___lam__4(v_a_4110_, v___x_4111_, v___x_4112_, v___x_1434__boxed_4117_, v___f_4114_, v_x_4115_);
return v_res_4118_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__5(lean_object* v___f_4119_, lean_object* v___f_4120_, lean_object* v___f_4121_, lean_object* v_a_4122_, lean_object* v_x_4123_){
_start:
{
if (lean_obj_tag(v_x_4123_) == 0)
{
lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4133_; 
lean_dec_ref(v_a_4122_);
lean_dec_ref(v___f_4121_);
lean_dec_ref(v___f_4120_);
lean_dec(v___f_4119_);
v_a_4125_ = lean_ctor_get(v_x_4123_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v_x_4123_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4127_ = v_x_4123_;
v_isShared_4128_ = v_isSharedCheck_4133_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v_x_4123_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4133_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___x_4130_; 
if (v_isShared_4128_ == 0)
{
v___x_4130_ = v___x_4127_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_a_4125_);
v___x_4130_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
lean_object* v___x_4131_; 
v___x_4131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4131_, 0, v___x_4130_);
return v___x_4131_;
}
}
}
else
{
lean_object* v_a_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4150_; 
v_a_4134_ = lean_ctor_get(v_x_4123_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v_x_4123_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4136_ = v_x_4123_;
v_isShared_4137_ = v_isSharedCheck_4150_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_a_4134_);
lean_dec(v_x_4123_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4150_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; uint8_t v___x_4141_; lean_object* v___x_4142_; lean_object* v___f_4143_; lean_object* v___x_4144_; lean_object* v___x_4146_; 
v___x_4138_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_4138_, 0, lean_box(0));
lean_closure_set(v___x_4138_, 1, lean_box(0));
lean_closure_set(v___x_4138_, 2, v___f_4119_);
lean_closure_set(v___x_4138_, 3, lean_box(0));
v___x_4139_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4139_, 0, lean_box(0));
lean_closure_set(v___x_4139_, 1, lean_box(0));
lean_closure_set(v___x_4139_, 2, lean_box(0));
lean_closure_set(v___x_4139_, 3, v___x_4138_);
lean_closure_set(v___x_4139_, 4, v___f_4120_);
v___x_4140_ = lean_unsigned_to_nat(0u);
v___x_4141_ = 0;
v___x_4142_ = lean_box(v___x_4141_);
lean_inc_ref(v___x_4139_);
v___f_4143_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__4___boxed), 7, 5);
lean_closure_set(v___f_4143_, 0, v_a_4134_);
lean_closure_set(v___f_4143_, 1, v___x_4139_);
lean_closure_set(v___f_4143_, 2, v___x_4140_);
lean_closure_set(v___f_4143_, 3, v___x_4142_);
lean_closure_set(v___f_4143_, 4, v___f_4121_);
v___x_4144_ = l_BaseIO_chainTask___redArg(v_a_4122_, v___x_4139_, v___x_4140_, v___x_4141_);
if (v_isShared_4137_ == 0)
{
lean_ctor_set(v___x_4136_, 0, v___x_4144_);
v___x_4146_ = v___x_4136_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v___x_4144_);
v___x_4146_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4147_, 0, v___x_4146_);
v___x_4148_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4140_, v___x_4141_, v___x_4147_, v___f_4143_);
return v___x_4148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__5___boxed(lean_object* v___f_4151_, lean_object* v___f_4152_, lean_object* v___f_4153_, lean_object* v_a_4154_, lean_object* v_x_4155_, lean_object* v___y_4156_){
_start:
{
lean_object* v_res_4157_; 
v_res_4157_ = l_Std_Async_EAsync_race___redArg___lam__5(v___f_4151_, v___f_4152_, v___f_4153_, v_a_4154_, v_x_4155_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__6(lean_object* v___f_4158_, lean_object* v___f_4159_, lean_object* v___f_4160_, lean_object* v_y_4161_, lean_object* v_prio_4162_, lean_object* v___f_4163_, lean_object* v_x_4164_){
_start:
{
if (lean_obj_tag(v_x_4164_) == 0)
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4174_; 
lean_dec_ref(v___f_4163_);
lean_dec(v_prio_4162_);
lean_dec_ref(v_y_4161_);
lean_dec_ref(v___f_4160_);
lean_dec_ref(v___f_4159_);
lean_dec(v___f_4158_);
v_a_4166_ = lean_ctor_get(v_x_4164_, 0);
v_isSharedCheck_4174_ = !lean_is_exclusive(v_x_4164_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4168_ = v_x_4164_;
v_isShared_4169_ = v_isSharedCheck_4174_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v_x_4164_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4174_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4171_; 
if (v_isShared_4169_ == 0)
{
v___x_4171_ = v___x_4168_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v_a_4166_);
v___x_4171_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
lean_object* v___x_4172_; 
v___x_4172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4171_);
return v___x_4172_;
}
}
}
else
{
lean_object* v_a_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4191_; 
v_a_4175_ = lean_ctor_get(v_x_4164_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v_x_4164_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4177_ = v_x_4164_;
v_isShared_4178_ = v_isSharedCheck_4191_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_a_4175_);
lean_dec(v_x_4164_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4191_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___f_4179_; lean_object* v___x_4180_; uint8_t v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; uint8_t v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4187_; 
v___f_4179_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__5___boxed), 6, 4);
lean_closure_set(v___f_4179_, 0, v___f_4158_);
lean_closure_set(v___f_4179_, 1, v___f_4159_);
lean_closure_set(v___f_4179_, 2, v___f_4160_);
lean_closure_set(v___f_4179_, 3, v_a_4175_);
v___x_4180_ = lean_unsigned_to_nat(0u);
v___x_4181_ = 0;
v___x_4182_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4182_, 0, lean_box(0));
lean_closure_set(v___x_4182_, 1, v_y_4161_);
v___x_4183_ = lean_io_as_task(v___x_4182_, v_prio_4162_);
v___x_4184_ = 1;
v___x_4185_ = lean_task_bind(v___x_4183_, v___f_4163_, v___x_4180_, v___x_4184_);
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 0, v___x_4185_);
v___x_4187_ = v___x_4177_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v___x_4185_);
v___x_4187_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
lean_object* v___x_4188_; lean_object* v___x_4189_; 
v___x_4188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4188_, 0, v___x_4187_);
v___x_4189_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4180_, v___x_4181_, v___x_4188_, v___f_4179_);
return v___x_4189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__6___boxed(lean_object* v___f_4192_, lean_object* v___f_4193_, lean_object* v___f_4194_, lean_object* v_y_4195_, lean_object* v_prio_4196_, lean_object* v___f_4197_, lean_object* v_x_4198_, lean_object* v___y_4199_){
_start:
{
lean_object* v_res_4200_; 
v_res_4200_ = l_Std_Async_EAsync_race___redArg___lam__6(v___f_4192_, v___f_4193_, v___f_4194_, v_y_4195_, v_prio_4196_, v___f_4197_, v_x_4198_);
return v_res_4200_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__7(lean_object* v___f_4201_, lean_object* v___f_4202_, lean_object* v___f_4203_, lean_object* v_y_4204_, lean_object* v_prio_4205_, lean_object* v___f_4206_, lean_object* v_x_4207_, lean_object* v___f_4208_, lean_object* v_x_4209_){
_start:
{
if (lean_obj_tag(v_x_4209_) == 0)
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4219_; 
lean_dec_ref(v___f_4208_);
lean_dec_ref(v_x_4207_);
lean_dec_ref(v___f_4206_);
lean_dec(v_prio_4205_);
lean_dec_ref(v_y_4204_);
lean_dec(v___f_4203_);
lean_dec_ref(v___f_4202_);
lean_dec_ref(v___f_4201_);
v_a_4211_ = lean_ctor_get(v_x_4209_, 0);
v_isSharedCheck_4219_ = !lean_is_exclusive(v_x_4209_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4213_ = v_x_4209_;
v_isShared_4214_ = v_isSharedCheck_4219_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v_x_4209_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4219_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4216_; 
if (v_isShared_4214_ == 0)
{
v___x_4216_ = v___x_4213_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_a_4211_);
v___x_4216_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
lean_object* v___x_4217_; 
v___x_4217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4217_, 0, v___x_4216_);
return v___x_4217_;
}
}
}
else
{
lean_object* v_a_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4238_; 
v_a_4220_ = lean_ctor_get(v_x_4209_, 0);
v_isSharedCheck_4238_ = !lean_is_exclusive(v_x_4209_);
if (v_isSharedCheck_4238_ == 0)
{
v___x_4222_ = v_x_4209_;
v_isShared_4223_ = v_isSharedCheck_4238_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_a_4220_);
lean_dec(v_x_4209_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4238_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
lean_object* v___f_4224_; lean_object* v___f_4225_; lean_object* v___f_4226_; lean_object* v___x_4227_; uint8_t v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; uint8_t v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4234_; 
lean_inc(v_a_4220_);
v___f_4224_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4224_, 0, v_a_4220_);
v___f_4225_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_4225_, 0, v_a_4220_);
lean_closure_set(v___f_4225_, 1, v___f_4201_);
lean_closure_set(v___f_4225_, 2, v___f_4202_);
lean_inc(v_prio_4205_);
v___f_4226_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__6___boxed), 8, 6);
lean_closure_set(v___f_4226_, 0, v___f_4203_);
lean_closure_set(v___f_4226_, 1, v___f_4224_);
lean_closure_set(v___f_4226_, 2, v___f_4225_);
lean_closure_set(v___f_4226_, 3, v_y_4204_);
lean_closure_set(v___f_4226_, 4, v_prio_4205_);
lean_closure_set(v___f_4226_, 5, v___f_4206_);
v___x_4227_ = lean_unsigned_to_nat(0u);
v___x_4228_ = 0;
v___x_4229_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4229_, 0, lean_box(0));
lean_closure_set(v___x_4229_, 1, v_x_4207_);
v___x_4230_ = lean_io_as_task(v___x_4229_, v_prio_4205_);
v___x_4231_ = 1;
v___x_4232_ = lean_task_bind(v___x_4230_, v___f_4208_, v___x_4227_, v___x_4231_);
if (v_isShared_4223_ == 0)
{
lean_ctor_set(v___x_4222_, 0, v___x_4232_);
v___x_4234_ = v___x_4222_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v___x_4232_);
v___x_4234_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
lean_object* v___x_4235_; lean_object* v___x_4236_; 
v___x_4235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4235_, 0, v___x_4234_);
v___x_4236_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4227_, v___x_4228_, v___x_4235_, v___f_4226_);
return v___x_4236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__7___boxed(lean_object* v___f_4239_, lean_object* v___f_4240_, lean_object* v___f_4241_, lean_object* v_y_4242_, lean_object* v_prio_4243_, lean_object* v___f_4244_, lean_object* v_x_4245_, lean_object* v___f_4246_, lean_object* v_x_4247_, lean_object* v___y_4248_){
_start:
{
lean_object* v_res_4249_; 
v_res_4249_ = l_Std_Async_EAsync_race___redArg___lam__7(v___f_4239_, v___f_4240_, v___f_4241_, v_y_4242_, v_prio_4243_, v___f_4244_, v_x_4245_, v___f_4246_, v_x_4247_);
return v_res_4249_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg(lean_object* v_x_4252_, lean_object* v_y_4253_, lean_object* v_prio_4254_){
_start:
{
lean_object* v___f_4256_; lean_object* v___f_4257_; lean_object* v___f_4258_; lean_object* v___f_4259_; lean_object* v___f_4260_; lean_object* v___x_4261_; uint8_t v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
v___f_4256_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___f_4257_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__0));
v___f_4258_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__1));
v___f_4259_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_4260_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_4260_, 0, v___f_4258_);
lean_closure_set(v___f_4260_, 1, v___f_4257_);
lean_closure_set(v___f_4260_, 2, v___f_4259_);
lean_closure_set(v___f_4260_, 3, v_y_4253_);
lean_closure_set(v___f_4260_, 4, v_prio_4254_);
lean_closure_set(v___f_4260_, 5, v___f_4256_);
lean_closure_set(v___f_4260_, 6, v_x_4252_);
lean_closure_set(v___f_4260_, 7, v___f_4256_);
v___x_4261_ = lean_unsigned_to_nat(0u);
v___x_4262_ = 0;
v___x_4263_ = lean_io_promise_new();
v___x_4264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4264_, 0, v___x_4263_);
v___x_4265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4265_, 0, v___x_4264_);
v___x_4266_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4261_, v___x_4262_, v___x_4265_, v___f_4260_);
return v___x_4266_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___boxed(lean_object* v_x_4267_, lean_object* v_y_4268_, lean_object* v_prio_4269_, lean_object* v_a_4270_){
_start:
{
lean_object* v_res_4271_; 
v_res_4271_ = l_Std_Async_EAsync_race___redArg(v_x_4267_, v_y_4268_, v_prio_4269_);
return v_res_4271_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race(lean_object* v_00_u03b1_4272_, lean_object* v_00_u03b5_4273_, lean_object* v_inst_4274_, lean_object* v_x_4275_, lean_object* v_y_4276_, lean_object* v_prio_4277_){
_start:
{
lean_object* v___f_4279_; lean_object* v___f_4280_; lean_object* v___f_4281_; lean_object* v___f_4282_; lean_object* v___f_4283_; lean_object* v___x_4284_; uint8_t v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; 
v___f_4279_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___f_4280_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__0));
v___f_4281_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__1));
v___f_4282_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_4283_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_4283_, 0, v___f_4281_);
lean_closure_set(v___f_4283_, 1, v___f_4280_);
lean_closure_set(v___f_4283_, 2, v___f_4282_);
lean_closure_set(v___f_4283_, 3, v_y_4276_);
lean_closure_set(v___f_4283_, 4, v_prio_4277_);
lean_closure_set(v___f_4283_, 5, v___f_4279_);
lean_closure_set(v___f_4283_, 6, v_x_4275_);
lean_closure_set(v___f_4283_, 7, v___f_4279_);
v___x_4284_ = lean_unsigned_to_nat(0u);
v___x_4285_ = 0;
v___x_4286_ = lean_io_promise_new();
v___x_4287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4286_);
v___x_4288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4288_, 0, v___x_4287_);
v___x_4289_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4284_, v___x_4285_, v___x_4288_, v___f_4283_);
return v___x_4289_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___boxed(lean_object* v_00_u03b1_4290_, lean_object* v_00_u03b5_4291_, lean_object* v_inst_4292_, lean_object* v_x_4293_, lean_object* v_y_4294_, lean_object* v_prio_4295_, lean_object* v_a_4296_){
_start:
{
lean_object* v_res_4297_; 
v_res_4297_ = l_Std_Async_EAsync_race(v_00_u03b1_4290_, v_00_u03b5_4291_, v_inst_4292_, v_x_4293_, v_y_4294_, v_prio_4295_);
lean_dec(v_inst_4292_);
return v_res_4297_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1(lean_object* v_prio_4298_, lean_object* v___f_4299_, lean_object* v_x_4300_){
_start:
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; uint8_t v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; 
v___x_4302_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4302_, 0, lean_box(0));
lean_closure_set(v___x_4302_, 1, v_x_4300_);
v___x_4303_ = lean_io_as_task(v___x_4302_, v_prio_4298_);
v___x_4304_ = lean_unsigned_to_nat(0u);
v___x_4305_ = 1;
v___x_4306_ = lean_task_bind(v___x_4303_, v___f_4299_, v___x_4304_, v___x_4305_);
v___x_4307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4306_);
v___x_4308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4307_);
return v___x_4308_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1___boxed(lean_object* v_prio_4309_, lean_object* v___f_4310_, lean_object* v_x_4311_, lean_object* v___y_4312_){
_start:
{
lean_object* v_res_4313_; 
v_res_4313_ = l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1(v_prio_4309_, v___f_4310_, v_x_4311_);
return v_res_4313_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__0(lean_object* v___y_4314_){
_start:
{
lean_object* v___x_4316_; 
v___x_4316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4316_, 0, v___y_4314_);
return v___x_4316_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__0___boxed(lean_object* v___y_4317_, lean_object* v___y_4318_){
_start:
{
lean_object* v_res_4319_; 
v_res_4319_ = l_Std_Async_EAsync_concurrentlyAll___redArg___lam__0(v___y_4317_);
return v_res_4319_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__2(lean_object* v___x_4320_, lean_object* v___f_4321_, lean_object* v_x_4322_){
_start:
{
if (lean_obj_tag(v_x_4322_) == 0)
{
lean_object* v_a_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4332_; 
lean_dec_ref(v___f_4321_);
lean_dec_ref(v___x_4320_);
v_a_4324_ = lean_ctor_get(v_x_4322_, 0);
v_isSharedCheck_4332_ = !lean_is_exclusive(v_x_4322_);
if (v_isSharedCheck_4332_ == 0)
{
v___x_4326_ = v_x_4322_;
v_isShared_4327_ = v_isSharedCheck_4332_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_a_4324_);
lean_dec(v_x_4322_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4332_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___x_4329_; 
if (v_isShared_4327_ == 0)
{
v___x_4329_ = v___x_4326_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v_a_4324_);
v___x_4329_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
lean_object* v___x_4330_; 
v___x_4330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4330_, 0, v___x_4329_);
return v___x_4330_;
}
}
}
else
{
lean_object* v_a_4333_; size_t v_sz_4334_; size_t v___x_4335_; lean_object* v___x_292__overap_4336_; lean_object* v___x_4337_; 
v_a_4333_ = lean_ctor_get(v_x_4322_, 0);
lean_inc(v_a_4333_);
lean_dec_ref_known(v_x_4322_, 1);
v_sz_4334_ = lean_array_size(v_a_4333_);
v___x_4335_ = ((size_t)0ULL);
v___x_292__overap_4336_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_4320_, v___f_4321_, v_sz_4334_, v___x_4335_, v_a_4333_);
v___x_4337_ = lean_apply_1(v___x_292__overap_4336_, lean_box(0));
return v___x_4337_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__2___boxed(lean_object* v___x_4338_, lean_object* v___f_4339_, lean_object* v_x_4340_, lean_object* v___y_4341_){
_start:
{
lean_object* v_res_4342_; 
v_res_4342_ = l_Std_Async_EAsync_concurrentlyAll___redArg___lam__2(v___x_4338_, v___f_4339_, v_x_4340_);
return v_res_4342_;
}
}
static lean_object* _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1(void){
_start:
{
lean_object* v___f_4344_; lean_object* v___x_4345_; lean_object* v___f_4346_; 
v___f_4344_ = ((lean_object*)(l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0));
v___x_4345_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___closed__0, &l_Std_Async_EAsync_instMonad___closed__0_once, _init_l_Std_Async_EAsync_instMonad___closed__0);
v___f_4346_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrentlyAll___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4346_, 0, v___x_4345_);
lean_closure_set(v___f_4346_, 1, v___f_4344_);
return v___f_4346_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg(lean_object* v_xs_4347_, lean_object* v_prio_4348_){
_start:
{
lean_object* v___f_4350_; lean_object* v___f_4351_; lean_object* v___x_4352_; lean_object* v___f_4353_; lean_object* v___x_4354_; uint8_t v___x_4355_; size_t v_sz_4356_; size_t v___x_4357_; lean_object* v___x_217__overap_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v___f_4350_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___f_4351_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4351_, 0, v_prio_4348_);
lean_closure_set(v___f_4351_, 1, v___f_4350_);
v___x_4352_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___closed__0, &l_Std_Async_EAsync_instMonad___closed__0_once, _init_l_Std_Async_EAsync_instMonad___closed__0);
v___f_4353_ = lean_obj_once(&l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1, &l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1_once, _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1);
v___x_4354_ = lean_unsigned_to_nat(0u);
v___x_4355_ = 0;
v_sz_4356_ = lean_array_size(v_xs_4347_);
v___x_4357_ = ((size_t)0ULL);
v___x_217__overap_4358_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_4352_, v___f_4351_, v_sz_4356_, v___x_4357_, v_xs_4347_);
v___x_4359_ = lean_apply_1(v___x_217__overap_4358_, lean_box(0));
v___x_4360_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4354_, v___x_4355_, v___x_4359_, v___f_4353_);
return v___x_4360_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___boxed(lean_object* v_xs_4361_, lean_object* v_prio_4362_, lean_object* v_a_4363_){
_start:
{
lean_object* v_res_4364_; 
v_res_4364_ = l_Std_Async_EAsync_concurrentlyAll___redArg(v_xs_4361_, v_prio_4362_);
return v_res_4364_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll(lean_object* v_00_u03b5_4365_, lean_object* v_00_u03b1_4366_, lean_object* v_xs_4367_, lean_object* v_prio_4368_){
_start:
{
lean_object* v___f_4370_; lean_object* v___f_4371_; lean_object* v___x_4372_; lean_object* v___f_4373_; lean_object* v___x_4374_; uint8_t v___x_4375_; size_t v_sz_4376_; size_t v___x_4377_; lean_object* v___x_258__overap_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; 
v___f_4370_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___f_4371_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4371_, 0, v_prio_4368_);
lean_closure_set(v___f_4371_, 1, v___f_4370_);
v___x_4372_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___closed__0, &l_Std_Async_EAsync_instMonad___closed__0_once, _init_l_Std_Async_EAsync_instMonad___closed__0);
v___f_4373_ = lean_obj_once(&l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1, &l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1_once, _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1);
v___x_4374_ = lean_unsigned_to_nat(0u);
v___x_4375_ = 0;
v_sz_4376_ = lean_array_size(v_xs_4367_);
v___x_4377_ = ((size_t)0ULL);
v___x_258__overap_4378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_4372_, v___f_4371_, v_sz_4376_, v___x_4377_, v_xs_4367_);
v___x_4379_ = lean_apply_1(v___x_258__overap_4378_, lean_box(0));
v___x_4380_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4374_, v___x_4375_, v___x_4379_, v___f_4373_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___boxed(lean_object* v_00_u03b5_4381_, lean_object* v_00_u03b1_4382_, lean_object* v_xs_4383_, lean_object* v_prio_4384_, lean_object* v_a_4385_){
_start:
{
lean_object* v_res_4386_; 
v_res_4386_ = l_Std_Async_EAsync_concurrentlyAll(v_00_u03b5_4381_, v_00_u03b1_4382_, v_xs_4383_, v_prio_4384_);
return v_res_4386_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__4(lean_object* v___f_4387_, lean_object* v___f_4388_, lean_object* v_x_4389_){
_start:
{
if (lean_obj_tag(v_x_4389_) == 0)
{
lean_object* v_a_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4399_; 
lean_dec_ref(v___f_4388_);
lean_dec(v___f_4387_);
v_a_4391_ = lean_ctor_get(v_x_4389_, 0);
v_isSharedCheck_4399_ = !lean_is_exclusive(v_x_4389_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4393_ = v_x_4389_;
v_isShared_4394_ = v_isSharedCheck_4399_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_a_4391_);
lean_dec(v_x_4389_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4399_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4396_; 
if (v_isShared_4394_ == 0)
{
v___x_4396_ = v___x_4393_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_a_4391_);
v___x_4396_ = v_reuseFailAlloc_4398_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
lean_object* v___x_4397_; 
v___x_4397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4397_, 0, v___x_4396_);
return v___x_4397_;
}
}
}
else
{
lean_object* v_a_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4413_; 
v_a_4400_ = lean_ctor_get(v_x_4389_, 0);
v_isSharedCheck_4413_ = !lean_is_exclusive(v_x_4389_);
if (v_isSharedCheck_4413_ == 0)
{
v___x_4402_ = v_x_4389_;
v_isShared_4403_ = v_isSharedCheck_4413_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_a_4400_);
lean_dec(v_x_4389_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4413_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; uint8_t v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4410_; 
v___x_4404_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_4404_, 0, lean_box(0));
lean_closure_set(v___x_4404_, 1, lean_box(0));
lean_closure_set(v___x_4404_, 2, v___f_4387_);
lean_closure_set(v___x_4404_, 3, lean_box(0));
v___x_4405_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4405_, 0, lean_box(0));
lean_closure_set(v___x_4405_, 1, lean_box(0));
lean_closure_set(v___x_4405_, 2, lean_box(0));
lean_closure_set(v___x_4405_, 3, v___x_4404_);
lean_closure_set(v___x_4405_, 4, v___f_4388_);
v___x_4406_ = lean_unsigned_to_nat(0u);
v___x_4407_ = 0;
v___x_4408_ = l_BaseIO_chainTask___redArg(v_a_4400_, v___x_4405_, v___x_4406_, v___x_4407_);
if (v_isShared_4403_ == 0)
{
lean_ctor_set(v___x_4402_, 0, v___x_4408_);
v___x_4410_ = v___x_4402_;
goto v_reusejp_4409_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v___x_4408_);
v___x_4410_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4409_;
}
v_reusejp_4409_:
{
lean_object* v___x_4411_; 
v___x_4411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4411_, 0, v___x_4410_);
return v___x_4411_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__4___boxed(lean_object* v___f_4414_, lean_object* v___f_4415_, lean_object* v_x_4416_, lean_object* v___y_4417_){
_start:
{
lean_object* v_res_4418_; 
v_res_4418_ = l_Std_Async_EAsync_raceAll___redArg___lam__4(v___f_4414_, v___f_4415_, v_x_4416_);
return v_res_4418_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__0(lean_object* v_prio_4419_, lean_object* v___f_4420_, lean_object* v___f_4421_, lean_object* v_x_4422_){
_start:
{
lean_object* v___x_4424_; uint8_t v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; uint8_t v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; 
v___x_4424_ = lean_unsigned_to_nat(0u);
v___x_4425_ = 0;
v___x_4426_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4426_, 0, lean_box(0));
lean_closure_set(v___x_4426_, 1, v_x_4422_);
v___x_4427_ = lean_io_as_task(v___x_4426_, v_prio_4419_);
v___x_4428_ = 1;
v___x_4429_ = lean_task_bind(v___x_4427_, v___f_4420_, v___x_4424_, v___x_4428_);
v___x_4430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4430_, 0, v___x_4429_);
v___x_4431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4431_, 0, v___x_4430_);
v___x_4432_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4424_, v___x_4425_, v___x_4431_, v___f_4421_);
return v___x_4432_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__0___boxed(lean_object* v_prio_4433_, lean_object* v___f_4434_, lean_object* v___f_4435_, lean_object* v_x_4436_, lean_object* v___y_4437_){
_start:
{
lean_object* v_res_4438_; 
v_res_4438_ = l_Std_Async_EAsync_raceAll___redArg___lam__0(v_prio_4433_, v___f_4434_, v___f_4435_, v_x_4436_);
return v_res_4438_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__2(lean_object* v___f_4439_, lean_object* v_prio_4440_, lean_object* v___f_4441_, lean_object* v___f_4442_, lean_object* v___f_4443_, lean_object* v_inst_4444_, lean_object* v_xs_4445_, lean_object* v_x_4446_){
_start:
{
if (lean_obj_tag(v_x_4446_) == 0)
{
lean_object* v_a_4448_; lean_object* v___x_4450_; uint8_t v_isShared_4451_; uint8_t v_isSharedCheck_4456_; 
lean_dec(v_xs_4445_);
lean_dec_ref(v_inst_4444_);
lean_dec_ref(v___f_4443_);
lean_dec_ref(v___f_4442_);
lean_dec_ref(v___f_4441_);
lean_dec(v_prio_4440_);
lean_dec(v___f_4439_);
v_a_4448_ = lean_ctor_get(v_x_4446_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v_x_4446_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4450_ = v_x_4446_;
v_isShared_4451_ = v_isSharedCheck_4456_;
goto v_resetjp_4449_;
}
else
{
lean_inc(v_a_4448_);
lean_dec(v_x_4446_);
v___x_4450_ = lean_box(0);
v_isShared_4451_ = v_isSharedCheck_4456_;
goto v_resetjp_4449_;
}
v_resetjp_4449_:
{
lean_object* v___x_4453_; 
if (v_isShared_4451_ == 0)
{
v___x_4453_ = v___x_4450_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v_a_4448_);
v___x_4453_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
lean_object* v___x_4454_; 
v___x_4454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4454_, 0, v___x_4453_);
return v___x_4454_;
}
}
}
else
{
lean_object* v_a_4457_; lean_object* v___f_4458_; lean_object* v___f_4459_; lean_object* v___f_4460_; lean_object* v___f_4461_; lean_object* v___x_4462_; uint8_t v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; 
v_a_4457_ = lean_ctor_get(v_x_4446_, 0);
lean_inc_n(v_a_4457_, 2);
lean_dec_ref_known(v_x_4446_, 1);
v___f_4458_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4458_, 0, v_a_4457_);
v___f_4459_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_raceAll___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_4459_, 0, v___f_4439_);
lean_closure_set(v___f_4459_, 1, v___f_4458_);
v___f_4460_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_raceAll___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4460_, 0, v_prio_4440_);
lean_closure_set(v___f_4460_, 1, v___f_4441_);
lean_closure_set(v___f_4460_, 2, v___f_4459_);
v___f_4461_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_4461_, 0, v_a_4457_);
lean_closure_set(v___f_4461_, 1, v___f_4442_);
lean_closure_set(v___f_4461_, 2, v___f_4443_);
v___x_4462_ = lean_unsigned_to_nat(0u);
v___x_4463_ = 0;
v___x_4464_ = lean_apply_3(v_inst_4444_, v_xs_4445_, v___f_4460_, lean_box(0));
v___x_4465_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4462_, v___x_4463_, v___x_4464_, v___f_4461_);
return v___x_4465_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__2___boxed(lean_object* v___f_4466_, lean_object* v_prio_4467_, lean_object* v___f_4468_, lean_object* v___f_4469_, lean_object* v___f_4470_, lean_object* v_inst_4471_, lean_object* v_xs_4472_, lean_object* v_x_4473_, lean_object* v___y_4474_){
_start:
{
lean_object* v_res_4475_; 
v_res_4475_ = l_Std_Async_EAsync_raceAll___redArg___lam__2(v___f_4466_, v_prio_4467_, v___f_4468_, v___f_4469_, v___f_4470_, v_inst_4471_, v_xs_4472_, v_x_4473_);
return v_res_4475_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg(lean_object* v_inst_4476_, lean_object* v_xs_4477_, lean_object* v_prio_4478_){
_start:
{
lean_object* v___f_4480_; lean_object* v___f_4481_; lean_object* v___f_4482_; lean_object* v___f_4483_; lean_object* v___f_4484_; lean_object* v___x_4485_; uint8_t v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; 
v___f_4480_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__1));
v___f_4481_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__0));
v___f_4482_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___f_4483_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_4484_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_raceAll___redArg___lam__2___boxed), 9, 7);
lean_closure_set(v___f_4484_, 0, v___f_4483_);
lean_closure_set(v___f_4484_, 1, v_prio_4478_);
lean_closure_set(v___f_4484_, 2, v___f_4482_);
lean_closure_set(v___f_4484_, 3, v___f_4480_);
lean_closure_set(v___f_4484_, 4, v___f_4481_);
lean_closure_set(v___f_4484_, 5, v_inst_4476_);
lean_closure_set(v___f_4484_, 6, v_xs_4477_);
v___x_4485_ = lean_unsigned_to_nat(0u);
v___x_4486_ = 0;
v___x_4487_ = lean_io_promise_new();
v___x_4488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4488_, 0, v___x_4487_);
v___x_4489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4489_, 0, v___x_4488_);
v___x_4490_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4485_, v___x_4486_, v___x_4489_, v___f_4484_);
return v___x_4490_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___boxed(lean_object* v_inst_4491_, lean_object* v_xs_4492_, lean_object* v_prio_4493_, lean_object* v_a_4494_){
_start:
{
lean_object* v_res_4495_; 
v_res_4495_ = l_Std_Async_EAsync_raceAll___redArg(v_inst_4491_, v_xs_4492_, v_prio_4493_);
return v_res_4495_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll(lean_object* v_00_u03b1_4496_, lean_object* v_00_u03b5_4497_, lean_object* v_c_4498_, lean_object* v_inst_4499_, lean_object* v_inst_4500_, lean_object* v_xs_4501_, lean_object* v_prio_4502_){
_start:
{
lean_object* v___f_4504_; lean_object* v___f_4505_; lean_object* v___f_4506_; lean_object* v___f_4507_; lean_object* v___f_4508_; lean_object* v___x_4509_; uint8_t v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; 
v___f_4504_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__1));
v___f_4505_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__0));
v___f_4506_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___f_4507_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_4508_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_raceAll___redArg___lam__2___boxed), 9, 7);
lean_closure_set(v___f_4508_, 0, v___f_4507_);
lean_closure_set(v___f_4508_, 1, v_prio_4502_);
lean_closure_set(v___f_4508_, 2, v___f_4506_);
lean_closure_set(v___f_4508_, 3, v___f_4504_);
lean_closure_set(v___f_4508_, 4, v___f_4505_);
lean_closure_set(v___f_4508_, 5, v_inst_4500_);
lean_closure_set(v___f_4508_, 6, v_xs_4501_);
v___x_4509_ = lean_unsigned_to_nat(0u);
v___x_4510_ = 0;
v___x_4511_ = lean_io_promise_new();
v___x_4512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4512_, 0, v___x_4511_);
v___x_4513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4513_, 0, v___x_4512_);
v___x_4514_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4509_, v___x_4510_, v___x_4513_, v___f_4508_);
return v___x_4514_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___boxed(lean_object* v_00_u03b1_4515_, lean_object* v_00_u03b5_4516_, lean_object* v_c_4517_, lean_object* v_inst_4518_, lean_object* v_inst_4519_, lean_object* v_xs_4520_, lean_object* v_prio_4521_, lean_object* v_a_4522_){
_start:
{
lean_object* v_res_4523_; 
v_res_4523_ = l_Std_Async_EAsync_raceAll(v_00_u03b1_4515_, v_00_u03b5_4516_, v_c_4517_, v_inst_4518_, v_inst_4519_, v_xs_4520_, v_prio_4521_);
lean_dec(v_inst_4518_);
return v_res_4523_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_toIO___redArg(lean_object* v_x_4524_){
_start:
{
lean_object* v___x_4526_; 
v___x_4526_ = lean_apply_1(v_x_4524_, lean_box(0));
if (lean_obj_tag(v___x_4526_) == 0)
{
lean_object* v_a_4527_; lean_object* v___x_4529_; uint8_t v_isShared_4530_; uint8_t v_isSharedCheck_4535_; 
v_a_4527_ = lean_ctor_get(v___x_4526_, 0);
v_isSharedCheck_4535_ = !lean_is_exclusive(v___x_4526_);
if (v_isSharedCheck_4535_ == 0)
{
v___x_4529_ = v___x_4526_;
v_isShared_4530_ = v_isSharedCheck_4535_;
goto v_resetjp_4528_;
}
else
{
lean_inc(v_a_4527_);
lean_dec(v___x_4526_);
v___x_4529_ = lean_box(0);
v_isShared_4530_ = v_isSharedCheck_4535_;
goto v_resetjp_4528_;
}
v_resetjp_4528_:
{
lean_object* v___x_4531_; lean_object* v___x_4533_; 
v___x_4531_ = lean_task_pure(v_a_4527_);
if (v_isShared_4530_ == 0)
{
lean_ctor_set(v___x_4529_, 0, v___x_4531_);
v___x_4533_ = v___x_4529_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4534_; 
v_reuseFailAlloc_4534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4534_, 0, v___x_4531_);
v___x_4533_ = v_reuseFailAlloc_4534_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
return v___x_4533_;
}
}
}
else
{
lean_object* v_a_4536_; lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4543_; 
v_a_4536_ = lean_ctor_get(v___x_4526_, 0);
v_isSharedCheck_4543_ = !lean_is_exclusive(v___x_4526_);
if (v_isSharedCheck_4543_ == 0)
{
v___x_4538_ = v___x_4526_;
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
else
{
lean_inc(v_a_4536_);
lean_dec(v___x_4526_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v___x_4541_; 
if (v_isShared_4539_ == 0)
{
lean_ctor_set_tag(v___x_4538_, 0);
v___x_4541_ = v___x_4538_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v_a_4536_);
v___x_4541_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
return v___x_4541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_toIO___redArg___boxed(lean_object* v_x_4544_, lean_object* v_a_4545_){
_start:
{
lean_object* v_res_4546_; 
v_res_4546_ = l_Std_Async_Async_toIO___redArg(v_x_4544_);
return v_res_4546_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_toIO(lean_object* v_00_u03b1_4547_, lean_object* v_x_4548_){
_start:
{
lean_object* v___x_4550_; 
v___x_4550_ = lean_apply_1(v_x_4548_, lean_box(0));
if (lean_obj_tag(v___x_4550_) == 0)
{
lean_object* v_a_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4559_; 
v_a_4551_ = lean_ctor_get(v___x_4550_, 0);
v_isSharedCheck_4559_ = !lean_is_exclusive(v___x_4550_);
if (v_isSharedCheck_4559_ == 0)
{
v___x_4553_ = v___x_4550_;
v_isShared_4554_ = v_isSharedCheck_4559_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_a_4551_);
lean_dec(v___x_4550_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4559_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v___x_4555_; lean_object* v___x_4557_; 
v___x_4555_ = lean_task_pure(v_a_4551_);
if (v_isShared_4554_ == 0)
{
lean_ctor_set(v___x_4553_, 0, v___x_4555_);
v___x_4557_ = v___x_4553_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v___x_4555_);
v___x_4557_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
return v___x_4557_;
}
}
}
else
{
lean_object* v_a_4560_; lean_object* v___x_4562_; uint8_t v_isShared_4563_; uint8_t v_isSharedCheck_4567_; 
v_a_4560_ = lean_ctor_get(v___x_4550_, 0);
v_isSharedCheck_4567_ = !lean_is_exclusive(v___x_4550_);
if (v_isSharedCheck_4567_ == 0)
{
v___x_4562_ = v___x_4550_;
v_isShared_4563_ = v_isSharedCheck_4567_;
goto v_resetjp_4561_;
}
else
{
lean_inc(v_a_4560_);
lean_dec(v___x_4550_);
v___x_4562_ = lean_box(0);
v_isShared_4563_ = v_isSharedCheck_4567_;
goto v_resetjp_4561_;
}
v_resetjp_4561_:
{
lean_object* v___x_4565_; 
if (v_isShared_4563_ == 0)
{
lean_ctor_set_tag(v___x_4562_, 0);
v___x_4565_ = v___x_4562_;
goto v_reusejp_4564_;
}
else
{
lean_object* v_reuseFailAlloc_4566_; 
v_reuseFailAlloc_4566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4566_, 0, v_a_4560_);
v___x_4565_ = v_reuseFailAlloc_4566_;
goto v_reusejp_4564_;
}
v_reusejp_4564_:
{
return v___x_4565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_toIO___boxed(lean_object* v_00_u03b1_4568_, lean_object* v_x_4569_, lean_object* v_a_4570_){
_start:
{
lean_object* v_res_4571_; 
v_res_4571_ = l_Std_Async_Async_toIO(v_00_u03b1_4568_, v_x_4569_);
return v_res_4571_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_block___redArg(lean_object* v_x_4572_, lean_object* v_prio_4573_){
_start:
{
lean_object* v___f_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; uint8_t v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; 
v___f_4575_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___x_4576_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4576_, 0, lean_box(0));
lean_closure_set(v___x_4576_, 1, v_x_4572_);
v___x_4577_ = lean_io_as_task(v___x_4576_, v_prio_4573_);
v___x_4578_ = lean_unsigned_to_nat(0u);
v___x_4579_ = 1;
v___x_4580_ = lean_task_bind(v___x_4577_, v___f_4575_, v___x_4578_, v___x_4579_);
v___x_4581_ = lean_task_get_own(v___x_4580_);
if (lean_obj_tag(v___x_4581_) == 0)
{
lean_object* v_a_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4589_; 
v_a_4582_ = lean_ctor_get(v___x_4581_, 0);
v_isSharedCheck_4589_ = !lean_is_exclusive(v___x_4581_);
if (v_isSharedCheck_4589_ == 0)
{
v___x_4584_ = v___x_4581_;
v_isShared_4585_ = v_isSharedCheck_4589_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_a_4582_);
lean_dec(v___x_4581_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4589_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
lean_object* v___x_4587_; 
if (v_isShared_4585_ == 0)
{
lean_ctor_set_tag(v___x_4584_, 1);
v___x_4587_ = v___x_4584_;
goto v_reusejp_4586_;
}
else
{
lean_object* v_reuseFailAlloc_4588_; 
v_reuseFailAlloc_4588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4588_, 0, v_a_4582_);
v___x_4587_ = v_reuseFailAlloc_4588_;
goto v_reusejp_4586_;
}
v_reusejp_4586_:
{
return v___x_4587_;
}
}
}
else
{
lean_object* v_a_4590_; lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4597_; 
v_a_4590_ = lean_ctor_get(v___x_4581_, 0);
v_isSharedCheck_4597_ = !lean_is_exclusive(v___x_4581_);
if (v_isSharedCheck_4597_ == 0)
{
v___x_4592_ = v___x_4581_;
v_isShared_4593_ = v_isSharedCheck_4597_;
goto v_resetjp_4591_;
}
else
{
lean_inc(v_a_4590_);
lean_dec(v___x_4581_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4597_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
lean_object* v___x_4595_; 
if (v_isShared_4593_ == 0)
{
lean_ctor_set_tag(v___x_4592_, 0);
v___x_4595_ = v___x_4592_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v_a_4590_);
v___x_4595_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4594_;
}
v_reusejp_4594_:
{
return v___x_4595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_block___redArg___boxed(lean_object* v_x_4598_, lean_object* v_prio_4599_, lean_object* v_a_4600_){
_start:
{
lean_object* v_res_4601_; 
v_res_4601_ = l_Std_Async_Async_block___redArg(v_x_4598_, v_prio_4599_);
return v_res_4601_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_block(lean_object* v_00_u03b1_4602_, lean_object* v_x_4603_, lean_object* v_prio_4604_){
_start:
{
lean_object* v___f_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; uint8_t v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; 
v___f_4606_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___x_4607_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4607_, 0, lean_box(0));
lean_closure_set(v___x_4607_, 1, v_x_4603_);
v___x_4608_ = lean_io_as_task(v___x_4607_, v_prio_4604_);
v___x_4609_ = lean_unsigned_to_nat(0u);
v___x_4610_ = 1;
v___x_4611_ = lean_task_bind(v___x_4608_, v___f_4606_, v___x_4609_, v___x_4610_);
v___x_4612_ = lean_task_get_own(v___x_4611_);
if (lean_obj_tag(v___x_4612_) == 0)
{
lean_object* v_a_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4620_; 
v_a_4613_ = lean_ctor_get(v___x_4612_, 0);
v_isSharedCheck_4620_ = !lean_is_exclusive(v___x_4612_);
if (v_isSharedCheck_4620_ == 0)
{
v___x_4615_ = v___x_4612_;
v_isShared_4616_ = v_isSharedCheck_4620_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_a_4613_);
lean_dec(v___x_4612_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4620_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v___x_4618_; 
if (v_isShared_4616_ == 0)
{
lean_ctor_set_tag(v___x_4615_, 1);
v___x_4618_ = v___x_4615_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v_a_4613_);
v___x_4618_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
return v___x_4618_;
}
}
}
else
{
lean_object* v_a_4621_; lean_object* v___x_4623_; uint8_t v_isShared_4624_; uint8_t v_isSharedCheck_4628_; 
v_a_4621_ = lean_ctor_get(v___x_4612_, 0);
v_isSharedCheck_4628_ = !lean_is_exclusive(v___x_4612_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4623_ = v___x_4612_;
v_isShared_4624_ = v_isSharedCheck_4628_;
goto v_resetjp_4622_;
}
else
{
lean_inc(v_a_4621_);
lean_dec(v___x_4612_);
v___x_4623_ = lean_box(0);
v_isShared_4624_ = v_isSharedCheck_4628_;
goto v_resetjp_4622_;
}
v_resetjp_4622_:
{
lean_object* v___x_4626_; 
if (v_isShared_4624_ == 0)
{
lean_ctor_set_tag(v___x_4623_, 0);
v___x_4626_ = v___x_4623_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v_a_4621_);
v___x_4626_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
return v___x_4626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_block___boxed(lean_object* v_00_u03b1_4629_, lean_object* v_x_4630_, lean_object* v_prio_4631_, lean_object* v_a_4632_){
_start:
{
lean_object* v_res_4633_; 
v_res_4633_ = l_Std_Async_Async_block(v_00_u03b1_4629_, v_x_4630_, v_prio_4631_);
return v_res_4633_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise___redArg___lam__1(lean_object* v___f_4634_, lean_object* v_x_4635_){
_start:
{
if (lean_obj_tag(v_x_4635_) == 0)
{
lean_object* v_a_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4645_; 
lean_dec_ref(v___f_4634_);
v_a_4637_ = lean_ctor_get(v_x_4635_, 0);
v_isSharedCheck_4645_ = !lean_is_exclusive(v_x_4635_);
if (v_isSharedCheck_4645_ == 0)
{
v___x_4639_ = v_x_4635_;
v_isShared_4640_ = v_isSharedCheck_4645_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_a_4637_);
lean_dec(v_x_4635_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4645_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
lean_object* v___x_4642_; 
if (v_isShared_4640_ == 0)
{
v___x_4642_ = v___x_4639_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v_a_4637_);
v___x_4642_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
lean_object* v___x_4643_; 
v___x_4643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4643_, 0, v___x_4642_);
return v___x_4643_;
}
}
}
else
{
lean_object* v_a_4646_; 
v_a_4646_ = lean_ctor_get(v_x_4635_, 0);
lean_inc(v_a_4646_);
lean_dec_ref_known(v_x_4635_, 1);
if (lean_obj_tag(v_a_4646_) == 0)
{
lean_object* v_a_4647_; lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4655_; 
lean_dec_ref(v___f_4634_);
v_a_4647_ = lean_ctor_get(v_a_4646_, 0);
v_isSharedCheck_4655_ = !lean_is_exclusive(v_a_4646_);
if (v_isSharedCheck_4655_ == 0)
{
v___x_4649_ = v_a_4646_;
v_isShared_4650_ = v_isSharedCheck_4655_;
goto v_resetjp_4648_;
}
else
{
lean_inc(v_a_4647_);
lean_dec(v_a_4646_);
v___x_4649_ = lean_box(0);
v_isShared_4650_ = v_isSharedCheck_4655_;
goto v_resetjp_4648_;
}
v_resetjp_4648_:
{
lean_object* v___x_4652_; 
if (v_isShared_4650_ == 0)
{
v___x_4652_ = v___x_4649_;
goto v_reusejp_4651_;
}
else
{
lean_object* v_reuseFailAlloc_4654_; 
v_reuseFailAlloc_4654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4654_, 0, v_a_4647_);
v___x_4652_ = v_reuseFailAlloc_4654_;
goto v_reusejp_4651_;
}
v_reusejp_4651_:
{
lean_object* v___x_4653_; 
v___x_4653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4653_, 0, v___x_4652_);
return v___x_4653_;
}
}
}
else
{
lean_object* v_a_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; uint8_t v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; 
v_a_4656_ = lean_ctor_get(v_a_4646_, 0);
lean_inc(v_a_4656_);
lean_dec_ref_known(v_a_4646_, 1);
v___x_4657_ = lean_io_promise_result_opt(v_a_4656_);
lean_dec(v_a_4656_);
v___x_4658_ = lean_unsigned_to_nat(0u);
v___x_4659_ = 0;
v___x_4660_ = lean_task_map(v___f_4634_, v___x_4657_, v___x_4658_, v___x_4659_);
v___x_4661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4661_, 0, v___x_4660_);
return v___x_4661_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise___redArg___lam__1___boxed(lean_object* v___f_4662_, lean_object* v_x_4663_, lean_object* v___y_4664_){
_start:
{
lean_object* v_res_4665_; 
v_res_4665_ = l_Std_Async_Async_ofPromise___redArg___lam__1(v___f_4662_, v_x_4663_);
return v_res_4665_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise___redArg(lean_object* v_task_4666_, lean_object* v_error_4667_){
_start:
{
lean_object* v___f_4669_; lean_object* v___f_4670_; lean_object* v___x_4671_; uint8_t v___x_4672_; lean_object* v_val_4674_; lean_object* v___x_4678_; 
v___f_4669_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPromise___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4669_, 0, v_error_4667_);
v___f_4670_ = lean_alloc_closure((void*)(l_Std_Async_Async_ofPromise___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4670_, 0, v___f_4669_);
v___x_4671_ = lean_unsigned_to_nat(0u);
v___x_4672_ = 0;
v___x_4678_ = lean_apply_1(v_task_4666_, lean_box(0));
if (lean_obj_tag(v___x_4678_) == 0)
{
lean_object* v_a_4679_; lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4686_; 
v_a_4679_ = lean_ctor_get(v___x_4678_, 0);
v_isSharedCheck_4686_ = !lean_is_exclusive(v___x_4678_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4681_ = v___x_4678_;
v_isShared_4682_ = v_isSharedCheck_4686_;
goto v_resetjp_4680_;
}
else
{
lean_inc(v_a_4679_);
lean_dec(v___x_4678_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4686_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
lean_object* v___x_4684_; 
if (v_isShared_4682_ == 0)
{
lean_ctor_set_tag(v___x_4681_, 1);
v___x_4684_ = v___x_4681_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_a_4679_);
v___x_4684_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
v_val_4674_ = v___x_4684_;
goto v___jp_4673_;
}
}
}
else
{
lean_object* v_a_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4694_; 
v_a_4687_ = lean_ctor_get(v___x_4678_, 0);
v_isSharedCheck_4694_ = !lean_is_exclusive(v___x_4678_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4689_ = v___x_4678_;
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_a_4687_);
lean_dec(v___x_4678_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4692_; 
if (v_isShared_4690_ == 0)
{
lean_ctor_set_tag(v___x_4689_, 0);
v___x_4692_ = v___x_4689_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_a_4687_);
v___x_4692_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
v_val_4674_ = v___x_4692_;
goto v___jp_4673_;
}
}
}
v___jp_4673_:
{
lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; 
v___x_4675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4675_, 0, v_val_4674_);
v___x_4676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4676_, 0, v___x_4675_);
v___x_4677_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4671_, v___x_4672_, v___x_4676_, v___f_4670_);
return v___x_4677_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise___redArg___boxed(lean_object* v_task_4695_, lean_object* v_error_4696_, lean_object* v_a_4697_){
_start:
{
lean_object* v_res_4698_; 
v_res_4698_ = l_Std_Async_Async_ofPromise___redArg(v_task_4695_, v_error_4696_);
return v_res_4698_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise(lean_object* v_00_u03b1_4699_, lean_object* v_task_4700_, lean_object* v_error_4701_){
_start:
{
lean_object* v___f_4703_; lean_object* v___f_4704_; lean_object* v___x_4705_; uint8_t v___x_4706_; lean_object* v_val_4708_; lean_object* v___x_4712_; 
v___f_4703_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPromise___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4703_, 0, v_error_4701_);
v___f_4704_ = lean_alloc_closure((void*)(l_Std_Async_Async_ofPromise___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4704_, 0, v___f_4703_);
v___x_4705_ = lean_unsigned_to_nat(0u);
v___x_4706_ = 0;
v___x_4712_ = lean_apply_1(v_task_4700_, lean_box(0));
if (lean_obj_tag(v___x_4712_) == 0)
{
lean_object* v_a_4713_; lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4720_; 
v_a_4713_ = lean_ctor_get(v___x_4712_, 0);
v_isSharedCheck_4720_ = !lean_is_exclusive(v___x_4712_);
if (v_isSharedCheck_4720_ == 0)
{
v___x_4715_ = v___x_4712_;
v_isShared_4716_ = v_isSharedCheck_4720_;
goto v_resetjp_4714_;
}
else
{
lean_inc(v_a_4713_);
lean_dec(v___x_4712_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4720_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
lean_object* v___x_4718_; 
if (v_isShared_4716_ == 0)
{
lean_ctor_set_tag(v___x_4715_, 1);
v___x_4718_ = v___x_4715_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v_a_4713_);
v___x_4718_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
v_val_4708_ = v___x_4718_;
goto v___jp_4707_;
}
}
}
else
{
lean_object* v_a_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4728_; 
v_a_4721_ = lean_ctor_get(v___x_4712_, 0);
v_isSharedCheck_4728_ = !lean_is_exclusive(v___x_4712_);
if (v_isSharedCheck_4728_ == 0)
{
v___x_4723_ = v___x_4712_;
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
else
{
lean_inc(v_a_4721_);
lean_dec(v___x_4712_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v___x_4726_; 
if (v_isShared_4724_ == 0)
{
lean_ctor_set_tag(v___x_4723_, 0);
v___x_4726_ = v___x_4723_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v_a_4721_);
v___x_4726_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
v_val_4708_ = v___x_4726_;
goto v___jp_4707_;
}
}
}
v___jp_4707_:
{
lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; 
v___x_4709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4709_, 0, v_val_4708_);
v___x_4710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4710_, 0, v___x_4709_);
v___x_4711_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4705_, v___x_4706_, v___x_4710_, v___f_4704_);
return v___x_4711_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise___boxed(lean_object* v_00_u03b1_4729_, lean_object* v_task_4730_, lean_object* v_error_4731_, lean_object* v_a_4732_){
_start:
{
lean_object* v_res_4733_; 
v_res_4733_ = l_Std_Async_Async_ofPromise(v_00_u03b1_4729_, v_task_4730_, v_error_4731_);
return v_res_4733_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofAsyncTask___redArg(lean_object* v_task_4734_){
_start:
{
lean_object* v___x_4736_; 
v___x_4736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4736_, 0, v_task_4734_);
return v___x_4736_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofAsyncTask___redArg___boxed(lean_object* v_task_4737_, lean_object* v_a_4738_){
_start:
{
lean_object* v_res_4739_; 
v_res_4739_ = l_Std_Async_Async_ofAsyncTask___redArg(v_task_4737_);
return v_res_4739_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofAsyncTask(lean_object* v_00_u03b1_4740_, lean_object* v_task_4741_){
_start:
{
lean_object* v___x_4743_; 
v___x_4743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4743_, 0, v_task_4741_);
return v___x_4743_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofAsyncTask___boxed(lean_object* v_00_u03b1_4744_, lean_object* v_task_4745_, lean_object* v_a_4746_){
_start:
{
lean_object* v_res_4747_; 
v_res_4747_ = l_Std_Async_Async_ofAsyncTask(v_00_u03b1_4744_, v_task_4745_);
return v_res_4747_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___redArg___lam__0(lean_object* v_a_4748_){
_start:
{
lean_object* v___x_4749_; 
v___x_4749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4749_, 0, v_a_4748_);
return v___x_4749_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___redArg___lam__1(lean_object* v___f_4750_, lean_object* v_x_4751_){
_start:
{
if (lean_obj_tag(v_x_4751_) == 0)
{
lean_object* v_a_4753_; lean_object* v___x_4755_; uint8_t v_isShared_4756_; uint8_t v_isSharedCheck_4761_; 
lean_dec_ref(v___f_4750_);
v_a_4753_ = lean_ctor_get(v_x_4751_, 0);
v_isSharedCheck_4761_ = !lean_is_exclusive(v_x_4751_);
if (v_isSharedCheck_4761_ == 0)
{
v___x_4755_ = v_x_4751_;
v_isShared_4756_ = v_isSharedCheck_4761_;
goto v_resetjp_4754_;
}
else
{
lean_inc(v_a_4753_);
lean_dec(v_x_4751_);
v___x_4755_ = lean_box(0);
v_isShared_4756_ = v_isSharedCheck_4761_;
goto v_resetjp_4754_;
}
v_resetjp_4754_:
{
lean_object* v___x_4758_; 
if (v_isShared_4756_ == 0)
{
v___x_4758_ = v___x_4755_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4760_; 
v_reuseFailAlloc_4760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4760_, 0, v_a_4753_);
v___x_4758_ = v_reuseFailAlloc_4760_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
lean_object* v___x_4759_; 
v___x_4759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4759_, 0, v___x_4758_);
return v___x_4759_;
}
}
}
else
{
lean_object* v_a_4762_; 
v_a_4762_ = lean_ctor_get(v_x_4751_, 0);
lean_inc(v_a_4762_);
lean_dec_ref_known(v_x_4751_, 1);
if (lean_obj_tag(v_a_4762_) == 0)
{
lean_object* v_a_4763_; lean_object* v___x_4765_; uint8_t v_isShared_4766_; uint8_t v_isSharedCheck_4771_; 
lean_dec_ref(v___f_4750_);
v_a_4763_ = lean_ctor_get(v_a_4762_, 0);
v_isSharedCheck_4771_ = !lean_is_exclusive(v_a_4762_);
if (v_isSharedCheck_4771_ == 0)
{
v___x_4765_ = v_a_4762_;
v_isShared_4766_ = v_isSharedCheck_4771_;
goto v_resetjp_4764_;
}
else
{
lean_inc(v_a_4763_);
lean_dec(v_a_4762_);
v___x_4765_ = lean_box(0);
v_isShared_4766_ = v_isSharedCheck_4771_;
goto v_resetjp_4764_;
}
v_resetjp_4764_:
{
lean_object* v___x_4768_; 
if (v_isShared_4766_ == 0)
{
v___x_4768_ = v___x_4765_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4770_; 
v_reuseFailAlloc_4770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4770_, 0, v_a_4763_);
v___x_4768_ = v_reuseFailAlloc_4770_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
lean_object* v___x_4769_; 
v___x_4769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4769_, 0, v___x_4768_);
return v___x_4769_;
}
}
}
else
{
lean_object* v_a_4772_; lean_object* v___x_4773_; uint8_t v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; 
v_a_4772_ = lean_ctor_get(v_a_4762_, 0);
lean_inc(v_a_4772_);
lean_dec_ref_known(v_a_4762_, 1);
v___x_4773_ = lean_unsigned_to_nat(0u);
v___x_4774_ = 0;
v___x_4775_ = lean_task_map(v___f_4750_, v_a_4772_, v___x_4773_, v___x_4774_);
v___x_4776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4776_, 0, v___x_4775_);
return v___x_4776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___redArg___lam__1___boxed(lean_object* v___f_4777_, lean_object* v_x_4778_, lean_object* v___y_4779_){
_start:
{
lean_object* v_res_4780_; 
v_res_4780_ = l_Std_Async_Async_ofIOTask___redArg___lam__1(v___f_4777_, v_x_4778_);
return v_res_4780_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___redArg(lean_object* v_task_4784_){
_start:
{
lean_object* v___f_4786_; lean_object* v___x_4787_; uint8_t v___x_4788_; lean_object* v_val_4790_; lean_object* v___x_4794_; 
v___f_4786_ = ((lean_object*)(l_Std_Async_Async_ofIOTask___redArg___closed__1));
v___x_4787_ = lean_unsigned_to_nat(0u);
v___x_4788_ = 0;
v___x_4794_ = lean_apply_1(v_task_4784_, lean_box(0));
if (lean_obj_tag(v___x_4794_) == 0)
{
lean_object* v_a_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4802_; 
v_a_4795_ = lean_ctor_get(v___x_4794_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___x_4794_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4797_ = v___x_4794_;
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_a_4795_);
lean_dec(v___x_4794_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v___x_4800_; 
if (v_isShared_4798_ == 0)
{
lean_ctor_set_tag(v___x_4797_, 1);
v___x_4800_ = v___x_4797_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v_a_4795_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
v_val_4790_ = v___x_4800_;
goto v___jp_4789_;
}
}
}
else
{
lean_object* v_a_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4810_; 
v_a_4803_ = lean_ctor_get(v___x_4794_, 0);
v_isSharedCheck_4810_ = !lean_is_exclusive(v___x_4794_);
if (v_isSharedCheck_4810_ == 0)
{
v___x_4805_ = v___x_4794_;
v_isShared_4806_ = v_isSharedCheck_4810_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_a_4803_);
lean_dec(v___x_4794_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4810_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
lean_object* v___x_4808_; 
if (v_isShared_4806_ == 0)
{
lean_ctor_set_tag(v___x_4805_, 0);
v___x_4808_ = v___x_4805_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v_a_4803_);
v___x_4808_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
v_val_4790_ = v___x_4808_;
goto v___jp_4789_;
}
}
}
v___jp_4789_:
{
lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; 
v___x_4791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4791_, 0, v_val_4790_);
v___x_4792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4792_, 0, v___x_4791_);
v___x_4793_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4787_, v___x_4788_, v___x_4792_, v___f_4786_);
return v___x_4793_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___redArg___boxed(lean_object* v_task_4811_, lean_object* v_a_4812_){
_start:
{
lean_object* v_res_4813_; 
v_res_4813_ = l_Std_Async_Async_ofIOTask___redArg(v_task_4811_);
return v_res_4813_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask(lean_object* v_00_u03b1_4814_, lean_object* v_task_4815_){
_start:
{
lean_object* v___f_4817_; lean_object* v___x_4818_; uint8_t v___x_4819_; lean_object* v_val_4821_; lean_object* v___x_4825_; 
v___f_4817_ = ((lean_object*)(l_Std_Async_Async_ofIOTask___redArg___closed__1));
v___x_4818_ = lean_unsigned_to_nat(0u);
v___x_4819_ = 0;
v___x_4825_ = lean_apply_1(v_task_4815_, lean_box(0));
if (lean_obj_tag(v___x_4825_) == 0)
{
lean_object* v_a_4826_; lean_object* v___x_4828_; uint8_t v_isShared_4829_; uint8_t v_isSharedCheck_4833_; 
v_a_4826_ = lean_ctor_get(v___x_4825_, 0);
v_isSharedCheck_4833_ = !lean_is_exclusive(v___x_4825_);
if (v_isSharedCheck_4833_ == 0)
{
v___x_4828_ = v___x_4825_;
v_isShared_4829_ = v_isSharedCheck_4833_;
goto v_resetjp_4827_;
}
else
{
lean_inc(v_a_4826_);
lean_dec(v___x_4825_);
v___x_4828_ = lean_box(0);
v_isShared_4829_ = v_isSharedCheck_4833_;
goto v_resetjp_4827_;
}
v_resetjp_4827_:
{
lean_object* v___x_4831_; 
if (v_isShared_4829_ == 0)
{
lean_ctor_set_tag(v___x_4828_, 1);
v___x_4831_ = v___x_4828_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v_a_4826_);
v___x_4831_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
v_val_4821_ = v___x_4831_;
goto v___jp_4820_;
}
}
}
else
{
lean_object* v_a_4834_; lean_object* v___x_4836_; uint8_t v_isShared_4837_; uint8_t v_isSharedCheck_4841_; 
v_a_4834_ = lean_ctor_get(v___x_4825_, 0);
v_isSharedCheck_4841_ = !lean_is_exclusive(v___x_4825_);
if (v_isSharedCheck_4841_ == 0)
{
v___x_4836_ = v___x_4825_;
v_isShared_4837_ = v_isSharedCheck_4841_;
goto v_resetjp_4835_;
}
else
{
lean_inc(v_a_4834_);
lean_dec(v___x_4825_);
v___x_4836_ = lean_box(0);
v_isShared_4837_ = v_isSharedCheck_4841_;
goto v_resetjp_4835_;
}
v_resetjp_4835_:
{
lean_object* v___x_4839_; 
if (v_isShared_4837_ == 0)
{
lean_ctor_set_tag(v___x_4836_, 0);
v___x_4839_ = v___x_4836_;
goto v_reusejp_4838_;
}
else
{
lean_object* v_reuseFailAlloc_4840_; 
v_reuseFailAlloc_4840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4840_, 0, v_a_4834_);
v___x_4839_ = v_reuseFailAlloc_4840_;
goto v_reusejp_4838_;
}
v_reusejp_4838_:
{
v_val_4821_ = v___x_4839_;
goto v___jp_4820_;
}
}
}
v___jp_4820_:
{
lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; 
v___x_4822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4822_, 0, v_val_4821_);
v___x_4823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4823_, 0, v___x_4822_);
v___x_4824_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4818_, v___x_4819_, v___x_4823_, v___f_4817_);
return v___x_4824_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___boxed(lean_object* v_00_u03b1_4842_, lean_object* v_task_4843_, lean_object* v_a_4844_){
_start:
{
lean_object* v_res_4845_; 
v_res_4845_ = l_Std_Async_Async_ofIOTask(v_00_u03b1_4842_, v_task_4843_);
return v_res_4845_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofExcept___redArg(lean_object* v_except_4846_){
_start:
{
lean_object* v___x_4848_; 
v___x_4848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4848_, 0, v_except_4846_);
return v___x_4848_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofExcept___redArg___boxed(lean_object* v_except_4849_, lean_object* v_a_4850_){
_start:
{
lean_object* v_res_4851_; 
v_res_4851_ = l_Std_Async_Async_ofExcept___redArg(v_except_4849_);
return v_res_4851_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofExcept(lean_object* v_00_u03b1_4852_, lean_object* v_except_4853_){
_start:
{
lean_object* v___x_4855_; 
v___x_4855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4855_, 0, v_except_4853_);
return v___x_4855_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofExcept___boxed(lean_object* v_00_u03b1_4856_, lean_object* v_except_4857_, lean_object* v_a_4858_){
_start:
{
lean_object* v_res_4859_; 
v_res_4859_ = l_Std_Async_Async_ofExcept(v_00_u03b1_4856_, v_except_4857_);
return v_res_4859_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofTask___redArg(lean_object* v_task_4860_){
_start:
{
lean_object* v___f_4862_; lean_object* v___x_4863_; uint8_t v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; 
v___f_4862_ = ((lean_object*)(l_Std_Async_Async_ofIOTask___redArg___closed__0));
v___x_4863_ = lean_unsigned_to_nat(0u);
v___x_4864_ = 0;
v___x_4865_ = lean_task_map(v___f_4862_, v_task_4860_, v___x_4863_, v___x_4864_);
v___x_4866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4866_, 0, v___x_4865_);
return v___x_4866_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofTask___redArg___boxed(lean_object* v_task_4867_, lean_object* v_a_4868_){
_start:
{
lean_object* v_res_4869_; 
v_res_4869_ = l_Std_Async_Async_ofTask___redArg(v_task_4867_);
return v_res_4869_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofTask(lean_object* v_00_u03b1_4870_, lean_object* v_task_4871_){
_start:
{
lean_object* v___f_4873_; lean_object* v___x_4874_; uint8_t v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; 
v___f_4873_ = ((lean_object*)(l_Std_Async_Async_ofIOTask___redArg___closed__0));
v___x_4874_ = lean_unsigned_to_nat(0u);
v___x_4875_ = 0;
v___x_4876_ = lean_task_map(v___f_4873_, v_task_4871_, v___x_4874_, v___x_4875_);
v___x_4877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4877_, 0, v___x_4876_);
return v___x_4877_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofTask___boxed(lean_object* v_00_u03b1_4878_, lean_object* v_task_4879_, lean_object* v_a_4880_){
_start:
{
lean_object* v_res_4881_; 
v_res_4881_ = l_Std_Async_Async_ofTask(v_00_u03b1_4878_, v_task_4879_);
return v_res_4881_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPurePromise___redArg(lean_object* v_task_4882_, lean_object* v_error_4883_){
_start:
{
lean_object* v___f_4885_; lean_object* v___x_4886_; 
v___f_4885_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPurePromise___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4885_, 0, v_error_4883_);
v___x_4886_ = lean_apply_1(v_task_4882_, lean_box(0));
if (lean_obj_tag(v___x_4886_) == 0)
{
lean_object* v_a_4887_; lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4898_; 
v_a_4887_ = lean_ctor_get(v___x_4886_, 0);
v_isSharedCheck_4898_ = !lean_is_exclusive(v___x_4886_);
if (v_isSharedCheck_4898_ == 0)
{
v___x_4889_ = v___x_4886_;
v_isShared_4890_ = v_isSharedCheck_4898_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_a_4887_);
lean_dec(v___x_4886_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4898_;
goto v_resetjp_4888_;
}
v_resetjp_4888_:
{
lean_object* v___x_4891_; lean_object* v___x_4892_; uint8_t v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4896_; 
v___x_4891_ = lean_io_promise_result_opt(v_a_4887_);
lean_dec(v_a_4887_);
v___x_4892_ = lean_unsigned_to_nat(0u);
v___x_4893_ = 0;
v___x_4894_ = lean_task_map(v___f_4885_, v___x_4891_, v___x_4892_, v___x_4893_);
if (v_isShared_4890_ == 0)
{
lean_ctor_set_tag(v___x_4889_, 1);
lean_ctor_set(v___x_4889_, 0, v___x_4894_);
v___x_4896_ = v___x_4889_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4897_; 
v_reuseFailAlloc_4897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4897_, 0, v___x_4894_);
v___x_4896_ = v_reuseFailAlloc_4897_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
return v___x_4896_;
}
}
}
else
{
lean_object* v_a_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4907_; 
lean_dec_ref(v___f_4885_);
v_a_4899_ = lean_ctor_get(v___x_4886_, 0);
v_isSharedCheck_4907_ = !lean_is_exclusive(v___x_4886_);
if (v_isSharedCheck_4907_ == 0)
{
v___x_4901_ = v___x_4886_;
v_isShared_4902_ = v_isSharedCheck_4907_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_a_4899_);
lean_dec(v___x_4886_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4907_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v___x_4904_; 
if (v_isShared_4902_ == 0)
{
lean_ctor_set_tag(v___x_4901_, 0);
v___x_4904_ = v___x_4901_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v_a_4899_);
v___x_4904_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
lean_object* v___x_4905_; 
v___x_4905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4905_, 0, v___x_4904_);
return v___x_4905_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPurePromise___redArg___boxed(lean_object* v_task_4908_, lean_object* v_error_4909_, lean_object* v_a_4910_){
_start:
{
lean_object* v_res_4911_; 
v_res_4911_ = l_Std_Async_Async_ofPurePromise___redArg(v_task_4908_, v_error_4909_);
return v_res_4911_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPurePromise(lean_object* v_00_u03b1_4912_, lean_object* v_task_4913_, lean_object* v_error_4914_){
_start:
{
lean_object* v___f_4916_; lean_object* v___x_4917_; 
v___f_4916_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPurePromise___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4916_, 0, v_error_4914_);
v___x_4917_ = lean_apply_1(v_task_4913_, lean_box(0));
if (lean_obj_tag(v___x_4917_) == 0)
{
lean_object* v_a_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4929_; 
v_a_4918_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_4929_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4929_ == 0)
{
v___x_4920_ = v___x_4917_;
v_isShared_4921_ = v_isSharedCheck_4929_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_a_4918_);
lean_dec(v___x_4917_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4929_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v___x_4922_; lean_object* v___x_4923_; uint8_t v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4927_; 
v___x_4922_ = lean_io_promise_result_opt(v_a_4918_);
lean_dec(v_a_4918_);
v___x_4923_ = lean_unsigned_to_nat(0u);
v___x_4924_ = 0;
v___x_4925_ = lean_task_map(v___f_4916_, v___x_4922_, v___x_4923_, v___x_4924_);
if (v_isShared_4921_ == 0)
{
lean_ctor_set_tag(v___x_4920_, 1);
lean_ctor_set(v___x_4920_, 0, v___x_4925_);
v___x_4927_ = v___x_4920_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_4928_; 
v_reuseFailAlloc_4928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4928_, 0, v___x_4925_);
v___x_4927_ = v_reuseFailAlloc_4928_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
return v___x_4927_;
}
}
}
else
{
lean_object* v_a_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4938_; 
lean_dec_ref(v___f_4916_);
v_a_4930_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_4938_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4938_ == 0)
{
v___x_4932_ = v___x_4917_;
v_isShared_4933_ = v_isSharedCheck_4938_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_a_4930_);
lean_dec(v___x_4917_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4938_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v___x_4935_; 
if (v_isShared_4933_ == 0)
{
lean_ctor_set_tag(v___x_4932_, 0);
v___x_4935_ = v___x_4932_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4937_; 
v_reuseFailAlloc_4937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4937_, 0, v_a_4930_);
v___x_4935_ = v_reuseFailAlloc_4937_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
lean_object* v___x_4936_; 
v___x_4936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4936_, 0, v___x_4935_);
return v___x_4936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPurePromise___boxed(lean_object* v_00_u03b1_4939_, lean_object* v_task_4940_, lean_object* v_error_4941_, lean_object* v_a_4942_){
_start:
{
lean_object* v_res_4943_; 
v_res_4943_ = l_Std_Async_Async_ofPurePromise(v_00_u03b1_4939_, v_task_4940_, v_error_4941_);
return v_res_4943_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___redArg(lean_object* v_t_4945_){
_start:
{
lean_object* v___x_4947_; 
v___x_4947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4947_, 0, v_t_4945_);
return v___x_4947_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___redArg___boxed(lean_object* v_t_4948_, lean_object* v_a_4949_){
_start:
{
lean_object* v_res_4950_; 
v_res_4950_ = l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___redArg(v_t_4948_);
return v_res_4950_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1(lean_object* v_00_u03b1_4951_, lean_object* v_t_4952_){
_start:
{
lean_object* v___x_4954_; 
v___x_4954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4954_, 0, v_t_4952_);
return v___x_4954_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___boxed(lean_object* v_00_u03b1_4955_, lean_object* v_t_4956_, lean_object* v_a_4957_){
_start:
{
lean_object* v_res_4958_; 
v_res_4958_ = l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1(v_00_u03b1_4955_, v_t_4956_);
return v_res_4958_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitPromise___aux__1___redArg(lean_object* v_t_4961_){
_start:
{
lean_object* v___f_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; uint8_t v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; 
v___f_4963_ = ((lean_object*)(l_Std_Async_Async_ofIOTask___redArg___closed__0));
v___x_4964_ = l_IO_Promise_result_x21___redArg(v_t_4961_);
v___x_4965_ = lean_unsigned_to_nat(0u);
v___x_4966_ = 0;
v___x_4967_ = lean_task_map(v___f_4963_, v___x_4964_, v___x_4965_, v___x_4966_);
v___x_4968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4968_, 0, v___x_4967_);
return v___x_4968_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitPromise___aux__1___redArg___boxed(lean_object* v_t_4969_, lean_object* v_a_4970_){
_start:
{
lean_object* v_res_4971_; 
v_res_4971_ = l_Std_Async_Async_instMonadAwaitPromise___aux__1___redArg(v_t_4969_);
lean_dec(v_t_4969_);
return v_res_4971_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitPromise___aux__1(lean_object* v_00_u03b1_4972_, lean_object* v_t_4973_){
_start:
{
lean_object* v___f_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; uint8_t v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; 
v___f_4975_ = ((lean_object*)(l_Std_Async_Async_ofIOTask___redArg___closed__0));
v___x_4976_ = l_IO_Promise_result_x21___redArg(v_t_4973_);
v___x_4977_ = lean_unsigned_to_nat(0u);
v___x_4978_ = 0;
v___x_4979_ = lean_task_map(v___f_4975_, v___x_4976_, v___x_4977_, v___x_4978_);
v___x_4980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4980_, 0, v___x_4979_);
return v___x_4980_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitPromise___aux__1___boxed(lean_object* v_00_u03b1_4981_, lean_object* v_t_4982_, lean_object* v_a_4983_){
_start:
{
lean_object* v_res_4984_; 
v_res_4984_ = l_Std_Async_Async_instMonadAwaitPromise___aux__1(v_00_u03b1_4981_, v_t_4982_);
lean_dec(v_t_4982_);
return v_res_4984_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__1(lean_object* v_a_4987_, lean_object* v_x_4988_){
_start:
{
if (lean_obj_tag(v_x_4988_) == 0)
{
lean_object* v_a_4990_; lean_object* v___x_4992_; uint8_t v_isShared_4993_; uint8_t v_isSharedCheck_4998_; 
lean_dec(v_a_4987_);
v_a_4990_ = lean_ctor_get(v_x_4988_, 0);
v_isSharedCheck_4998_ = !lean_is_exclusive(v_x_4988_);
if (v_isSharedCheck_4998_ == 0)
{
v___x_4992_ = v_x_4988_;
v_isShared_4993_ = v_isSharedCheck_4998_;
goto v_resetjp_4991_;
}
else
{
lean_inc(v_a_4990_);
lean_dec(v_x_4988_);
v___x_4992_ = lean_box(0);
v_isShared_4993_ = v_isSharedCheck_4998_;
goto v_resetjp_4991_;
}
v_resetjp_4991_:
{
lean_object* v___x_4995_; 
if (v_isShared_4993_ == 0)
{
v___x_4995_ = v___x_4992_;
goto v_reusejp_4994_;
}
else
{
lean_object* v_reuseFailAlloc_4997_; 
v_reuseFailAlloc_4997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4997_, 0, v_a_4990_);
v___x_4995_ = v_reuseFailAlloc_4997_;
goto v_reusejp_4994_;
}
v_reusejp_4994_:
{
lean_object* v___x_4996_; 
v___x_4996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4996_, 0, v___x_4995_);
return v___x_4996_;
}
}
}
else
{
lean_object* v_a_4999_; lean_object* v___x_5001_; uint8_t v_isShared_5002_; uint8_t v_isSharedCheck_5008_; 
v_a_4999_ = lean_ctor_get(v_x_4988_, 0);
v_isSharedCheck_5008_ = !lean_is_exclusive(v_x_4988_);
if (v_isSharedCheck_5008_ == 0)
{
v___x_5001_ = v_x_4988_;
v_isShared_5002_ = v_isSharedCheck_5008_;
goto v_resetjp_5000_;
}
else
{
lean_inc(v_a_4999_);
lean_dec(v_x_4988_);
v___x_5001_ = lean_box(0);
v_isShared_5002_ = v_isSharedCheck_5008_;
goto v_resetjp_5000_;
}
v_resetjp_5000_:
{
lean_object* v___x_5003_; lean_object* v___x_5005_; 
v___x_5003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5003_, 0, v_a_4987_);
lean_ctor_set(v___x_5003_, 1, v_a_4999_);
if (v_isShared_5002_ == 0)
{
lean_ctor_set(v___x_5001_, 0, v___x_5003_);
v___x_5005_ = v___x_5001_;
goto v_reusejp_5004_;
}
else
{
lean_object* v_reuseFailAlloc_5007_; 
v_reuseFailAlloc_5007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5007_, 0, v___x_5003_);
v___x_5005_ = v_reuseFailAlloc_5007_;
goto v_reusejp_5004_;
}
v_reusejp_5004_:
{
lean_object* v___x_5006_; 
v___x_5006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5006_, 0, v___x_5005_);
return v___x_5006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__1___boxed(lean_object* v_a_5009_, lean_object* v_x_5010_, lean_object* v___y_5011_){
_start:
{
lean_object* v_res_5012_; 
v_res_5012_ = l_Std_Async_Async_concurrently___redArg___lam__1(v_a_5009_, v_x_5010_);
return v_res_5012_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__0(lean_object* v_a_5013_, lean_object* v_x_5014_){
_start:
{
if (lean_obj_tag(v_x_5014_) == 0)
{
lean_object* v_a_5016_; lean_object* v___x_5018_; uint8_t v_isShared_5019_; uint8_t v_isSharedCheck_5024_; 
lean_dec_ref(v_a_5013_);
v_a_5016_ = lean_ctor_get(v_x_5014_, 0);
v_isSharedCheck_5024_ = !lean_is_exclusive(v_x_5014_);
if (v_isSharedCheck_5024_ == 0)
{
v___x_5018_ = v_x_5014_;
v_isShared_5019_ = v_isSharedCheck_5024_;
goto v_resetjp_5017_;
}
else
{
lean_inc(v_a_5016_);
lean_dec(v_x_5014_);
v___x_5018_ = lean_box(0);
v_isShared_5019_ = v_isSharedCheck_5024_;
goto v_resetjp_5017_;
}
v_resetjp_5017_:
{
lean_object* v___x_5021_; 
if (v_isShared_5019_ == 0)
{
v___x_5021_ = v___x_5018_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5023_; 
v_reuseFailAlloc_5023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5023_, 0, v_a_5016_);
v___x_5021_ = v_reuseFailAlloc_5023_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
lean_object* v___x_5022_; 
v___x_5022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5022_, 0, v___x_5021_);
return v___x_5022_;
}
}
}
else
{
lean_object* v_a_5025_; lean_object* v___f_5026_; lean_object* v___x_5027_; uint8_t v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; 
v_a_5025_ = lean_ctor_get(v_x_5014_, 0);
lean_inc(v_a_5025_);
lean_dec_ref_known(v_x_5014_, 1);
v___f_5026_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrently___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_5026_, 0, v_a_5025_);
v___x_5027_ = lean_unsigned_to_nat(0u);
v___x_5028_ = 0;
v___x_5029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5029_, 0, v_a_5013_);
v___x_5030_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5027_, v___x_5028_, v___x_5029_, v___f_5026_);
return v___x_5030_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__0___boxed(lean_object* v_a_5031_, lean_object* v_x_5032_, lean_object* v___y_5033_){
_start:
{
lean_object* v_res_5034_; 
v_res_5034_ = l_Std_Async_Async_concurrently___redArg___lam__0(v_a_5031_, v_x_5032_);
return v_res_5034_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__2(lean_object* v_a_5035_, lean_object* v_x_5036_){
_start:
{
if (lean_obj_tag(v_x_5036_) == 0)
{
lean_object* v_a_5038_; lean_object* v___x_5040_; uint8_t v_isShared_5041_; uint8_t v_isSharedCheck_5046_; 
lean_dec_ref(v_a_5035_);
v_a_5038_ = lean_ctor_get(v_x_5036_, 0);
v_isSharedCheck_5046_ = !lean_is_exclusive(v_x_5036_);
if (v_isSharedCheck_5046_ == 0)
{
v___x_5040_ = v_x_5036_;
v_isShared_5041_ = v_isSharedCheck_5046_;
goto v_resetjp_5039_;
}
else
{
lean_inc(v_a_5038_);
lean_dec(v_x_5036_);
v___x_5040_ = lean_box(0);
v_isShared_5041_ = v_isSharedCheck_5046_;
goto v_resetjp_5039_;
}
v_resetjp_5039_:
{
lean_object* v___x_5043_; 
if (v_isShared_5041_ == 0)
{
v___x_5043_ = v___x_5040_;
goto v_reusejp_5042_;
}
else
{
lean_object* v_reuseFailAlloc_5045_; 
v_reuseFailAlloc_5045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5045_, 0, v_a_5038_);
v___x_5043_ = v_reuseFailAlloc_5045_;
goto v_reusejp_5042_;
}
v_reusejp_5042_:
{
lean_object* v___x_5044_; 
v___x_5044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5044_, 0, v___x_5043_);
return v___x_5044_;
}
}
}
else
{
lean_object* v_a_5047_; lean_object* v___f_5048_; lean_object* v___x_5049_; uint8_t v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; 
v_a_5047_ = lean_ctor_get(v_x_5036_, 0);
lean_inc(v_a_5047_);
lean_dec_ref_known(v_x_5036_, 1);
v___f_5048_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrently___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5048_, 0, v_a_5047_);
v___x_5049_ = lean_unsigned_to_nat(0u);
v___x_5050_ = 0;
v___x_5051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5051_, 0, v_a_5035_);
v___x_5052_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5049_, v___x_5050_, v___x_5051_, v___f_5048_);
return v___x_5052_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__2___boxed(lean_object* v_a_5053_, lean_object* v_x_5054_, lean_object* v___y_5055_){
_start:
{
lean_object* v_res_5056_; 
v_res_5056_ = l_Std_Async_Async_concurrently___redArg___lam__2(v_a_5053_, v_x_5054_);
return v_res_5056_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__3(lean_object* v_y_5057_, lean_object* v_prio_5058_, lean_object* v___f_5059_, lean_object* v_x_5060_){
_start:
{
if (lean_obj_tag(v_x_5060_) == 0)
{
lean_object* v_a_5062_; lean_object* v___x_5064_; uint8_t v_isShared_5065_; uint8_t v_isSharedCheck_5070_; 
lean_dec_ref(v___f_5059_);
lean_dec(v_prio_5058_);
lean_dec_ref(v_y_5057_);
v_a_5062_ = lean_ctor_get(v_x_5060_, 0);
v_isSharedCheck_5070_ = !lean_is_exclusive(v_x_5060_);
if (v_isSharedCheck_5070_ == 0)
{
v___x_5064_ = v_x_5060_;
v_isShared_5065_ = v_isSharedCheck_5070_;
goto v_resetjp_5063_;
}
else
{
lean_inc(v_a_5062_);
lean_dec(v_x_5060_);
v___x_5064_ = lean_box(0);
v_isShared_5065_ = v_isSharedCheck_5070_;
goto v_resetjp_5063_;
}
v_resetjp_5063_:
{
lean_object* v___x_5067_; 
if (v_isShared_5065_ == 0)
{
v___x_5067_ = v___x_5064_;
goto v_reusejp_5066_;
}
else
{
lean_object* v_reuseFailAlloc_5069_; 
v_reuseFailAlloc_5069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5069_, 0, v_a_5062_);
v___x_5067_ = v_reuseFailAlloc_5069_;
goto v_reusejp_5066_;
}
v_reusejp_5066_:
{
lean_object* v___x_5068_; 
v___x_5068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5068_, 0, v___x_5067_);
return v___x_5068_;
}
}
}
else
{
lean_object* v_a_5071_; lean_object* v___x_5073_; uint8_t v_isShared_5074_; uint8_t v_isSharedCheck_5087_; 
v_a_5071_ = lean_ctor_get(v_x_5060_, 0);
v_isSharedCheck_5087_ = !lean_is_exclusive(v_x_5060_);
if (v_isSharedCheck_5087_ == 0)
{
v___x_5073_ = v_x_5060_;
v_isShared_5074_ = v_isSharedCheck_5087_;
goto v_resetjp_5072_;
}
else
{
lean_inc(v_a_5071_);
lean_dec(v_x_5060_);
v___x_5073_ = lean_box(0);
v_isShared_5074_ = v_isSharedCheck_5087_;
goto v_resetjp_5072_;
}
v_resetjp_5072_:
{
lean_object* v___f_5075_; lean_object* v___x_5076_; uint8_t v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; uint8_t v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5083_; 
v___f_5075_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrently___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_5075_, 0, v_a_5071_);
v___x_5076_ = lean_unsigned_to_nat(0u);
v___x_5077_ = 0;
v___x_5078_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5078_, 0, lean_box(0));
lean_closure_set(v___x_5078_, 1, v_y_5057_);
v___x_5079_ = lean_io_as_task(v___x_5078_, v_prio_5058_);
v___x_5080_ = 1;
v___x_5081_ = lean_task_bind(v___x_5079_, v___f_5059_, v___x_5076_, v___x_5080_);
if (v_isShared_5074_ == 0)
{
lean_ctor_set(v___x_5073_, 0, v___x_5081_);
v___x_5083_ = v___x_5073_;
goto v_reusejp_5082_;
}
else
{
lean_object* v_reuseFailAlloc_5086_; 
v_reuseFailAlloc_5086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5086_, 0, v___x_5081_);
v___x_5083_ = v_reuseFailAlloc_5086_;
goto v_reusejp_5082_;
}
v_reusejp_5082_:
{
lean_object* v___x_5084_; lean_object* v___x_5085_; 
v___x_5084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5084_, 0, v___x_5083_);
v___x_5085_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5076_, v___x_5077_, v___x_5084_, v___f_5075_);
return v___x_5085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__3___boxed(lean_object* v_y_5088_, lean_object* v_prio_5089_, lean_object* v___f_5090_, lean_object* v_x_5091_, lean_object* v___y_5092_){
_start:
{
lean_object* v_res_5093_; 
v_res_5093_ = l_Std_Async_Async_concurrently___redArg___lam__3(v_y_5088_, v_prio_5089_, v___f_5090_, v_x_5091_);
return v_res_5093_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg(lean_object* v_x_5094_, lean_object* v_y_5095_, lean_object* v_prio_5096_){
_start:
{
lean_object* v___f_5098_; lean_object* v___f_5099_; lean_object* v___x_5100_; uint8_t v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; uint8_t v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; 
v___f_5098_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
lean_inc(v_prio_5096_);
v___f_5099_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrently___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_5099_, 0, v_y_5095_);
lean_closure_set(v___f_5099_, 1, v_prio_5096_);
lean_closure_set(v___f_5099_, 2, v___f_5098_);
v___x_5100_ = lean_unsigned_to_nat(0u);
v___x_5101_ = 0;
v___x_5102_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5102_, 0, lean_box(0));
lean_closure_set(v___x_5102_, 1, v_x_5094_);
v___x_5103_ = lean_io_as_task(v___x_5102_, v_prio_5096_);
v___x_5104_ = 1;
v___x_5105_ = lean_task_bind(v___x_5103_, v___f_5098_, v___x_5100_, v___x_5104_);
v___x_5106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5106_, 0, v___x_5105_);
v___x_5107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5107_, 0, v___x_5106_);
v___x_5108_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5100_, v___x_5101_, v___x_5107_, v___f_5099_);
return v___x_5108_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___boxed(lean_object* v_x_5109_, lean_object* v_y_5110_, lean_object* v_prio_5111_, lean_object* v_a_5112_){
_start:
{
lean_object* v_res_5113_; 
v_res_5113_ = l_Std_Async_Async_concurrently___redArg(v_x_5109_, v_y_5110_, v_prio_5111_);
return v_res_5113_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently(lean_object* v_00_u03b1_5114_, lean_object* v_00_u03b2_5115_, lean_object* v_x_5116_, lean_object* v_y_5117_, lean_object* v_prio_5118_){
_start:
{
lean_object* v___f_5120_; lean_object* v___f_5121_; lean_object* v___x_5122_; uint8_t v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; uint8_t v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; 
v___f_5120_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
lean_inc(v_prio_5118_);
v___f_5121_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrently___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_5121_, 0, v_y_5117_);
lean_closure_set(v___f_5121_, 1, v_prio_5118_);
lean_closure_set(v___f_5121_, 2, v___f_5120_);
v___x_5122_ = lean_unsigned_to_nat(0u);
v___x_5123_ = 0;
v___x_5124_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5124_, 0, lean_box(0));
lean_closure_set(v___x_5124_, 1, v_x_5116_);
v___x_5125_ = lean_io_as_task(v___x_5124_, v_prio_5118_);
v___x_5126_ = 1;
v___x_5127_ = lean_task_bind(v___x_5125_, v___f_5120_, v___x_5122_, v___x_5126_);
v___x_5128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5128_, 0, v___x_5127_);
v___x_5129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5129_, 0, v___x_5128_);
v___x_5130_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5122_, v___x_5123_, v___x_5129_, v___f_5121_);
return v___x_5130_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___boxed(lean_object* v_00_u03b1_5131_, lean_object* v_00_u03b2_5132_, lean_object* v_x_5133_, lean_object* v_y_5134_, lean_object* v_prio_5135_, lean_object* v_a_5136_){
_start:
{
lean_object* v_res_5137_; 
v_res_5137_ = l_Std_Async_Async_concurrently(v_00_u03b1_5131_, v_00_u03b2_5132_, v_x_5133_, v_y_5134_, v_prio_5135_);
return v_res_5137_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__1(lean_object* v_x_5138_){
_start:
{
if (lean_obj_tag(v_x_5138_) == 0)
{
lean_object* v_a_5140_; lean_object* v___x_5142_; uint8_t v_isShared_5143_; uint8_t v_isSharedCheck_5148_; 
v_a_5140_ = lean_ctor_get(v_x_5138_, 0);
v_isSharedCheck_5148_ = !lean_is_exclusive(v_x_5138_);
if (v_isSharedCheck_5148_ == 0)
{
v___x_5142_ = v_x_5138_;
v_isShared_5143_ = v_isSharedCheck_5148_;
goto v_resetjp_5141_;
}
else
{
lean_inc(v_a_5140_);
lean_dec(v_x_5138_);
v___x_5142_ = lean_box(0);
v_isShared_5143_ = v_isSharedCheck_5148_;
goto v_resetjp_5141_;
}
v_resetjp_5141_:
{
lean_object* v___x_5145_; 
if (v_isShared_5143_ == 0)
{
v___x_5145_ = v___x_5142_;
goto v_reusejp_5144_;
}
else
{
lean_object* v_reuseFailAlloc_5147_; 
v_reuseFailAlloc_5147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5147_, 0, v_a_5140_);
v___x_5145_ = v_reuseFailAlloc_5147_;
goto v_reusejp_5144_;
}
v_reusejp_5144_:
{
lean_object* v___x_5146_; 
v___x_5146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5146_, 0, v___x_5145_);
return v___x_5146_;
}
}
}
else
{
lean_object* v_a_5149_; lean_object* v___x_5150_; 
v_a_5149_ = lean_ctor_get(v_x_5138_, 0);
lean_inc(v_a_5149_);
lean_dec_ref_known(v_x_5138_, 1);
v___x_5150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5150_, 0, v_a_5149_);
return v___x_5150_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__1___boxed(lean_object* v_x_5151_, lean_object* v___y_5152_){
_start:
{
lean_object* v_res_5153_; 
v_res_5153_ = l_Std_Async_Async_race___redArg___lam__1(v_x_5151_);
return v_res_5153_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__0(lean_object* v_a_5154_){
_start:
{
lean_object* v___x_5155_; 
v___x_5155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5155_, 0, v_a_5154_);
return v___x_5155_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__3(lean_object* v_a_5156_, lean_object* v_value_5157_){
_start:
{
lean_object* v___x_5159_; 
v___x_5159_ = lean_io_promise_resolve(v_value_5157_, v_a_5156_);
return v___x_5159_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__3___boxed(lean_object* v_a_5160_, lean_object* v_value_5161_, lean_object* v___y_5162_){
_start:
{
lean_object* v_res_5163_; 
v_res_5163_ = l_Std_Async_Async_race___redArg___lam__3(v_a_5160_, v_value_5161_);
lean_dec(v_a_5160_);
return v_res_5163_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__2(lean_object* v_a_5164_, lean_object* v___f_5165_, lean_object* v___f_5166_, lean_object* v_x_5167_){
_start:
{
if (lean_obj_tag(v_x_5167_) == 0)
{
lean_object* v_a_5169_; lean_object* v___x_5171_; uint8_t v_isShared_5172_; uint8_t v_isSharedCheck_5177_; 
lean_dec_ref(v___f_5166_);
lean_dec_ref(v___f_5165_);
v_a_5169_ = lean_ctor_get(v_x_5167_, 0);
v_isSharedCheck_5177_ = !lean_is_exclusive(v_x_5167_);
if (v_isSharedCheck_5177_ == 0)
{
v___x_5171_ = v_x_5167_;
v_isShared_5172_ = v_isSharedCheck_5177_;
goto v_resetjp_5170_;
}
else
{
lean_inc(v_a_5169_);
lean_dec(v_x_5167_);
v___x_5171_ = lean_box(0);
v_isShared_5172_ = v_isSharedCheck_5177_;
goto v_resetjp_5170_;
}
v_resetjp_5170_:
{
lean_object* v___x_5174_; 
if (v_isShared_5172_ == 0)
{
v___x_5174_ = v___x_5171_;
goto v_reusejp_5173_;
}
else
{
lean_object* v_reuseFailAlloc_5176_; 
v_reuseFailAlloc_5176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5176_, 0, v_a_5169_);
v___x_5174_ = v_reuseFailAlloc_5176_;
goto v_reusejp_5173_;
}
v_reusejp_5173_:
{
lean_object* v___x_5175_; 
v___x_5175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5175_, 0, v___x_5174_);
return v___x_5175_;
}
}
}
else
{
lean_object* v___x_5178_; uint8_t v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; 
lean_dec_ref_known(v_x_5167_, 1);
v___x_5178_ = lean_unsigned_to_nat(0u);
v___x_5179_ = 0;
v___x_5180_ = l_IO_Promise_result_x21___redArg(v_a_5164_);
v___x_5181_ = lean_task_map(v___f_5165_, v___x_5180_, v___x_5178_, v___x_5179_);
v___x_5182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5182_, 0, v___x_5181_);
v___x_5183_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5178_, v___x_5179_, v___x_5182_, v___f_5166_);
return v___x_5183_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__2___boxed(lean_object* v_a_5184_, lean_object* v___f_5185_, lean_object* v___f_5186_, lean_object* v_x_5187_, lean_object* v___y_5188_){
_start:
{
lean_object* v_res_5189_; 
v_res_5189_ = l_Std_Async_Async_race___redArg___lam__2(v_a_5184_, v___f_5185_, v___f_5186_, v_x_5187_);
lean_dec(v_a_5184_);
return v_res_5189_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__4(lean_object* v_a_5190_, lean_object* v___x_5191_, lean_object* v___x_5192_, uint8_t v___x_5193_, lean_object* v___f_5194_, lean_object* v_x_5195_){
_start:
{
if (lean_obj_tag(v_x_5195_) == 0)
{
lean_object* v_a_5197_; lean_object* v___x_5199_; uint8_t v_isShared_5200_; uint8_t v_isSharedCheck_5205_; 
lean_dec_ref(v___f_5194_);
lean_dec(v___x_5192_);
lean_dec_ref(v___x_5191_);
lean_dec_ref(v_a_5190_);
v_a_5197_ = lean_ctor_get(v_x_5195_, 0);
v_isSharedCheck_5205_ = !lean_is_exclusive(v_x_5195_);
if (v_isSharedCheck_5205_ == 0)
{
v___x_5199_ = v_x_5195_;
v_isShared_5200_ = v_isSharedCheck_5205_;
goto v_resetjp_5198_;
}
else
{
lean_inc(v_a_5197_);
lean_dec(v_x_5195_);
v___x_5199_ = lean_box(0);
v_isShared_5200_ = v_isSharedCheck_5205_;
goto v_resetjp_5198_;
}
v_resetjp_5198_:
{
lean_object* v___x_5202_; 
if (v_isShared_5200_ == 0)
{
v___x_5202_ = v___x_5199_;
goto v_reusejp_5201_;
}
else
{
lean_object* v_reuseFailAlloc_5204_; 
v_reuseFailAlloc_5204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5204_, 0, v_a_5197_);
v___x_5202_ = v_reuseFailAlloc_5204_;
goto v_reusejp_5201_;
}
v_reusejp_5201_:
{
lean_object* v___x_5203_; 
v___x_5203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5203_, 0, v___x_5202_);
return v___x_5203_;
}
}
}
else
{
lean_object* v___x_5207_; uint8_t v_isShared_5208_; uint8_t v_isSharedCheck_5215_; 
v_isSharedCheck_5215_ = !lean_is_exclusive(v_x_5195_);
if (v_isSharedCheck_5215_ == 0)
{
lean_object* v_unused_5216_; 
v_unused_5216_ = lean_ctor_get(v_x_5195_, 0);
lean_dec(v_unused_5216_);
v___x_5207_ = v_x_5195_;
v_isShared_5208_ = v_isSharedCheck_5215_;
goto v_resetjp_5206_;
}
else
{
lean_dec(v_x_5195_);
v___x_5207_ = lean_box(0);
v_isShared_5208_ = v_isSharedCheck_5215_;
goto v_resetjp_5206_;
}
v_resetjp_5206_:
{
lean_object* v___x_5209_; lean_object* v___x_5211_; 
lean_inc(v___x_5192_);
v___x_5209_ = l_BaseIO_chainTask___redArg(v_a_5190_, v___x_5191_, v___x_5192_, v___x_5193_);
if (v_isShared_5208_ == 0)
{
lean_ctor_set(v___x_5207_, 0, v___x_5209_);
v___x_5211_ = v___x_5207_;
goto v_reusejp_5210_;
}
else
{
lean_object* v_reuseFailAlloc_5214_; 
v_reuseFailAlloc_5214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5214_, 0, v___x_5209_);
v___x_5211_ = v_reuseFailAlloc_5214_;
goto v_reusejp_5210_;
}
v_reusejp_5210_:
{
lean_object* v___x_5212_; lean_object* v___x_5213_; 
v___x_5212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5212_, 0, v___x_5211_);
v___x_5213_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5192_, v___x_5193_, v___x_5212_, v___f_5194_);
return v___x_5213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__4___boxed(lean_object* v_a_5217_, lean_object* v___x_5218_, lean_object* v___x_5219_, lean_object* v___x_5220_, lean_object* v___f_5221_, lean_object* v_x_5222_, lean_object* v___y_5223_){
_start:
{
uint8_t v___x_1414__boxed_5224_; lean_object* v_res_5225_; 
v___x_1414__boxed_5224_ = lean_unbox(v___x_5220_);
v_res_5225_ = l_Std_Async_Async_race___redArg___lam__4(v_a_5217_, v___x_5218_, v___x_5219_, v___x_1414__boxed_5224_, v___f_5221_, v_x_5222_);
return v_res_5225_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__5(lean_object* v___f_5226_, lean_object* v___f_5227_, lean_object* v___f_5228_, lean_object* v_a_5229_, lean_object* v_x_5230_){
_start:
{
if (lean_obj_tag(v_x_5230_) == 0)
{
lean_object* v_a_5232_; lean_object* v___x_5234_; uint8_t v_isShared_5235_; uint8_t v_isSharedCheck_5240_; 
lean_dec_ref(v_a_5229_);
lean_dec_ref(v___f_5228_);
lean_dec_ref(v___f_5227_);
lean_dec(v___f_5226_);
v_a_5232_ = lean_ctor_get(v_x_5230_, 0);
v_isSharedCheck_5240_ = !lean_is_exclusive(v_x_5230_);
if (v_isSharedCheck_5240_ == 0)
{
v___x_5234_ = v_x_5230_;
v_isShared_5235_ = v_isSharedCheck_5240_;
goto v_resetjp_5233_;
}
else
{
lean_inc(v_a_5232_);
lean_dec(v_x_5230_);
v___x_5234_ = lean_box(0);
v_isShared_5235_ = v_isSharedCheck_5240_;
goto v_resetjp_5233_;
}
v_resetjp_5233_:
{
lean_object* v___x_5237_; 
if (v_isShared_5235_ == 0)
{
v___x_5237_ = v___x_5234_;
goto v_reusejp_5236_;
}
else
{
lean_object* v_reuseFailAlloc_5239_; 
v_reuseFailAlloc_5239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5239_, 0, v_a_5232_);
v___x_5237_ = v_reuseFailAlloc_5239_;
goto v_reusejp_5236_;
}
v_reusejp_5236_:
{
lean_object* v___x_5238_; 
v___x_5238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5238_, 0, v___x_5237_);
return v___x_5238_;
}
}
}
else
{
lean_object* v_a_5241_; lean_object* v___x_5243_; uint8_t v_isShared_5244_; uint8_t v_isSharedCheck_5257_; 
v_a_5241_ = lean_ctor_get(v_x_5230_, 0);
v_isSharedCheck_5257_ = !lean_is_exclusive(v_x_5230_);
if (v_isSharedCheck_5257_ == 0)
{
v___x_5243_ = v_x_5230_;
v_isShared_5244_ = v_isSharedCheck_5257_;
goto v_resetjp_5242_;
}
else
{
lean_inc(v_a_5241_);
lean_dec(v_x_5230_);
v___x_5243_ = lean_box(0);
v_isShared_5244_ = v_isSharedCheck_5257_;
goto v_resetjp_5242_;
}
v_resetjp_5242_:
{
lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; uint8_t v___x_5248_; lean_object* v___x_5249_; lean_object* v___f_5250_; lean_object* v___x_5251_; lean_object* v___x_5253_; 
v___x_5245_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_5245_, 0, lean_box(0));
lean_closure_set(v___x_5245_, 1, lean_box(0));
lean_closure_set(v___x_5245_, 2, v___f_5226_);
lean_closure_set(v___x_5245_, 3, lean_box(0));
v___x_5246_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_5246_, 0, lean_box(0));
lean_closure_set(v___x_5246_, 1, lean_box(0));
lean_closure_set(v___x_5246_, 2, lean_box(0));
lean_closure_set(v___x_5246_, 3, v___x_5245_);
lean_closure_set(v___x_5246_, 4, v___f_5227_);
v___x_5247_ = lean_unsigned_to_nat(0u);
v___x_5248_ = 0;
v___x_5249_ = lean_box(v___x_5248_);
lean_inc_ref(v___x_5246_);
v___f_5250_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__4___boxed), 7, 5);
lean_closure_set(v___f_5250_, 0, v_a_5241_);
lean_closure_set(v___f_5250_, 1, v___x_5246_);
lean_closure_set(v___f_5250_, 2, v___x_5247_);
lean_closure_set(v___f_5250_, 3, v___x_5249_);
lean_closure_set(v___f_5250_, 4, v___f_5228_);
v___x_5251_ = l_BaseIO_chainTask___redArg(v_a_5229_, v___x_5246_, v___x_5247_, v___x_5248_);
if (v_isShared_5244_ == 0)
{
lean_ctor_set(v___x_5243_, 0, v___x_5251_);
v___x_5253_ = v___x_5243_;
goto v_reusejp_5252_;
}
else
{
lean_object* v_reuseFailAlloc_5256_; 
v_reuseFailAlloc_5256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5256_, 0, v___x_5251_);
v___x_5253_ = v_reuseFailAlloc_5256_;
goto v_reusejp_5252_;
}
v_reusejp_5252_:
{
lean_object* v___x_5254_; lean_object* v___x_5255_; 
v___x_5254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5254_, 0, v___x_5253_);
v___x_5255_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5247_, v___x_5248_, v___x_5254_, v___f_5250_);
return v___x_5255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__5___boxed(lean_object* v___f_5258_, lean_object* v___f_5259_, lean_object* v___f_5260_, lean_object* v_a_5261_, lean_object* v_x_5262_, lean_object* v___y_5263_){
_start:
{
lean_object* v_res_5264_; 
v_res_5264_ = l_Std_Async_Async_race___redArg___lam__5(v___f_5258_, v___f_5259_, v___f_5260_, v_a_5261_, v_x_5262_);
return v_res_5264_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__6(lean_object* v___f_5265_, lean_object* v___f_5266_, lean_object* v___f_5267_, lean_object* v_y_5268_, lean_object* v_prio_5269_, lean_object* v___f_5270_, lean_object* v_x_5271_){
_start:
{
if (lean_obj_tag(v_x_5271_) == 0)
{
lean_object* v_a_5273_; lean_object* v___x_5275_; uint8_t v_isShared_5276_; uint8_t v_isSharedCheck_5281_; 
lean_dec_ref(v___f_5270_);
lean_dec(v_prio_5269_);
lean_dec_ref(v_y_5268_);
lean_dec_ref(v___f_5267_);
lean_dec_ref(v___f_5266_);
lean_dec(v___f_5265_);
v_a_5273_ = lean_ctor_get(v_x_5271_, 0);
v_isSharedCheck_5281_ = !lean_is_exclusive(v_x_5271_);
if (v_isSharedCheck_5281_ == 0)
{
v___x_5275_ = v_x_5271_;
v_isShared_5276_ = v_isSharedCheck_5281_;
goto v_resetjp_5274_;
}
else
{
lean_inc(v_a_5273_);
lean_dec(v_x_5271_);
v___x_5275_ = lean_box(0);
v_isShared_5276_ = v_isSharedCheck_5281_;
goto v_resetjp_5274_;
}
v_resetjp_5274_:
{
lean_object* v___x_5278_; 
if (v_isShared_5276_ == 0)
{
v___x_5278_ = v___x_5275_;
goto v_reusejp_5277_;
}
else
{
lean_object* v_reuseFailAlloc_5280_; 
v_reuseFailAlloc_5280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5280_, 0, v_a_5273_);
v___x_5278_ = v_reuseFailAlloc_5280_;
goto v_reusejp_5277_;
}
v_reusejp_5277_:
{
lean_object* v___x_5279_; 
v___x_5279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5279_, 0, v___x_5278_);
return v___x_5279_;
}
}
}
else
{
lean_object* v_a_5282_; lean_object* v___x_5284_; uint8_t v_isShared_5285_; uint8_t v_isSharedCheck_5298_; 
v_a_5282_ = lean_ctor_get(v_x_5271_, 0);
v_isSharedCheck_5298_ = !lean_is_exclusive(v_x_5271_);
if (v_isSharedCheck_5298_ == 0)
{
v___x_5284_ = v_x_5271_;
v_isShared_5285_ = v_isSharedCheck_5298_;
goto v_resetjp_5283_;
}
else
{
lean_inc(v_a_5282_);
lean_dec(v_x_5271_);
v___x_5284_ = lean_box(0);
v_isShared_5285_ = v_isSharedCheck_5298_;
goto v_resetjp_5283_;
}
v_resetjp_5283_:
{
lean_object* v___f_5286_; lean_object* v___x_5287_; uint8_t v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; uint8_t v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5294_; 
v___f_5286_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__5___boxed), 6, 4);
lean_closure_set(v___f_5286_, 0, v___f_5265_);
lean_closure_set(v___f_5286_, 1, v___f_5266_);
lean_closure_set(v___f_5286_, 2, v___f_5267_);
lean_closure_set(v___f_5286_, 3, v_a_5282_);
v___x_5287_ = lean_unsigned_to_nat(0u);
v___x_5288_ = 0;
v___x_5289_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5289_, 0, lean_box(0));
lean_closure_set(v___x_5289_, 1, v_y_5268_);
v___x_5290_ = lean_io_as_task(v___x_5289_, v_prio_5269_);
v___x_5291_ = 1;
v___x_5292_ = lean_task_bind(v___x_5290_, v___f_5270_, v___x_5287_, v___x_5291_);
if (v_isShared_5285_ == 0)
{
lean_ctor_set(v___x_5284_, 0, v___x_5292_);
v___x_5294_ = v___x_5284_;
goto v_reusejp_5293_;
}
else
{
lean_object* v_reuseFailAlloc_5297_; 
v_reuseFailAlloc_5297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5297_, 0, v___x_5292_);
v___x_5294_ = v_reuseFailAlloc_5297_;
goto v_reusejp_5293_;
}
v_reusejp_5293_:
{
lean_object* v___x_5295_; lean_object* v___x_5296_; 
v___x_5295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5295_, 0, v___x_5294_);
v___x_5296_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5287_, v___x_5288_, v___x_5295_, v___f_5286_);
return v___x_5296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__6___boxed(lean_object* v___f_5299_, lean_object* v___f_5300_, lean_object* v___f_5301_, lean_object* v_y_5302_, lean_object* v_prio_5303_, lean_object* v___f_5304_, lean_object* v_x_5305_, lean_object* v___y_5306_){
_start:
{
lean_object* v_res_5307_; 
v_res_5307_ = l_Std_Async_Async_race___redArg___lam__6(v___f_5299_, v___f_5300_, v___f_5301_, v_y_5302_, v_prio_5303_, v___f_5304_, v_x_5305_);
return v_res_5307_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__7(lean_object* v___f_5308_, lean_object* v___f_5309_, lean_object* v___f_5310_, lean_object* v_y_5311_, lean_object* v_prio_5312_, lean_object* v___f_5313_, lean_object* v_x_5314_, lean_object* v___f_5315_, lean_object* v_x_5316_){
_start:
{
if (lean_obj_tag(v_x_5316_) == 0)
{
lean_object* v_a_5318_; lean_object* v___x_5320_; uint8_t v_isShared_5321_; uint8_t v_isSharedCheck_5326_; 
lean_dec_ref(v___f_5315_);
lean_dec_ref(v_x_5314_);
lean_dec_ref(v___f_5313_);
lean_dec(v_prio_5312_);
lean_dec_ref(v_y_5311_);
lean_dec(v___f_5310_);
lean_dec_ref(v___f_5309_);
lean_dec_ref(v___f_5308_);
v_a_5318_ = lean_ctor_get(v_x_5316_, 0);
v_isSharedCheck_5326_ = !lean_is_exclusive(v_x_5316_);
if (v_isSharedCheck_5326_ == 0)
{
v___x_5320_ = v_x_5316_;
v_isShared_5321_ = v_isSharedCheck_5326_;
goto v_resetjp_5319_;
}
else
{
lean_inc(v_a_5318_);
lean_dec(v_x_5316_);
v___x_5320_ = lean_box(0);
v_isShared_5321_ = v_isSharedCheck_5326_;
goto v_resetjp_5319_;
}
v_resetjp_5319_:
{
lean_object* v___x_5323_; 
if (v_isShared_5321_ == 0)
{
v___x_5323_ = v___x_5320_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5325_; 
v_reuseFailAlloc_5325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5325_, 0, v_a_5318_);
v___x_5323_ = v_reuseFailAlloc_5325_;
goto v_reusejp_5322_;
}
v_reusejp_5322_:
{
lean_object* v___x_5324_; 
v___x_5324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5324_, 0, v___x_5323_);
return v___x_5324_;
}
}
}
else
{
lean_object* v_a_5327_; lean_object* v___x_5329_; uint8_t v_isShared_5330_; uint8_t v_isSharedCheck_5345_; 
v_a_5327_ = lean_ctor_get(v_x_5316_, 0);
v_isSharedCheck_5345_ = !lean_is_exclusive(v_x_5316_);
if (v_isSharedCheck_5345_ == 0)
{
v___x_5329_ = v_x_5316_;
v_isShared_5330_ = v_isSharedCheck_5345_;
goto v_resetjp_5328_;
}
else
{
lean_inc(v_a_5327_);
lean_dec(v_x_5316_);
v___x_5329_ = lean_box(0);
v_isShared_5330_ = v_isSharedCheck_5345_;
goto v_resetjp_5328_;
}
v_resetjp_5328_:
{
lean_object* v___f_5331_; lean_object* v___f_5332_; lean_object* v___f_5333_; lean_object* v___x_5334_; uint8_t v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; uint8_t v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5341_; 
lean_inc(v_a_5327_);
v___f_5331_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_5331_, 0, v_a_5327_);
v___f_5332_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_5332_, 0, v_a_5327_);
lean_closure_set(v___f_5332_, 1, v___f_5308_);
lean_closure_set(v___f_5332_, 2, v___f_5309_);
lean_inc(v_prio_5312_);
v___f_5333_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__6___boxed), 8, 6);
lean_closure_set(v___f_5333_, 0, v___f_5310_);
lean_closure_set(v___f_5333_, 1, v___f_5331_);
lean_closure_set(v___f_5333_, 2, v___f_5332_);
lean_closure_set(v___f_5333_, 3, v_y_5311_);
lean_closure_set(v___f_5333_, 4, v_prio_5312_);
lean_closure_set(v___f_5333_, 5, v___f_5313_);
v___x_5334_ = lean_unsigned_to_nat(0u);
v___x_5335_ = 0;
v___x_5336_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5336_, 0, lean_box(0));
lean_closure_set(v___x_5336_, 1, v_x_5314_);
v___x_5337_ = lean_io_as_task(v___x_5336_, v_prio_5312_);
v___x_5338_ = 1;
v___x_5339_ = lean_task_bind(v___x_5337_, v___f_5315_, v___x_5334_, v___x_5338_);
if (v_isShared_5330_ == 0)
{
lean_ctor_set(v___x_5329_, 0, v___x_5339_);
v___x_5341_ = v___x_5329_;
goto v_reusejp_5340_;
}
else
{
lean_object* v_reuseFailAlloc_5344_; 
v_reuseFailAlloc_5344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5344_, 0, v___x_5339_);
v___x_5341_ = v_reuseFailAlloc_5344_;
goto v_reusejp_5340_;
}
v_reusejp_5340_:
{
lean_object* v___x_5342_; lean_object* v___x_5343_; 
v___x_5342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5342_, 0, v___x_5341_);
v___x_5343_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5334_, v___x_5335_, v___x_5342_, v___f_5333_);
return v___x_5343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__7___boxed(lean_object* v___f_5346_, lean_object* v___f_5347_, lean_object* v___f_5348_, lean_object* v_y_5349_, lean_object* v_prio_5350_, lean_object* v___f_5351_, lean_object* v_x_5352_, lean_object* v___f_5353_, lean_object* v_x_5354_, lean_object* v___y_5355_){
_start:
{
lean_object* v_res_5356_; 
v_res_5356_ = l_Std_Async_Async_race___redArg___lam__7(v___f_5346_, v___f_5347_, v___f_5348_, v_y_5349_, v_prio_5350_, v___f_5351_, v_x_5352_, v___f_5353_, v_x_5354_);
return v_res_5356_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg(lean_object* v_x_5359_, lean_object* v_y_5360_, lean_object* v_prio_5361_){
_start:
{
lean_object* v___f_5363_; lean_object* v___f_5364_; lean_object* v___f_5365_; lean_object* v___f_5366_; lean_object* v___f_5367_; lean_object* v___x_5368_; uint8_t v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; 
v___f_5363_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___f_5364_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__0));
v___f_5365_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__1));
v___f_5366_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_5367_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_5367_, 0, v___f_5365_);
lean_closure_set(v___f_5367_, 1, v___f_5364_);
lean_closure_set(v___f_5367_, 2, v___f_5366_);
lean_closure_set(v___f_5367_, 3, v_y_5360_);
lean_closure_set(v___f_5367_, 4, v_prio_5361_);
lean_closure_set(v___f_5367_, 5, v___f_5363_);
lean_closure_set(v___f_5367_, 6, v_x_5359_);
lean_closure_set(v___f_5367_, 7, v___f_5363_);
v___x_5368_ = lean_unsigned_to_nat(0u);
v___x_5369_ = 0;
v___x_5370_ = lean_io_promise_new();
v___x_5371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5371_, 0, v___x_5370_);
v___x_5372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5372_, 0, v___x_5371_);
v___x_5373_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5368_, v___x_5369_, v___x_5372_, v___f_5367_);
return v___x_5373_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___boxed(lean_object* v_x_5374_, lean_object* v_y_5375_, lean_object* v_prio_5376_, lean_object* v_a_5377_){
_start:
{
lean_object* v_res_5378_; 
v_res_5378_ = l_Std_Async_Async_race___redArg(v_x_5374_, v_y_5375_, v_prio_5376_);
return v_res_5378_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race(lean_object* v_00_u03b1_5379_, lean_object* v_inst_5380_, lean_object* v_x_5381_, lean_object* v_y_5382_, lean_object* v_prio_5383_){
_start:
{
lean_object* v___f_5385_; lean_object* v___f_5386_; lean_object* v___f_5387_; lean_object* v___f_5388_; lean_object* v___f_5389_; lean_object* v___x_5390_; uint8_t v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; 
v___f_5385_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___f_5386_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__0));
v___f_5387_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__1));
v___f_5388_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_5389_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_5389_, 0, v___f_5387_);
lean_closure_set(v___f_5389_, 1, v___f_5386_);
lean_closure_set(v___f_5389_, 2, v___f_5388_);
lean_closure_set(v___f_5389_, 3, v_y_5382_);
lean_closure_set(v___f_5389_, 4, v_prio_5383_);
lean_closure_set(v___f_5389_, 5, v___f_5385_);
lean_closure_set(v___f_5389_, 6, v_x_5381_);
lean_closure_set(v___f_5389_, 7, v___f_5385_);
v___x_5390_ = lean_unsigned_to_nat(0u);
v___x_5391_ = 0;
v___x_5392_ = lean_io_promise_new();
v___x_5393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5393_, 0, v___x_5392_);
v___x_5394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5394_, 0, v___x_5393_);
v___x_5395_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5390_, v___x_5391_, v___x_5394_, v___f_5389_);
return v___x_5395_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___boxed(lean_object* v_00_u03b1_5396_, lean_object* v_inst_5397_, lean_object* v_x_5398_, lean_object* v_y_5399_, lean_object* v_prio_5400_, lean_object* v_a_5401_){
_start:
{
lean_object* v_res_5402_; 
v_res_5402_ = l_Std_Async_Async_race(v_00_u03b1_5396_, v_inst_5397_, v_x_5398_, v_y_5399_, v_prio_5400_);
lean_dec(v_inst_5397_);
return v_res_5402_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg___lam__1(lean_object* v_prio_5403_, lean_object* v___f_5404_, lean_object* v_x_5405_){
_start:
{
lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; uint8_t v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; 
v___x_5407_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5407_, 0, lean_box(0));
lean_closure_set(v___x_5407_, 1, v_x_5405_);
v___x_5408_ = lean_io_as_task(v___x_5407_, v_prio_5403_);
v___x_5409_ = lean_unsigned_to_nat(0u);
v___x_5410_ = 1;
v___x_5411_ = lean_task_bind(v___x_5408_, v___f_5404_, v___x_5409_, v___x_5410_);
v___x_5412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5412_, 0, v___x_5411_);
v___x_5413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5413_, 0, v___x_5412_);
return v___x_5413_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg___lam__1___boxed(lean_object* v_prio_5414_, lean_object* v___f_5415_, lean_object* v_x_5416_, lean_object* v___y_5417_){
_start:
{
lean_object* v_res_5418_; 
v_res_5418_ = l_Std_Async_Async_concurrentlyAll___redArg___lam__1(v_prio_5414_, v___f_5415_, v_x_5416_);
return v_res_5418_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg___lam__0(lean_object* v___x_5420_, lean_object* v_x_5421_){
_start:
{
if (lean_obj_tag(v_x_5421_) == 0)
{
lean_object* v_a_5423_; lean_object* v___x_5425_; uint8_t v_isShared_5426_; uint8_t v_isSharedCheck_5431_; 
lean_dec_ref(v___x_5420_);
v_a_5423_ = lean_ctor_get(v_x_5421_, 0);
v_isSharedCheck_5431_ = !lean_is_exclusive(v_x_5421_);
if (v_isSharedCheck_5431_ == 0)
{
v___x_5425_ = v_x_5421_;
v_isShared_5426_ = v_isSharedCheck_5431_;
goto v_resetjp_5424_;
}
else
{
lean_inc(v_a_5423_);
lean_dec(v_x_5421_);
v___x_5425_ = lean_box(0);
v_isShared_5426_ = v_isSharedCheck_5431_;
goto v_resetjp_5424_;
}
v_resetjp_5424_:
{
lean_object* v___x_5428_; 
if (v_isShared_5426_ == 0)
{
v___x_5428_ = v___x_5425_;
goto v_reusejp_5427_;
}
else
{
lean_object* v_reuseFailAlloc_5430_; 
v_reuseFailAlloc_5430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5430_, 0, v_a_5423_);
v___x_5428_ = v_reuseFailAlloc_5430_;
goto v_reusejp_5427_;
}
v_reusejp_5427_:
{
lean_object* v___x_5429_; 
v___x_5429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5429_, 0, v___x_5428_);
return v___x_5429_;
}
}
}
else
{
lean_object* v_a_5432_; lean_object* v___x_5433_; size_t v_sz_5434_; size_t v___x_5435_; lean_object* v___x_271__overap_5436_; lean_object* v___x_5437_; 
v_a_5432_ = lean_ctor_get(v_x_5421_, 0);
lean_inc(v_a_5432_);
lean_dec_ref_known(v_x_5421_, 1);
v___x_5433_ = ((lean_object*)(l_Std_Async_Async_concurrentlyAll___redArg___lam__0___closed__0));
v_sz_5434_ = lean_array_size(v_a_5432_);
v___x_5435_ = ((size_t)0ULL);
v___x_271__overap_5436_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_5420_, v___x_5433_, v_sz_5434_, v___x_5435_, v_a_5432_);
v___x_5437_ = lean_apply_1(v___x_271__overap_5436_, lean_box(0));
return v___x_5437_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg___lam__0___boxed(lean_object* v___x_5438_, lean_object* v_x_5439_, lean_object* v___y_5440_){
_start:
{
lean_object* v_res_5441_; 
v_res_5441_ = l_Std_Async_Async_concurrentlyAll___redArg___lam__0(v___x_5438_, v_x_5439_);
return v_res_5441_;
}
}
static lean_object* _init_l_Std_Async_Async_concurrentlyAll___redArg___closed__0(void){
_start:
{
lean_object* v___x_5442_; lean_object* v___f_5443_; 
v___x_5442_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___closed__0, &l_Std_Async_EAsync_instMonad___closed__0_once, _init_l_Std_Async_EAsync_instMonad___closed__0);
v___f_5443_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrentlyAll___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5443_, 0, v___x_5442_);
return v___f_5443_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg(lean_object* v_xs_5444_, lean_object* v_prio_5445_){
_start:
{
lean_object* v___f_5447_; lean_object* v___f_5448_; lean_object* v___x_5449_; lean_object* v___f_5450_; lean_object* v___x_5451_; uint8_t v___x_5452_; size_t v_sz_5453_; size_t v___x_5454_; lean_object* v___x_204__overap_5455_; lean_object* v___x_5456_; lean_object* v___x_5457_; 
v___f_5447_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___f_5448_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrentlyAll___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_5448_, 0, v_prio_5445_);
lean_closure_set(v___f_5448_, 1, v___f_5447_);
v___x_5449_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___closed__0, &l_Std_Async_EAsync_instMonad___closed__0_once, _init_l_Std_Async_EAsync_instMonad___closed__0);
v___f_5450_ = lean_obj_once(&l_Std_Async_Async_concurrentlyAll___redArg___closed__0, &l_Std_Async_Async_concurrentlyAll___redArg___closed__0_once, _init_l_Std_Async_Async_concurrentlyAll___redArg___closed__0);
v___x_5451_ = lean_unsigned_to_nat(0u);
v___x_5452_ = 0;
v_sz_5453_ = lean_array_size(v_xs_5444_);
v___x_5454_ = ((size_t)0ULL);
v___x_204__overap_5455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_5449_, v___f_5448_, v_sz_5453_, v___x_5454_, v_xs_5444_);
v___x_5456_ = lean_apply_1(v___x_204__overap_5455_, lean_box(0));
v___x_5457_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5451_, v___x_5452_, v___x_5456_, v___f_5450_);
return v___x_5457_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg___boxed(lean_object* v_xs_5458_, lean_object* v_prio_5459_, lean_object* v_a_5460_){
_start:
{
lean_object* v_res_5461_; 
v_res_5461_ = l_Std_Async_Async_concurrentlyAll___redArg(v_xs_5458_, v_prio_5459_);
return v_res_5461_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll(lean_object* v_00_u03b1_5462_, lean_object* v_xs_5463_, lean_object* v_prio_5464_){
_start:
{
lean_object* v___f_5466_; lean_object* v___f_5467_; lean_object* v___x_5468_; lean_object* v___f_5469_; lean_object* v___x_5470_; uint8_t v___x_5471_; size_t v_sz_5472_; size_t v___x_5473_; lean_object* v___x_241__overap_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; 
v___f_5466_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___f_5467_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrentlyAll___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_5467_, 0, v_prio_5464_);
lean_closure_set(v___f_5467_, 1, v___f_5466_);
v___x_5468_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___closed__0, &l_Std_Async_EAsync_instMonad___closed__0_once, _init_l_Std_Async_EAsync_instMonad___closed__0);
v___f_5469_ = lean_obj_once(&l_Std_Async_Async_concurrentlyAll___redArg___closed__0, &l_Std_Async_Async_concurrentlyAll___redArg___closed__0_once, _init_l_Std_Async_Async_concurrentlyAll___redArg___closed__0);
v___x_5470_ = lean_unsigned_to_nat(0u);
v___x_5471_ = 0;
v_sz_5472_ = lean_array_size(v_xs_5463_);
v___x_5473_ = ((size_t)0ULL);
v___x_241__overap_5474_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_5468_, v___f_5467_, v_sz_5472_, v___x_5473_, v_xs_5463_);
v___x_5475_ = lean_apply_1(v___x_241__overap_5474_, lean_box(0));
v___x_5476_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5470_, v___x_5471_, v___x_5475_, v___f_5469_);
return v___x_5476_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___boxed(lean_object* v_00_u03b1_5477_, lean_object* v_xs_5478_, lean_object* v_prio_5479_, lean_object* v_a_5480_){
_start:
{
lean_object* v_res_5481_; 
v_res_5481_ = l_Std_Async_Async_concurrentlyAll(v_00_u03b1_5477_, v_xs_5478_, v_prio_5479_);
return v_res_5481_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__4(lean_object* v___f_5482_, lean_object* v___f_5483_, lean_object* v_x_5484_){
_start:
{
if (lean_obj_tag(v_x_5484_) == 0)
{
lean_object* v_a_5486_; lean_object* v___x_5488_; uint8_t v_isShared_5489_; uint8_t v_isSharedCheck_5494_; 
lean_dec_ref(v___f_5483_);
lean_dec(v___f_5482_);
v_a_5486_ = lean_ctor_get(v_x_5484_, 0);
v_isSharedCheck_5494_ = !lean_is_exclusive(v_x_5484_);
if (v_isSharedCheck_5494_ == 0)
{
v___x_5488_ = v_x_5484_;
v_isShared_5489_ = v_isSharedCheck_5494_;
goto v_resetjp_5487_;
}
else
{
lean_inc(v_a_5486_);
lean_dec(v_x_5484_);
v___x_5488_ = lean_box(0);
v_isShared_5489_ = v_isSharedCheck_5494_;
goto v_resetjp_5487_;
}
v_resetjp_5487_:
{
lean_object* v___x_5491_; 
if (v_isShared_5489_ == 0)
{
v___x_5491_ = v___x_5488_;
goto v_reusejp_5490_;
}
else
{
lean_object* v_reuseFailAlloc_5493_; 
v_reuseFailAlloc_5493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5493_, 0, v_a_5486_);
v___x_5491_ = v_reuseFailAlloc_5493_;
goto v_reusejp_5490_;
}
v_reusejp_5490_:
{
lean_object* v___x_5492_; 
v___x_5492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5492_, 0, v___x_5491_);
return v___x_5492_;
}
}
}
else
{
lean_object* v_a_5495_; lean_object* v___x_5497_; uint8_t v_isShared_5498_; uint8_t v_isSharedCheck_5508_; 
v_a_5495_ = lean_ctor_get(v_x_5484_, 0);
v_isSharedCheck_5508_ = !lean_is_exclusive(v_x_5484_);
if (v_isSharedCheck_5508_ == 0)
{
v___x_5497_ = v_x_5484_;
v_isShared_5498_ = v_isSharedCheck_5508_;
goto v_resetjp_5496_;
}
else
{
lean_inc(v_a_5495_);
lean_dec(v_x_5484_);
v___x_5497_ = lean_box(0);
v_isShared_5498_ = v_isSharedCheck_5508_;
goto v_resetjp_5496_;
}
v_resetjp_5496_:
{
lean_object* v___x_5499_; lean_object* v___x_5500_; lean_object* v___x_5501_; uint8_t v___x_5502_; lean_object* v___x_5503_; lean_object* v___x_5505_; 
v___x_5499_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_5499_, 0, lean_box(0));
lean_closure_set(v___x_5499_, 1, lean_box(0));
lean_closure_set(v___x_5499_, 2, v___f_5482_);
lean_closure_set(v___x_5499_, 3, lean_box(0));
v___x_5500_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_5500_, 0, lean_box(0));
lean_closure_set(v___x_5500_, 1, lean_box(0));
lean_closure_set(v___x_5500_, 2, lean_box(0));
lean_closure_set(v___x_5500_, 3, v___x_5499_);
lean_closure_set(v___x_5500_, 4, v___f_5483_);
v___x_5501_ = lean_unsigned_to_nat(0u);
v___x_5502_ = 0;
v___x_5503_ = l_BaseIO_chainTask___redArg(v_a_5495_, v___x_5500_, v___x_5501_, v___x_5502_);
if (v_isShared_5498_ == 0)
{
lean_ctor_set(v___x_5497_, 0, v___x_5503_);
v___x_5505_ = v___x_5497_;
goto v_reusejp_5504_;
}
else
{
lean_object* v_reuseFailAlloc_5507_; 
v_reuseFailAlloc_5507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5507_, 0, v___x_5503_);
v___x_5505_ = v_reuseFailAlloc_5507_;
goto v_reusejp_5504_;
}
v_reusejp_5504_:
{
lean_object* v___x_5506_; 
v___x_5506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5506_, 0, v___x_5505_);
return v___x_5506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__4___boxed(lean_object* v___f_5509_, lean_object* v___f_5510_, lean_object* v_x_5511_, lean_object* v___y_5512_){
_start:
{
lean_object* v_res_5513_; 
v_res_5513_ = l_Std_Async_Async_raceAll___redArg___lam__4(v___f_5509_, v___f_5510_, v_x_5511_);
return v_res_5513_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__0(lean_object* v_prio_5514_, lean_object* v___f_5515_, lean_object* v___f_5516_, lean_object* v_x_5517_){
_start:
{
lean_object* v___x_5519_; uint8_t v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; uint8_t v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; 
v___x_5519_ = lean_unsigned_to_nat(0u);
v___x_5520_ = 0;
v___x_5521_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5521_, 0, lean_box(0));
lean_closure_set(v___x_5521_, 1, v_x_5517_);
v___x_5522_ = lean_io_as_task(v___x_5521_, v_prio_5514_);
v___x_5523_ = 1;
v___x_5524_ = lean_task_bind(v___x_5522_, v___f_5515_, v___x_5519_, v___x_5523_);
v___x_5525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5525_, 0, v___x_5524_);
v___x_5526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5526_, 0, v___x_5525_);
v___x_5527_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5519_, v___x_5520_, v___x_5526_, v___f_5516_);
return v___x_5527_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__0___boxed(lean_object* v_prio_5528_, lean_object* v___f_5529_, lean_object* v___f_5530_, lean_object* v_x_5531_, lean_object* v___y_5532_){
_start:
{
lean_object* v_res_5533_; 
v_res_5533_ = l_Std_Async_Async_raceAll___redArg___lam__0(v_prio_5528_, v___f_5529_, v___f_5530_, v_x_5531_);
return v_res_5533_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__2(lean_object* v___f_5534_, lean_object* v_prio_5535_, lean_object* v___f_5536_, lean_object* v___f_5537_, lean_object* v___f_5538_, lean_object* v_inst_5539_, lean_object* v_xs_5540_, lean_object* v_x_5541_){
_start:
{
if (lean_obj_tag(v_x_5541_) == 0)
{
lean_object* v_a_5543_; lean_object* v___x_5545_; uint8_t v_isShared_5546_; uint8_t v_isSharedCheck_5551_; 
lean_dec(v_xs_5540_);
lean_dec_ref(v_inst_5539_);
lean_dec_ref(v___f_5538_);
lean_dec_ref(v___f_5537_);
lean_dec_ref(v___f_5536_);
lean_dec(v_prio_5535_);
lean_dec(v___f_5534_);
v_a_5543_ = lean_ctor_get(v_x_5541_, 0);
v_isSharedCheck_5551_ = !lean_is_exclusive(v_x_5541_);
if (v_isSharedCheck_5551_ == 0)
{
v___x_5545_ = v_x_5541_;
v_isShared_5546_ = v_isSharedCheck_5551_;
goto v_resetjp_5544_;
}
else
{
lean_inc(v_a_5543_);
lean_dec(v_x_5541_);
v___x_5545_ = lean_box(0);
v_isShared_5546_ = v_isSharedCheck_5551_;
goto v_resetjp_5544_;
}
v_resetjp_5544_:
{
lean_object* v___x_5548_; 
if (v_isShared_5546_ == 0)
{
v___x_5548_ = v___x_5545_;
goto v_reusejp_5547_;
}
else
{
lean_object* v_reuseFailAlloc_5550_; 
v_reuseFailAlloc_5550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5550_, 0, v_a_5543_);
v___x_5548_ = v_reuseFailAlloc_5550_;
goto v_reusejp_5547_;
}
v_reusejp_5547_:
{
lean_object* v___x_5549_; 
v___x_5549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5549_, 0, v___x_5548_);
return v___x_5549_;
}
}
}
else
{
lean_object* v_a_5552_; lean_object* v___f_5553_; lean_object* v___f_5554_; lean_object* v___f_5555_; lean_object* v___f_5556_; lean_object* v___x_5557_; uint8_t v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; 
v_a_5552_ = lean_ctor_get(v_x_5541_, 0);
lean_inc_n(v_a_5552_, 2);
lean_dec_ref_known(v_x_5541_, 1);
v___f_5553_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_5553_, 0, v_a_5552_);
v___f_5554_ = lean_alloc_closure((void*)(l_Std_Async_Async_raceAll___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_5554_, 0, v___f_5534_);
lean_closure_set(v___f_5554_, 1, v___f_5553_);
v___f_5555_ = lean_alloc_closure((void*)(l_Std_Async_Async_raceAll___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_5555_, 0, v_prio_5535_);
lean_closure_set(v___f_5555_, 1, v___f_5536_);
lean_closure_set(v___f_5555_, 2, v___f_5554_);
v___f_5556_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_5556_, 0, v_a_5552_);
lean_closure_set(v___f_5556_, 1, v___f_5537_);
lean_closure_set(v___f_5556_, 2, v___f_5538_);
v___x_5557_ = lean_unsigned_to_nat(0u);
v___x_5558_ = 0;
v___x_5559_ = lean_apply_3(v_inst_5539_, v_xs_5540_, v___f_5555_, lean_box(0));
v___x_5560_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5557_, v___x_5558_, v___x_5559_, v___f_5556_);
return v___x_5560_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__2___boxed(lean_object* v___f_5561_, lean_object* v_prio_5562_, lean_object* v___f_5563_, lean_object* v___f_5564_, lean_object* v___f_5565_, lean_object* v_inst_5566_, lean_object* v_xs_5567_, lean_object* v_x_5568_, lean_object* v___y_5569_){
_start:
{
lean_object* v_res_5570_; 
v_res_5570_ = l_Std_Async_Async_raceAll___redArg___lam__2(v___f_5561_, v_prio_5562_, v___f_5563_, v___f_5564_, v___f_5565_, v_inst_5566_, v_xs_5567_, v_x_5568_);
return v_res_5570_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg(lean_object* v_inst_5571_, lean_object* v_xs_5572_, lean_object* v_prio_5573_){
_start:
{
lean_object* v___f_5575_; lean_object* v___f_5576_; lean_object* v___f_5577_; lean_object* v___f_5578_; lean_object* v___f_5579_; lean_object* v___x_5580_; uint8_t v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; 
v___f_5575_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__1));
v___f_5576_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__0));
v___f_5577_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___f_5578_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_5579_ = lean_alloc_closure((void*)(l_Std_Async_Async_raceAll___redArg___lam__2___boxed), 9, 7);
lean_closure_set(v___f_5579_, 0, v___f_5578_);
lean_closure_set(v___f_5579_, 1, v_prio_5573_);
lean_closure_set(v___f_5579_, 2, v___f_5577_);
lean_closure_set(v___f_5579_, 3, v___f_5575_);
lean_closure_set(v___f_5579_, 4, v___f_5576_);
lean_closure_set(v___f_5579_, 5, v_inst_5571_);
lean_closure_set(v___f_5579_, 6, v_xs_5572_);
v___x_5580_ = lean_unsigned_to_nat(0u);
v___x_5581_ = 0;
v___x_5582_ = lean_io_promise_new();
v___x_5583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5583_, 0, v___x_5582_);
v___x_5584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5584_, 0, v___x_5583_);
v___x_5585_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5580_, v___x_5581_, v___x_5584_, v___f_5579_);
return v___x_5585_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___boxed(lean_object* v_inst_5586_, lean_object* v_xs_5587_, lean_object* v_prio_5588_, lean_object* v_a_5589_){
_start:
{
lean_object* v_res_5590_; 
v_res_5590_ = l_Std_Async_Async_raceAll___redArg(v_inst_5586_, v_xs_5587_, v_prio_5588_);
return v_res_5590_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll(lean_object* v_c_5591_, lean_object* v_00_u03b1_5592_, lean_object* v_inst_5593_, lean_object* v_xs_5594_, lean_object* v_prio_5595_){
_start:
{
lean_object* v___f_5597_; lean_object* v___f_5598_; lean_object* v___f_5599_; lean_object* v___f_5600_; lean_object* v___f_5601_; lean_object* v___x_5602_; uint8_t v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; 
v___f_5597_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__1));
v___f_5598_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__0));
v___f_5599_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___f_5600_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_5601_ = lean_alloc_closure((void*)(l_Std_Async_Async_raceAll___redArg___lam__2___boxed), 9, 7);
lean_closure_set(v___f_5601_, 0, v___f_5600_);
lean_closure_set(v___f_5601_, 1, v_prio_5595_);
lean_closure_set(v___f_5601_, 2, v___f_5599_);
lean_closure_set(v___f_5601_, 3, v___f_5597_);
lean_closure_set(v___f_5601_, 4, v___f_5598_);
lean_closure_set(v___f_5601_, 5, v_inst_5593_);
lean_closure_set(v___f_5601_, 6, v_xs_5594_);
v___x_5602_ = lean_unsigned_to_nat(0u);
v___x_5603_ = 0;
v___x_5604_ = lean_io_promise_new();
v___x_5605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5605_, 0, v___x_5604_);
v___x_5606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5606_, 0, v___x_5605_);
v___x_5607_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5602_, v___x_5603_, v___x_5606_, v___f_5601_);
return v___x_5607_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___boxed(lean_object* v_c_5608_, lean_object* v_00_u03b1_5609_, lean_object* v_inst_5610_, lean_object* v_xs_5611_, lean_object* v_prio_5612_, lean_object* v_a_5613_){
_start:
{
lean_object* v_res_5614_; 
v_res_5614_ = l_Std_Async_Async_raceAll(v_c_5608_, v_00_u03b1_5609_, v_inst_5610_, v_xs_5611_, v_prio_5612_);
return v_res_5614_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_background___redArg(lean_object* v_inst_5615_, lean_object* v_inst_5616_, lean_object* v_action_5617_, lean_object* v_prio_5618_){
_start:
{
lean_object* v_toApplicative_5619_; lean_object* v_toFunctor_5620_; lean_object* v_mapConst_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; 
v_toApplicative_5619_ = lean_ctor_get(v_inst_5615_, 0);
lean_inc_ref(v_toApplicative_5619_);
lean_dec_ref(v_inst_5615_);
v_toFunctor_5620_ = lean_ctor_get(v_toApplicative_5619_, 0);
lean_inc_ref(v_toFunctor_5620_);
lean_dec_ref(v_toApplicative_5619_);
v_mapConst_5621_ = lean_ctor_get(v_toFunctor_5620_, 1);
lean_inc(v_mapConst_5621_);
lean_dec_ref(v_toFunctor_5620_);
v___x_5622_ = lean_apply_3(v_inst_5616_, lean_box(0), v_action_5617_, v_prio_5618_);
v___x_5623_ = lean_box(0);
v___x_5624_ = lean_apply_4(v_mapConst_5621_, lean_box(0), lean_box(0), v___x_5623_, v___x_5622_);
return v___x_5624_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_background(lean_object* v_m_5625_, lean_object* v_t_5626_, lean_object* v_00_u03b1_5627_, lean_object* v_inst_5628_, lean_object* v_inst_5629_, lean_object* v_action_5630_, lean_object* v_prio_5631_){
_start:
{
lean_object* v_toApplicative_5632_; lean_object* v_toFunctor_5633_; lean_object* v_mapConst_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; 
v_toApplicative_5632_ = lean_ctor_get(v_inst_5628_, 0);
lean_inc_ref(v_toApplicative_5632_);
lean_dec_ref(v_inst_5628_);
v_toFunctor_5633_ = lean_ctor_get(v_toApplicative_5632_, 0);
lean_inc_ref(v_toFunctor_5633_);
lean_dec_ref(v_toApplicative_5632_);
v_mapConst_5634_ = lean_ctor_get(v_toFunctor_5633_, 1);
lean_inc(v_mapConst_5634_);
lean_dec_ref(v_toFunctor_5633_);
v___x_5635_ = lean_apply_3(v_inst_5629_, lean_box(0), v_action_5630_, v_prio_5631_);
v___x_5636_ = lean_box(0);
v___x_5637_ = lean_apply_4(v_mapConst_5634_, lean_box(0), lean_box(0), v___x_5636_, v___x_5635_);
return v___x_5637_;
}
}
lean_object* runtime_initialize_Init_System_Promise(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Async_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
