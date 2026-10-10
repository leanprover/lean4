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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorIdx___impl___boxed(lean_object*, lean_object*);
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
lean_object* l_Std_Async_ETask_map___redArg(lean_object* v_f_180_, lean_object* v_x_181_, lean_object* v_prio_182_, uint8_t v_sync_183_){
_start:
{
lean_object* v___f_184_; lean_object* v___x_185_; 
v___f_184_ = lean_alloc_closure((void*)(l_Std_Async_ETask_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_184_, 0, v_f_180_);
v___x_185_ = lean_task_map(v___f_184_, v_x_181_, v_prio_182_, v_sync_183_);
return v___x_185_;
}
}
LEAN_EXPORT void l_Std_Async_ETask_map___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_180_ = stack[0].m_obj;
lean_object* v_x_181_ = stack[1].m_obj;
lean_object* v_prio_182_ = stack[2].m_obj;
uint8_t v_sync_183_ = stack[3].m_num;
lean_object* v_res_186_;
v_res_186_ = l_Std_Async_ETask_map___redArg(v_f_180_, v_x_181_, v_prio_182_, v_sync_183_);
stack->m_obj
 = v_res_186_;
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_map___redArg___boxed(lean_object* v_f_187_, lean_object* v_x_188_, lean_object* v_prio_189_, lean_object* v_sync_190_){
_start:
{
uint8_t v_sync_boxed_191_; lean_object* v_res_192_; 
v_sync_boxed_191_ = lean_unbox(v_sync_190_);
v_res_192_ = l_Std_Async_ETask_map___redArg(v_f_187_, v_x_188_, v_prio_189_, v_sync_boxed_191_);
return v_res_192_;
}
}
lean_object* l_Std_Async_ETask_map(lean_object* v_00_u03b1_193_, lean_object* v_00_u03b2_194_, lean_object* v_00_u03b5_195_, lean_object* v_f_196_, lean_object* v_x_197_, lean_object* v_prio_198_, uint8_t v_sync_199_){
_start:
{
lean_object* v___f_200_; lean_object* v___x_201_; 
v___f_200_ = lean_alloc_closure((void*)(l_Std_Async_ETask_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_200_, 0, v_f_196_);
v___x_201_ = lean_task_map(v___f_200_, v_x_197_, v_prio_198_, v_sync_199_);
return v___x_201_;
}
}
LEAN_EXPORT void l_Std_Async_ETask_map_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_196_ = stack[3].m_obj;
lean_object* v_x_197_ = stack[4].m_obj;
lean_object* v_prio_198_ = stack[5].m_obj;
uint8_t v_sync_199_ = stack[6].m_num;
lean_object* v_res_202_;
v_res_202_ = l_Std_Async_ETask_map(lean_box(0), lean_box(0), lean_box(0), v_f_196_, v_x_197_, v_prio_198_, v_sync_199_);
stack->m_obj
 = v_res_202_;
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_map___boxed(lean_object* v_00_u03b1_203_, lean_object* v_00_u03b2_204_, lean_object* v_00_u03b5_205_, lean_object* v_f_206_, lean_object* v_x_207_, lean_object* v_prio_208_, lean_object* v_sync_209_){
_start:
{
uint8_t v_sync_boxed_210_; lean_object* v_res_211_; 
v_sync_boxed_210_ = lean_unbox(v_sync_209_);
v_res_211_ = l_Std_Async_ETask_map(v_00_u03b1_203_, v_00_u03b2_204_, v_00_u03b5_205_, v_f_206_, v_x_207_, v_prio_208_, v_sync_boxed_210_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_bind___redArg___lam__0(lean_object* v_f_212_, lean_object* v_x_213_){
_start:
{
if (lean_obj_tag(v_x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_222_; 
lean_dec_ref(v_f_212_);
v_a_214_ = lean_ctor_get(v_x_213_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v_x_213_);
if (v_isSharedCheck_222_ == 0)
{
v___x_216_ = v_x_213_;
v_isShared_217_ = v_isSharedCheck_222_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v_x_213_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_222_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_219_; 
if (v_isShared_217_ == 0)
{
v___x_219_ = v___x_216_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_a_214_);
v___x_219_ = v_reuseFailAlloc_221_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
lean_object* v___x_220_; 
v___x_220_ = lean_task_pure(v___x_219_);
return v___x_220_;
}
}
}
else
{
lean_object* v_a_223_; lean_object* v___x_224_; 
v_a_223_ = lean_ctor_get(v_x_213_, 0);
lean_inc(v_a_223_);
lean_dec_ref_known(v_x_213_, 1);
v___x_224_ = lean_apply_1(v_f_212_, v_a_223_);
return v___x_224_;
}
}
}
lean_object* l_Std_Async_ETask_bind___redArg(lean_object* v_x_225_, lean_object* v_f_226_, lean_object* v_prio_227_, uint8_t v_sync_228_){
_start:
{
lean_object* v___f_229_; lean_object* v___x_230_; 
v___f_229_ = lean_alloc_closure((void*)(l_Std_Async_ETask_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_229_, 0, v_f_226_);
v___x_230_ = lean_task_bind(v_x_225_, v___f_229_, v_prio_227_, v_sync_228_);
return v___x_230_;
}
}
LEAN_EXPORT void l_Std_Async_ETask_bind___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_225_ = stack[0].m_obj;
lean_object* v_f_226_ = stack[1].m_obj;
lean_object* v_prio_227_ = stack[2].m_obj;
uint8_t v_sync_228_ = stack[3].m_num;
lean_object* v_res_231_;
v_res_231_ = l_Std_Async_ETask_bind___redArg(v_x_225_, v_f_226_, v_prio_227_, v_sync_228_);
stack->m_obj
 = v_res_231_;
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_bind___redArg___boxed(lean_object* v_x_232_, lean_object* v_f_233_, lean_object* v_prio_234_, lean_object* v_sync_235_){
_start:
{
uint8_t v_sync_boxed_236_; lean_object* v_res_237_; 
v_sync_boxed_236_ = lean_unbox(v_sync_235_);
v_res_237_ = l_Std_Async_ETask_bind___redArg(v_x_232_, v_f_233_, v_prio_234_, v_sync_boxed_236_);
return v_res_237_;
}
}
lean_object* l_Std_Async_ETask_bind(lean_object* v_00_u03b5_238_, lean_object* v_00_u03b1_239_, lean_object* v_00_u03b2_240_, lean_object* v_x_241_, lean_object* v_f_242_, lean_object* v_prio_243_, uint8_t v_sync_244_){
_start:
{
lean_object* v___f_245_; lean_object* v___x_246_; 
v___f_245_ = lean_alloc_closure((void*)(l_Std_Async_ETask_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_245_, 0, v_f_242_);
v___x_246_ = lean_task_bind(v_x_241_, v___f_245_, v_prio_243_, v_sync_244_);
return v___x_246_;
}
}
LEAN_EXPORT void l_Std_Async_ETask_bind_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_241_ = stack[3].m_obj;
lean_object* v_f_242_ = stack[4].m_obj;
lean_object* v_prio_243_ = stack[5].m_obj;
uint8_t v_sync_244_ = stack[6].m_num;
lean_object* v_res_247_;
v_res_247_ = l_Std_Async_ETask_bind(lean_box(0), lean_box(0), lean_box(0), v_x_241_, v_f_242_, v_prio_243_, v_sync_244_);
stack->m_obj
 = v_res_247_;
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_bind___boxed(lean_object* v_00_u03b5_248_, lean_object* v_00_u03b1_249_, lean_object* v_00_u03b2_250_, lean_object* v_x_251_, lean_object* v_f_252_, lean_object* v_prio_253_, lean_object* v_sync_254_){
_start:
{
uint8_t v_sync_boxed_255_; lean_object* v_res_256_; 
v_sync_boxed_255_ = lean_unbox(v_sync_254_);
v_res_256_ = l_Std_Async_ETask_bind(v_00_u03b5_248_, v_00_u03b1_249_, v_00_u03b2_250_, v_x_251_, v_f_252_, v_prio_253_, v_sync_boxed_255_);
return v_res_256_;
}
}
lean_object* l_Std_Async_ETask_bindEIO___redArg___lam__0(lean_object* v_f_257_, lean_object* v_a_258_){
_start:
{
lean_object* v_a_261_; 
if (lean_obj_tag(v_a_258_) == 0)
{
lean_object* v_a_264_; 
lean_dec_ref(v_f_257_);
v_a_264_ = lean_ctor_get(v_a_258_, 0);
lean_inc(v_a_264_);
lean_dec_ref_known(v_a_258_, 1);
v_a_261_ = v_a_264_;
goto v___jp_260_;
}
else
{
lean_object* v_a_265_; lean_object* v___x_266_; 
v_a_265_ = lean_ctor_get(v_a_258_, 0);
lean_inc(v_a_265_);
lean_dec_ref_known(v_a_258_, 1);
v___x_266_ = lean_apply_2(v_f_257_, v_a_265_, lean_box(0));
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_a_267_);
lean_dec_ref_known(v___x_266_, 1);
return v_a_267_;
}
else
{
lean_object* v_a_268_; 
v_a_268_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_a_268_);
lean_dec_ref_known(v___x_266_, 1);
v_a_261_ = v_a_268_;
goto v___jp_260_;
}
}
v___jp_260_:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_262_, 0, v_a_261_);
v___x_263_ = lean_task_pure(v___x_262_);
return v___x_263_;
}
}
}
LEAN_EXPORT void l_Std_Async_ETask_bindEIO___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_257_ = stack[0].m_obj;
lean_object* v_a_258_ = stack[1].m_obj;
lean_object* v_res_269_;
v_res_269_ = l_Std_Async_ETask_bindEIO___redArg___lam__0(v_f_257_, v_a_258_);
stack->m_obj
 = v_res_269_;
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_bindEIO___redArg___lam__0___boxed(lean_object* v_f_270_, lean_object* v_a_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Std_Async_ETask_bindEIO___redArg___lam__0(v_f_270_, v_a_271_);
return v_res_273_;
}
}
lean_object* l_Std_Async_ETask_bindEIO___redArg(lean_object* v_x_274_, lean_object* v_f_275_, lean_object* v_prio_276_, uint8_t v_sync_277_){
_start:
{
lean_object* v___f_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___f_279_ = lean_alloc_closure((void*)(l_Std_Async_ETask_bindEIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_279_, 0, v_f_275_);
v___x_280_ = lean_io_bind_task(v_x_274_, v___f_279_, v_prio_276_, v_sync_277_);
v___x_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT void l_Std_Async_ETask_bindEIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_274_ = stack[0].m_obj;
lean_object* v_f_275_ = stack[1].m_obj;
lean_object* v_prio_276_ = stack[2].m_obj;
uint8_t v_sync_277_ = stack[3].m_num;
lean_object* v_res_282_;
v_res_282_ = l_Std_Async_ETask_bindEIO___redArg(v_x_274_, v_f_275_, v_prio_276_, v_sync_277_);
stack->m_obj
 = v_res_282_;
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_bindEIO___redArg___boxed(lean_object* v_x_283_, lean_object* v_f_284_, lean_object* v_prio_285_, lean_object* v_sync_286_, lean_object* v_a_287_){
_start:
{
uint8_t v_sync_boxed_288_; lean_object* v_res_289_; 
v_sync_boxed_288_ = lean_unbox(v_sync_286_);
v_res_289_ = l_Std_Async_ETask_bindEIO___redArg(v_x_283_, v_f_284_, v_prio_285_, v_sync_boxed_288_);
return v_res_289_;
}
}
lean_object* l_Std_Async_ETask_bindEIO(lean_object* v_00_u03b5_290_, lean_object* v_00_u03b1_291_, lean_object* v_00_u03b2_292_, lean_object* v_x_293_, lean_object* v_f_294_, lean_object* v_prio_295_, uint8_t v_sync_296_){
_start:
{
lean_object* v___f_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___f_298_ = lean_alloc_closure((void*)(l_Std_Async_ETask_bindEIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_298_, 0, v_f_294_);
v___x_299_ = lean_io_bind_task(v_x_293_, v___f_298_, v_prio_295_, v_sync_296_);
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT void l_Std_Async_ETask_bindEIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_293_ = stack[3].m_obj;
lean_object* v_f_294_ = stack[4].m_obj;
lean_object* v_prio_295_ = stack[5].m_obj;
uint8_t v_sync_296_ = stack[6].m_num;
lean_object* v_res_301_;
v_res_301_ = l_Std_Async_ETask_bindEIO(lean_box(0), lean_box(0), lean_box(0), v_x_293_, v_f_294_, v_prio_295_, v_sync_296_);
stack->m_obj
 = v_res_301_;
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_bindEIO___boxed(lean_object* v_00_u03b5_302_, lean_object* v_00_u03b1_303_, lean_object* v_00_u03b2_304_, lean_object* v_x_305_, lean_object* v_f_306_, lean_object* v_prio_307_, lean_object* v_sync_308_, lean_object* v_a_309_){
_start:
{
uint8_t v_sync_boxed_310_; lean_object* v_res_311_; 
v_sync_boxed_310_ = lean_unbox(v_sync_308_);
v_res_311_ = l_Std_Async_ETask_bindEIO(v_00_u03b5_302_, v_00_u03b1_303_, v_00_u03b2_304_, v_x_305_, v_f_306_, v_prio_307_, v_sync_boxed_310_);
return v_res_311_;
}
}
lean_object* l_Std_Async_ETask_mapEIO___redArg___lam__0(lean_object* v_f_312_, lean_object* v_a_313_){
_start:
{
lean_object* v_a_316_; 
if (lean_obj_tag(v_a_313_) == 0)
{
lean_object* v_a_318_; 
lean_dec_ref(v_f_312_);
v_a_318_ = lean_ctor_get(v_a_313_, 0);
lean_inc(v_a_318_);
lean_dec_ref_known(v_a_313_, 1);
v_a_316_ = v_a_318_;
goto v___jp_315_;
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_329_; 
v_a_319_ = lean_ctor_get(v_a_313_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v_a_313_);
if (v_isSharedCheck_329_ == 0)
{
v___x_321_ = v_a_313_;
v_isShared_322_ = v_isSharedCheck_329_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v_a_313_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_329_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; 
v___x_323_ = lean_apply_2(v_f_312_, v_a_319_, lean_box(0));
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v_a_324_; lean_object* v___x_326_; 
v_a_324_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_a_324_);
lean_dec_ref_known(v___x_323_, 1);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v_a_324_);
v___x_326_ = v___x_321_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_324_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
else
{
lean_object* v_a_328_; 
lean_del_object(v___x_321_);
v_a_328_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_a_328_);
lean_dec_ref_known(v___x_323_, 1);
v_a_316_ = v_a_328_;
goto v___jp_315_;
}
}
}
v___jp_315_:
{
lean_object* v___x_317_; 
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v_a_316_);
return v___x_317_;
}
}
}
LEAN_EXPORT void l_Std_Async_ETask_mapEIO___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_312_ = stack[0].m_obj;
lean_object* v_a_313_ = stack[1].m_obj;
lean_object* v_res_330_;
v_res_330_ = l_Std_Async_ETask_mapEIO___redArg___lam__0(v_f_312_, v_a_313_);
stack->m_obj
 = v_res_330_;
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_mapEIO___redArg___lam__0___boxed(lean_object* v_f_331_, lean_object* v_a_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Std_Async_ETask_mapEIO___redArg___lam__0(v_f_331_, v_a_332_);
return v_res_334_;
}
}
lean_object* l_Std_Async_ETask_mapEIO___redArg(lean_object* v_f_335_, lean_object* v_x_336_, lean_object* v_prio_337_, uint8_t v_sync_338_){
_start:
{
lean_object* v___f_340_; lean_object* v___x_341_; 
v___f_340_ = lean_alloc_closure((void*)(l_Std_Async_ETask_mapEIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_340_, 0, v_f_335_);
v___x_341_ = lean_io_map_task(v___f_340_, v_x_336_, v_prio_337_, v_sync_338_);
return v___x_341_;
}
}
LEAN_EXPORT void l_Std_Async_ETask_mapEIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_335_ = stack[0].m_obj;
lean_object* v_x_336_ = stack[1].m_obj;
lean_object* v_prio_337_ = stack[2].m_obj;
uint8_t v_sync_338_ = stack[3].m_num;
lean_object* v_res_342_;
v_res_342_ = l_Std_Async_ETask_mapEIO___redArg(v_f_335_, v_x_336_, v_prio_337_, v_sync_338_);
stack->m_obj
 = v_res_342_;
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_mapEIO___redArg___boxed(lean_object* v_f_343_, lean_object* v_x_344_, lean_object* v_prio_345_, lean_object* v_sync_346_, lean_object* v_a_347_){
_start:
{
uint8_t v_sync_boxed_348_; lean_object* v_res_349_; 
v_sync_boxed_348_ = lean_unbox(v_sync_346_);
v_res_349_ = l_Std_Async_ETask_mapEIO___redArg(v_f_343_, v_x_344_, v_prio_345_, v_sync_boxed_348_);
return v_res_349_;
}
}
lean_object* l_Std_Async_ETask_mapEIO(lean_object* v_00_u03b1_350_, lean_object* v_00_u03b5_351_, lean_object* v_00_u03b2_352_, lean_object* v_f_353_, lean_object* v_x_354_, lean_object* v_prio_355_, uint8_t v_sync_356_){
_start:
{
lean_object* v___f_358_; lean_object* v___x_359_; 
v___f_358_ = lean_alloc_closure((void*)(l_Std_Async_ETask_mapEIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_358_, 0, v_f_353_);
v___x_359_ = lean_io_map_task(v___f_358_, v_x_354_, v_prio_355_, v_sync_356_);
return v___x_359_;
}
}
LEAN_EXPORT void l_Std_Async_ETask_mapEIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_353_ = stack[3].m_obj;
lean_object* v_x_354_ = stack[4].m_obj;
lean_object* v_prio_355_ = stack[5].m_obj;
uint8_t v_sync_356_ = stack[6].m_num;
lean_object* v_res_360_;
v_res_360_ = l_Std_Async_ETask_mapEIO(lean_box(0), lean_box(0), lean_box(0), v_f_353_, v_x_354_, v_prio_355_, v_sync_356_);
stack->m_obj
 = v_res_360_;
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_mapEIO___boxed(lean_object* v_00_u03b1_361_, lean_object* v_00_u03b5_362_, lean_object* v_00_u03b2_363_, lean_object* v_f_364_, lean_object* v_x_365_, lean_object* v_prio_366_, lean_object* v_sync_367_, lean_object* v_a_368_){
_start:
{
uint8_t v_sync_boxed_369_; lean_object* v_res_370_; 
v_sync_boxed_369_ = lean_unbox(v_sync_367_);
v_res_370_ = l_Std_Async_ETask_mapEIO(v_00_u03b1_361_, v_00_u03b5_362_, v_00_u03b2_363_, v_f_364_, v_x_365_, v_prio_366_, v_sync_boxed_369_);
return v_res_370_;
}
}
lean_object* l_Std_Async_ETask_block___redArg(lean_object* v_x_371_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = lean_task_get_own(v_x_371_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
lean_ctor_set_tag(v___x_376_, 1);
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
v_a_382_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_373_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_373_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
lean_ctor_set_tag(v___x_384_, 0);
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ETask_block___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_371_ = stack[0].m_obj;
lean_object* v_res_390_;
v_res_390_ = l_Std_Async_ETask_block___redArg(v_x_371_);
stack->m_obj
 = v_res_390_;
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_block___redArg___boxed(lean_object* v_x_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Std_Async_ETask_block___redArg(v_x_391_);
return v_res_393_;
}
}
lean_object* l_Std_Async_ETask_block(lean_object* v_00_u03b5_394_, lean_object* v_00_u03b1_395_, lean_object* v_x_396_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = lean_task_get_own(v_x_396_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_398_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_398_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
lean_ctor_set_tag(v___x_401_, 1);
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
v_a_407_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_398_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_398_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
lean_ctor_set_tag(v___x_409_, 0);
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
return v___x_412_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_ETask_block_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_396_ = stack[2].m_obj;
lean_object* v_res_415_;
v_res_415_ = l_Std_Async_ETask_block(lean_box(0), lean_box(0), v_x_396_);
stack->m_obj
 = v_res_415_;
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_block___boxed(lean_object* v_00_u03b5_416_, lean_object* v_00_u03b1_417_, lean_object* v_x_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Std_Async_ETask_block(v_00_u03b5_416_, v_00_u03b1_417_, v_x_418_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_ofPromise_x21___redArg(lean_object* v_x_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_IO_Promise_result_x21___redArg(v_x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_ofPromise_x21___redArg___boxed(lean_object* v_x_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Std_Async_ETask_ofPromise_x21___redArg(v_x_423_);
lean_dec(v_x_423_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_ofPromise_x21(lean_object* v_00_u03b5_425_, lean_object* v_00_u03b1_426_, lean_object* v_x_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_IO_Promise_result_x21___redArg(v_x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_ofPromise_x21___boxed(lean_object* v_00_u03b5_429_, lean_object* v_00_u03b1_430_, lean_object* v_x_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Std_Async_ETask_ofPromise_x21(v_00_u03b5_429_, v_00_u03b1_430_, v_x_431_);
lean_dec(v_x_431_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_ofPurePromise___redArg(lean_object* v_x_434_){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; lean_object* v___x_439_; 
v___x_435_ = ((lean_object*)(l_Std_Async_ETask_ofPurePromise___redArg___closed__0));
v___x_436_ = l_IO_Promise_result_x21___redArg(v_x_434_);
v___x_437_ = lean_unsigned_to_nat(0u);
v___x_438_ = 1;
v___x_439_ = lean_task_map(v___x_435_, v___x_436_, v___x_437_, v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_ofPurePromise___redArg___boxed(lean_object* v_x_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Std_Async_ETask_ofPurePromise___redArg(v_x_440_);
lean_dec(v_x_440_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_ofPurePromise(lean_object* v_00_u03b1_442_, lean_object* v_00_u03b5_443_, lean_object* v_x_444_){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; lean_object* v___x_449_; 
v___x_445_ = ((lean_object*)(l_Std_Async_ETask_ofPurePromise___redArg___closed__0));
v___x_446_ = l_IO_Promise_result_x21___redArg(v_x_444_);
v___x_447_ = lean_unsigned_to_nat(0u);
v___x_448_ = 1;
v___x_449_ = lean_task_map(v___x_445_, v___x_446_, v___x_447_, v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_ofPurePromise___boxed(lean_object* v_00_u03b1_450_, lean_object* v_00_u03b5_451_, lean_object* v_x_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Std_Async_ETask_ofPurePromise(v_00_u03b1_450_, v_00_u03b5_451_, v_x_452_);
lean_dec(v_x_452_);
return v_res_453_;
}
}
uint8_t l_Std_Async_ETask_getState___redArg(lean_object* v_x_454_){
_start:
{
uint8_t v___x_456_; 
v___x_456_ = lean_io_get_task_state(v_x_454_);
return v___x_456_;
}
}
LEAN_EXPORT void l_Std_Async_ETask_getState___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_454_ = stack[0].m_obj;
uint8_t v_res_457_;
v_res_457_ = l_Std_Async_ETask_getState___redArg(v_x_454_);
stack->m_num = v_res_457_;
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_getState___redArg___boxed(lean_object* v_x_458_, lean_object* v_a_459_){
_start:
{
uint8_t v_res_460_; lean_object* v_r_461_; 
v_res_460_ = l_Std_Async_ETask_getState___redArg(v_x_458_);
lean_dec_ref(v_x_458_);
v_r_461_ = lean_box(v_res_460_);
return v_r_461_;
}
}
uint8_t l_Std_Async_ETask_getState(lean_object* v_00_u03b5_462_, lean_object* v_00_u03b1_463_, lean_object* v_x_464_){
_start:
{
uint8_t v___x_466_; 
v___x_466_ = lean_io_get_task_state(v_x_464_);
return v___x_466_;
}
}
LEAN_EXPORT void l_Std_Async_ETask_getState_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_464_ = stack[2].m_obj;
uint8_t v_res_467_;
v_res_467_ = l_Std_Async_ETask_getState(lean_box(0), lean_box(0), v_x_464_);
stack->m_num = v_res_467_;
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_getState___boxed(lean_object* v_00_u03b5_468_, lean_object* v_00_u03b1_469_, lean_object* v_x_470_, lean_object* v_a_471_){
_start:
{
uint8_t v_res_472_; lean_object* v_r_473_; 
v_res_472_ = l_Std_Async_ETask_getState(v_00_u03b5_468_, v_00_u03b1_469_, v_x_470_);
lean_dec_ref(v_x_470_);
v_r_473_ = lean_box(v_res_472_);
return v_r_473_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instFunctor___redArg___lam__1(lean_object* v_00_u03b1_474_, lean_object* v_00_u03b2_475_, lean_object* v_f_476_, lean_object* v_x_477_){
_start:
{
lean_object* v___f_478_; lean_object* v___x_479_; uint8_t v___x_480_; lean_object* v___x_481_; 
v___f_478_ = lean_alloc_closure((void*)(l_Std_Async_ETask_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_478_, 0, v_f_476_);
v___x_479_ = lean_unsigned_to_nat(0u);
v___x_480_ = 0;
v___x_481_ = lean_task_map(v___f_478_, v_x_477_, v___x_479_, v___x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instFunctor___redArg___lam__0(lean_object* v___f_482_, lean_object* v_00_u03b1_483_, lean_object* v_00_u03b2_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_487_, 0, lean_box(0));
lean_closure_set(v___x_487_, 1, lean_box(0));
lean_closure_set(v___x_487_, 2, v___y_485_);
v___x_488_ = lean_apply_4(v___f_482_, lean_box(0), lean_box(0), v___x_487_, v___y_486_);
return v___x_488_;
}
}
lean_object* l_Std_Async_ETask_instFunctor___redArg(){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = ((lean_object*)(l_Std_Async_ETask_instFunctor___redArg___closed__2));
return v___x_496_;
}
}
LEAN_EXPORT void l_Std_Async_ETask_instFunctor___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_497_;
v_res_497_ = l_Std_Async_ETask_instFunctor___redArg();
stack->m_obj
 = v_res_497_;
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instFunctor___redArg___boxed(lean_object* v___dummy_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Std_Async_ETask_instFunctor___redArg();
return v_res_499_;
}
}
static lean_object* _init_l_Std_Async_ETask_instFunctor___closed__0(void){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Std_Async_ETask_instFunctor___redArg();
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instFunctor(lean_object* v_00_u03b5_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = lean_obj_once(&l_Std_Async_ETask_instFunctor___closed__0, &l_Std_Async_ETask_instFunctor___closed__0_once, _init_l_Std_Async_ETask_instFunctor___closed__0);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__0(lean_object* v_00_u03b1_503_, lean_object* v___y_504_){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_505_, 0, v___y_504_);
v___x_506_ = lean_task_pure(v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__1(lean_object* v_a_507_, lean_object* v_x_508_){
_start:
{
if (lean_obj_tag(v_x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_dec(v_a_507_);
v_a_509_ = lean_ctor_get(v_x_508_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v_x_508_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v_x_508_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v_x_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_525_; 
v_a_517_ = lean_ctor_get(v_x_508_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v_x_508_);
if (v_isSharedCheck_525_ == 0)
{
v___x_519_ = v_x_508_;
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v_x_508_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_521_ = lean_apply_1(v_a_507_, v_a_517_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v___x_521_);
v___x_523_ = v___x_519_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__2(lean_object* v_x_526_, lean_object* v_x_527_){
_start:
{
if (lean_obj_tag(v_x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_536_; 
lean_dec_ref(v_x_526_);
v_a_528_ = lean_ctor_get(v_x_527_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v_x_527_);
if (v_isSharedCheck_536_ == 0)
{
v___x_530_ = v_x_527_;
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v_x_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_535_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_534_; 
v___x_534_ = lean_task_pure(v___x_533_);
return v___x_534_;
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___f_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; lean_object* v___x_543_; 
v_a_537_ = lean_ctor_get(v_x_527_, 0);
lean_inc(v_a_537_);
lean_dec_ref_known(v_x_527_, 1);
v___f_538_ = lean_alloc_closure((void*)(l_Std_Async_ETask_instMonad___redArg___lam__1), 2, 1);
lean_closure_set(v___f_538_, 0, v_a_537_);
v___x_539_ = lean_box(0);
v___x_540_ = lean_apply_1(v_x_526_, v___x_539_);
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_542_ = 0;
v___x_543_ = lean_task_map(v___f_538_, v___x_540_, v___x_541_, v___x_542_);
return v___x_543_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__3(lean_object* v_00_u03b1_544_, lean_object* v_00_u03b2_545_, lean_object* v_f_546_, lean_object* v_x_547_){
_start:
{
lean_object* v___f_548_; lean_object* v___x_549_; uint8_t v___x_550_; lean_object* v___x_551_; 
v___f_548_ = lean_alloc_closure((void*)(l_Std_Async_ETask_instMonad___redArg___lam__2), 2, 1);
lean_closure_set(v___f_548_, 0, v_x_547_);
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = 0;
v___x_551_ = lean_task_bind(v_f_546_, v___f_548_, v___x_549_, v___x_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__5(lean_object* v_00_u03b1_552_, lean_object* v_00_u03b2_553_, lean_object* v_x_554_, lean_object* v_f_555_){
_start:
{
lean_object* v___f_556_; lean_object* v___x_557_; uint8_t v___x_558_; lean_object* v___x_559_; 
v___f_556_ = lean_alloc_closure((void*)(l_Std_Async_ETask_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_556_, 0, v_f_555_);
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = 0;
v___x_559_ = lean_task_bind(v_x_554_, v___f_556_, v___x_557_, v___x_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__4(lean_object* v___f_560_, lean_object* v_a_561_, lean_object* v_x_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = lean_apply_2(v___f_560_, lean_box(0), v_a_561_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__4___boxed(lean_object* v___f_564_, lean_object* v_a_565_, lean_object* v_x_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Std_Async_ETask_instMonad___redArg___lam__4(v___f_564_, v_a_565_, v_x_566_);
lean_dec(v_x_566_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__6(lean_object* v___f_568_, lean_object* v_y_569_, lean_object* v___f_570_, lean_object* v_a_571_){
_start:
{
lean_object* v___f_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___f_572_ = lean_alloc_closure((void*)(l_Std_Async_ETask_instMonad___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_572_, 0, v___f_568_);
lean_closure_set(v___f_572_, 1, v_a_571_);
v___x_573_ = lean_box(0);
v___x_574_ = lean_apply_1(v_y_569_, v___x_573_);
v___x_575_ = lean_apply_4(v___f_570_, lean_box(0), lean_box(0), v___x_574_, v___f_572_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__7(lean_object* v___f_576_, lean_object* v___f_577_, lean_object* v_00_u03b1_578_, lean_object* v_00_u03b2_579_, lean_object* v_x_580_, lean_object* v_y_581_){
_start:
{
lean_object* v___f_582_; lean_object* v___x_583_; 
lean_inc_ref(v___f_577_);
v___f_582_ = lean_alloc_closure((void*)(l_Std_Async_ETask_instMonad___redArg___lam__6), 4, 3);
lean_closure_set(v___f_582_, 0, v___f_576_);
lean_closure_set(v___f_582_, 1, v_y_581_);
lean_closure_set(v___f_582_, 2, v___f_577_);
v___x_583_ = lean_apply_4(v___f_577_, lean_box(0), lean_box(0), v_x_580_, v___f_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__8(lean_object* v_y_584_, lean_object* v_x_585_){
_start:
{
if (lean_obj_tag(v_x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_594_; 
lean_dec_ref(v_y_584_);
v_a_586_ = lean_ctor_get(v_x_585_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v_x_585_);
if (v_isSharedCheck_594_ == 0)
{
v___x_588_ = v_x_585_;
v_isShared_589_ = v_isSharedCheck_594_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v_x_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_594_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_593_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_592_; 
v___x_592_ = lean_task_pure(v___x_591_);
return v___x_592_;
}
}
}
else
{
lean_object* v___x_595_; lean_object* v___x_596_; 
lean_dec_ref_known(v_x_585_, 1);
v___x_595_ = lean_box(0);
v___x_596_ = lean_apply_1(v_y_584_, v___x_595_);
return v___x_596_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___lam__9(lean_object* v_00_u03b1_597_, lean_object* v_00_u03b2_598_, lean_object* v_x_599_, lean_object* v_y_600_){
_start:
{
lean_object* v___f_601_; lean_object* v___x_602_; uint8_t v___x_603_; lean_object* v___x_604_; 
v___f_601_ = lean_alloc_closure((void*)(l_Std_Async_ETask_instMonad___redArg___lam__8), 2, 1);
lean_closure_set(v___f_601_, 0, v_y_600_);
v___x_602_ = lean_unsigned_to_nat(0u);
v___x_603_ = 0;
v___x_604_ = lean_task_bind(v_x_599_, v___f_601_, v___x_602_, v___x_603_);
return v___x_604_;
}
}
static lean_object* _init_l_Std_Async_ETask_instMonad___redArg___closed__5(void){
_start:
{
lean_object* v___f_612_; lean_object* v___f_613_; lean_object* v___f_614_; lean_object* v___f_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___f_612_ = ((lean_object*)(l_Std_Async_ETask_instMonad___redArg___closed__4));
v___f_613_ = ((lean_object*)(l_Std_Async_ETask_instMonad___redArg___closed__3));
v___f_614_ = ((lean_object*)(l_Std_Async_ETask_instMonad___redArg___closed__1));
v___f_615_ = ((lean_object*)(l_Std_Async_ETask_instMonad___redArg___closed__0));
v___x_616_ = lean_obj_once(&l_Std_Async_ETask_instFunctor___closed__0, &l_Std_Async_ETask_instFunctor___closed__0_once, _init_l_Std_Async_ETask_instFunctor___closed__0);
v___x_617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v___f_615_);
lean_ctor_set(v___x_617_, 2, v___f_614_);
lean_ctor_set(v___x_617_, 3, v___f_613_);
lean_ctor_set(v___x_617_, 4, v___f_612_);
return v___x_617_;
}
}
static lean_object* _init_l_Std_Async_ETask_instMonad___redArg___closed__6(void){
_start:
{
lean_object* v___f_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___f_618_ = ((lean_object*)(l_Std_Async_ETask_instMonad___redArg___closed__2));
v___x_619_ = lean_obj_once(&l_Std_Async_ETask_instMonad___redArg___closed__5, &l_Std_Async_ETask_instMonad___redArg___closed__5_once, _init_l_Std_Async_ETask_instMonad___redArg___closed__5);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v___f_618_);
return v___x_620_;
}
}
lean_object* l_Std_Async_ETask_instMonad___redArg(){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = lean_obj_once(&l_Std_Async_ETask_instMonad___redArg___closed__6, &l_Std_Async_ETask_instMonad___redArg___closed__6_once, _init_l_Std_Async_ETask_instMonad___redArg___closed__6);
return v___x_622_;
}
}
LEAN_EXPORT void l_Std_Async_ETask_instMonad___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_623_;
v_res_623_ = l_Std_Async_ETask_instMonad___redArg();
stack->m_obj
 = v_res_623_;
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad___redArg___boxed(lean_object* v___dummy_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Std_Async_ETask_instMonad___redArg();
return v_res_625_;
}
}
static lean_object* _init_l_Std_Async_ETask_instMonad___closed__0(void){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Std_Async_ETask_instMonad___redArg();
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_ETask_instMonad(lean_object* v_00_u03b5_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = lean_obj_once(&l_Std_Async_ETask_instMonad___closed__0, &l_Std_Async_ETask_instMonad___closed__0_once, _init_l_Std_Async_ETask_instMonad___closed__0);
return v___x_628_;
}
}
lean_object* l_Std_Async_AsyncTask_mapIO___redArg___lam__0(lean_object* v_f_629_, lean_object* v_a_630_){
_start:
{
lean_object* v_a_633_; 
if (lean_obj_tag(v_a_630_) == 0)
{
lean_object* v_a_635_; 
lean_dec_ref(v_f_629_);
v_a_635_ = lean_ctor_get(v_a_630_, 0);
lean_inc(v_a_635_);
lean_dec_ref_known(v_a_630_, 1);
v_a_633_ = v_a_635_;
goto v___jp_632_;
}
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_646_; 
v_a_636_ = lean_ctor_get(v_a_630_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v_a_630_);
if (v_isSharedCheck_646_ == 0)
{
v___x_638_ = v_a_630_;
v_isShared_639_ = v_isSharedCheck_646_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v_a_630_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_646_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; 
v___x_640_ = lean_apply_2(v_f_629_, v_a_636_, lean_box(0));
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v___x_643_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_a_641_);
lean_dec_ref_known(v___x_640_, 1);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v_a_641_);
v___x_643_ = v___x_638_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
else
{
lean_object* v_a_645_; 
lean_del_object(v___x_638_);
v_a_645_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_a_645_);
lean_dec_ref_known(v___x_640_, 1);
v_a_633_ = v_a_645_;
goto v___jp_632_;
}
}
}
v___jp_632_:
{
lean_object* v___x_634_; 
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v_a_633_);
return v___x_634_;
}
}
}
LEAN_EXPORT void l_Std_Async_AsyncTask_mapIO___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_629_ = stack[0].m_obj;
lean_object* v_a_630_ = stack[1].m_obj;
lean_object* v_res_647_;
v_res_647_ = l_Std_Async_AsyncTask_mapIO___redArg___lam__0(v_f_629_, v_a_630_);
stack->m_obj
 = v_res_647_;
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapIO___redArg___lam__0___boxed(lean_object* v_f_648_, lean_object* v_a_649_, lean_object* v___y_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Std_Async_AsyncTask_mapIO___redArg___lam__0(v_f_648_, v_a_649_);
return v_res_651_;
}
}
lean_object* l_Std_Async_AsyncTask_mapIO___redArg(lean_object* v_f_652_, lean_object* v_x_653_, lean_object* v_prio_654_, uint8_t v_sync_655_){
_start:
{
lean_object* v___f_657_; lean_object* v___x_658_; 
v___f_657_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_mapIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_657_, 0, v_f_652_);
v___x_658_ = lean_io_map_task(v___f_657_, v_x_653_, v_prio_654_, v_sync_655_);
return v___x_658_;
}
}
LEAN_EXPORT void l_Std_Async_AsyncTask_mapIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_652_ = stack[0].m_obj;
lean_object* v_x_653_ = stack[1].m_obj;
lean_object* v_prio_654_ = stack[2].m_obj;
uint8_t v_sync_655_ = stack[3].m_num;
lean_object* v_res_659_;
v_res_659_ = l_Std_Async_AsyncTask_mapIO___redArg(v_f_652_, v_x_653_, v_prio_654_, v_sync_655_);
stack->m_obj
 = v_res_659_;
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapIO___redArg___boxed(lean_object* v_f_660_, lean_object* v_x_661_, lean_object* v_prio_662_, lean_object* v_sync_663_, lean_object* v_a_664_){
_start:
{
uint8_t v_sync_boxed_665_; lean_object* v_res_666_; 
v_sync_boxed_665_ = lean_unbox(v_sync_663_);
v_res_666_ = l_Std_Async_AsyncTask_mapIO___redArg(v_f_660_, v_x_661_, v_prio_662_, v_sync_boxed_665_);
return v_res_666_;
}
}
lean_object* l_Std_Async_AsyncTask_mapIO(lean_object* v_00_u03b1_667_, lean_object* v_00_u03b2_668_, lean_object* v_f_669_, lean_object* v_x_670_, lean_object* v_prio_671_, uint8_t v_sync_672_){
_start:
{
lean_object* v___f_674_; lean_object* v___x_675_; 
v___f_674_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_mapIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_674_, 0, v_f_669_);
v___x_675_ = lean_io_map_task(v___f_674_, v_x_670_, v_prio_671_, v_sync_672_);
return v___x_675_;
}
}
LEAN_EXPORT void l_Std_Async_AsyncTask_mapIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_669_ = stack[2].m_obj;
lean_object* v_x_670_ = stack[3].m_obj;
lean_object* v_prio_671_ = stack[4].m_obj;
uint8_t v_sync_672_ = stack[5].m_num;
lean_object* v_res_676_;
v_res_676_ = l_Std_Async_AsyncTask_mapIO(lean_box(0), lean_box(0), v_f_669_, v_x_670_, v_prio_671_, v_sync_672_);
stack->m_obj
 = v_res_676_;
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapIO___boxed(lean_object* v_00_u03b1_677_, lean_object* v_00_u03b2_678_, lean_object* v_f_679_, lean_object* v_x_680_, lean_object* v_prio_681_, lean_object* v_sync_682_, lean_object* v_a_683_){
_start:
{
uint8_t v_sync_boxed_684_; lean_object* v_res_685_; 
v_sync_boxed_684_ = lean_unbox(v_sync_682_);
v_res_685_ = l_Std_Async_AsyncTask_mapIO(v_00_u03b1_677_, v_00_u03b2_678_, v_f_679_, v_x_680_, v_prio_681_, v_sync_boxed_684_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_pure___redArg(lean_object* v_x_686_){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_687_, 0, v_x_686_);
v___x_688_ = lean_task_pure(v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_pure(lean_object* v_00_u03b1_689_, lean_object* v_x_690_){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_691_, 0, v_x_690_);
v___x_692_ = lean_task_pure(v___x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bind___redArg___lam__0(lean_object* v_f_693_, lean_object* v_x_694_){
_start:
{
if (lean_obj_tag(v_x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_703_; 
lean_dec_ref(v_f_693_);
v_a_695_ = lean_ctor_get(v_x_694_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v_x_694_);
if (v_isSharedCheck_703_ == 0)
{
v___x_697_ = v_x_694_;
v_isShared_698_ = v_isSharedCheck_703_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v_x_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_703_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_702_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_701_; 
v___x_701_ = lean_task_pure(v___x_700_);
return v___x_701_;
}
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_705_; 
v_a_704_ = lean_ctor_get(v_x_694_, 0);
lean_inc(v_a_704_);
lean_dec_ref_known(v_x_694_, 1);
v___x_705_ = lean_apply_1(v_f_693_, v_a_704_);
return v___x_705_;
}
}
}
lean_object* l_Std_Async_AsyncTask_bind___redArg(lean_object* v_x_706_, lean_object* v_f_707_, lean_object* v_prio_708_, uint8_t v_sync_709_){
_start:
{
lean_object* v___f_710_; lean_object* v___x_711_; 
v___f_710_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_710_, 0, v_f_707_);
v___x_711_ = lean_task_bind(v_x_706_, v___f_710_, v_prio_708_, v_sync_709_);
return v___x_711_;
}
}
LEAN_EXPORT void l_Std_Async_AsyncTask_bind___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_706_ = stack[0].m_obj;
lean_object* v_f_707_ = stack[1].m_obj;
lean_object* v_prio_708_ = stack[2].m_obj;
uint8_t v_sync_709_ = stack[3].m_num;
lean_object* v_res_712_;
v_res_712_ = l_Std_Async_AsyncTask_bind___redArg(v_x_706_, v_f_707_, v_prio_708_, v_sync_709_);
stack->m_obj
 = v_res_712_;
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bind___redArg___boxed(lean_object* v_x_713_, lean_object* v_f_714_, lean_object* v_prio_715_, lean_object* v_sync_716_){
_start:
{
uint8_t v_sync_boxed_717_; lean_object* v_res_718_; 
v_sync_boxed_717_ = lean_unbox(v_sync_716_);
v_res_718_ = l_Std_Async_AsyncTask_bind___redArg(v_x_713_, v_f_714_, v_prio_715_, v_sync_boxed_717_);
return v_res_718_;
}
}
lean_object* l_Std_Async_AsyncTask_bind(lean_object* v_00_u03b1_719_, lean_object* v_00_u03b2_720_, lean_object* v_x_721_, lean_object* v_f_722_, lean_object* v_prio_723_, uint8_t v_sync_724_){
_start:
{
lean_object* v___f_725_; lean_object* v___x_726_; 
v___f_725_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_725_, 0, v_f_722_);
v___x_726_ = lean_task_bind(v_x_721_, v___f_725_, v_prio_723_, v_sync_724_);
return v___x_726_;
}
}
LEAN_EXPORT void l_Std_Async_AsyncTask_bind_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_721_ = stack[2].m_obj;
lean_object* v_f_722_ = stack[3].m_obj;
lean_object* v_prio_723_ = stack[4].m_obj;
uint8_t v_sync_724_ = stack[5].m_num;
lean_object* v_res_727_;
v_res_727_ = l_Std_Async_AsyncTask_bind(lean_box(0), lean_box(0), v_x_721_, v_f_722_, v_prio_723_, v_sync_724_);
stack->m_obj
 = v_res_727_;
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bind___boxed(lean_object* v_00_u03b1_728_, lean_object* v_00_u03b2_729_, lean_object* v_x_730_, lean_object* v_f_731_, lean_object* v_prio_732_, lean_object* v_sync_733_){
_start:
{
uint8_t v_sync_boxed_734_; lean_object* v_res_735_; 
v_sync_boxed_734_ = lean_unbox(v_sync_733_);
v_res_735_ = l_Std_Async_AsyncTask_bind(v_00_u03b1_728_, v_00_u03b2_729_, v_x_730_, v_f_731_, v_prio_732_, v_sync_boxed_734_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_map___redArg___lam__0(lean_object* v_f_736_, lean_object* v_x_737_){
_start:
{
if (lean_obj_tag(v_x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec(v_f_736_);
v_a_738_ = lean_ctor_get(v_x_737_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v_x_737_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v_x_737_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v_x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_754_; 
v_a_746_ = lean_ctor_get(v_x_737_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v_x_737_);
if (v_isSharedCheck_754_ == 0)
{
v___x_748_ = v_x_737_;
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v_x_737_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_750_ = lean_apply_1(v_f_736_, v_a_746_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v___x_750_);
v___x_752_ = v___x_748_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
lean_object* l_Std_Async_AsyncTask_map___redArg(lean_object* v_f_755_, lean_object* v_x_756_, lean_object* v_prio_757_, uint8_t v_sync_758_){
_start:
{
lean_object* v___f_759_; lean_object* v___x_760_; 
v___f_759_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_759_, 0, v_f_755_);
v___x_760_ = lean_task_map(v___f_759_, v_x_756_, v_prio_757_, v_sync_758_);
return v___x_760_;
}
}
LEAN_EXPORT void l_Std_Async_AsyncTask_map___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_755_ = stack[0].m_obj;
lean_object* v_x_756_ = stack[1].m_obj;
lean_object* v_prio_757_ = stack[2].m_obj;
uint8_t v_sync_758_ = stack[3].m_num;
lean_object* v_res_761_;
v_res_761_ = l_Std_Async_AsyncTask_map___redArg(v_f_755_, v_x_756_, v_prio_757_, v_sync_758_);
stack->m_obj
 = v_res_761_;
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_map___redArg___boxed(lean_object* v_f_762_, lean_object* v_x_763_, lean_object* v_prio_764_, lean_object* v_sync_765_){
_start:
{
uint8_t v_sync_boxed_766_; lean_object* v_res_767_; 
v_sync_boxed_766_ = lean_unbox(v_sync_765_);
v_res_767_ = l_Std_Async_AsyncTask_map___redArg(v_f_762_, v_x_763_, v_prio_764_, v_sync_boxed_766_);
return v_res_767_;
}
}
lean_object* l_Std_Async_AsyncTask_map(lean_object* v_00_u03b1_768_, lean_object* v_00_u03b2_769_, lean_object* v_f_770_, lean_object* v_x_771_, lean_object* v_prio_772_, uint8_t v_sync_773_){
_start:
{
lean_object* v___f_774_; lean_object* v___x_775_; 
v___f_774_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_774_, 0, v_f_770_);
v___x_775_ = lean_task_map(v___f_774_, v_x_771_, v_prio_772_, v_sync_773_);
return v___x_775_;
}
}
LEAN_EXPORT void l_Std_Async_AsyncTask_map_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_770_ = stack[2].m_obj;
lean_object* v_x_771_ = stack[3].m_obj;
lean_object* v_prio_772_ = stack[4].m_obj;
uint8_t v_sync_773_ = stack[5].m_num;
lean_object* v_res_776_;
v_res_776_ = l_Std_Async_AsyncTask_map(lean_box(0), lean_box(0), v_f_770_, v_x_771_, v_prio_772_, v_sync_773_);
stack->m_obj
 = v_res_776_;
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_map___boxed(lean_object* v_00_u03b1_777_, lean_object* v_00_u03b2_778_, lean_object* v_f_779_, lean_object* v_x_780_, lean_object* v_prio_781_, lean_object* v_sync_782_){
_start:
{
uint8_t v_sync_boxed_783_; lean_object* v_res_784_; 
v_sync_boxed_783_ = lean_unbox(v_sync_782_);
v_res_784_ = l_Std_Async_AsyncTask_map(v_00_u03b1_777_, v_00_u03b2_778_, v_f_779_, v_x_780_, v_prio_781_, v_sync_boxed_783_);
return v_res_784_;
}
}
lean_object* l_Std_Async_AsyncTask_bindIO___redArg___lam__0(lean_object* v_f_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_a_789_; 
if (lean_obj_tag(v_a_786_) == 0)
{
lean_object* v_a_792_; 
lean_dec_ref(v_f_785_);
v_a_792_ = lean_ctor_get(v_a_786_, 0);
lean_inc(v_a_792_);
lean_dec_ref_known(v_a_786_, 1);
v_a_789_ = v_a_792_;
goto v___jp_788_;
}
else
{
lean_object* v_a_793_; lean_object* v___x_794_; 
v_a_793_ = lean_ctor_get(v_a_786_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v_a_786_, 1);
v___x_794_ = lean_apply_2(v_f_785_, v_a_793_, lean_box(0));
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_795_);
lean_dec_ref_known(v___x_794_, 1);
return v_a_795_;
}
else
{
lean_object* v_a_796_; 
v_a_796_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_796_);
lean_dec_ref_known(v___x_794_, 1);
v_a_789_ = v_a_796_;
goto v___jp_788_;
}
}
v___jp_788_:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v_a_789_);
v___x_791_ = lean_task_pure(v___x_790_);
return v___x_791_;
}
}
}
LEAN_EXPORT void l_Std_Async_AsyncTask_bindIO___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_785_ = stack[0].m_obj;
lean_object* v_a_786_ = stack[1].m_obj;
lean_object* v_res_797_;
v_res_797_ = l_Std_Async_AsyncTask_bindIO___redArg___lam__0(v_f_785_, v_a_786_);
stack->m_obj
 = v_res_797_;
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bindIO___redArg___lam__0___boxed(lean_object* v_f_798_, lean_object* v_a_799_, lean_object* v___y_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Std_Async_AsyncTask_bindIO___redArg___lam__0(v_f_798_, v_a_799_);
return v_res_801_;
}
}
lean_object* l_Std_Async_AsyncTask_bindIO___redArg(lean_object* v_x_802_, lean_object* v_f_803_, lean_object* v_prio_804_, uint8_t v_sync_805_){
_start:
{
lean_object* v___f_807_; lean_object* v___x_808_; 
v___f_807_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_bindIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_807_, 0, v_f_803_);
v___x_808_ = lean_io_bind_task(v_x_802_, v___f_807_, v_prio_804_, v_sync_805_);
return v___x_808_;
}
}
LEAN_EXPORT void l_Std_Async_AsyncTask_bindIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_802_ = stack[0].m_obj;
lean_object* v_f_803_ = stack[1].m_obj;
lean_object* v_prio_804_ = stack[2].m_obj;
uint8_t v_sync_805_ = stack[3].m_num;
lean_object* v_res_809_;
v_res_809_ = l_Std_Async_AsyncTask_bindIO___redArg(v_x_802_, v_f_803_, v_prio_804_, v_sync_805_);
stack->m_obj
 = v_res_809_;
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bindIO___redArg___boxed(lean_object* v_x_810_, lean_object* v_f_811_, lean_object* v_prio_812_, lean_object* v_sync_813_, lean_object* v_a_814_){
_start:
{
uint8_t v_sync_boxed_815_; lean_object* v_res_816_; 
v_sync_boxed_815_ = lean_unbox(v_sync_813_);
v_res_816_ = l_Std_Async_AsyncTask_bindIO___redArg(v_x_810_, v_f_811_, v_prio_812_, v_sync_boxed_815_);
return v_res_816_;
}
}
lean_object* l_Std_Async_AsyncTask_bindIO(lean_object* v_00_u03b1_817_, lean_object* v_00_u03b2_818_, lean_object* v_x_819_, lean_object* v_f_820_, lean_object* v_prio_821_, uint8_t v_sync_822_){
_start:
{
lean_object* v___f_824_; lean_object* v___x_825_; 
v___f_824_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_bindIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_824_, 0, v_f_820_);
v___x_825_ = lean_io_bind_task(v_x_819_, v___f_824_, v_prio_821_, v_sync_822_);
return v___x_825_;
}
}
LEAN_EXPORT void l_Std_Async_AsyncTask_bindIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_819_ = stack[2].m_obj;
lean_object* v_f_820_ = stack[3].m_obj;
lean_object* v_prio_821_ = stack[4].m_obj;
uint8_t v_sync_822_ = stack[5].m_num;
lean_object* v_res_826_;
v_res_826_ = l_Std_Async_AsyncTask_bindIO(lean_box(0), lean_box(0), v_x_819_, v_f_820_, v_prio_821_, v_sync_822_);
stack->m_obj
 = v_res_826_;
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_bindIO___boxed(lean_object* v_00_u03b1_827_, lean_object* v_00_u03b2_828_, lean_object* v_x_829_, lean_object* v_f_830_, lean_object* v_prio_831_, lean_object* v_sync_832_, lean_object* v_a_833_){
_start:
{
uint8_t v_sync_boxed_834_; lean_object* v_res_835_; 
v_sync_boxed_834_ = lean_unbox(v_sync_832_);
v_res_835_ = l_Std_Async_AsyncTask_bindIO(v_00_u03b1_827_, v_00_u03b2_828_, v_x_829_, v_f_830_, v_prio_831_, v_sync_boxed_834_);
return v_res_835_;
}
}
lean_object* l_Std_Async_AsyncTask_mapTaskIO___redArg(lean_object* v_f_836_, lean_object* v_x_837_, lean_object* v_prio_838_, uint8_t v_sync_839_){
_start:
{
lean_object* v___f_841_; lean_object* v___x_842_; 
v___f_841_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_mapIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_841_, 0, v_f_836_);
v___x_842_ = lean_io_map_task(v___f_841_, v_x_837_, v_prio_838_, v_sync_839_);
return v___x_842_;
}
}
LEAN_EXPORT void l_Std_Async_AsyncTask_mapTaskIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_836_ = stack[0].m_obj;
lean_object* v_x_837_ = stack[1].m_obj;
lean_object* v_prio_838_ = stack[2].m_obj;
uint8_t v_sync_839_ = stack[3].m_num;
lean_object* v_res_843_;
v_res_843_ = l_Std_Async_AsyncTask_mapTaskIO___redArg(v_f_836_, v_x_837_, v_prio_838_, v_sync_839_);
stack->m_obj
 = v_res_843_;
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapTaskIO___redArg___boxed(lean_object* v_f_844_, lean_object* v_x_845_, lean_object* v_prio_846_, lean_object* v_sync_847_, lean_object* v_a_848_){
_start:
{
uint8_t v_sync_boxed_849_; lean_object* v_res_850_; 
v_sync_boxed_849_ = lean_unbox(v_sync_847_);
v_res_850_ = l_Std_Async_AsyncTask_mapTaskIO___redArg(v_f_844_, v_x_845_, v_prio_846_, v_sync_boxed_849_);
return v_res_850_;
}
}
lean_object* l_Std_Async_AsyncTask_mapTaskIO(lean_object* v_00_u03b1_851_, lean_object* v_00_u03b2_852_, lean_object* v_f_853_, lean_object* v_x_854_, lean_object* v_prio_855_, uint8_t v_sync_856_){
_start:
{
lean_object* v___f_858_; lean_object* v___x_859_; 
v___f_858_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_mapIO___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_858_, 0, v_f_853_);
v___x_859_ = lean_io_map_task(v___f_858_, v_x_854_, v_prio_855_, v_sync_856_);
return v___x_859_;
}
}
LEAN_EXPORT void l_Std_Async_AsyncTask_mapTaskIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_853_ = stack[2].m_obj;
lean_object* v_x_854_ = stack[3].m_obj;
lean_object* v_prio_855_ = stack[4].m_obj;
uint8_t v_sync_856_ = stack[5].m_num;
lean_object* v_res_860_;
v_res_860_ = l_Std_Async_AsyncTask_mapTaskIO(lean_box(0), lean_box(0), v_f_853_, v_x_854_, v_prio_855_, v_sync_856_);
stack->m_obj
 = v_res_860_;
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_mapTaskIO___boxed(lean_object* v_00_u03b1_861_, lean_object* v_00_u03b2_862_, lean_object* v_f_863_, lean_object* v_x_864_, lean_object* v_prio_865_, lean_object* v_sync_866_, lean_object* v_a_867_){
_start:
{
uint8_t v_sync_boxed_868_; lean_object* v_res_869_; 
v_sync_boxed_868_ = lean_unbox(v_sync_866_);
v_res_869_ = l_Std_Async_AsyncTask_mapTaskIO(v_00_u03b1_861_, v_00_u03b2_862_, v_f_863_, v_x_864_, v_prio_865_, v_sync_boxed_868_);
return v_res_869_;
}
}
lean_object* l_Std_Async_AsyncTask_block___redArg(lean_object* v_x_870_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = lean_task_get_own(v_x_870_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_872_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_872_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
lean_ctor_set_tag(v___x_875_, 1);
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
v_a_881_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_872_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_872_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
lean_ctor_set_tag(v___x_883_, 0);
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_AsyncTask_block___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_870_ = stack[0].m_obj;
lean_object* v_res_889_;
v_res_889_ = l_Std_Async_AsyncTask_block___redArg(v_x_870_);
stack->m_obj
 = v_res_889_;
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_block___redArg___boxed(lean_object* v_x_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Std_Async_AsyncTask_block___redArg(v_x_890_);
return v_res_892_;
}
}
lean_object* l_Std_Async_AsyncTask_block(lean_object* v_00_u03b1_893_, lean_object* v_x_894_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Std_Async_AsyncTask_block___redArg(v_x_894_);
return v___x_896_;
}
}
LEAN_EXPORT void l_Std_Async_AsyncTask_block_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_894_ = stack[1].m_obj;
lean_object* v_res_897_;
v_res_897_ = l_Std_Async_AsyncTask_block(lean_box(0), v_x_894_);
stack->m_obj
 = v_res_897_;
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_block___boxed(lean_object* v_00_u03b1_898_, lean_object* v_x_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Std_Async_AsyncTask_block(v_00_u03b1_898_, v_x_899_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPromise___redArg___lam__0(lean_object* v_error_902_, lean_object* v_x_903_){
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
lean_object* v_val_906_; 
lean_dec_ref(v_error_902_);
v_val_906_ = lean_ctor_get(v_x_903_, 0);
lean_inc(v_val_906_);
return v_val_906_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPromise___redArg___lam__0___boxed(lean_object* v_error_907_, lean_object* v_x_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Std_Async_AsyncTask_ofPromise___redArg___lam__0(v_error_907_, v_x_908_);
lean_dec(v_x_908_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPromise___redArg(lean_object* v_x_910_, lean_object* v_error_911_){
_start:
{
lean_object* v___f_912_; lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; lean_object* v___x_916_; 
v___f_912_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPromise___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_912_, 0, v_error_911_);
v___x_913_ = lean_io_promise_result_opt(v_x_910_);
v___x_914_ = lean_unsigned_to_nat(0u);
v___x_915_ = 0;
v___x_916_ = lean_task_map(v___f_912_, v___x_913_, v___x_914_, v___x_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPromise___redArg___boxed(lean_object* v_x_917_, lean_object* v_error_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Std_Async_AsyncTask_ofPromise___redArg(v_x_917_, v_error_918_);
lean_dec(v_x_917_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPromise(lean_object* v_00_u03b1_920_, lean_object* v_x_921_, lean_object* v_error_922_){
_start:
{
lean_object* v___f_923_; lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; lean_object* v___x_927_; 
v___f_923_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPromise___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_923_, 0, v_error_922_);
v___x_924_ = lean_io_promise_result_opt(v_x_921_);
v___x_925_ = lean_unsigned_to_nat(0u);
v___x_926_ = 0;
v___x_927_ = lean_task_map(v___f_923_, v___x_924_, v___x_925_, v___x_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPromise___boxed(lean_object* v_00_u03b1_928_, lean_object* v_x_929_, lean_object* v_error_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Std_Async_AsyncTask_ofPromise(v_00_u03b1_928_, v_x_929_, v_error_930_);
lean_dec(v_x_929_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPurePromise___redArg___lam__0(lean_object* v_error_932_, lean_object* v_x_933_){
_start:
{
if (lean_obj_tag(v_x_933_) == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = lean_mk_io_user_error(v_error_932_);
v___x_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
return v___x_935_;
}
else
{
lean_object* v_val_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
lean_dec_ref(v_error_932_);
v_val_936_ = lean_ctor_get(v_x_933_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v_x_933_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v_x_933_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_val_936_);
lean_dec(v_x_933_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_val_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPurePromise___redArg(lean_object* v_x_944_, lean_object* v_error_945_){
_start:
{
lean_object* v___f_946_; lean_object* v___x_947_; lean_object* v___x_948_; uint8_t v___x_949_; lean_object* v___x_950_; 
v___f_946_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPurePromise___redArg___lam__0), 2, 1);
lean_closure_set(v___f_946_, 0, v_error_945_);
v___x_947_ = lean_io_promise_result_opt(v_x_944_);
v___x_948_ = lean_unsigned_to_nat(0u);
v___x_949_ = 1;
v___x_950_ = lean_task_map(v___f_946_, v___x_947_, v___x_948_, v___x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPurePromise___redArg___boxed(lean_object* v_x_951_, lean_object* v_error_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Std_Async_AsyncTask_ofPurePromise___redArg(v_x_951_, v_error_952_);
lean_dec(v_x_951_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPurePromise(lean_object* v_00_u03b1_954_, lean_object* v_x_955_, lean_object* v_error_956_){
_start:
{
lean_object* v___f_957_; lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; lean_object* v___x_961_; 
v___f_957_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPurePromise___redArg___lam__0), 2, 1);
lean_closure_set(v___f_957_, 0, v_error_956_);
v___x_958_ = lean_io_promise_result_opt(v_x_955_);
v___x_959_ = lean_unsigned_to_nat(0u);
v___x_960_ = 1;
v___x_961_ = lean_task_map(v___f_957_, v___x_958_, v___x_959_, v___x_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_ofPurePromise___boxed(lean_object* v_00_u03b1_962_, lean_object* v_x_963_, lean_object* v_error_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Std_Async_AsyncTask_ofPurePromise(v_00_u03b1_962_, v_x_963_, v_error_964_);
lean_dec(v_x_963_);
return v_res_965_;
}
}
uint8_t l_Std_Async_AsyncTask_getState___redArg(lean_object* v_x_966_){
_start:
{
uint8_t v___x_968_; 
v___x_968_ = lean_io_get_task_state(v_x_966_);
return v___x_968_;
}
}
LEAN_EXPORT void l_Std_Async_AsyncTask_getState___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_966_ = stack[0].m_obj;
uint8_t v_res_969_;
v_res_969_ = l_Std_Async_AsyncTask_getState___redArg(v_x_966_);
stack->m_num = v_res_969_;
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_getState___redArg___boxed(lean_object* v_x_970_, lean_object* v_a_971_){
_start:
{
uint8_t v_res_972_; lean_object* v_r_973_; 
v_res_972_ = l_Std_Async_AsyncTask_getState___redArg(v_x_970_);
lean_dec_ref(v_x_970_);
v_r_973_ = lean_box(v_res_972_);
return v_r_973_;
}
}
uint8_t l_Std_Async_AsyncTask_getState(lean_object* v_00_u03b1_974_, lean_object* v_x_975_){
_start:
{
uint8_t v___x_977_; 
v___x_977_ = lean_io_get_task_state(v_x_975_);
return v___x_977_;
}
}
LEAN_EXPORT void l_Std_Async_AsyncTask_getState_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_975_ = stack[1].m_obj;
uint8_t v_res_978_;
v_res_978_ = l_Std_Async_AsyncTask_getState(lean_box(0), v_x_975_);
stack->m_num = v_res_978_;
}
LEAN_EXPORT lean_object* l_Std_Async_AsyncTask_getState___boxed(lean_object* v_00_u03b1_979_, lean_object* v_x_980_, lean_object* v_a_981_){
_start:
{
uint8_t v_res_982_; lean_object* v_r_983_; 
v_res_982_ = l_Std_Async_AsyncTask_getState(v_00_u03b1_979_, v_x_980_);
lean_dec_ref(v_x_980_);
v_r_983_ = lean_box(v_res_982_);
return v_r_983_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorIdx___impl___redArg(lean_object* v_x_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = lean_obj_tag_nat(v_x_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorIdx___impl___redArg___boxed(lean_object* v_x_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Std_Async_MaybeTask_ctorIdx___impl___redArg(v_x_986_);
lean_dec_ref(v_x_986_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorIdx___impl(lean_object* v_00_u03b1_988_, lean_object* v_x_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = lean_obj_tag_nat(v_x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorIdx___impl___boxed(lean_object* v_00_u03b1_991_, lean_object* v_x_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Std_Async_MaybeTask_ctorIdx___impl(v_00_u03b1_991_, v_x_992_);
lean_dec_ref(v_x_992_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorElim___redArg(lean_object* v_t_994_, lean_object* v_k_995_){
_start:
{
if (lean_obj_tag(v_t_994_) == 0)
{
lean_object* v_a_996_; lean_object* v___x_997_; 
v_a_996_ = lean_ctor_get(v_t_994_, 0);
lean_inc(v_a_996_);
lean_dec_ref_known(v_t_994_, 1);
v___x_997_ = lean_apply_1(v_k_995_, v_a_996_);
return v___x_997_;
}
else
{
lean_object* v_a_998_; lean_object* v___x_999_; 
v_a_998_ = lean_ctor_get(v_t_994_, 0);
lean_inc_ref(v_a_998_);
lean_dec_ref_known(v_t_994_, 1);
v___x_999_ = lean_apply_1(v_k_995_, v_a_998_);
return v___x_999_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorElim(lean_object* v_00_u03b1_1000_, lean_object* v_motive_1001_, lean_object* v_ctorIdx_1002_, lean_object* v_t_1003_, lean_object* v_h_1004_, lean_object* v_k_1005_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Std_Async_MaybeTask_ctorElim___redArg(v_t_1003_, v_k_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorElim___boxed(lean_object* v_00_u03b1_1007_, lean_object* v_motive_1008_, lean_object* v_ctorIdx_1009_, lean_object* v_t_1010_, lean_object* v_h_1011_, lean_object* v_k_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Std_Async_MaybeTask_ctorElim(v_00_u03b1_1007_, v_motive_1008_, v_ctorIdx_1009_, v_t_1010_, v_h_1011_, v_k_1012_);
lean_dec(v_ctorIdx_1009_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_pure_elim___redArg(lean_object* v_t_1014_, lean_object* v_pure_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Std_Async_MaybeTask_ctorElim___redArg(v_t_1014_, v_pure_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_pure_elim(lean_object* v_00_u03b1_1017_, lean_object* v_motive_1018_, lean_object* v_t_1019_, lean_object* v_h_1020_, lean_object* v_pure_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Std_Async_MaybeTask_ctorElim___redArg(v_t_1019_, v_pure_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ofTask_elim___redArg(lean_object* v_t_1023_, lean_object* v_ofTask_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Std_Async_MaybeTask_ctorElim___redArg(v_t_1023_, v_ofTask_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ofTask_elim(lean_object* v_00_u03b1_1026_, lean_object* v_motive_1027_, lean_object* v_t_1028_, lean_object* v_h_1029_, lean_object* v_ofTask_1030_){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Std_Async_MaybeTask_ctorElim___redArg(v_t_1028_, v_ofTask_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_toTask___redArg(lean_object* v_x_1032_){
_start:
{
if (lean_obj_tag(v_x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1034_; 
v_a_1033_ = lean_ctor_get(v_x_1032_, 0);
lean_inc(v_a_1033_);
lean_dec_ref_known(v_x_1032_, 1);
v___x_1034_ = lean_task_pure(v_a_1033_);
return v___x_1034_;
}
else
{
lean_object* v_a_1035_; 
v_a_1035_ = lean_ctor_get(v_x_1032_, 0);
lean_inc_ref(v_a_1035_);
lean_dec_ref_known(v_x_1032_, 1);
return v_a_1035_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_toTask(lean_object* v_00_u03b1_1036_, lean_object* v_x_1037_){
_start:
{
if (lean_obj_tag(v_x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1039_; 
v_a_1038_ = lean_ctor_get(v_x_1037_, 0);
lean_inc(v_a_1038_);
lean_dec_ref_known(v_x_1037_, 1);
v___x_1039_ = lean_task_pure(v_a_1038_);
return v___x_1039_;
}
else
{
lean_object* v_a_1040_; 
v_a_1040_ = lean_ctor_get(v_x_1037_, 0);
lean_inc_ref(v_a_1040_);
lean_dec_ref_known(v_x_1037_, 1);
return v_a_1040_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_get___redArg(lean_object* v_x_1041_){
_start:
{
if (lean_obj_tag(v_x_1041_) == 0)
{
lean_object* v_a_1042_; 
v_a_1042_ = lean_ctor_get(v_x_1041_, 0);
lean_inc(v_a_1042_);
lean_dec_ref_known(v_x_1041_, 1);
return v_a_1042_;
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1044_; 
v_a_1043_ = lean_ctor_get(v_x_1041_, 0);
lean_inc_ref(v_a_1043_);
lean_dec_ref_known(v_x_1041_, 1);
v___x_1044_ = lean_task_get_own(v_a_1043_);
return v___x_1044_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_get(lean_object* v_00_u03b1_1045_, lean_object* v_x_1046_){
_start:
{
if (lean_obj_tag(v_x_1046_) == 0)
{
lean_object* v_a_1047_; 
v_a_1047_ = lean_ctor_get(v_x_1046_, 0);
lean_inc(v_a_1047_);
lean_dec_ref_known(v_x_1046_, 1);
return v_a_1047_;
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1049_; 
v_a_1048_ = lean_ctor_get(v_x_1046_, 0);
lean_inc_ref(v_a_1048_);
lean_dec_ref_known(v_x_1046_, 1);
v___x_1049_ = lean_task_get_own(v_a_1048_);
return v___x_1049_;
}
}
}
lean_object* l_Std_Async_MaybeTask_map___redArg(lean_object* v_f_1050_, lean_object* v_prio_1051_, uint8_t v_sync_1052_, lean_object* v_x_1053_){
_start:
{
if (lean_obj_tag(v_x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1062_; 
lean_dec(v_prio_1051_);
v_a_1054_ = lean_ctor_get(v_x_1053_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_x_1053_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1056_ = v_x_1053_;
v_isShared_1057_ = v_isSharedCheck_1062_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v_x_1053_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1062_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1058_ = lean_apply_1(v_f_1050_, v_a_1054_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v___x_1058_);
v___x_1060_ = v___x_1056_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1058_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1071_; 
v_a_1063_ = lean_ctor_get(v_x_1053_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_x_1053_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1065_ = v_x_1053_;
v_isShared_1066_ = v_isSharedCheck_1071_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v_x_1053_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1071_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1067_ = lean_task_map(v_f_1050_, v_a_1063_, v_prio_1051_, v_sync_1052_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1067_);
v___x_1069_ = v___x_1065_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_MaybeTask_map___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1050_ = stack[0].m_obj;
lean_object* v_prio_1051_ = stack[1].m_obj;
uint8_t v_sync_1052_ = stack[2].m_num;
lean_object* v_x_1053_ = stack[3].m_obj;
lean_object* v_res_1072_;
v_res_1072_ = l_Std_Async_MaybeTask_map___redArg(v_f_1050_, v_prio_1051_, v_sync_1052_, v_x_1053_);
stack->m_obj
 = v_res_1072_;
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_map___redArg___boxed(lean_object* v_f_1073_, lean_object* v_prio_1074_, lean_object* v_sync_1075_, lean_object* v_x_1076_){
_start:
{
uint8_t v_sync_boxed_1077_; lean_object* v_res_1078_; 
v_sync_boxed_1077_ = lean_unbox(v_sync_1075_);
v_res_1078_ = l_Std_Async_MaybeTask_map___redArg(v_f_1073_, v_prio_1074_, v_sync_boxed_1077_, v_x_1076_);
return v_res_1078_;
}
}
lean_object* l_Std_Async_MaybeTask_map(lean_object* v_00_u03b1_1079_, lean_object* v_00_u03b2_1080_, lean_object* v_f_1081_, lean_object* v_prio_1082_, uint8_t v_sync_1083_, lean_object* v_x_1084_){
_start:
{
if (lean_obj_tag(v_x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1093_; 
lean_dec(v_prio_1082_);
v_a_1085_ = lean_ctor_get(v_x_1084_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_x_1084_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1087_ = v_x_1084_;
v_isShared_1088_ = v_isSharedCheck_1093_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v_x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1093_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1089_ = lean_apply_1(v_f_1081_, v_a_1085_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1089_);
v___x_1091_ = v___x_1087_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1102_; 
v_a_1094_ = lean_ctor_get(v_x_1084_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_x_1084_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1096_ = v_x_1084_;
v_isShared_1097_ = v_isSharedCheck_1102_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v_x_1084_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1102_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1098_ = lean_task_map(v_f_1081_, v_a_1094_, v_prio_1082_, v_sync_1083_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 0, v___x_1098_);
v___x_1100_ = v___x_1096_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_MaybeTask_map_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1081_ = stack[2].m_obj;
lean_object* v_prio_1082_ = stack[3].m_obj;
uint8_t v_sync_1083_ = stack[4].m_num;
lean_object* v_x_1084_ = stack[5].m_obj;
lean_object* v_res_1103_;
v_res_1103_ = l_Std_Async_MaybeTask_map(lean_box(0), lean_box(0), v_f_1081_, v_prio_1082_, v_sync_1083_, v_x_1084_);
stack->m_obj
 = v_res_1103_;
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_map___boxed(lean_object* v_00_u03b1_1104_, lean_object* v_00_u03b2_1105_, lean_object* v_f_1106_, lean_object* v_prio_1107_, lean_object* v_sync_1108_, lean_object* v_x_1109_){
_start:
{
uint8_t v_sync_boxed_1110_; lean_object* v_res_1111_; 
v_sync_boxed_1110_ = lean_unbox(v_sync_1108_);
v_res_1111_ = l_Std_Async_MaybeTask_map(v_00_u03b1_1104_, v_00_u03b2_1105_, v_f_1106_, v_prio_1107_, v_sync_boxed_1110_, v_x_1109_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_bind___redArg___lam__0(lean_object* v_f_1112_, lean_object* v_x_1113_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_apply_1(v_f_1112_, v_x_1113_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1116_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v___x_1114_, 1);
v___x_1116_ = lean_task_pure(v_a_1115_);
return v___x_1116_;
}
else
{
lean_object* v_a_1117_; 
v_a_1117_ = lean_ctor_get(v___x_1114_, 0);
lean_inc_ref(v_a_1117_);
lean_dec_ref_known(v___x_1114_, 1);
return v_a_1117_;
}
}
}
lean_object* l_Std_Async_MaybeTask_bind___redArg(lean_object* v_t_1118_, lean_object* v_f_1119_, lean_object* v_prio_1120_, uint8_t v_sync_1121_){
_start:
{
if (lean_obj_tag(v_t_1118_) == 0)
{
lean_object* v_a_1122_; lean_object* v___x_1123_; 
lean_dec(v_prio_1120_);
v_a_1122_ = lean_ctor_get(v_t_1118_, 0);
lean_inc(v_a_1122_);
lean_dec_ref_known(v_t_1118_, 1);
v___x_1123_ = lean_apply_1(v_f_1119_, v_a_1122_);
return v___x_1123_;
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1133_; 
v_a_1124_ = lean_ctor_get(v_t_1118_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_t_1118_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1126_ = v_t_1118_;
v_isShared_1127_ = v_isSharedCheck_1133_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v_t_1118_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1133_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___f_1128_; lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___f_1128_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1128_, 0, v_f_1119_);
v___x_1129_ = lean_task_bind(v_a_1124_, v___f_1128_, v_prio_1120_, v_sync_1121_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v___x_1129_);
v___x_1131_ = v___x_1126_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_MaybeTask_bind___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1118_ = stack[0].m_obj;
lean_object* v_f_1119_ = stack[1].m_obj;
lean_object* v_prio_1120_ = stack[2].m_obj;
uint8_t v_sync_1121_ = stack[3].m_num;
lean_object* v_res_1134_;
v_res_1134_ = l_Std_Async_MaybeTask_bind___redArg(v_t_1118_, v_f_1119_, v_prio_1120_, v_sync_1121_);
stack->m_obj
 = v_res_1134_;
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_bind___redArg___boxed(lean_object* v_t_1135_, lean_object* v_f_1136_, lean_object* v_prio_1137_, lean_object* v_sync_1138_){
_start:
{
uint8_t v_sync_boxed_1139_; lean_object* v_res_1140_; 
v_sync_boxed_1139_ = lean_unbox(v_sync_1138_);
v_res_1140_ = l_Std_Async_MaybeTask_bind___redArg(v_t_1135_, v_f_1136_, v_prio_1137_, v_sync_boxed_1139_);
return v_res_1140_;
}
}
lean_object* l_Std_Async_MaybeTask_bind(lean_object* v_00_u03b1_1141_, lean_object* v_00_u03b2_1142_, lean_object* v_t_1143_, lean_object* v_f_1144_, lean_object* v_prio_1145_, uint8_t v_sync_1146_){
_start:
{
if (lean_obj_tag(v_t_1143_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1148_; 
lean_dec(v_prio_1145_);
v_a_1147_ = lean_ctor_get(v_t_1143_, 0);
lean_inc(v_a_1147_);
lean_dec_ref_known(v_t_1143_, 1);
v___x_1148_ = lean_apply_1(v_f_1144_, v_a_1147_);
return v___x_1148_;
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1158_; 
v_a_1149_ = lean_ctor_get(v_t_1143_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_t_1143_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1151_ = v_t_1143_;
v_isShared_1152_ = v_isSharedCheck_1158_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v_t_1143_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1158_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___f_1153_; lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___f_1153_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1153_, 0, v_f_1144_);
v___x_1154_ = lean_task_bind(v_a_1149_, v___f_1153_, v_prio_1145_, v_sync_1146_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1154_);
v___x_1156_ = v___x_1151_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_MaybeTask_bind_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1143_ = stack[2].m_obj;
lean_object* v_f_1144_ = stack[3].m_obj;
lean_object* v_prio_1145_ = stack[4].m_obj;
uint8_t v_sync_1146_ = stack[5].m_num;
lean_object* v_res_1159_;
v_res_1159_ = l_Std_Async_MaybeTask_bind(lean_box(0), lean_box(0), v_t_1143_, v_f_1144_, v_prio_1145_, v_sync_1146_);
stack->m_obj
 = v_res_1159_;
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_bind___boxed(lean_object* v_00_u03b1_1160_, lean_object* v_00_u03b2_1161_, lean_object* v_t_1162_, lean_object* v_f_1163_, lean_object* v_prio_1164_, lean_object* v_sync_1165_){
_start:
{
uint8_t v_sync_boxed_1166_; lean_object* v_res_1167_; 
v_sync_boxed_1166_ = lean_unbox(v_sync_1165_);
v_res_1167_ = l_Std_Async_MaybeTask_bind(v_00_u03b1_1160_, v_00_u03b2_1161_, v_t_1162_, v_f_1163_, v_prio_1164_, v_sync_boxed_1166_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_joinTask___redArg___lam__0(lean_object* v_x_1168_){
_start:
{
if (lean_obj_tag(v_x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v___x_1170_; 
v_a_1169_ = lean_ctor_get(v_x_1168_, 0);
lean_inc(v_a_1169_);
lean_dec_ref_known(v_x_1168_, 1);
v___x_1170_ = lean_task_pure(v_a_1169_);
return v___x_1170_;
}
else
{
lean_object* v_a_1171_; 
v_a_1171_ = lean_ctor_get(v_x_1168_, 0);
lean_inc_ref(v_a_1171_);
lean_dec_ref_known(v_x_1168_, 1);
return v_a_1171_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_joinTask___redArg(lean_object* v_t_1173_){
_start:
{
lean_object* v___f_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; lean_object* v___x_1177_; 
v___f_1174_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___x_1175_ = lean_unsigned_to_nat(0u);
v___x_1176_ = 1;
v___x_1177_ = lean_task_bind(v_t_1173_, v___f_1174_, v___x_1175_, v___x_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_joinTask(lean_object* v_00_u03b1_1178_, lean_object* v_t_1179_){
_start:
{
lean_object* v___f_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; lean_object* v___x_1183_; 
v___f_1180_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___x_1181_ = lean_unsigned_to_nat(0u);
v___x_1182_ = 1;
v___x_1183_ = lean_task_bind(v_t_1179_, v___f_1180_, v___x_1181_, v___x_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instFunctor___lam__0(lean_object* v_00_u03b1_1184_, lean_object* v_00_u03b2_1185_, lean_object* v_f_1186_, lean_object* v___y_1187_){
_start:
{
if (lean_obj_tag(v___y_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1196_; 
v_a_1188_ = lean_ctor_get(v___y_1187_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___y_1187_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1190_ = v___y_1187_;
v_isShared_1191_ = v_isSharedCheck_1196_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___y_1187_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1196_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1192_ = lean_apply_1(v_f_1186_, v_a_1188_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1192_);
v___x_1194_ = v___x_1190_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1207_; 
v_a_1197_ = lean_ctor_get(v___y_1187_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___y_1187_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1199_ = v___y_1187_;
v_isShared_1200_ = v_isSharedCheck_1207_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___y_1187_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1207_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1201_; uint8_t v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1201_ = lean_unsigned_to_nat(0u);
v___x_1202_ = 0;
v___x_1203_ = lean_task_map(v_f_1186_, v_a_1197_, v___x_1201_, v___x_1202_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 0, v___x_1203_);
v___x_1205_ = v___x_1199_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instFunctor___lam__1(lean_object* v___f_1208_, lean_object* v_00_u03b1_1209_, lean_object* v_00_u03b2_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_1213_, 0, lean_box(0));
lean_closure_set(v___x_1213_, 1, lean_box(0));
lean_closure_set(v___x_1213_, 2, v___y_1211_);
v___x_1214_ = lean_apply_4(v___f_1208_, lean_box(0), lean_box(0), v___x_1213_, v___y_1212_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__0(lean_object* v_00_u03b1_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___y_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__1(lean_object* v_x_1225_, lean_object* v_y_1226_){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = lean_box(0);
v___x_1228_ = lean_apply_1(v_x_1225_, v___x_1227_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1237_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1231_ = v___x_1228_;
v_isShared_1232_ = v_isSharedCheck_1237_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1228_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1237_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1233_ = lean_apply_1(v_y_1226_, v_a_1229_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v___x_1233_);
v___x_1235_ = v___x_1231_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1233_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
else
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1248_; 
v_a_1238_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1240_ = v___x_1228_;
v_isShared_1241_ = v_isSharedCheck_1248_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1228_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1248_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1242_; uint8_t v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1246_; 
v___x_1242_ = lean_unsigned_to_nat(0u);
v___x_1243_ = 0;
v___x_1244_ = lean_task_map(v_y_1226_, v_a_1238_, v___x_1242_, v___x_1243_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 0, v___x_1244_);
v___x_1246_ = v___x_1240_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1244_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__2(lean_object* v___f_1249_, lean_object* v_x_1250_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = lean_apply_1(v___f_1249_, v_x_1250_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v___x_1253_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
lean_dec_ref_known(v___x_1251_, 1);
v___x_1253_ = lean_task_pure(v_a_1252_);
return v___x_1253_;
}
else
{
lean_object* v_a_1254_; 
v_a_1254_ = lean_ctor_get(v___x_1251_, 0);
lean_inc_ref(v_a_1254_);
lean_dec_ref_known(v___x_1251_, 1);
return v_a_1254_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__3(lean_object* v_00_u03b1_1255_, lean_object* v_00_u03b2_1256_, lean_object* v_f_1257_, lean_object* v_x_1258_){
_start:
{
lean_object* v___f_1259_; 
lean_inc_ref(v_x_1258_);
v___f_1259_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_instMonad___lam__1), 2, 1);
lean_closure_set(v___f_1259_, 0, v_x_1258_);
if (lean_obj_tag(v_f_1257_) == 0)
{
lean_object* v_a_1260_; lean_object* v___x_1261_; 
lean_dec_ref(v___f_1259_);
v_a_1260_ = lean_ctor_get(v_f_1257_, 0);
lean_inc(v_a_1260_);
lean_dec_ref_known(v_f_1257_, 1);
v___x_1261_ = l_Std_Async_MaybeTask_instMonad___lam__1(v_x_1258_, v_a_1260_);
return v___x_1261_;
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1273_; 
lean_dec_ref(v_x_1258_);
v_a_1262_ = lean_ctor_get(v_f_1257_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_f_1257_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1264_ = v_f_1257_;
v_isShared_1265_ = v_isSharedCheck_1273_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v_f_1257_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1273_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___f_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1271_; 
v___f_1266_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_instMonad___lam__2), 2, 1);
lean_closure_set(v___f_1266_, 0, v___f_1259_);
v___x_1267_ = lean_unsigned_to_nat(0u);
v___x_1268_ = 0;
v___x_1269_ = lean_task_bind(v_a_1262_, v___f_1266_, v___x_1267_, v___x_1268_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1269_);
v___x_1271_ = v___x_1264_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__5(lean_object* v_00_u03b1_1274_, lean_object* v_00_u03b2_1275_, lean_object* v_t_1276_, lean_object* v_f_1277_){
_start:
{
if (lean_obj_tag(v_t_1276_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1279_; 
v_a_1278_ = lean_ctor_get(v_t_1276_, 0);
lean_inc(v_a_1278_);
lean_dec_ref_known(v_t_1276_, 1);
v___x_1279_ = lean_apply_1(v_f_1277_, v_a_1278_);
return v___x_1279_;
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1291_; 
v_a_1280_ = lean_ctor_get(v_t_1276_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_t_1276_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1282_ = v_t_1276_;
v_isShared_1283_ = v_isSharedCheck_1291_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v_t_1276_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1291_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___f_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___f_1284_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1284_, 0, v_f_1277_);
v___x_1285_ = lean_unsigned_to_nat(0u);
v___x_1286_ = 0;
v___x_1287_ = lean_task_bind(v_a_1280_, v___f_1284_, v___x_1285_, v___x_1286_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 0, v___x_1287_);
v___x_1289_ = v___x_1282_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__4(lean_object* v_a_1292_, lean_object* v_x_1293_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1294_, 0, v_a_1292_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__4___boxed(lean_object* v_a_1295_, lean_object* v_x_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Std_Async_MaybeTask_instMonad___lam__4(v_a_1295_, v_x_1296_);
lean_dec(v_x_1296_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__6(lean_object* v_y_1298_, lean_object* v___f_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v___f_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___f_1301_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_instMonad___lam__4___boxed), 2, 1);
lean_closure_set(v___f_1301_, 0, v_a_1300_);
v___x_1302_ = lean_box(0);
v___x_1303_ = lean_apply_1(v_y_1298_, v___x_1302_);
v___x_1304_ = lean_apply_4(v___f_1299_, lean_box(0), lean_box(0), v___x_1303_, v___f_1301_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__7(lean_object* v___f_1305_, lean_object* v_00_u03b1_1306_, lean_object* v_00_u03b2_1307_, lean_object* v_x_1308_, lean_object* v_y_1309_){
_start:
{
lean_object* v___f_1310_; lean_object* v___x_1311_; 
lean_inc_ref(v___f_1305_);
v___f_1310_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_instMonad___lam__6), 3, 2);
lean_closure_set(v___f_1310_, 0, v_y_1309_);
lean_closure_set(v___f_1310_, 1, v___f_1305_);
v___x_1311_ = lean_apply_4(v___f_1305_, lean_box(0), lean_box(0), v_x_1308_, v___f_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__8(lean_object* v_y_1312_, lean_object* v_x_1313_){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_box(0);
v___x_1315_ = lean_apply_1(v_y_1312_, v___x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__8___boxed(lean_object* v_y_1316_, lean_object* v_x_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Std_Async_MaybeTask_instMonad___lam__8(v_y_1316_, v_x_1317_);
lean_dec(v_x_1317_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__9(lean_object* v___f_1319_, lean_object* v_x_1320_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = lean_apply_1(v___f_1319_, v_x_1320_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1323_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_a_1322_);
lean_dec_ref_known(v___x_1321_, 1);
v___x_1323_ = lean_task_pure(v_a_1322_);
return v___x_1323_;
}
else
{
lean_object* v_a_1324_; 
v_a_1324_ = lean_ctor_get(v___x_1321_, 0);
lean_inc_ref(v_a_1324_);
lean_dec_ref_known(v___x_1321_, 1);
return v_a_1324_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__10(lean_object* v_00_u03b1_1325_, lean_object* v_00_u03b2_1326_, lean_object* v_x_1327_, lean_object* v_y_1328_){
_start:
{
lean_object* v___f_1329_; 
lean_inc_ref(v_y_1328_);
v___f_1329_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_instMonad___lam__8___boxed), 2, 1);
lean_closure_set(v___f_1329_, 0, v_y_1328_);
if (lean_obj_tag(v_x_1327_) == 0)
{
lean_object* v_a_1330_; lean_object* v___x_1331_; 
lean_dec_ref(v___f_1329_);
v_a_1330_ = lean_ctor_get(v_x_1327_, 0);
lean_inc(v_a_1330_);
lean_dec_ref_known(v_x_1327_, 1);
v___x_1331_ = l_Std_Async_MaybeTask_instMonad___lam__8(v_y_1328_, v_a_1330_);
lean_dec(v_a_1330_);
return v___x_1331_;
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1343_; 
lean_dec_ref(v_y_1328_);
v_a_1332_ = lean_ctor_get(v_x_1327_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_x_1327_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1334_ = v_x_1327_;
v_isShared_1335_ = v_isSharedCheck_1343_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v_x_1327_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1343_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___f_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___f_1336_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_instMonad___lam__9), 2, 1);
lean_closure_set(v___f_1336_, 0, v___f_1329_);
v___x_1337_ = lean_unsigned_to_nat(0u);
v___x_1338_ = 0;
v___x_1339_ = lean_task_bind(v_a_1332_, v___f_1336_, v___x_1337_, v___x_1338_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1339_);
v___x_1341_ = v___x_1334_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
}
lean_object* l_Std_Async_BaseAsync_mk___redArg(lean_object* v_x_1360_){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = lean_apply_1(v_x_1360_, lean_box(0));
return v___x_1362_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_mk___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1360_ = stack[0].m_obj;
lean_object* v_res_1363_;
v_res_1363_ = l_Std_Async_BaseAsync_mk___redArg(v_x_1360_);
stack->m_obj
 = v_res_1363_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_mk___redArg___boxed(lean_object* v_x_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Std_Async_BaseAsync_mk___redArg(v_x_1364_);
return v_res_1366_;
}
}
lean_object* l_Std_Async_BaseAsync_mk(lean_object* v_00_u03b1_1367_, lean_object* v_x_1368_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_apply_1(v_x_1368_, lean_box(0));
return v___x_1370_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_mk_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1368_ = stack[1].m_obj;
lean_object* v_res_1371_;
v_res_1371_ = l_Std_Async_BaseAsync_mk(lean_box(0), v_x_1368_);
stack->m_obj
 = v_res_1371_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_mk___boxed(lean_object* v_00_u03b1_1372_, lean_object* v_x_1373_, lean_object* v_a_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_Std_Async_BaseAsync_mk(v_00_u03b1_1372_, v_x_1373_);
return v_res_1375_;
}
}
lean_object* l_Std_Async_BaseAsync_toRawBaseIO___redArg(lean_object* v_x_1376_){
_start:
{
lean_object* v___x_1378_; 
v___x_1378_ = lean_apply_1(v_x_1376_, lean_box(0));
return v___x_1378_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_toRawBaseIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1376_ = stack[0].m_obj;
lean_object* v_res_1379_;
v_res_1379_ = l_Std_Async_BaseAsync_toRawBaseIO___redArg(v_x_1376_);
stack->m_obj
 = v_res_1379_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toRawBaseIO___redArg___boxed(lean_object* v_x_1380_, lean_object* v_a_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l_Std_Async_BaseAsync_toRawBaseIO___redArg(v_x_1380_);
return v_res_1382_;
}
}
lean_object* l_Std_Async_BaseAsync_toRawBaseIO(lean_object* v_00_u03b1_1383_, lean_object* v_x_1384_){
_start:
{
lean_object* v___x_1386_; 
v___x_1386_ = lean_apply_1(v_x_1384_, lean_box(0));
return v___x_1386_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_toRawBaseIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1384_ = stack[1].m_obj;
lean_object* v_res_1387_;
v_res_1387_ = l_Std_Async_BaseAsync_toRawBaseIO(lean_box(0), v_x_1384_);
stack->m_obj
 = v_res_1387_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toRawBaseIO___boxed(lean_object* v_00_u03b1_1388_, lean_object* v_x_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Std_Async_BaseAsync_toRawBaseIO(v_00_u03b1_1388_, v_x_1389_);
return v_res_1391_;
}
}
lean_object* l_Std_Async_BaseAsync_toBaseIO___redArg(lean_object* v_x_1392_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = lean_apply_1(v_x_1392_, lean_box(0));
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v___x_1396_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_a_1395_);
lean_dec_ref_known(v___x_1394_, 1);
v___x_1396_ = lean_task_pure(v_a_1395_);
return v___x_1396_;
}
else
{
lean_object* v_a_1397_; 
v_a_1397_ = lean_ctor_get(v___x_1394_, 0);
lean_inc_ref(v_a_1397_);
lean_dec_ref_known(v___x_1394_, 1);
return v_a_1397_;
}
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_toBaseIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1392_ = stack[0].m_obj;
lean_object* v_res_1398_;
v_res_1398_ = l_Std_Async_BaseAsync_toBaseIO___redArg(v_x_1392_);
stack->m_obj
 = v_res_1398_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toBaseIO___redArg___boxed(lean_object* v_x_1399_, lean_object* v_a_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Std_Async_BaseAsync_toBaseIO___redArg(v_x_1399_);
return v_res_1401_;
}
}
lean_object* l_Std_Async_BaseAsync_toBaseIO(lean_object* v_00_u03b1_1402_, lean_object* v_x_1403_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = lean_apply_1(v_x_1403_, lean_box(0));
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1407_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_a_1406_);
lean_dec_ref_known(v___x_1405_, 1);
v___x_1407_ = lean_task_pure(v_a_1406_);
return v___x_1407_;
}
else
{
lean_object* v_a_1408_; 
v_a_1408_ = lean_ctor_get(v___x_1405_, 0);
lean_inc_ref(v_a_1408_);
lean_dec_ref_known(v___x_1405_, 1);
return v_a_1408_;
}
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_toBaseIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1403_ = stack[1].m_obj;
lean_object* v_res_1409_;
v_res_1409_ = l_Std_Async_BaseAsync_toBaseIO(lean_box(0), v_x_1403_);
stack->m_obj
 = v_res_1409_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toBaseIO___boxed(lean_object* v_00_u03b1_1410_, lean_object* v_x_1411_, lean_object* v_a_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Std_Async_BaseAsync_toBaseIO(v_00_u03b1_1410_, v_x_1411_);
return v_res_1413_;
}
}
lean_object* l_Std_Async_BaseAsync_ofTask___redArg(lean_object* v_x_1414_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1416_, 0, v_x_1414_);
return v___x_1416_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_ofTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1414_ = stack[0].m_obj;
lean_object* v_res_1417_;
v_res_1417_ = l_Std_Async_BaseAsync_ofTask___redArg(v_x_1414_);
stack->m_obj
 = v_res_1417_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofTask___redArg___boxed(lean_object* v_x_1418_, lean_object* v_a_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Std_Async_BaseAsync_ofTask___redArg(v_x_1418_);
return v_res_1420_;
}
}
lean_object* l_Std_Async_BaseAsync_ofTask(lean_object* v_00_u03b1_1421_, lean_object* v_x_1422_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1424_, 0, v_x_1422_);
return v___x_1424_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_ofTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1422_ = stack[1].m_obj;
lean_object* v_res_1425_;
v_res_1425_ = l_Std_Async_BaseAsync_ofTask(lean_box(0), v_x_1422_);
stack->m_obj
 = v_res_1425_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofTask___boxed(lean_object* v_00_u03b1_1426_, lean_object* v_x_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Std_Async_BaseAsync_ofTask(v_00_u03b1_1426_, v_x_1427_);
return v_res_1429_;
}
}
lean_object* l_Std_Async_BaseAsync_pure___redArg(lean_object* v_a_1430_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1432_, 0, v_a_1430_);
return v___x_1432_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_pure___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1430_ = stack[0].m_obj;
lean_object* v_res_1433_;
v_res_1433_ = l_Std_Async_BaseAsync_pure___redArg(v_a_1430_);
stack->m_obj
 = v_res_1433_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_pure___redArg___boxed(lean_object* v_a_1434_, lean_object* v_a_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Std_Async_BaseAsync_pure___redArg(v_a_1434_);
return v_res_1436_;
}
}
lean_object* l_Std_Async_BaseAsync_pure(lean_object* v_00_u03b1_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1440_, 0, v_a_1438_);
return v___x_1440_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_pure_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1438_ = stack[1].m_obj;
lean_object* v_res_1441_;
v_res_1441_ = l_Std_Async_BaseAsync_pure(lean_box(0), v_a_1438_);
stack->m_obj
 = v_res_1441_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_pure___boxed(lean_object* v_00_u03b1_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Std_Async_BaseAsync_pure(v_00_u03b1_1442_, v_a_1443_);
return v_res_1445_;
}
}
lean_object* l_Std_Async_BaseAsync_map___redArg(lean_object* v_f_1446_, lean_object* v_self_1447_, lean_object* v_prio_1448_, uint8_t v_sync_1449_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = lean_apply_1(v_self_1447_, lean_box(0));
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1460_; 
lean_dec(v_prio_1448_);
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1454_ = v___x_1451_;
v_isShared_1455_ = v_isSharedCheck_1460_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1451_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1460_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1456_; lean_object* v___x_1458_; 
v___x_1456_ = lean_apply_1(v_f_1446_, v_a_1452_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 0, v___x_1456_);
v___x_1458_ = v___x_1454_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1469_; 
v_a_1461_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1463_ = v___x_1451_;
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1451_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1465_; lean_object* v___x_1467_; 
v___x_1465_ = lean_task_map(v_f_1446_, v_a_1461_, v_prio_1448_, v_sync_1449_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 0, v___x_1465_);
v___x_1467_ = v___x_1463_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_map___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1446_ = stack[0].m_obj;
lean_object* v_self_1447_ = stack[1].m_obj;
lean_object* v_prio_1448_ = stack[2].m_obj;
uint8_t v_sync_1449_ = stack[3].m_num;
lean_object* v_res_1470_;
v_res_1470_ = l_Std_Async_BaseAsync_map___redArg(v_f_1446_, v_self_1447_, v_prio_1448_, v_sync_1449_);
stack->m_obj
 = v_res_1470_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_map___redArg___boxed(lean_object* v_f_1471_, lean_object* v_self_1472_, lean_object* v_prio_1473_, lean_object* v_sync_1474_, lean_object* v_a_1475_){
_start:
{
uint8_t v_sync_boxed_1476_; lean_object* v_res_1477_; 
v_sync_boxed_1476_ = lean_unbox(v_sync_1474_);
v_res_1477_ = l_Std_Async_BaseAsync_map___redArg(v_f_1471_, v_self_1472_, v_prio_1473_, v_sync_boxed_1476_);
return v_res_1477_;
}
}
lean_object* l_Std_Async_BaseAsync_map(lean_object* v_00_u03b1_1478_, lean_object* v_00_u03b2_1479_, lean_object* v_f_1480_, lean_object* v_self_1481_, lean_object* v_prio_1482_, uint8_t v_sync_1483_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = lean_apply_1(v_self_1481_, lean_box(0));
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1494_; 
lean_dec(v_prio_1482_);
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1494_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1494_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1490_ = lean_apply_1(v_f_1480_, v_a_1486_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1490_);
v___x_1492_ = v___x_1488_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1503_; 
v_a_1495_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1497_ = v___x_1485_;
v_isShared_1498_ = v_isSharedCheck_1503_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1485_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1503_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1499_; lean_object* v___x_1501_; 
v___x_1499_ = lean_task_map(v_f_1480_, v_a_1495_, v_prio_1482_, v_sync_1483_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v___x_1499_);
v___x_1501_ = v___x_1497_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_map_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1480_ = stack[2].m_obj;
lean_object* v_self_1481_ = stack[3].m_obj;
lean_object* v_prio_1482_ = stack[4].m_obj;
uint8_t v_sync_1483_ = stack[5].m_num;
lean_object* v_res_1504_;
v_res_1504_ = l_Std_Async_BaseAsync_map(lean_box(0), lean_box(0), v_f_1480_, v_self_1481_, v_prio_1482_, v_sync_1483_);
stack->m_obj
 = v_res_1504_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_map___boxed(lean_object* v_00_u03b1_1505_, lean_object* v_00_u03b2_1506_, lean_object* v_f_1507_, lean_object* v_self_1508_, lean_object* v_prio_1509_, lean_object* v_sync_1510_, lean_object* v_a_1511_){
_start:
{
uint8_t v_sync_boxed_1512_; lean_object* v_res_1513_; 
v_sync_boxed_1512_ = lean_unbox(v_sync_1510_);
v_res_1513_ = l_Std_Async_BaseAsync_map(v_00_u03b1_1505_, v_00_u03b2_1506_, v_f_1507_, v_self_1508_, v_prio_1509_, v_sync_boxed_1512_);
return v_res_1513_;
}
}
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___lam__0(lean_object* v_f_1514_, lean_object* v_a_1515_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = lean_apply_2(v_f_1514_, v_a_1515_, lean_box(0));
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1519_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v___x_1517_, 1);
v___x_1519_ = lean_task_pure(v_a_1518_);
return v___x_1519_;
}
else
{
lean_object* v_a_1520_; 
v_a_1520_ = lean_ctor_get(v___x_1517_, 0);
lean_inc_ref(v_a_1520_);
lean_dec_ref_known(v___x_1517_, 1);
return v_a_1520_;
}
}
}
LEAN_EXPORT void l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1514_ = stack[0].m_obj;
lean_object* v_a_1515_ = stack[1].m_obj;
lean_object* v_res_1521_;
v_res_1521_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___lam__0(v_f_1514_, v_a_1515_);
stack->m_obj
 = v_res_1521_;
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___lam__0___boxed(lean_object* v_f_1522_, lean_object* v_a_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___lam__0(v_f_1522_, v_a_1523_);
return v_res_1525_;
}
}
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(lean_object* v_prio_1526_, uint8_t v_sync_1527_, lean_object* v_t_1528_, lean_object* v_f_1529_){
_start:
{
if (lean_obj_tag(v_t_1528_) == 0)
{
lean_object* v_a_1531_; lean_object* v___x_1532_; 
lean_dec(v_prio_1526_);
v_a_1531_ = lean_ctor_get(v_t_1528_, 0);
lean_inc(v_a_1531_);
lean_dec_ref_known(v_t_1528_, 1);
v___x_1532_ = lean_apply_2(v_f_1529_, v_a_1531_, lean_box(0));
return v___x_1532_;
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1542_; 
v_a_1533_ = lean_ctor_get(v_t_1528_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_t_1528_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1535_ = v_t_1528_;
v_isShared_1536_ = v_isSharedCheck_1542_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v_t_1528_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1542_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___f_1537_; lean_object* v___x_1538_; lean_object* v___x_1540_; 
v___f_1537_ = lean_alloc_closure((void*)(l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1537_, 0, v_f_1529_);
v___x_1538_ = lean_io_bind_task(v_a_1533_, v___f_1537_, v_prio_1526_, v_sync_1527_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 0, v___x_1538_);
v___x_1540_ = v___x_1535_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1538_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_prio_1526_ = stack[0].m_obj;
uint8_t v_sync_1527_ = stack[1].m_num;
lean_object* v_t_1528_ = stack[2].m_obj;
lean_object* v_f_1529_ = stack[3].m_obj;
lean_object* v_res_1543_;
v_res_1543_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_1526_, v_sync_1527_, v_t_1528_, v_f_1529_);
stack->m_obj
 = v_res_1543_;
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___boxed(lean_object* v_prio_1544_, lean_object* v_sync_1545_, lean_object* v_t_1546_, lean_object* v_f_1547_, lean_object* v_a_1548_){
_start:
{
uint8_t v_sync_boxed_1549_; lean_object* v_res_1550_; 
v_sync_boxed_1549_ = lean_unbox(v_sync_1545_);
v_res_1550_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_1544_, v_sync_boxed_1549_, v_t_1546_, v_f_1547_);
return v_res_1550_;
}
}
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object* v_00_u03b1_1551_, lean_object* v_00_u03b2_1552_, lean_object* v_prio_1553_, uint8_t v_sync_1554_, lean_object* v_t_1555_, lean_object* v_f_1556_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_1553_, v_sync_1554_, v_t_1555_, v_f_1556_);
return v___x_1558_;
}
}
LEAN_EXPORT void l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_prio_1553_ = stack[2].m_obj;
uint8_t v_sync_1554_ = stack[3].m_num;
lean_object* v_t_1555_ = stack[4].m_obj;
lean_object* v_f_1556_ = stack[5].m_obj;
lean_object* v_res_1559_;
v_res_1559_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v_prio_1553_, v_sync_1554_, v_t_1555_, v_f_1556_);
stack->m_obj
 = v_res_1559_;
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___boxed(lean_object* v_00_u03b1_1560_, lean_object* v_00_u03b2_1561_, lean_object* v_prio_1562_, lean_object* v_sync_1563_, lean_object* v_t_1564_, lean_object* v_f_1565_, lean_object* v_a_1566_){
_start:
{
uint8_t v_sync_boxed_1567_; lean_object* v_res_1568_; 
v_sync_boxed_1567_ = lean_unbox(v_sync_1563_);
v_res_1568_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(v_00_u03b1_1560_, v_00_u03b2_1561_, v_prio_1562_, v_sync_boxed_1567_, v_t_1564_, v_f_1565_);
return v_res_1568_;
}
}
lean_object* l_Std_Async_BaseAsync_bind___redArg(lean_object* v_self_1569_, lean_object* v_f_1570_, lean_object* v_prio_1571_, uint8_t v_sync_1572_){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = lean_apply_1(v_self_1569_, lean_box(0));
v___x_1575_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_1571_, v_sync_1572_, v___x_1574_, v_f_1570_);
return v___x_1575_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_bind___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1569_ = stack[0].m_obj;
lean_object* v_f_1570_ = stack[1].m_obj;
lean_object* v_prio_1571_ = stack[2].m_obj;
uint8_t v_sync_1572_ = stack[3].m_num;
lean_object* v_res_1576_;
v_res_1576_ = l_Std_Async_BaseAsync_bind___redArg(v_self_1569_, v_f_1570_, v_prio_1571_, v_sync_1572_);
stack->m_obj
 = v_res_1576_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_bind___redArg___boxed(lean_object* v_self_1577_, lean_object* v_f_1578_, lean_object* v_prio_1579_, lean_object* v_sync_1580_, lean_object* v_a_1581_){
_start:
{
uint8_t v_sync_boxed_1582_; lean_object* v_res_1583_; 
v_sync_boxed_1582_ = lean_unbox(v_sync_1580_);
v_res_1583_ = l_Std_Async_BaseAsync_bind___redArg(v_self_1577_, v_f_1578_, v_prio_1579_, v_sync_boxed_1582_);
return v_res_1583_;
}
}
lean_object* l_Std_Async_BaseAsync_bind(lean_object* v_00_u03b1_1584_, lean_object* v_00_u03b2_1585_, lean_object* v_self_1586_, lean_object* v_f_1587_, lean_object* v_prio_1588_, uint8_t v_sync_1589_){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = lean_apply_1(v_self_1586_, lean_box(0));
v___x_1592_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_1588_, v_sync_1589_, v___x_1591_, v_f_1587_);
return v___x_1592_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_bind_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1586_ = stack[2].m_obj;
lean_object* v_f_1587_ = stack[3].m_obj;
lean_object* v_prio_1588_ = stack[4].m_obj;
uint8_t v_sync_1589_ = stack[5].m_num;
lean_object* v_res_1593_;
v_res_1593_ = l_Std_Async_BaseAsync_bind(lean_box(0), lean_box(0), v_self_1586_, v_f_1587_, v_prio_1588_, v_sync_1589_);
stack->m_obj
 = v_res_1593_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_bind___boxed(lean_object* v_00_u03b1_1594_, lean_object* v_00_u03b2_1595_, lean_object* v_self_1596_, lean_object* v_f_1597_, lean_object* v_prio_1598_, lean_object* v_sync_1599_, lean_object* v_a_1600_){
_start:
{
uint8_t v_sync_boxed_1601_; lean_object* v_res_1602_; 
v_sync_boxed_1601_ = lean_unbox(v_sync_1599_);
v_res_1602_ = l_Std_Async_BaseAsync_bind(v_00_u03b1_1594_, v_00_u03b2_1595_, v_self_1596_, v_f_1597_, v_prio_1598_, v_sync_boxed_1601_);
return v_res_1602_;
}
}
lean_object* l_Std_Async_BaseAsync_lift___redArg(lean_object* v_x_1603_){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = lean_apply_1(v_x_1603_, lean_box(0));
v___x_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_lift___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1603_ = stack[0].m_obj;
lean_object* v_res_1607_;
v_res_1607_ = l_Std_Async_BaseAsync_lift___redArg(v_x_1603_);
stack->m_obj
 = v_res_1607_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_lift___redArg___boxed(lean_object* v_x_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Std_Async_BaseAsync_lift___redArg(v_x_1608_);
return v_res_1610_;
}
}
lean_object* l_Std_Async_BaseAsync_lift(lean_object* v_00_u03b1_1611_, lean_object* v_x_1612_){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = lean_apply_1(v_x_1612_, lean_box(0));
v___x_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_lift_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1612_ = stack[1].m_obj;
lean_object* v_res_1616_;
v_res_1616_ = l_Std_Async_BaseAsync_lift(lean_box(0), v_x_1612_);
stack->m_obj
 = v_res_1616_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_lift___boxed(lean_object* v_00_u03b1_1617_, lean_object* v_x_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Std_Async_BaseAsync_lift(v_00_u03b1_1617_, v_x_1618_);
return v_res_1620_;
}
}
lean_object* l_Std_Async_BaseAsync_wait___redArg(lean_object* v_self_1621_){
_start:
{
lean_object* v_val_1624_; lean_object* v___x_1626_; 
v___x_1626_ = lean_apply_1(v_self_1621_, lean_box(0));
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; lean_object* v___x_1628_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v___x_1626_, 1);
v___x_1628_ = lean_task_pure(v_a_1627_);
v_val_1624_ = v___x_1628_;
goto v___jp_1623_;
}
else
{
lean_object* v_a_1629_; 
v_a_1629_ = lean_ctor_get(v___x_1626_, 0);
lean_inc_ref(v_a_1629_);
lean_dec_ref_known(v___x_1626_, 1);
v_val_1624_ = v_a_1629_;
goto v___jp_1623_;
}
v___jp_1623_:
{
lean_object* v___x_1625_; 
v___x_1625_ = lean_task_get_own(v_val_1624_);
return v___x_1625_;
}
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_wait___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1621_ = stack[0].m_obj;
lean_object* v_res_1630_;
v_res_1630_ = l_Std_Async_BaseAsync_wait___redArg(v_self_1621_);
stack->m_obj
 = v_res_1630_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_wait___redArg___boxed(lean_object* v_self_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Std_Async_BaseAsync_wait___redArg(v_self_1631_);
return v_res_1633_;
}
}
lean_object* l_Std_Async_BaseAsync_wait(lean_object* v_00_u03b1_1634_, lean_object* v_self_1635_){
_start:
{
lean_object* v_val_1638_; lean_object* v___x_1640_; 
v___x_1640_ = lean_apply_1(v_self_1635_, lean_box(0));
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; lean_object* v___x_1642_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_a_1641_);
lean_dec_ref_known(v___x_1640_, 1);
v___x_1642_ = lean_task_pure(v_a_1641_);
v_val_1638_ = v___x_1642_;
goto v___jp_1637_;
}
else
{
lean_object* v_a_1643_; 
v_a_1643_ = lean_ctor_get(v___x_1640_, 0);
lean_inc_ref(v_a_1643_);
lean_dec_ref_known(v___x_1640_, 1);
v_val_1638_ = v_a_1643_;
goto v___jp_1637_;
}
v___jp_1637_:
{
lean_object* v___x_1639_; 
v___x_1639_ = lean_task_get_own(v_val_1638_);
return v___x_1639_;
}
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_wait_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1635_ = stack[1].m_obj;
lean_object* v_res_1644_;
v_res_1644_ = l_Std_Async_BaseAsync_wait(lean_box(0), v_self_1635_);
stack->m_obj
 = v_res_1644_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_wait___boxed(lean_object* v_00_u03b1_1645_, lean_object* v_self_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Std_Async_BaseAsync_wait(v_00_u03b1_1645_, v_self_1646_);
return v_res_1648_;
}
}
lean_object* l_Std_Async_BaseAsync_asTask___redArg(lean_object* v_x_1649_, lean_object* v_prio_1650_){
_start:
{
lean_object* v___f_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; lean_object* v___x_1657_; 
v___f_1652_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___x_1653_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1653_, 0, lean_box(0));
lean_closure_set(v___x_1653_, 1, v_x_1649_);
v___x_1654_ = lean_io_as_task(v___x_1653_, v_prio_1650_);
v___x_1655_ = lean_unsigned_to_nat(0u);
v___x_1656_ = 1;
v___x_1657_ = lean_task_bind(v___x_1654_, v___f_1652_, v___x_1655_, v___x_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_asTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1649_ = stack[0].m_obj;
lean_object* v_prio_1650_ = stack[1].m_obj;
lean_object* v_res_1658_;
v_res_1658_ = l_Std_Async_BaseAsync_asTask___redArg(v_x_1649_, v_prio_1650_);
stack->m_obj
 = v_res_1658_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_asTask___redArg___boxed(lean_object* v_x_1659_, lean_object* v_prio_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Std_Async_BaseAsync_asTask___redArg(v_x_1659_, v_prio_1660_);
return v_res_1662_;
}
}
lean_object* l_Std_Async_BaseAsync_asTask(lean_object* v_00_u03b1_1663_, lean_object* v_x_1664_, lean_object* v_prio_1665_){
_start:
{
lean_object* v___f_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; uint8_t v___x_1671_; lean_object* v___x_1672_; 
v___f_1667_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___x_1668_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1668_, 0, lean_box(0));
lean_closure_set(v___x_1668_, 1, v_x_1664_);
v___x_1669_ = lean_io_as_task(v___x_1668_, v_prio_1665_);
v___x_1670_ = lean_unsigned_to_nat(0u);
v___x_1671_ = 1;
v___x_1672_ = lean_task_bind(v___x_1669_, v___f_1667_, v___x_1670_, v___x_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_asTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1664_ = stack[1].m_obj;
lean_object* v_prio_1665_ = stack[2].m_obj;
lean_object* v_res_1673_;
v_res_1673_ = l_Std_Async_BaseAsync_asTask(lean_box(0), v_x_1664_, v_prio_1665_);
stack->m_obj
 = v_res_1673_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_asTask___boxed(lean_object* v_00_u03b1_1674_, lean_object* v_x_1675_, lean_object* v_prio_1676_, lean_object* v_a_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Std_Async_BaseAsync_asTask(v_00_u03b1_1674_, v_x_1675_, v_prio_1676_);
return v_res_1678_;
}
}
lean_object* l_Std_Async_BaseAsync_await___redArg(lean_object* v_t_1679_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1681_, 0, v_t_1679_);
return v___x_1681_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_await___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1679_ = stack[0].m_obj;
lean_object* v_res_1682_;
v_res_1682_ = l_Std_Async_BaseAsync_await___redArg(v_t_1679_);
stack->m_obj
 = v_res_1682_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_await___redArg___boxed(lean_object* v_t_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Std_Async_BaseAsync_await___redArg(v_t_1683_);
return v_res_1685_;
}
}
lean_object* l_Std_Async_BaseAsync_await(lean_object* v_00_u03b1_1686_, lean_object* v_t_1687_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1689_, 0, v_t_1687_);
return v___x_1689_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_await_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1687_ = stack[1].m_obj;
lean_object* v_res_1690_;
v_res_1690_ = l_Std_Async_BaseAsync_await(lean_box(0), v_t_1687_);
stack->m_obj
 = v_res_1690_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_await___boxed(lean_object* v_00_u03b1_1691_, lean_object* v_t_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Std_Async_BaseAsync_await(v_00_u03b1_1691_, v_t_1692_);
return v_res_1694_;
}
}
lean_object* l_Std_Async_BaseAsync_async___redArg(lean_object* v_self_1695_, lean_object* v_prio_1696_){
_start:
{
lean_object* v___f_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; uint8_t v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___f_1698_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___x_1699_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1699_, 0, lean_box(0));
lean_closure_set(v___x_1699_, 1, v_self_1695_);
v___x_1700_ = lean_io_as_task(v___x_1699_, v_prio_1696_);
v___x_1701_ = lean_unsigned_to_nat(0u);
v___x_1702_ = 1;
v___x_1703_ = lean_task_bind(v___x_1700_, v___f_1698_, v___x_1701_, v___x_1702_);
v___x_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_async___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1695_ = stack[0].m_obj;
lean_object* v_prio_1696_ = stack[1].m_obj;
lean_object* v_res_1705_;
v_res_1705_ = l_Std_Async_BaseAsync_async___redArg(v_self_1695_, v_prio_1696_);
stack->m_obj
 = v_res_1705_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_async___redArg___boxed(lean_object* v_self_1706_, lean_object* v_prio_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Std_Async_BaseAsync_async___redArg(v_self_1706_, v_prio_1707_);
return v_res_1709_;
}
}
lean_object* l_Std_Async_BaseAsync_async(lean_object* v_00_u03b1_1710_, lean_object* v_self_1711_, lean_object* v_prio_1712_){
_start:
{
lean_object* v___f_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___f_1714_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___x_1715_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1715_, 0, lean_box(0));
lean_closure_set(v___x_1715_, 1, v_self_1711_);
v___x_1716_ = lean_io_as_task(v___x_1715_, v_prio_1712_);
v___x_1717_ = lean_unsigned_to_nat(0u);
v___x_1718_ = 1;
v___x_1719_ = lean_task_bind(v___x_1716_, v___f_1714_, v___x_1717_, v___x_1718_);
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_async_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1711_ = stack[1].m_obj;
lean_object* v_prio_1712_ = stack[2].m_obj;
lean_object* v_res_1721_;
v_res_1721_ = l_Std_Async_BaseAsync_async(lean_box(0), v_self_1711_, v_prio_1712_);
stack->m_obj
 = v_res_1721_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_async___boxed(lean_object* v_00_u03b1_1722_, lean_object* v_self_1723_, lean_object* v_prio_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Std_Async_BaseAsync_async(v_00_u03b1_1722_, v_self_1723_, v_prio_1724_);
return v_res_1726_;
}
}
lean_object* l_Std_Async_BaseAsync_instFunctor___lam__0(lean_object* v_00_u03b1_1727_, lean_object* v_00_u03b2_1728_, lean_object* v_f_1729_, lean_object* v_self_1730_){
_start:
{
lean_object* v___x_1732_; uint8_t v___x_1733_; lean_object* v___x_1734_; 
v___x_1732_ = lean_unsigned_to_nat(0u);
v___x_1733_ = 0;
v___x_1734_ = lean_apply_1(v_self_1730_, lean_box(0));
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1743_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1737_ = v___x_1734_;
v_isShared_1738_ = v_isSharedCheck_1743_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1734_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1743_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1739_; lean_object* v___x_1741_; 
v___x_1739_ = lean_apply_1(v_f_1729_, v_a_1735_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 0, v___x_1739_);
v___x_1741_ = v___x_1737_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1752_; 
v_a_1744_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1746_ = v___x_1734_;
v_isShared_1747_ = v_isSharedCheck_1752_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1734_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1752_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1748_; lean_object* v___x_1750_; 
v___x_1748_ = lean_task_map(v_f_1729_, v_a_1744_, v___x_1732_, v___x_1733_);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 0, v___x_1748_);
v___x_1750_ = v___x_1746_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1748_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_instFunctor___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1729_ = stack[2].m_obj;
lean_object* v_self_1730_ = stack[3].m_obj;
lean_object* v_res_1753_;
v_res_1753_ = l_Std_Async_BaseAsync_instFunctor___lam__0(lean_box(0), lean_box(0), v_f_1729_, v_self_1730_);
stack->m_obj
 = v_res_1753_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instFunctor___lam__0___boxed(lean_object* v_00_u03b1_1754_, lean_object* v_00_u03b2_1755_, lean_object* v_f_1756_, lean_object* v_self_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Std_Async_BaseAsync_instFunctor___lam__0(v_00_u03b1_1754_, v_00_u03b2_1755_, v_f_1756_, v_self_1757_);
return v_res_1759_;
}
}
lean_object* l_Std_Async_BaseAsync_instFunctor___lam__1(lean_object* v___f_1760_, lean_object* v_00_u03b1_1761_, lean_object* v_00_u03b2_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_1766_, 0, lean_box(0));
lean_closure_set(v___x_1766_, 1, lean_box(0));
lean_closure_set(v___x_1766_, 2, v___y_1763_);
v___x_1767_ = lean_apply_5(v___f_1760_, lean_box(0), lean_box(0), v___x_1766_, v___y_1764_, lean_box(0));
return v___x_1767_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_instFunctor___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1760_ = stack[0].m_obj;
lean_object* v___y_1763_ = stack[3].m_obj;
lean_object* v___y_1764_ = stack[4].m_obj;
lean_object* v_res_1768_;
v_res_1768_ = l_Std_Async_BaseAsync_instFunctor___lam__1(v___f_1760_, lean_box(0), lean_box(0), v___y_1763_, v___y_1764_);
stack->m_obj
 = v_res_1768_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instFunctor___lam__1___boxed(lean_object* v___f_1769_, lean_object* v_00_u03b1_1770_, lean_object* v_00_u03b2_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Std_Async_BaseAsync_instFunctor___lam__1(v___f_1769_, v_00_u03b1_1770_, v_00_u03b2_1771_, v___y_1772_, v___y_1773_);
return v_res_1775_;
}
}
lean_object* l_Std_Async_BaseAsync_instMonad___lam__0(lean_object* v_x_1783_, lean_object* v_y_1784_){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; lean_object* v___x_1789_; 
v___x_1786_ = lean_box(0);
v___x_1787_ = lean_unsigned_to_nat(0u);
v___x_1788_ = 0;
v___x_1789_ = lean_apply_2(v_x_1783_, v___x_1786_, lean_box(0));
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1798_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1792_ = v___x_1789_;
v_isShared_1793_ = v_isSharedCheck_1798_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1789_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1798_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1794_; lean_object* v___x_1796_; 
v___x_1794_ = lean_apply_1(v_y_1784_, v_a_1790_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 0, v___x_1794_);
v___x_1796_ = v___x_1792_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1794_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1807_; 
v_a_1799_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1801_ = v___x_1789_;
v_isShared_1802_ = v_isSharedCheck_1807_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1789_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1807_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___x_1803_ = lean_task_map(v_y_1784_, v_a_1799_, v___x_1787_, v___x_1788_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v___x_1803_);
v___x_1805_ = v___x_1801_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_instMonad___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1783_ = stack[0].m_obj;
lean_object* v_y_1784_ = stack[1].m_obj;
lean_object* v_res_1808_;
v_res_1808_ = l_Std_Async_BaseAsync_instMonad___lam__0(v_x_1783_, v_y_1784_);
stack->m_obj
 = v_res_1808_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__0___boxed(lean_object* v_x_1809_, lean_object* v_y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Std_Async_BaseAsync_instMonad___lam__0(v_x_1809_, v_y_1810_);
return v_res_1812_;
}
}
lean_object* l_Std_Async_BaseAsync_instMonad___lam__1(lean_object* v_00_u03b1_1813_, lean_object* v_00_u03b2_1814_, lean_object* v_f_1815_, lean_object* v_x_1816_){
_start:
{
lean_object* v___f_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___f_1818_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_instMonad___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1818_, 0, v_x_1816_);
v___x_1819_ = lean_unsigned_to_nat(0u);
v___x_1820_ = 0;
v___x_1821_ = lean_apply_1(v_f_1815_, lean_box(0));
v___x_1822_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_1819_, v___x_1820_, v___x_1821_, v___f_1818_);
return v___x_1822_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_instMonad___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1815_ = stack[2].m_obj;
lean_object* v_x_1816_ = stack[3].m_obj;
lean_object* v_res_1823_;
v_res_1823_ = l_Std_Async_BaseAsync_instMonad___lam__1(lean_box(0), lean_box(0), v_f_1815_, v_x_1816_);
stack->m_obj
 = v_res_1823_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__1___boxed(lean_object* v_00_u03b1_1824_, lean_object* v_00_u03b2_1825_, lean_object* v_f_1826_, lean_object* v_x_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_Std_Async_BaseAsync_instMonad___lam__1(v_00_u03b1_1824_, v_00_u03b2_1825_, v_f_1826_, v_x_1827_);
return v_res_1829_;
}
}
lean_object* l_Std_Async_BaseAsync_instMonad___lam__2(lean_object* v_00_u03b1_1830_, lean_object* v_00_u03b2_1831_, lean_object* v_self_1832_, lean_object* v_f_1833_){
_start:
{
lean_object* v___x_1835_; uint8_t v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1835_ = lean_unsigned_to_nat(0u);
v___x_1836_ = 0;
v___x_1837_ = lean_apply_1(v_self_1832_, lean_box(0));
v___x_1838_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_1835_, v___x_1836_, v___x_1837_, v_f_1833_);
return v___x_1838_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_instMonad___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1832_ = stack[2].m_obj;
lean_object* v_f_1833_ = stack[3].m_obj;
lean_object* v_res_1839_;
v_res_1839_ = l_Std_Async_BaseAsync_instMonad___lam__2(lean_box(0), lean_box(0), v_self_1832_, v_f_1833_);
stack->m_obj
 = v_res_1839_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__2___boxed(lean_object* v_00_u03b1_1840_, lean_object* v_00_u03b2_1841_, lean_object* v_self_1842_, lean_object* v_f_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_Std_Async_BaseAsync_instMonad___lam__2(v_00_u03b1_1840_, v_00_u03b2_1841_, v_self_1842_, v_f_1843_);
return v_res_1845_;
}
}
lean_object* l_Std_Async_BaseAsync_instMonad___lam__3(lean_object* v_a_1846_, lean_object* v_x_1847_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1849_, 0, v_a_1846_);
return v___x_1849_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_instMonad___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1846_ = stack[0].m_obj;
lean_object* v_x_1847_ = stack[1].m_obj;
lean_object* v_res_1850_;
v_res_1850_ = l_Std_Async_BaseAsync_instMonad___lam__3(v_a_1846_, v_x_1847_);
stack->m_obj
 = v_res_1850_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__3___boxed(lean_object* v_a_1851_, lean_object* v_x_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Std_Async_BaseAsync_instMonad___lam__3(v_a_1851_, v_x_1852_);
lean_dec(v_x_1852_);
return v_res_1854_;
}
}
lean_object* l_Std_Async_BaseAsync_instMonad___lam__4(lean_object* v_y_1855_, lean_object* v___f_1856_, lean_object* v_a_1857_){
_start:
{
lean_object* v___f_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___f_1859_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_instMonad___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1859_, 0, v_a_1857_);
v___x_1860_ = lean_box(0);
v___x_1861_ = lean_apply_1(v_y_1855_, v___x_1860_);
v___x_1862_ = lean_apply_5(v___f_1856_, lean_box(0), lean_box(0), v___x_1861_, v___f_1859_, lean_box(0));
return v___x_1862_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_instMonad___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_y_1855_ = stack[0].m_obj;
lean_object* v___f_1856_ = stack[1].m_obj;
lean_object* v_a_1857_ = stack[2].m_obj;
lean_object* v_res_1863_;
v_res_1863_ = l_Std_Async_BaseAsync_instMonad___lam__4(v_y_1855_, v___f_1856_, v_a_1857_);
stack->m_obj
 = v_res_1863_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__4___boxed(lean_object* v_y_1864_, lean_object* v___f_1865_, lean_object* v_a_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Std_Async_BaseAsync_instMonad___lam__4(v_y_1864_, v___f_1865_, v_a_1866_);
return v_res_1868_;
}
}
lean_object* l_Std_Async_BaseAsync_instMonad___lam__5(lean_object* v___f_1869_, lean_object* v_00_u03b1_1870_, lean_object* v_00_u03b2_1871_, lean_object* v_x_1872_, lean_object* v_y_1873_){
_start:
{
lean_object* v___f_1875_; lean_object* v___x_1876_; 
lean_inc_ref(v___f_1869_);
v___f_1875_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_instMonad___lam__4___boxed), 4, 2);
lean_closure_set(v___f_1875_, 0, v_y_1873_);
lean_closure_set(v___f_1875_, 1, v___f_1869_);
v___x_1876_ = lean_apply_5(v___f_1869_, lean_box(0), lean_box(0), v_x_1872_, v___f_1875_, lean_box(0));
return v___x_1876_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_instMonad___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1869_ = stack[0].m_obj;
lean_object* v_x_1872_ = stack[3].m_obj;
lean_object* v_y_1873_ = stack[4].m_obj;
lean_object* v_res_1877_;
v_res_1877_ = l_Std_Async_BaseAsync_instMonad___lam__5(v___f_1869_, lean_box(0), lean_box(0), v_x_1872_, v_y_1873_);
stack->m_obj
 = v_res_1877_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__5___boxed(lean_object* v___f_1878_, lean_object* v_00_u03b1_1879_, lean_object* v_00_u03b2_1880_, lean_object* v_x_1881_, lean_object* v_y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Std_Async_BaseAsync_instMonad___lam__5(v___f_1878_, v_00_u03b1_1879_, v_00_u03b2_1880_, v_x_1881_, v_y_1882_);
return v_res_1884_;
}
}
lean_object* l_Std_Async_BaseAsync_instMonad___lam__6(lean_object* v_y_1885_, lean_object* v_x_1886_){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = lean_box(0);
v___x_1889_ = lean_apply_2(v_y_1885_, v___x_1888_, lean_box(0));
return v___x_1889_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_instMonad___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_y_1885_ = stack[0].m_obj;
lean_object* v_x_1886_ = stack[1].m_obj;
lean_object* v_res_1890_;
v_res_1890_ = l_Std_Async_BaseAsync_instMonad___lam__6(v_y_1885_, v_x_1886_);
stack->m_obj
 = v_res_1890_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__6___boxed(lean_object* v_y_1891_, lean_object* v_x_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Std_Async_BaseAsync_instMonad___lam__6(v_y_1891_, v_x_1892_);
lean_dec(v_x_1892_);
return v_res_1894_;
}
}
lean_object* l_Std_Async_BaseAsync_instMonad___lam__7(lean_object* v_00_u03b1_1895_, lean_object* v_00_u03b2_1896_, lean_object* v_x_1897_, lean_object* v_y_1898_){
_start:
{
lean_object* v___f_1900_; lean_object* v___x_1901_; uint8_t v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___f_1900_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_instMonad___lam__6___boxed), 3, 1);
lean_closure_set(v___f_1900_, 0, v_y_1898_);
v___x_1901_ = lean_unsigned_to_nat(0u);
v___x_1902_ = 0;
v___x_1903_ = lean_apply_1(v_x_1897_, lean_box(0));
v___x_1904_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_1901_, v___x_1902_, v___x_1903_, v___f_1900_);
return v___x_1904_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_instMonad___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1897_ = stack[2].m_obj;
lean_object* v_y_1898_ = stack[3].m_obj;
lean_object* v_res_1905_;
v_res_1905_ = l_Std_Async_BaseAsync_instMonad___lam__7(lean_box(0), lean_box(0), v_x_1897_, v_y_1898_);
stack->m_obj
 = v_res_1905_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__7___boxed(lean_object* v_00_u03b1_1906_, lean_object* v_00_u03b2_1907_, lean_object* v_x_1908_, lean_object* v_y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_Std_Async_BaseAsync_instMonad___lam__7(v_00_u03b1_1906_, v_00_u03b2_1907_, v_x_1908_, v_y_1909_);
return v_res_1911_;
}
}
lean_object* l_Std_Async_BaseAsync_instMonadAsyncTask___lam__1(lean_object* v___f_1932_, lean_object* v_00_u03b1_1933_, lean_object* v_t_1934_, lean_object* v_prio_1935_){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; uint8_t v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1937_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1937_, 0, lean_box(0));
lean_closure_set(v___x_1937_, 1, v_t_1934_);
v___x_1938_ = lean_io_as_task(v___x_1937_, v_prio_1935_);
v___x_1939_ = lean_unsigned_to_nat(0u);
v___x_1940_ = 1;
v___x_1941_ = lean_task_bind(v___x_1938_, v___f_1932_, v___x_1939_, v___x_1940_);
v___x_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
return v___x_1942_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_instMonadAsyncTask___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1932_ = stack[0].m_obj;
lean_object* v_t_1934_ = stack[2].m_obj;
lean_object* v_prio_1935_ = stack[3].m_obj;
lean_object* v_res_1943_;
v_res_1943_ = l_Std_Async_BaseAsync_instMonadAsyncTask___lam__1(v___f_1932_, lean_box(0), v_t_1934_, v_prio_1935_);
stack->m_obj
 = v_res_1943_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadAsyncTask___lam__1___boxed(lean_object* v___f_1944_, lean_object* v_00_u03b1_1945_, lean_object* v_t_1946_, lean_object* v_prio_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Std_Async_BaseAsync_instMonadAsyncTask___lam__1(v___f_1944_, v_00_u03b1_1945_, v_t_1946_, v_prio_1947_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instInhabited___redArg(lean_object* v_inst_1953_){
_start:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1954_, 0, v_inst_1953_);
v___x_1955_ = lean_alloc_closure((void*)(l_instMonadBaseIO___aux__5___boxed), 3, 2);
lean_closure_set(v___x_1955_, 0, lean_box(0));
lean_closure_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_mk___boxed), 3, 2);
lean_closure_set(v___x_1956_, 0, lean_box(0));
lean_closure_set(v___x_1956_, 1, v___x_1955_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instInhabited(lean_object* v_00_u03b1_1957_, lean_object* v_inst_1958_){
_start:
{
lean_object* v___x_1959_; 
v___x_1959_ = l_Std_Async_BaseAsync_instInhabited___redArg(v_inst_1958_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadFinally___lam__0(lean_object* v_res_1960_, lean_object* v_snd_1961_){
_start:
{
lean_object* v___x_1962_; 
v___x_1962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1962_, 0, v_res_1960_);
lean_ctor_set(v___x_1962_, 1, v_snd_1961_);
return v___x_1962_;
}
}
lean_object* l_Std_Async_BaseAsync_instMonadFinally___lam__1(lean_object* v_f_1963_, lean_object* v_res_1964_){
_start:
{
lean_object* v___f_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; lean_object* v___x_1970_; 
lean_inc_n(v_res_1964_, 2);
v___f_1966_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_instMonadFinally___lam__0), 2, 1);
lean_closure_set(v___f_1966_, 0, v_res_1964_);
v___x_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1967_, 0, v_res_1964_);
v___x_1968_ = lean_unsigned_to_nat(0u);
v___x_1969_ = 0;
v___x_1970_ = lean_apply_2(v_f_1963_, v___x_1967_, lean_box(0));
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1979_; 
lean_dec_ref(v___f_1966_);
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1973_ = v___x_1970_;
v_isShared_1974_ = v_isSharedCheck_1979_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1970_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1979_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1975_; lean_object* v___x_1977_; 
v___x_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1975_, 0, v_res_1964_);
lean_ctor_set(v___x_1975_, 1, v_a_1971_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v___x_1975_);
v___x_1977_ = v___x_1973_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1988_; 
lean_dec(v_res_1964_);
v_a_1980_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1982_ = v___x_1970_;
v_isShared_1983_ = v_isSharedCheck_1988_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1970_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1988_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1984_; lean_object* v___x_1986_; 
v___x_1984_ = lean_task_map(v___f_1966_, v_a_1980_, v___x_1968_, v___x_1969_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_1984_);
v___x_1986_ = v___x_1982_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1984_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_instMonadFinally___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1963_ = stack[0].m_obj;
lean_object* v_res_1964_ = stack[1].m_obj;
lean_object* v_res_1989_;
v_res_1989_ = l_Std_Async_BaseAsync_instMonadFinally___lam__1(v_f_1963_, v_res_1964_);
stack->m_obj
 = v_res_1989_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadFinally___lam__1___boxed(lean_object* v_f_1990_, lean_object* v_res_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Std_Async_BaseAsync_instMonadFinally___lam__1(v_f_1990_, v_res_1991_);
return v_res_1993_;
}
}
lean_object* l_Std_Async_BaseAsync_instMonadFinally___lam__2(lean_object* v_00_u03b1_1994_, lean_object* v_00_u03b2_1995_, lean_object* v_x_1996_, lean_object* v_f_1997_){
_start:
{
lean_object* v___f_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___f_1999_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_instMonadFinally___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1999_, 0, v_f_1997_);
v___x_2000_ = lean_unsigned_to_nat(0u);
v___x_2001_ = 0;
v___x_2002_ = lean_apply_1(v_x_1996_, lean_box(0));
v___x_2003_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2000_, v___x_2001_, v___x_2002_, v___f_1999_);
return v___x_2003_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_instMonadFinally___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1996_ = stack[2].m_obj;
lean_object* v_f_1997_ = stack[3].m_obj;
lean_object* v_res_2004_;
v_res_2004_ = l_Std_Async_BaseAsync_instMonadFinally___lam__2(lean_box(0), lean_box(0), v_x_1996_, v_f_1997_);
stack->m_obj
 = v_res_2004_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadFinally___lam__2___boxed(lean_object* v_00_u03b1_2005_, lean_object* v_00_u03b2_2006_, lean_object* v_x_2007_, lean_object* v_f_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Std_Async_BaseAsync_instMonadFinally___lam__2(v_00_u03b1_2005_, v_00_u03b2_2006_, v_x_2007_, v_f_2008_);
return v_res_2010_;
}
}
lean_object* l_Std_Async_BaseAsync_ofExcept___redArg(lean_object* v_except_2013_){
_start:
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
v_a_2015_ = lean_ctor_get(v_except_2013_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_except_2013_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v_except_2013_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v_except_2013_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set_tag(v___x_2017_, 0);
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_ofExcept___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_except_2013_ = stack[0].m_obj;
lean_object* v_res_2023_;
v_res_2023_ = l_Std_Async_BaseAsync_ofExcept___redArg(v_except_2013_);
stack->m_obj
 = v_res_2023_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofExcept___redArg___boxed(lean_object* v_except_2024_, lean_object* v_a_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Std_Async_BaseAsync_ofExcept___redArg(v_except_2024_);
return v_res_2026_;
}
}
lean_object* l_Std_Async_BaseAsync_ofExcept(lean_object* v_00_u03b1_2027_, lean_object* v_except_2028_){
_start:
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
v_a_2030_ = lean_ctor_get(v_except_2028_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_except_2028_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v_except_2028_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v_except_2028_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
lean_ctor_set_tag(v___x_2032_, 0);
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_ofExcept_0interp(lean_interpreter_value* stack)
{
lean_object* v_except_2028_ = stack[1].m_obj;
lean_object* v_res_2038_;
v_res_2038_ = l_Std_Async_BaseAsync_ofExcept(lean_box(0), v_except_2028_);
stack->m_obj
 = v_res_2038_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofExcept___boxed(lean_object* v_00_u03b1_2039_, lean_object* v_except_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_Std_Async_BaseAsync_ofExcept(v_00_u03b1_2039_, v_except_2040_);
return v_res_2042_;
}
}
lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__1(lean_object* v_resultX_2043_, lean_object* v_resultY_2044_){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2046_, 0, v_resultX_2043_);
lean_ctor_set(v___x_2046_, 1, v_resultY_2044_);
v___x_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_concurrently___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_resultX_2043_ = stack[0].m_obj;
lean_object* v_resultY_2044_ = stack[1].m_obj;
lean_object* v_res_2048_;
v_res_2048_ = l_Std_Async_BaseAsync_concurrently___redArg___lam__1(v_resultX_2043_, v_resultY_2044_);
stack->m_obj
 = v_res_2048_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__1___boxed(lean_object* v_resultX_2049_, lean_object* v_resultY_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Std_Async_BaseAsync_concurrently___redArg___lam__1(v_resultX_2049_, v_resultY_2050_);
return v_res_2052_;
}
}
lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__0(lean_object* v_taskY_2053_, lean_object* v_resultX_2054_){
_start:
{
lean_object* v___f_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___f_2056_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrently___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2056_, 0, v_resultX_2054_);
v___x_2057_ = lean_unsigned_to_nat(0u);
v___x_2058_ = 0;
v___x_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2059_, 0, v_taskY_2053_);
v___x_2060_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2057_, v___x_2058_, v___x_2059_, v___f_2056_);
return v___x_2060_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_concurrently___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_taskY_2053_ = stack[0].m_obj;
lean_object* v_resultX_2054_ = stack[1].m_obj;
lean_object* v_res_2061_;
v_res_2061_ = l_Std_Async_BaseAsync_concurrently___redArg___lam__0(v_taskY_2053_, v_resultX_2054_);
stack->m_obj
 = v_res_2061_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__0___boxed(lean_object* v_taskY_2062_, lean_object* v_resultX_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Std_Async_BaseAsync_concurrently___redArg___lam__0(v_taskY_2062_, v_resultX_2063_);
return v_res_2065_;
}
}
lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__2(lean_object* v_taskX_2066_, lean_object* v_taskY_2067_){
_start:
{
lean_object* v___f_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___f_2069_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrently___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2069_, 0, v_taskY_2067_);
v___x_2070_ = lean_unsigned_to_nat(0u);
v___x_2071_ = 0;
v___x_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2072_, 0, v_taskX_2066_);
v___x_2073_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2070_, v___x_2071_, v___x_2072_, v___f_2069_);
return v___x_2073_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_concurrently___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_taskX_2066_ = stack[0].m_obj;
lean_object* v_taskY_2067_ = stack[1].m_obj;
lean_object* v_res_2074_;
v_res_2074_ = l_Std_Async_BaseAsync_concurrently___redArg___lam__2(v_taskX_2066_, v_taskY_2067_);
stack->m_obj
 = v_res_2074_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__2___boxed(lean_object* v_taskX_2075_, lean_object* v_taskY_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Std_Async_BaseAsync_concurrently___redArg___lam__2(v_taskX_2075_, v_taskY_2076_);
return v_res_2078_;
}
}
lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__3(lean_object* v_y_2079_, lean_object* v_prio_2080_, lean_object* v___f_2081_, lean_object* v_taskX_2082_){
_start:
{
lean_object* v___f_2084_; lean_object* v___x_2085_; uint8_t v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___f_2084_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrently___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2084_, 0, v_taskX_2082_);
v___x_2085_ = lean_unsigned_to_nat(0u);
v___x_2086_ = 0;
v___x_2087_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2087_, 0, lean_box(0));
lean_closure_set(v___x_2087_, 1, v_y_2079_);
v___x_2088_ = lean_io_as_task(v___x_2087_, v_prio_2080_);
v___x_2089_ = 1;
v___x_2090_ = lean_task_bind(v___x_2088_, v___f_2081_, v___x_2085_, v___x_2089_);
v___x_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
v___x_2092_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2085_, v___x_2086_, v___x_2091_, v___f_2084_);
return v___x_2092_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_concurrently___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_y_2079_ = stack[0].m_obj;
lean_object* v_prio_2080_ = stack[1].m_obj;
lean_object* v___f_2081_ = stack[2].m_obj;
lean_object* v_taskX_2082_ = stack[3].m_obj;
lean_object* v_res_2093_;
v_res_2093_ = l_Std_Async_BaseAsync_concurrently___redArg___lam__3(v_y_2079_, v_prio_2080_, v___f_2081_, v_taskX_2082_);
stack->m_obj
 = v_res_2093_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__3___boxed(lean_object* v_y_2094_, lean_object* v_prio_2095_, lean_object* v___f_2096_, lean_object* v_taskX_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_Std_Async_BaseAsync_concurrently___redArg___lam__3(v_y_2094_, v_prio_2095_, v___f_2096_, v_taskX_2097_);
return v_res_2099_;
}
}
lean_object* l_Std_Async_BaseAsync_concurrently___redArg(lean_object* v_x_2100_, lean_object* v_y_2101_, lean_object* v_prio_2102_){
_start:
{
lean_object* v___f_2104_; lean_object* v___f_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; uint8_t v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___f_2104_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
lean_inc(v_prio_2102_);
v___f_2105_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrently___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2105_, 0, v_y_2101_);
lean_closure_set(v___f_2105_, 1, v_prio_2102_);
lean_closure_set(v___f_2105_, 2, v___f_2104_);
v___x_2106_ = lean_unsigned_to_nat(0u);
v___x_2107_ = 0;
v___x_2108_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2108_, 0, lean_box(0));
lean_closure_set(v___x_2108_, 1, v_x_2100_);
v___x_2109_ = lean_io_as_task(v___x_2108_, v_prio_2102_);
v___x_2110_ = 1;
v___x_2111_ = lean_task_bind(v___x_2109_, v___f_2104_, v___x_2106_, v___x_2110_);
v___x_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
v___x_2113_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2106_, v___x_2107_, v___x_2112_, v___f_2105_);
return v___x_2113_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_concurrently___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2100_ = stack[0].m_obj;
lean_object* v_y_2101_ = stack[1].m_obj;
lean_object* v_prio_2102_ = stack[2].m_obj;
lean_object* v_res_2114_;
v_res_2114_ = l_Std_Async_BaseAsync_concurrently___redArg(v_x_2100_, v_y_2101_, v_prio_2102_);
stack->m_obj
 = v_res_2114_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___boxed(lean_object* v_x_2115_, lean_object* v_y_2116_, lean_object* v_prio_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l_Std_Async_BaseAsync_concurrently___redArg(v_x_2115_, v_y_2116_, v_prio_2117_);
return v_res_2119_;
}
}
lean_object* l_Std_Async_BaseAsync_concurrently(lean_object* v_00_u03b1_2120_, lean_object* v_00_u03b2_2121_, lean_object* v_x_2122_, lean_object* v_y_2123_, lean_object* v_prio_2124_){
_start:
{
lean_object* v___f_2126_; lean_object* v___f_2127_; lean_object* v___x_2128_; uint8_t v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; uint8_t v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___f_2126_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
lean_inc(v_prio_2124_);
v___f_2127_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrently___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2127_, 0, v_y_2123_);
lean_closure_set(v___f_2127_, 1, v_prio_2124_);
lean_closure_set(v___f_2127_, 2, v___f_2126_);
v___x_2128_ = lean_unsigned_to_nat(0u);
v___x_2129_ = 0;
v___x_2130_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2130_, 0, lean_box(0));
lean_closure_set(v___x_2130_, 1, v_x_2122_);
v___x_2131_ = lean_io_as_task(v___x_2130_, v_prio_2124_);
v___x_2132_ = 1;
v___x_2133_ = lean_task_bind(v___x_2131_, v___f_2126_, v___x_2128_, v___x_2132_);
v___x_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
v___x_2135_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2128_, v___x_2129_, v___x_2134_, v___f_2127_);
return v___x_2135_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_concurrently_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2122_ = stack[2].m_obj;
lean_object* v_y_2123_ = stack[3].m_obj;
lean_object* v_prio_2124_ = stack[4].m_obj;
lean_object* v_res_2136_;
v_res_2136_ = l_Std_Async_BaseAsync_concurrently(lean_box(0), lean_box(0), v_x_2122_, v_y_2123_, v_prio_2124_);
stack->m_obj
 = v_res_2136_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___boxed(lean_object* v_00_u03b1_2137_, lean_object* v_00_u03b2_2138_, lean_object* v_x_2139_, lean_object* v_y_2140_, lean_object* v_prio_2141_, lean_object* v_a_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_Std_Async_BaseAsync_concurrently(v_00_u03b1_2137_, v_00_u03b2_2138_, v_x_2139_, v_y_2140_, v_prio_2141_);
return v_res_2143_;
}
}
lean_object* l_Std_Async_BaseAsync_race___redArg___lam__2(lean_object* v_promise_2144_, lean_object* v_value_2145_){
_start:
{
lean_object* v___x_2147_; 
v___x_2147_ = lean_io_promise_resolve(v_value_2145_, v_promise_2144_);
return v___x_2147_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_race___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_promise_2144_ = stack[0].m_obj;
lean_object* v_value_2145_ = stack[1].m_obj;
lean_object* v_res_2148_;
v_res_2148_ = l_Std_Async_BaseAsync_race___redArg___lam__2(v_promise_2144_, v_value_2145_);
stack->m_obj
 = v_res_2148_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__2___boxed(lean_object* v_promise_2149_, lean_object* v_value_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Std_Async_BaseAsync_race___redArg___lam__2(v_promise_2149_, v_value_2150_);
lean_dec(v_promise_2149_);
return v_res_2152_;
}
}
lean_object* l_Std_Async_BaseAsync_race___redArg___lam__0(lean_object* v_promise_2153_, lean_object* v_____r_2154_){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = l_IO_Promise_result_x21___redArg(v_promise_2153_);
v___x_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_race___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_promise_2153_ = stack[0].m_obj;
lean_object* v_____r_2154_ = stack[1].m_obj;
lean_object* v_res_2158_;
v_res_2158_ = l_Std_Async_BaseAsync_race___redArg___lam__0(v_promise_2153_, v_____r_2154_);
stack->m_obj
 = v_res_2158_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__0___boxed(lean_object* v_promise_2159_, lean_object* v_____r_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Std_Async_BaseAsync_race___redArg___lam__0(v_promise_2159_, v_____r_2160_);
lean_dec(v_promise_2159_);
return v_res_2162_;
}
}
lean_object* l_Std_Async_BaseAsync_race___redArg___lam__1(lean_object* v_task_u2082_2163_, lean_object* v___x_2164_, lean_object* v___x_2165_, uint8_t v___x_2166_, lean_object* v___f_2167_, lean_object* v_____r_2168_){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
lean_inc(v___x_2165_);
v___x_2170_ = l_BaseIO_chainTask___redArg(v_task_u2082_2163_, v___x_2164_, v___x_2165_, v___x_2166_);
v___x_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
v___x_2172_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2165_, v___x_2166_, v___x_2171_, v___f_2167_);
return v___x_2172_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_race___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_task_u2082_2163_ = stack[0].m_obj;
lean_object* v___x_2164_ = stack[1].m_obj;
lean_object* v___x_2165_ = stack[2].m_obj;
uint8_t v___x_2166_ = stack[3].m_num;
lean_object* v___f_2167_ = stack[4].m_obj;
lean_object* v_____r_2168_ = stack[5].m_obj;
lean_object* v_res_2173_;
v_res_2173_ = l_Std_Async_BaseAsync_race___redArg___lam__1(v_task_u2082_2163_, v___x_2164_, v___x_2165_, v___x_2166_, v___f_2167_, v_____r_2168_);
stack->m_obj
 = v_res_2173_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__1___boxed(lean_object* v_task_u2082_2174_, lean_object* v___x_2175_, lean_object* v___x_2176_, lean_object* v___x_2177_, lean_object* v___f_2178_, lean_object* v_____r_2179_, lean_object* v___y_2180_){
_start:
{
uint8_t v___x_633__boxed_2181_; lean_object* v_res_2182_; 
v___x_633__boxed_2181_ = lean_unbox(v___x_2177_);
v_res_2182_ = l_Std_Async_BaseAsync_race___redArg___lam__1(v_task_u2082_2174_, v___x_2175_, v___x_2176_, v___x_633__boxed_2181_, v___f_2178_, v_____r_2179_);
return v_res_2182_;
}
}
lean_object* l_Std_Async_BaseAsync_race___redArg___lam__3(lean_object* v___f_2183_, lean_object* v___f_2184_, lean_object* v___f_2185_, lean_object* v_task_u2081_2186_, lean_object* v_task_u2082_2187_){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; lean_object* v___x_2193_; lean_object* v___f_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2189_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_2189_, 0, lean_box(0));
lean_closure_set(v___x_2189_, 1, lean_box(0));
lean_closure_set(v___x_2189_, 2, v___f_2183_);
lean_closure_set(v___x_2189_, 3, lean_box(0));
v___x_2190_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_2190_, 0, lean_box(0));
lean_closure_set(v___x_2190_, 1, lean_box(0));
lean_closure_set(v___x_2190_, 2, lean_box(0));
lean_closure_set(v___x_2190_, 3, v___x_2189_);
lean_closure_set(v___x_2190_, 4, v___f_2184_);
v___x_2191_ = lean_unsigned_to_nat(0u);
v___x_2192_ = 0;
v___x_2193_ = lean_box(v___x_2192_);
lean_inc_ref(v___x_2190_);
v___f_2194_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2194_, 0, v_task_u2082_2187_);
lean_closure_set(v___f_2194_, 1, v___x_2190_);
lean_closure_set(v___f_2194_, 2, v___x_2191_);
lean_closure_set(v___f_2194_, 3, v___x_2193_);
lean_closure_set(v___f_2194_, 4, v___f_2185_);
v___x_2195_ = l_BaseIO_chainTask___redArg(v_task_u2081_2186_, v___x_2190_, v___x_2191_, v___x_2192_);
v___x_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
v___x_2197_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2191_, v___x_2192_, v___x_2196_, v___f_2194_);
return v___x_2197_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_race___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2183_ = stack[0].m_obj;
lean_object* v___f_2184_ = stack[1].m_obj;
lean_object* v___f_2185_ = stack[2].m_obj;
lean_object* v_task_u2081_2186_ = stack[3].m_obj;
lean_object* v_task_u2082_2187_ = stack[4].m_obj;
lean_object* v_res_2198_;
v_res_2198_ = l_Std_Async_BaseAsync_race___redArg___lam__3(v___f_2183_, v___f_2184_, v___f_2185_, v_task_u2081_2186_, v_task_u2082_2187_);
stack->m_obj
 = v_res_2198_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__3___boxed(lean_object* v___f_2199_, lean_object* v___f_2200_, lean_object* v___f_2201_, lean_object* v_task_u2081_2202_, lean_object* v_task_u2082_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l_Std_Async_BaseAsync_race___redArg___lam__3(v___f_2199_, v___f_2200_, v___f_2201_, v_task_u2081_2202_, v_task_u2082_2203_);
return v_res_2205_;
}
}
lean_object* l_Std_Async_BaseAsync_race___redArg___lam__4(lean_object* v___f_2206_, lean_object* v___f_2207_, lean_object* v___f_2208_, lean_object* v_y_2209_, lean_object* v_prio_2210_, lean_object* v___f_2211_, lean_object* v_task_u2081_2212_){
_start:
{
lean_object* v___f_2214_; lean_object* v___x_2215_; uint8_t v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; uint8_t v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___f_2214_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_2214_, 0, v___f_2206_);
lean_closure_set(v___f_2214_, 1, v___f_2207_);
lean_closure_set(v___f_2214_, 2, v___f_2208_);
lean_closure_set(v___f_2214_, 3, v_task_u2081_2212_);
v___x_2215_ = lean_unsigned_to_nat(0u);
v___x_2216_ = 0;
v___x_2217_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2217_, 0, lean_box(0));
lean_closure_set(v___x_2217_, 1, v_y_2209_);
v___x_2218_ = lean_io_as_task(v___x_2217_, v_prio_2210_);
v___x_2219_ = 1;
v___x_2220_ = lean_task_bind(v___x_2218_, v___f_2211_, v___x_2215_, v___x_2219_);
v___x_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
v___x_2222_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2215_, v___x_2216_, v___x_2221_, v___f_2214_);
return v___x_2222_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_race___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2206_ = stack[0].m_obj;
lean_object* v___f_2207_ = stack[1].m_obj;
lean_object* v___f_2208_ = stack[2].m_obj;
lean_object* v_y_2209_ = stack[3].m_obj;
lean_object* v_prio_2210_ = stack[4].m_obj;
lean_object* v___f_2211_ = stack[5].m_obj;
lean_object* v_task_u2081_2212_ = stack[6].m_obj;
lean_object* v_res_2223_;
v_res_2223_ = l_Std_Async_BaseAsync_race___redArg___lam__4(v___f_2206_, v___f_2207_, v___f_2208_, v_y_2209_, v_prio_2210_, v___f_2211_, v_task_u2081_2212_);
stack->m_obj
 = v_res_2223_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__4___boxed(lean_object* v___f_2224_, lean_object* v___f_2225_, lean_object* v___f_2226_, lean_object* v_y_2227_, lean_object* v_prio_2228_, lean_object* v___f_2229_, lean_object* v_task_u2081_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Std_Async_BaseAsync_race___redArg___lam__4(v___f_2224_, v___f_2225_, v___f_2226_, v_y_2227_, v_prio_2228_, v___f_2229_, v_task_u2081_2230_);
return v_res_2232_;
}
}
lean_object* l_Std_Async_BaseAsync_race___redArg___lam__5(lean_object* v___f_2233_, lean_object* v_y_2234_, lean_object* v_prio_2235_, lean_object* v___f_2236_, lean_object* v_x_2237_, lean_object* v___f_2238_, lean_object* v_promise_2239_){
_start:
{
lean_object* v___f_2241_; lean_object* v___f_2242_; lean_object* v___f_2243_; lean_object* v___x_2244_; uint8_t v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; uint8_t v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
lean_inc(v_promise_2239_);
v___f_2241_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2241_, 0, v_promise_2239_);
v___f_2242_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2242_, 0, v_promise_2239_);
lean_inc(v_prio_2235_);
v___f_2243_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__4___boxed), 8, 6);
lean_closure_set(v___f_2243_, 0, v___f_2233_);
lean_closure_set(v___f_2243_, 1, v___f_2241_);
lean_closure_set(v___f_2243_, 2, v___f_2242_);
lean_closure_set(v___f_2243_, 3, v_y_2234_);
lean_closure_set(v___f_2243_, 4, v_prio_2235_);
lean_closure_set(v___f_2243_, 5, v___f_2236_);
v___x_2244_ = lean_unsigned_to_nat(0u);
v___x_2245_ = 0;
v___x_2246_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2246_, 0, lean_box(0));
lean_closure_set(v___x_2246_, 1, v_x_2237_);
v___x_2247_ = lean_io_as_task(v___x_2246_, v_prio_2235_);
v___x_2248_ = 1;
v___x_2249_ = lean_task_bind(v___x_2247_, v___f_2238_, v___x_2244_, v___x_2248_);
v___x_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
v___x_2251_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2244_, v___x_2245_, v___x_2250_, v___f_2243_);
return v___x_2251_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_race___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2233_ = stack[0].m_obj;
lean_object* v_y_2234_ = stack[1].m_obj;
lean_object* v_prio_2235_ = stack[2].m_obj;
lean_object* v___f_2236_ = stack[3].m_obj;
lean_object* v_x_2237_ = stack[4].m_obj;
lean_object* v___f_2238_ = stack[5].m_obj;
lean_object* v_promise_2239_ = stack[6].m_obj;
lean_object* v_res_2252_;
v_res_2252_ = l_Std_Async_BaseAsync_race___redArg___lam__5(v___f_2233_, v_y_2234_, v_prio_2235_, v___f_2236_, v_x_2237_, v___f_2238_, v_promise_2239_);
stack->m_obj
 = v_res_2252_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__5___boxed(lean_object* v___f_2253_, lean_object* v_y_2254_, lean_object* v_prio_2255_, lean_object* v___f_2256_, lean_object* v_x_2257_, lean_object* v___f_2258_, lean_object* v_promise_2259_, lean_object* v___y_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Std_Async_BaseAsync_race___redArg___lam__5(v___f_2253_, v_y_2254_, v_prio_2255_, v___f_2256_, v_x_2257_, v___f_2258_, v_promise_2259_);
return v_res_2261_;
}
}
lean_object* l_Std_Async_BaseAsync_race___redArg(lean_object* v_x_2263_, lean_object* v_y_2264_, lean_object* v_prio_2265_){
_start:
{
lean_object* v___f_2267_; lean_object* v___f_2268_; lean_object* v___f_2269_; lean_object* v___x_2270_; uint8_t v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___f_2267_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___f_2268_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_2269_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__5___boxed), 8, 6);
lean_closure_set(v___f_2269_, 0, v___f_2268_);
lean_closure_set(v___f_2269_, 1, v_y_2264_);
lean_closure_set(v___f_2269_, 2, v_prio_2265_);
lean_closure_set(v___f_2269_, 3, v___f_2267_);
lean_closure_set(v___f_2269_, 4, v_x_2263_);
lean_closure_set(v___f_2269_, 5, v___f_2267_);
v___x_2270_ = lean_unsigned_to_nat(0u);
v___x_2271_ = 0;
v___x_2272_ = lean_io_promise_new();
v___x_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
v___x_2274_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2270_, v___x_2271_, v___x_2273_, v___f_2269_);
return v___x_2274_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_race___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2263_ = stack[0].m_obj;
lean_object* v_y_2264_ = stack[1].m_obj;
lean_object* v_prio_2265_ = stack[2].m_obj;
lean_object* v_res_2275_;
v_res_2275_ = l_Std_Async_BaseAsync_race___redArg(v_x_2263_, v_y_2264_, v_prio_2265_);
stack->m_obj
 = v_res_2275_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___boxed(lean_object* v_x_2276_, lean_object* v_y_2277_, lean_object* v_prio_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Std_Async_BaseAsync_race___redArg(v_x_2276_, v_y_2277_, v_prio_2278_);
return v_res_2280_;
}
}
lean_object* l_Std_Async_BaseAsync_race(lean_object* v_00_u03b1_2281_, lean_object* v_inst_2282_, lean_object* v_x_2283_, lean_object* v_y_2284_, lean_object* v_prio_2285_){
_start:
{
lean_object* v___f_2287_; lean_object* v___f_2288_; lean_object* v___f_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___f_2287_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___f_2288_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_2289_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__5___boxed), 8, 6);
lean_closure_set(v___f_2289_, 0, v___f_2288_);
lean_closure_set(v___f_2289_, 1, v_y_2284_);
lean_closure_set(v___f_2289_, 2, v_prio_2285_);
lean_closure_set(v___f_2289_, 3, v___f_2287_);
lean_closure_set(v___f_2289_, 4, v_x_2283_);
lean_closure_set(v___f_2289_, 5, v___f_2287_);
v___x_2290_ = lean_unsigned_to_nat(0u);
v___x_2291_ = 0;
v___x_2292_ = lean_io_promise_new();
v___x_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
v___x_2294_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2290_, v___x_2291_, v___x_2293_, v___f_2289_);
return v___x_2294_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_race_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2282_ = stack[1].m_obj;
lean_object* v_x_2283_ = stack[2].m_obj;
lean_object* v_y_2284_ = stack[3].m_obj;
lean_object* v_prio_2285_ = stack[4].m_obj;
lean_object* v_res_2295_;
v_res_2295_ = l_Std_Async_BaseAsync_race(lean_box(0), v_inst_2282_, v_x_2283_, v_y_2284_, v_prio_2285_);
stack->m_obj
 = v_res_2295_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___boxed(lean_object* v_00_u03b1_2296_, lean_object* v_inst_2297_, lean_object* v_x_2298_, lean_object* v_y_2299_, lean_object* v_prio_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Std_Async_BaseAsync_race(v_00_u03b1_2296_, v_inst_2297_, v_x_2298_, v_y_2299_, v_prio_2300_);
lean_dec(v_inst_2297_);
return v_res_2302_;
}
}
lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1(lean_object* v_prio_2303_, lean_object* v___f_2304_, lean_object* v_x_2305_){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2307_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2307_, 0, lean_box(0));
lean_closure_set(v___x_2307_, 1, v_x_2305_);
v___x_2308_ = lean_io_as_task(v___x_2307_, v_prio_2303_);
v___x_2309_ = lean_unsigned_to_nat(0u);
v___x_2310_ = 1;
v___x_2311_ = lean_task_bind(v___x_2308_, v___f_2304_, v___x_2309_, v___x_2310_);
v___x_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
return v___x_2312_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_prio_2303_ = stack[0].m_obj;
lean_object* v___f_2304_ = stack[1].m_obj;
lean_object* v_x_2305_ = stack[2].m_obj;
lean_object* v_res_2313_;
v_res_2313_ = l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1(v_prio_2303_, v___f_2304_, v_x_2305_);
stack->m_obj
 = v_res_2313_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1___boxed(lean_object* v_prio_2314_, lean_object* v___f_2315_, lean_object* v_x_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1(v_prio_2314_, v___f_2315_, v_x_2316_);
return v_res_2318_;
}
}
lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0(lean_object* v___x_2320_, lean_object* v_tasks_2321_){
_start:
{
lean_object* v___x_2323_; size_t v_sz_2324_; size_t v___x_2325_; lean_object* v___x_219__overap_2326_; lean_object* v___x_2327_; 
v___x_2323_ = ((lean_object*)(l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0___closed__0));
v_sz_2324_ = lean_array_size(v_tasks_2321_);
v___x_2325_ = ((size_t)0ULL);
v___x_219__overap_2326_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2320_, v___x_2323_, v_sz_2324_, v___x_2325_, v_tasks_2321_);
v___x_2327_ = lean_apply_1(v___x_219__overap_2326_, lean_box(0));
return v___x_2327_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2320_ = stack[0].m_obj;
lean_object* v_tasks_2321_ = stack[1].m_obj;
lean_object* v_res_2328_;
v_res_2328_ = l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0(v___x_2320_, v_tasks_2321_);
stack->m_obj
 = v_res_2328_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0___boxed(lean_object* v___x_2329_, lean_object* v_tasks_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0(v___x_2329_, v_tasks_2330_);
return v_res_2332_;
}
}
lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg(lean_object* v_xs_2335_, lean_object* v_prio_2336_){
_start:
{
lean_object* v___f_2338_; lean_object* v___f_2339_; lean_object* v___x_2340_; lean_object* v___f_2341_; lean_object* v___x_2342_; uint8_t v___x_2343_; size_t v_sz_2344_; size_t v___x_2345_; lean_object* v___x_167__overap_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___f_2338_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___f_2339_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2339_, 0, v_prio_2336_);
lean_closure_set(v___f_2339_, 1, v___f_2338_);
v___x_2340_ = ((lean_object*)(l_Std_Async_BaseAsync_instMonad));
v___f_2341_ = ((lean_object*)(l_Std_Async_BaseAsync_concurrentlyAll___redArg___closed__0));
v___x_2342_ = lean_unsigned_to_nat(0u);
v___x_2343_ = 0;
v_sz_2344_ = lean_array_size(v_xs_2335_);
v___x_2345_ = ((size_t)0ULL);
v___x_167__overap_2346_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2340_, v___f_2339_, v_sz_2344_, v___x_2345_, v_xs_2335_);
v___x_2347_ = lean_apply_1(v___x_167__overap_2346_, lean_box(0));
v___x_2348_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2342_, v___x_2343_, v___x_2347_, v___f_2341_);
return v___x_2348_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_concurrentlyAll___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2335_ = stack[0].m_obj;
lean_object* v_prio_2336_ = stack[1].m_obj;
lean_object* v_res_2349_;
v_res_2349_ = l_Std_Async_BaseAsync_concurrentlyAll___redArg(v_xs_2335_, v_prio_2336_);
stack->m_obj
 = v_res_2349_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___boxed(lean_object* v_xs_2350_, lean_object* v_prio_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Std_Async_BaseAsync_concurrentlyAll___redArg(v_xs_2350_, v_prio_2351_);
return v_res_2353_;
}
}
lean_object* l_Std_Async_BaseAsync_concurrentlyAll(lean_object* v_00_u03b1_2354_, lean_object* v_xs_2355_, lean_object* v_prio_2356_){
_start:
{
lean_object* v___f_2358_; lean_object* v___f_2359_; lean_object* v___x_2360_; lean_object* v___f_2361_; lean_object* v___x_2362_; uint8_t v___x_2363_; size_t v_sz_2364_; size_t v___x_2365_; lean_object* v___x_196__overap_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___f_2358_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___f_2359_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2359_, 0, v_prio_2356_);
lean_closure_set(v___f_2359_, 1, v___f_2358_);
v___x_2360_ = ((lean_object*)(l_Std_Async_BaseAsync_instMonad));
v___f_2361_ = ((lean_object*)(l_Std_Async_BaseAsync_concurrentlyAll___redArg___closed__0));
v___x_2362_ = lean_unsigned_to_nat(0u);
v___x_2363_ = 0;
v_sz_2364_ = lean_array_size(v_xs_2355_);
v___x_2365_ = ((size_t)0ULL);
v___x_196__overap_2366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2360_, v___f_2359_, v_sz_2364_, v___x_2365_, v_xs_2355_);
v___x_2367_ = lean_apply_1(v___x_196__overap_2366_, lean_box(0));
v___x_2368_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2362_, v___x_2363_, v___x_2367_, v___f_2361_);
return v___x_2368_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_concurrentlyAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2355_ = stack[1].m_obj;
lean_object* v_prio_2356_ = stack[2].m_obj;
lean_object* v_res_2369_;
v_res_2369_ = l_Std_Async_BaseAsync_concurrentlyAll(lean_box(0), v_xs_2355_, v_prio_2356_);
stack->m_obj
 = v_res_2369_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___boxed(lean_object* v_00_u03b1_2370_, lean_object* v_xs_2371_, lean_object* v_prio_2372_, lean_object* v_a_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_Std_Async_BaseAsync_concurrentlyAll(v_00_u03b1_2370_, v_xs_2371_, v_prio_2372_);
return v_res_2374_;
}
}
lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__2(lean_object* v___f_2375_, lean_object* v___f_2376_, lean_object* v_task_u2081_2377_){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; uint8_t v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2379_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_2379_, 0, lean_box(0));
lean_closure_set(v___x_2379_, 1, lean_box(0));
lean_closure_set(v___x_2379_, 2, v___f_2375_);
lean_closure_set(v___x_2379_, 3, lean_box(0));
v___x_2380_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_2380_, 0, lean_box(0));
lean_closure_set(v___x_2380_, 1, lean_box(0));
lean_closure_set(v___x_2380_, 2, lean_box(0));
lean_closure_set(v___x_2380_, 3, v___x_2379_);
lean_closure_set(v___x_2380_, 4, v___f_2376_);
v___x_2381_ = lean_unsigned_to_nat(0u);
v___x_2382_ = 0;
v___x_2383_ = l_BaseIO_chainTask___redArg(v_task_u2081_2377_, v___x_2380_, v___x_2381_, v___x_2382_);
v___x_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2383_);
return v___x_2384_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_raceAll___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2375_ = stack[0].m_obj;
lean_object* v___f_2376_ = stack[1].m_obj;
lean_object* v_task_u2081_2377_ = stack[2].m_obj;
lean_object* v_res_2385_;
v_res_2385_ = l_Std_Async_BaseAsync_raceAll___redArg___lam__2(v___f_2375_, v___f_2376_, v_task_u2081_2377_);
stack->m_obj
 = v_res_2385_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__2___boxed(lean_object* v___f_2386_, lean_object* v___f_2387_, lean_object* v_task_u2081_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Std_Async_BaseAsync_raceAll___redArg___lam__2(v___f_2386_, v___f_2387_, v_task_u2081_2388_);
return v_res_2390_;
}
}
lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__0(lean_object* v_prio_2391_, lean_object* v___f_2392_, lean_object* v___f_2393_, lean_object* v_x_2394_){
_start:
{
lean_object* v___x_2396_; uint8_t v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; uint8_t v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2396_ = lean_unsigned_to_nat(0u);
v___x_2397_ = 0;
v___x_2398_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2398_, 0, lean_box(0));
lean_closure_set(v___x_2398_, 1, v_x_2394_);
v___x_2399_ = lean_io_as_task(v___x_2398_, v_prio_2391_);
v___x_2400_ = 1;
v___x_2401_ = lean_task_bind(v___x_2399_, v___f_2392_, v___x_2396_, v___x_2400_);
v___x_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2401_);
v___x_2403_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2396_, v___x_2397_, v___x_2402_, v___f_2393_);
return v___x_2403_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_raceAll___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_prio_2391_ = stack[0].m_obj;
lean_object* v___f_2392_ = stack[1].m_obj;
lean_object* v___f_2393_ = stack[2].m_obj;
lean_object* v_x_2394_ = stack[3].m_obj;
lean_object* v_res_2404_;
v_res_2404_ = l_Std_Async_BaseAsync_raceAll___redArg___lam__0(v_prio_2391_, v___f_2392_, v___f_2393_, v_x_2394_);
stack->m_obj
 = v_res_2404_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__0___boxed(lean_object* v_prio_2405_, lean_object* v___f_2406_, lean_object* v___f_2407_, lean_object* v_x_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Std_Async_BaseAsync_raceAll___redArg___lam__0(v_prio_2405_, v___f_2406_, v___f_2407_, v_x_2408_);
return v_res_2410_;
}
}
lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__3(lean_object* v___f_2411_, lean_object* v_prio_2412_, lean_object* v___f_2413_, lean_object* v_inst_2414_, lean_object* v_xs_2415_, lean_object* v_promise_2416_){
_start:
{
lean_object* v___f_2418_; lean_object* v___f_2419_; lean_object* v___f_2420_; lean_object* v___f_2421_; lean_object* v___x_2422_; uint8_t v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
lean_inc(v_promise_2416_);
v___f_2418_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2418_, 0, v_promise_2416_);
v___f_2419_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_raceAll___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2419_, 0, v___f_2411_);
lean_closure_set(v___f_2419_, 1, v___f_2418_);
v___f_2420_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_raceAll___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2420_, 0, v_prio_2412_);
lean_closure_set(v___f_2420_, 1, v___f_2413_);
lean_closure_set(v___f_2420_, 2, v___f_2419_);
v___f_2421_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2421_, 0, v_promise_2416_);
v___x_2422_ = lean_unsigned_to_nat(0u);
v___x_2423_ = 0;
v___x_2424_ = lean_apply_3(v_inst_2414_, v_xs_2415_, v___f_2420_, lean_box(0));
v___x_2425_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2422_, v___x_2423_, v___x_2424_, v___f_2421_);
return v___x_2425_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_raceAll___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2411_ = stack[0].m_obj;
lean_object* v_prio_2412_ = stack[1].m_obj;
lean_object* v___f_2413_ = stack[2].m_obj;
lean_object* v_inst_2414_ = stack[3].m_obj;
lean_object* v_xs_2415_ = stack[4].m_obj;
lean_object* v_promise_2416_ = stack[5].m_obj;
lean_object* v_res_2426_;
v_res_2426_ = l_Std_Async_BaseAsync_raceAll___redArg___lam__3(v___f_2411_, v_prio_2412_, v___f_2413_, v_inst_2414_, v_xs_2415_, v_promise_2416_);
stack->m_obj
 = v_res_2426_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__3___boxed(lean_object* v___f_2427_, lean_object* v_prio_2428_, lean_object* v___f_2429_, lean_object* v_inst_2430_, lean_object* v_xs_2431_, lean_object* v_promise_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l_Std_Async_BaseAsync_raceAll___redArg___lam__3(v___f_2427_, v_prio_2428_, v___f_2429_, v_inst_2430_, v_xs_2431_, v_promise_2432_);
return v_res_2434_;
}
}
lean_object* l_Std_Async_BaseAsync_raceAll___redArg(lean_object* v_inst_2435_, lean_object* v_xs_2436_, lean_object* v_prio_2437_){
_start:
{
lean_object* v___f_2439_; lean_object* v___f_2440_; lean_object* v___f_2441_; lean_object* v___x_2442_; uint8_t v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___f_2439_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___f_2440_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_2441_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_raceAll___redArg___lam__3___boxed), 7, 5);
lean_closure_set(v___f_2441_, 0, v___f_2440_);
lean_closure_set(v___f_2441_, 1, v_prio_2437_);
lean_closure_set(v___f_2441_, 2, v___f_2439_);
lean_closure_set(v___f_2441_, 3, v_inst_2435_);
lean_closure_set(v___f_2441_, 4, v_xs_2436_);
v___x_2442_ = lean_unsigned_to_nat(0u);
v___x_2443_ = 0;
v___x_2444_ = lean_io_promise_new();
v___x_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2444_);
v___x_2446_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2442_, v___x_2443_, v___x_2445_, v___f_2441_);
return v___x_2446_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_raceAll___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2435_ = stack[0].m_obj;
lean_object* v_xs_2436_ = stack[1].m_obj;
lean_object* v_prio_2437_ = stack[2].m_obj;
lean_object* v_res_2447_;
v_res_2447_ = l_Std_Async_BaseAsync_raceAll___redArg(v_inst_2435_, v_xs_2436_, v_prio_2437_);
stack->m_obj
 = v_res_2447_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___boxed(lean_object* v_inst_2448_, lean_object* v_xs_2449_, lean_object* v_prio_2450_, lean_object* v_a_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Std_Async_BaseAsync_raceAll___redArg(v_inst_2448_, v_xs_2449_, v_prio_2450_);
return v_res_2452_;
}
}
lean_object* l_Std_Async_BaseAsync_raceAll(lean_object* v_00_u03b1_2453_, lean_object* v_c_2454_, lean_object* v_inst_2455_, lean_object* v_inst_2456_, lean_object* v_xs_2457_, lean_object* v_prio_2458_){
_start:
{
lean_object* v___f_2460_; lean_object* v___f_2461_; lean_object* v___f_2462_; lean_object* v___x_2463_; uint8_t v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___f_2460_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___f_2461_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_2462_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_raceAll___redArg___lam__3___boxed), 7, 5);
lean_closure_set(v___f_2462_, 0, v___f_2461_);
lean_closure_set(v___f_2462_, 1, v_prio_2458_);
lean_closure_set(v___f_2462_, 2, v___f_2460_);
lean_closure_set(v___f_2462_, 3, v_inst_2456_);
lean_closure_set(v___f_2462_, 4, v_xs_2457_);
v___x_2463_ = lean_unsigned_to_nat(0u);
v___x_2464_ = 0;
v___x_2465_ = lean_io_promise_new();
v___x_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2465_);
v___x_2467_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2463_, v___x_2464_, v___x_2466_, v___f_2462_);
return v___x_2467_;
}
}
LEAN_EXPORT void l_Std_Async_BaseAsync_raceAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2455_ = stack[2].m_obj;
lean_object* v_inst_2456_ = stack[3].m_obj;
lean_object* v_xs_2457_ = stack[4].m_obj;
lean_object* v_prio_2458_ = stack[5].m_obj;
lean_object* v_res_2468_;
v_res_2468_ = l_Std_Async_BaseAsync_raceAll(lean_box(0), lean_box(0), v_inst_2455_, v_inst_2456_, v_xs_2457_, v_prio_2458_);
stack->m_obj
 = v_res_2468_;
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___boxed(lean_object* v_00_u03b1_2469_, lean_object* v_c_2470_, lean_object* v_inst_2471_, lean_object* v_inst_2472_, lean_object* v_xs_2473_, lean_object* v_prio_2474_, lean_object* v_a_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Std_Async_BaseAsync_raceAll(v_00_u03b1_2469_, v_c_2470_, v_inst_2471_, v_inst_2472_, v_xs_2473_, v_prio_2474_);
lean_dec(v_inst_2471_);
return v_res_2476_;
}
}
lean_object* l_Std_Async_EAsync_toBaseIO___redArg(lean_object* v_x_2477_){
_start:
{
lean_object* v___x_2479_; 
v___x_2479_ = lean_apply_1(v_x_2477_, lean_box(0));
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v_a_2480_; lean_object* v___x_2481_; 
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
lean_inc(v_a_2480_);
lean_dec_ref_known(v___x_2479_, 1);
v___x_2481_ = lean_task_pure(v_a_2480_);
return v___x_2481_;
}
else
{
lean_object* v_a_2482_; 
v_a_2482_ = lean_ctor_get(v___x_2479_, 0);
lean_inc_ref(v_a_2482_);
lean_dec_ref_known(v___x_2479_, 1);
return v_a_2482_;
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_toBaseIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2477_ = stack[0].m_obj;
lean_object* v_res_2483_;
v_res_2483_ = l_Std_Async_EAsync_toBaseIO___redArg(v_x_2477_);
stack->m_obj
 = v_res_2483_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toBaseIO___redArg___boxed(lean_object* v_x_2484_, lean_object* v_a_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Std_Async_EAsync_toBaseIO___redArg(v_x_2484_);
return v_res_2486_;
}
}
lean_object* l_Std_Async_EAsync_toBaseIO(lean_object* v_00_u03b5_2487_, lean_object* v_00_u03b1_2488_, lean_object* v_x_2489_){
_start:
{
lean_object* v___x_2491_; 
v___x_2491_ = lean_apply_1(v_x_2489_, lean_box(0));
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; lean_object* v___x_2493_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_a_2492_);
lean_dec_ref_known(v___x_2491_, 1);
v___x_2493_ = lean_task_pure(v_a_2492_);
return v___x_2493_;
}
else
{
lean_object* v_a_2494_; 
v_a_2494_ = lean_ctor_get(v___x_2491_, 0);
lean_inc_ref(v_a_2494_);
lean_dec_ref_known(v___x_2491_, 1);
return v_a_2494_;
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_toBaseIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2489_ = stack[2].m_obj;
lean_object* v_res_2495_;
v_res_2495_ = l_Std_Async_EAsync_toBaseIO(lean_box(0), lean_box(0), v_x_2489_);
stack->m_obj
 = v_res_2495_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toBaseIO___boxed(lean_object* v_00_u03b5_2496_, lean_object* v_00_u03b1_2497_, lean_object* v_x_2498_, lean_object* v_a_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_Std_Async_EAsync_toBaseIO(v_00_u03b5_2496_, v_00_u03b1_2497_, v_x_2498_);
return v_res_2500_;
}
}
lean_object* l_Std_Async_EAsync_ofTask___redArg(lean_object* v_x_2501_){
_start:
{
lean_object* v___x_2503_; 
v___x_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2503_, 0, v_x_2501_);
return v___x_2503_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_ofTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2501_ = stack[0].m_obj;
lean_object* v_res_2504_;
v_res_2504_ = l_Std_Async_EAsync_ofTask___redArg(v_x_2501_);
stack->m_obj
 = v_res_2504_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofTask___redArg___boxed(lean_object* v_x_2505_, lean_object* v_a_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_Std_Async_EAsync_ofTask___redArg(v_x_2505_);
return v_res_2507_;
}
}
lean_object* l_Std_Async_EAsync_ofTask(lean_object* v_00_u03b5_2508_, lean_object* v_00_u03b1_2509_, lean_object* v_x_2510_){
_start:
{
lean_object* v___x_2512_; 
v___x_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2512_, 0, v_x_2510_);
return v___x_2512_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_ofTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2510_ = stack[2].m_obj;
lean_object* v_res_2513_;
v_res_2513_ = l_Std_Async_EAsync_ofTask(lean_box(0), lean_box(0), v_x_2510_);
stack->m_obj
 = v_res_2513_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofTask___boxed(lean_object* v_00_u03b5_2514_, lean_object* v_00_u03b1_2515_, lean_object* v_x_2516_, lean_object* v_a_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l_Std_Async_EAsync_ofTask(v_00_u03b5_2514_, v_00_u03b1_2515_, v_x_2516_);
return v_res_2518_;
}
}
lean_object* l_Std_Async_EAsync_toEIO___redArg(lean_object* v_x_2519_){
_start:
{
lean_object* v___x_2521_; 
v___x_2521_ = lean_apply_1(v_x_2519_, lean_box(0));
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2530_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2524_ = v___x_2521_;
v_isShared_2525_ = v_isSharedCheck_2530_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2521_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2530_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2526_; lean_object* v___x_2528_; 
v___x_2526_ = lean_task_pure(v_a_2522_);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v___x_2526_);
v___x_2528_ = v___x_2524_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2526_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
v_a_2531_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2521_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2521_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
lean_ctor_set_tag(v___x_2533_, 0);
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_toEIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2519_ = stack[0].m_obj;
lean_object* v_res_2539_;
v_res_2539_ = l_Std_Async_EAsync_toEIO___redArg(v_x_2519_);
stack->m_obj
 = v_res_2539_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toEIO___redArg___boxed(lean_object* v_x_2540_, lean_object* v_a_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Std_Async_EAsync_toEIO___redArg(v_x_2540_);
return v_res_2542_;
}
}
lean_object* l_Std_Async_EAsync_toEIO(lean_object* v_00_u03b5_2543_, lean_object* v_00_u03b1_2544_, lean_object* v_x_2545_){
_start:
{
lean_object* v___x_2547_; 
v___x_2547_ = lean_apply_1(v_x_2545_, lean_box(0));
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2556_; 
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2550_ = v___x_2547_;
v_isShared_2551_ = v_isSharedCheck_2556_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2547_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2556_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2552_; lean_object* v___x_2554_; 
v___x_2552_ = lean_task_pure(v_a_2548_);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 0, v___x_2552_);
v___x_2554_ = v___x_2550_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2552_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
else
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
v_a_2557_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2559_ = v___x_2547_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2547_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
lean_ctor_set_tag(v___x_2559_, 0);
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_a_2557_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_toEIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2545_ = stack[2].m_obj;
lean_object* v_res_2565_;
v_res_2565_ = l_Std_Async_EAsync_toEIO(lean_box(0), lean_box(0), v_x_2545_);
stack->m_obj
 = v_res_2565_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toEIO___boxed(lean_object* v_00_u03b5_2566_, lean_object* v_00_u03b1_2567_, lean_object* v_x_2568_, lean_object* v_a_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_Std_Async_EAsync_toEIO(v_00_u03b5_2566_, v_00_u03b1_2567_, v_x_2568_);
return v_res_2570_;
}
}
lean_object* l_Std_Async_EAsync_ofETask___redArg(lean_object* v_x_2571_){
_start:
{
lean_object* v___x_2573_; 
v___x_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2573_, 0, v_x_2571_);
return v___x_2573_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_ofETask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2571_ = stack[0].m_obj;
lean_object* v_res_2574_;
v_res_2574_ = l_Std_Async_EAsync_ofETask___redArg(v_x_2571_);
stack->m_obj
 = v_res_2574_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofETask___redArg___boxed(lean_object* v_x_2575_, lean_object* v_a_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_Std_Async_EAsync_ofETask___redArg(v_x_2575_);
return v_res_2577_;
}
}
lean_object* l_Std_Async_EAsync_ofETask(lean_object* v_00_u03b5_2578_, lean_object* v_00_u03b1_2579_, lean_object* v_x_2580_){
_start:
{
lean_object* v___x_2582_; 
v___x_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2582_, 0, v_x_2580_);
return v___x_2582_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_ofETask_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2580_ = stack[2].m_obj;
lean_object* v_res_2583_;
v_res_2583_ = l_Std_Async_EAsync_ofETask(lean_box(0), lean_box(0), v_x_2580_);
stack->m_obj
 = v_res_2583_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofETask___boxed(lean_object* v_00_u03b5_2584_, lean_object* v_00_u03b1_2585_, lean_object* v_x_2586_, lean_object* v_a_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l_Std_Async_EAsync_ofETask(v_00_u03b5_2584_, v_00_u03b1_2585_, v_x_2586_);
return v_res_2588_;
}
}
lean_object* l_Std_Async_EAsync_pure___redArg(lean_object* v_a_2589_){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2591_, 0, v_a_2589_);
v___x_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
return v___x_2592_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_pure___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2589_ = stack[0].m_obj;
lean_object* v_res_2593_;
v_res_2593_ = l_Std_Async_EAsync_pure___redArg(v_a_2589_);
stack->m_obj
 = v_res_2593_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_pure___redArg___boxed(lean_object* v_a_2594_, lean_object* v_a_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_Std_Async_EAsync_pure___redArg(v_a_2594_);
return v_res_2596_;
}
}
lean_object* l_Std_Async_EAsync_pure(lean_object* v_00_u03b1_2597_, lean_object* v_00_u03b5_2598_, lean_object* v_a_2599_){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2601_, 0, v_a_2599_);
v___x_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2601_);
return v___x_2602_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_pure_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2599_ = stack[2].m_obj;
lean_object* v_res_2603_;
v_res_2603_ = l_Std_Async_EAsync_pure(lean_box(0), lean_box(0), v_a_2599_);
stack->m_obj
 = v_res_2603_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_pure___boxed(lean_object* v_00_u03b1_2604_, lean_object* v_00_u03b5_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l_Std_Async_EAsync_pure(v_00_u03b1_2604_, v_00_u03b5_2605_, v_a_2606_);
return v_res_2608_;
}
}
lean_object* l_Std_Async_EAsync_map___redArg(lean_object* v_f_2609_, lean_object* v_self_2610_){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; lean_object* v___x_2615_; lean_object* v___y_2617_; 
lean_inc(v_f_2609_);
v___x_2612_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_2612_, 0, lean_box(0));
lean_closure_set(v___x_2612_, 1, lean_box(0));
lean_closure_set(v___x_2612_, 2, lean_box(0));
lean_closure_set(v___x_2612_, 3, v_f_2609_);
v___x_2613_ = lean_unsigned_to_nat(0u);
v___x_2614_ = 0;
v___x_2615_ = lean_apply_1(v_self_2610_, lean_box(0));
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v_a_2619_; 
lean_dec_ref(v___x_2612_);
v_a_2619_ = lean_ctor_get(v___x_2615_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v___x_2615_, 1);
if (lean_obj_tag(v_a_2619_) == 0)
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_dec(v_f_2609_);
v_a_2620_ = lean_ctor_get(v_a_2619_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v_a_2619_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v_a_2619_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v_a_2619_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
v___y_2617_ = v___x_2625_;
goto v___jp_2616_;
}
}
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2636_; 
v_a_2628_ = lean_ctor_get(v_a_2619_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v_a_2619_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2630_ = v_a_2619_;
v_isShared_2631_ = v_isSharedCheck_2636_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v_a_2619_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2636_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2632_; lean_object* v___x_2634_; 
v___x_2632_ = lean_apply_1(v_f_2609_, v_a_2628_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 0, v___x_2632_);
v___x_2634_ = v___x_2630_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2632_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
v___y_2617_ = v___x_2634_;
goto v___jp_2616_;
}
}
}
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2645_; 
lean_dec(v_f_2609_);
v_a_2637_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2639_ = v___x_2615_;
v_isShared_2640_ = v_isSharedCheck_2645_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2615_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2645_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2641_; lean_object* v___x_2643_; 
v___x_2641_ = lean_task_map(v___x_2612_, v_a_2637_, v___x_2613_, v___x_2614_);
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 0, v___x_2641_);
v___x_2643_ = v___x_2639_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2641_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
v___jp_2616_:
{
lean_object* v___x_2618_; 
v___x_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2618_, 0, v___y_2617_);
return v___x_2618_;
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_map___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2609_ = stack[0].m_obj;
lean_object* v_self_2610_ = stack[1].m_obj;
lean_object* v_res_2646_;
v_res_2646_ = l_Std_Async_EAsync_map___redArg(v_f_2609_, v_self_2610_);
stack->m_obj
 = v_res_2646_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_map___redArg___boxed(lean_object* v_f_2647_, lean_object* v_self_2648_, lean_object* v_a_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l_Std_Async_EAsync_map___redArg(v_f_2647_, v_self_2648_);
return v_res_2650_;
}
}
lean_object* l_Std_Async_EAsync_map(lean_object* v_00_u03b1_2651_, lean_object* v_00_u03b2_2652_, lean_object* v_00_u03b5_2653_, lean_object* v_f_2654_, lean_object* v_self_2655_){
_start:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; uint8_t v___x_2659_; lean_object* v___x_2660_; lean_object* v___y_2662_; 
lean_inc(v_f_2654_);
v___x_2657_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_2657_, 0, lean_box(0));
lean_closure_set(v___x_2657_, 1, lean_box(0));
lean_closure_set(v___x_2657_, 2, lean_box(0));
lean_closure_set(v___x_2657_, 3, v_f_2654_);
v___x_2658_ = lean_unsigned_to_nat(0u);
v___x_2659_ = 0;
v___x_2660_ = lean_apply_1(v_self_2655_, lean_box(0));
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v_a_2664_; 
lean_dec_ref(v___x_2657_);
v_a_2664_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_a_2664_);
lean_dec_ref_known(v___x_2660_, 1);
if (lean_obj_tag(v_a_2664_) == 0)
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
lean_dec(v_f_2654_);
v_a_2665_ = lean_ctor_get(v_a_2664_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v_a_2664_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2667_ = v_a_2664_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v_a_2664_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
v___y_2662_ = v___x_2670_;
goto v___jp_2661_;
}
}
}
else
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2681_; 
v_a_2673_ = lean_ctor_get(v_a_2664_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v_a_2664_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2675_ = v_a_2664_;
v_isShared_2676_ = v_isSharedCheck_2681_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v_a_2664_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2681_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2677_; lean_object* v___x_2679_; 
v___x_2677_ = lean_apply_1(v_f_2654_, v_a_2673_);
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 0, v___x_2677_);
v___x_2679_ = v___x_2675_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2677_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
v___y_2662_ = v___x_2679_;
goto v___jp_2661_;
}
}
}
}
else
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2690_; 
lean_dec(v_f_2654_);
v_a_2682_ = lean_ctor_get(v___x_2660_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2684_ = v___x_2660_;
v_isShared_2685_ = v_isSharedCheck_2690_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2660_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2690_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2686_; lean_object* v___x_2688_; 
v___x_2686_ = lean_task_map(v___x_2657_, v_a_2682_, v___x_2658_, v___x_2659_);
if (v_isShared_2685_ == 0)
{
lean_ctor_set(v___x_2684_, 0, v___x_2686_);
v___x_2688_ = v___x_2684_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2686_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
v___jp_2661_:
{
lean_object* v___x_2663_; 
v___x_2663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2663_, 0, v___y_2662_);
return v___x_2663_;
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_map_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2654_ = stack[3].m_obj;
lean_object* v_self_2655_ = stack[4].m_obj;
lean_object* v_res_2691_;
v_res_2691_ = l_Std_Async_EAsync_map(lean_box(0), lean_box(0), lean_box(0), v_f_2654_, v_self_2655_);
stack->m_obj
 = v_res_2691_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_map___boxed(lean_object* v_00_u03b1_2692_, lean_object* v_00_u03b2_2693_, lean_object* v_00_u03b5_2694_, lean_object* v_f_2695_, lean_object* v_self_2696_, lean_object* v_a_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l_Std_Async_EAsync_map(v_00_u03b1_2692_, v_00_u03b2_2693_, v_00_u03b5_2694_, v_f_2695_, v_self_2696_);
return v_res_2698_;
}
}
lean_object* l_Std_Async_EAsync_bind___redArg___lam__0(lean_object* v_f_2699_, lean_object* v_x_2700_){
_start:
{
if (lean_obj_tag(v_x_2700_) == 0)
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2710_; 
lean_dec_ref(v_f_2699_);
v_a_2702_ = lean_ctor_get(v_x_2700_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v_x_2700_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2704_ = v_x_2700_;
v_isShared_2705_ = v_isSharedCheck_2710_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v_x_2700_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2710_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2702_);
v___x_2707_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
lean_object* v___x_2708_; 
v___x_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
return v___x_2708_;
}
}
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2712_; 
v_a_2711_ = lean_ctor_get(v_x_2700_, 0);
lean_inc(v_a_2711_);
lean_dec_ref_known(v_x_2700_, 1);
v___x_2712_ = lean_apply_2(v_f_2699_, v_a_2711_, lean_box(0));
return v___x_2712_;
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_bind___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2699_ = stack[0].m_obj;
lean_object* v_x_2700_ = stack[1].m_obj;
lean_object* v_res_2713_;
v_res_2713_ = l_Std_Async_EAsync_bind___redArg___lam__0(v_f_2699_, v_x_2700_);
stack->m_obj
 = v_res_2713_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind___redArg___lam__0___boxed(lean_object* v_f_2714_, lean_object* v_x_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Std_Async_EAsync_bind___redArg___lam__0(v_f_2714_, v_x_2715_);
return v_res_2717_;
}
}
lean_object* l_Std_Async_EAsync_bind___redArg(lean_object* v_self_2718_, lean_object* v_f_2719_){
_start:
{
lean_object* v___f_2721_; lean_object* v___x_2722_; uint8_t v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___f_2721_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_bind___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2721_, 0, v_f_2719_);
v___x_2722_ = lean_unsigned_to_nat(0u);
v___x_2723_ = 0;
v___x_2724_ = lean_apply_1(v_self_2718_, lean_box(0));
v___x_2725_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2722_, v___x_2723_, v___x_2724_, v___f_2721_);
return v___x_2725_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_bind___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_2718_ = stack[0].m_obj;
lean_object* v_f_2719_ = stack[1].m_obj;
lean_object* v_res_2726_;
v_res_2726_ = l_Std_Async_EAsync_bind___redArg(v_self_2718_, v_f_2719_);
stack->m_obj
 = v_res_2726_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind___redArg___boxed(lean_object* v_self_2727_, lean_object* v_f_2728_, lean_object* v_a_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_Std_Async_EAsync_bind___redArg(v_self_2727_, v_f_2728_);
return v_res_2730_;
}
}
lean_object* l_Std_Async_EAsync_bind(lean_object* v_00_u03b5_2731_, lean_object* v_00_u03b1_2732_, lean_object* v_00_u03b2_2733_, lean_object* v_self_2734_, lean_object* v_f_2735_){
_start:
{
lean_object* v___f_2737_; lean_object* v___x_2738_; uint8_t v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___f_2737_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_bind___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2737_, 0, v_f_2735_);
v___x_2738_ = lean_unsigned_to_nat(0u);
v___x_2739_ = 0;
v___x_2740_ = lean_apply_1(v_self_2734_, lean_box(0));
v___x_2741_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2738_, v___x_2739_, v___x_2740_, v___f_2737_);
return v___x_2741_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_bind_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_2734_ = stack[3].m_obj;
lean_object* v_f_2735_ = stack[4].m_obj;
lean_object* v_res_2742_;
v_res_2742_ = l_Std_Async_EAsync_bind(lean_box(0), lean_box(0), lean_box(0), v_self_2734_, v_f_2735_);
stack->m_obj
 = v_res_2742_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind___boxed(lean_object* v_00_u03b5_2743_, lean_object* v_00_u03b1_2744_, lean_object* v_00_u03b2_2745_, lean_object* v_self_2746_, lean_object* v_f_2747_, lean_object* v_a_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_Std_Async_EAsync_bind(v_00_u03b5_2743_, v_00_u03b1_2744_, v_00_u03b2_2745_, v_self_2746_, v_f_2747_);
return v_res_2749_;
}
}
lean_object* l_Std_Async_EAsync_lift___redArg(lean_object* v_x_2750_){
_start:
{
lean_object* v_val_2753_; lean_object* v___x_2755_; 
v___x_2755_ = lean_apply_1(v_x_2750_, lean_box(0));
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2755_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2755_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
lean_ctor_set_tag(v___x_2758_, 1);
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
v_val_2753_ = v___x_2761_;
goto v___jp_2752_;
}
}
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
v_a_2764_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2755_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2755_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
lean_ctor_set_tag(v___x_2766_, 0);
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
v_val_2753_ = v___x_2769_;
goto v___jp_2752_;
}
}
}
v___jp_2752_:
{
lean_object* v___x_2754_; 
v___x_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2754_, 0, v_val_2753_);
return v___x_2754_;
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_lift___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2750_ = stack[0].m_obj;
lean_object* v_res_2772_;
v_res_2772_ = l_Std_Async_EAsync_lift___redArg(v_x_2750_);
stack->m_obj
 = v_res_2772_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_lift___redArg___boxed(lean_object* v_x_2773_, lean_object* v_a_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Std_Async_EAsync_lift___redArg(v_x_2773_);
return v_res_2775_;
}
}
lean_object* l_Std_Async_EAsync_lift(lean_object* v_00_u03b5_2776_, lean_object* v_00_u03b1_2777_, lean_object* v_x_2778_){
_start:
{
lean_object* v_val_2781_; lean_object* v___x_2783_; 
v___x_2783_ = lean_apply_1(v_x_2778_, lean_box(0));
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2783_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2783_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
lean_ctor_set_tag(v___x_2786_, 1);
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
v_val_2781_ = v___x_2789_;
goto v___jp_2780_;
}
}
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
v_a_2792_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2783_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2783_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
lean_ctor_set_tag(v___x_2794_, 0);
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
v_val_2781_ = v___x_2797_;
goto v___jp_2780_;
}
}
}
v___jp_2780_:
{
lean_object* v___x_2782_; 
v___x_2782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2782_, 0, v_val_2781_);
return v___x_2782_;
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_lift_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2778_ = stack[2].m_obj;
lean_object* v_res_2800_;
v_res_2800_ = l_Std_Async_EAsync_lift(lean_box(0), lean_box(0), v_x_2778_);
stack->m_obj
 = v_res_2800_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_lift___boxed(lean_object* v_00_u03b5_2801_, lean_object* v_00_u03b1_2802_, lean_object* v_x_2803_, lean_object* v_a_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_Std_Async_EAsync_lift(v_00_u03b5_2801_, v_00_u03b1_2802_, v_x_2803_);
return v_res_2805_;
}
}
lean_object* l_Std_Async_EAsync_wait___redArg(lean_object* v_self_2806_){
_start:
{
lean_object* v_val_2809_; lean_object* v___x_2827_; 
v___x_2827_ = lean_apply_1(v_self_2806_, lean_box(0));
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2829_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2827_, 1);
v___x_2829_ = lean_task_pure(v_a_2828_);
v_val_2809_ = v___x_2829_;
goto v___jp_2808_;
}
else
{
lean_object* v_a_2830_; 
v_a_2830_ = lean_ctor_get(v___x_2827_, 0);
lean_inc_ref(v_a_2830_);
lean_dec_ref_known(v___x_2827_, 1);
v_val_2809_ = v_a_2830_;
goto v___jp_2808_;
}
v___jp_2808_:
{
lean_object* v___x_2810_; 
v___x_2810_ = lean_task_get_own(v_val_2809_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2818_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2813_ = v___x_2810_;
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2810_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
if (v_isShared_2814_ == 0)
{
lean_ctor_set_tag(v___x_2813_, 1);
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
v_a_2819_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2810_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2810_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
lean_ctor_set_tag(v___x_2821_, 0);
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 1, 0);
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
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_wait___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_2806_ = stack[0].m_obj;
lean_object* v_res_2831_;
v_res_2831_ = l_Std_Async_EAsync_wait___redArg(v_self_2806_);
stack->m_obj
 = v_res_2831_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_wait___redArg___boxed(lean_object* v_self_2832_, lean_object* v_a_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Std_Async_EAsync_wait___redArg(v_self_2832_);
return v_res_2834_;
}
}
lean_object* l_Std_Async_EAsync_wait(lean_object* v_00_u03b5_2835_, lean_object* v_00_u03b1_2836_, lean_object* v_self_2837_){
_start:
{
lean_object* v_val_2840_; lean_object* v___x_2858_; 
v___x_2858_ = lean_apply_1(v_self_2837_, lean_box(0));
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v_a_2859_; lean_object* v___x_2860_; 
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_a_2859_);
lean_dec_ref_known(v___x_2858_, 1);
v___x_2860_ = lean_task_pure(v_a_2859_);
v_val_2840_ = v___x_2860_;
goto v___jp_2839_;
}
else
{
lean_object* v_a_2861_; 
v_a_2861_ = lean_ctor_get(v___x_2858_, 0);
lean_inc_ref(v_a_2861_);
lean_dec_ref_known(v___x_2858_, 1);
v_val_2840_ = v_a_2861_;
goto v___jp_2839_;
}
v___jp_2839_:
{
lean_object* v___x_2841_; 
v___x_2841_ = lean_task_get_own(v_val_2840_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___x_2841_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2841_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
if (v_isShared_2845_ == 0)
{
lean_ctor_set_tag(v___x_2844_, 1);
v___x_2847_ = v___x_2844_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
else
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
v_a_2850_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2841_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2841_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2855_; 
if (v_isShared_2853_ == 0)
{
lean_ctor_set_tag(v___x_2852_, 0);
v___x_2855_ = v___x_2852_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_wait_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_2837_ = stack[2].m_obj;
lean_object* v_res_2862_;
v_res_2862_ = l_Std_Async_EAsync_wait(lean_box(0), lean_box(0), v_self_2837_);
stack->m_obj
 = v_res_2862_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_wait___boxed(lean_object* v_00_u03b5_2863_, lean_object* v_00_u03b1_2864_, lean_object* v_self_2865_, lean_object* v_a_2866_){
_start:
{
lean_object* v_res_2867_; 
v_res_2867_ = l_Std_Async_EAsync_wait(v_00_u03b5_2863_, v_00_u03b1_2864_, v_self_2865_);
return v_res_2867_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_asTask___redArg___lam__0(lean_object* v_x_2868_){
_start:
{
if (lean_obj_tag(v_x_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v___x_2870_; 
v_a_2869_ = lean_ctor_get(v_x_2868_, 0);
lean_inc(v_a_2869_);
lean_dec_ref_known(v_x_2868_, 1);
v___x_2870_ = lean_task_pure(v_a_2869_);
return v___x_2870_;
}
else
{
lean_object* v_a_2871_; 
v_a_2871_ = lean_ctor_get(v_x_2868_, 0);
lean_inc_ref(v_a_2871_);
lean_dec_ref_known(v_x_2868_, 1);
return v_a_2871_;
}
}
}
lean_object* l_Std_Async_EAsync_asTask___redArg(lean_object* v_x_2873_, lean_object* v_prio_2874_){
_start:
{
lean_object* v___f_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; uint8_t v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___f_2876_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___x_2877_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2877_, 0, lean_box(0));
lean_closure_set(v___x_2877_, 1, v_x_2873_);
v___x_2878_ = lean_io_as_task(v___x_2877_, v_prio_2874_);
v___x_2879_ = lean_unsigned_to_nat(0u);
v___x_2880_ = 1;
v___x_2881_ = lean_task_bind(v___x_2878_, v___f_2876_, v___x_2879_, v___x_2880_);
v___x_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
return v___x_2882_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_asTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2873_ = stack[0].m_obj;
lean_object* v_prio_2874_ = stack[1].m_obj;
lean_object* v_res_2883_;
v_res_2883_ = l_Std_Async_EAsync_asTask___redArg(v_x_2873_, v_prio_2874_);
stack->m_obj
 = v_res_2883_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_asTask___redArg___boxed(lean_object* v_x_2884_, lean_object* v_prio_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = l_Std_Async_EAsync_asTask___redArg(v_x_2884_, v_prio_2885_);
return v_res_2887_;
}
}
lean_object* l_Std_Async_EAsync_asTask(lean_object* v_00_u03b5_2888_, lean_object* v_00_u03b1_2889_, lean_object* v_x_2890_, lean_object* v_prio_2891_){
_start:
{
lean_object* v___f_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; uint8_t v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___f_2893_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___x_2894_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2894_, 0, lean_box(0));
lean_closure_set(v___x_2894_, 1, v_x_2890_);
v___x_2895_ = lean_io_as_task(v___x_2894_, v_prio_2891_);
v___x_2896_ = lean_unsigned_to_nat(0u);
v___x_2897_ = 1;
v___x_2898_ = lean_task_bind(v___x_2895_, v___f_2893_, v___x_2896_, v___x_2897_);
v___x_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
return v___x_2899_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_asTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2890_ = stack[2].m_obj;
lean_object* v_prio_2891_ = stack[3].m_obj;
lean_object* v_res_2900_;
v_res_2900_ = l_Std_Async_EAsync_asTask(lean_box(0), lean_box(0), v_x_2890_, v_prio_2891_);
stack->m_obj
 = v_res_2900_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_asTask___boxed(lean_object* v_00_u03b5_2901_, lean_object* v_00_u03b1_2902_, lean_object* v_x_2903_, lean_object* v_prio_2904_, lean_object* v_a_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l_Std_Async_EAsync_asTask(v_00_u03b5_2901_, v_00_u03b1_2902_, v_x_2903_, v_prio_2904_);
return v_res_2906_;
}
}
lean_object* l_Std_Async_EAsync_block___redArg(lean_object* v_x_2907_, lean_object* v_prio_2908_){
_start:
{
lean_object* v___f_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; uint8_t v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___f_2910_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___x_2911_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2911_, 0, lean_box(0));
lean_closure_set(v___x_2911_, 1, v_x_2907_);
v___x_2912_ = lean_io_as_task(v___x_2911_, v_prio_2908_);
v___x_2913_ = lean_unsigned_to_nat(0u);
v___x_2914_ = 1;
v___x_2915_ = lean_task_bind(v___x_2912_, v___f_2910_, v___x_2913_, v___x_2914_);
v___x_2916_ = lean_task_get_own(v___x_2915_);
if (lean_obj_tag(v___x_2916_) == 0)
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
v_a_2917_ = lean_ctor_get(v___x_2916_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2916_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2916_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
lean_ctor_set_tag(v___x_2919_, 1);
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
v_a_2925_ = lean_ctor_get(v___x_2916_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2916_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2916_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
lean_ctor_set_tag(v___x_2927_, 0);
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_block___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2907_ = stack[0].m_obj;
lean_object* v_prio_2908_ = stack[1].m_obj;
lean_object* v_res_2933_;
v_res_2933_ = l_Std_Async_EAsync_block___redArg(v_x_2907_, v_prio_2908_);
stack->m_obj
 = v_res_2933_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_block___redArg___boxed(lean_object* v_x_2934_, lean_object* v_prio_2935_, lean_object* v_a_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l_Std_Async_EAsync_block___redArg(v_x_2934_, v_prio_2935_);
return v_res_2937_;
}
}
lean_object* l_Std_Async_EAsync_block(lean_object* v_00_u03b5_2938_, lean_object* v_00_u03b1_2939_, lean_object* v_x_2940_, lean_object* v_prio_2941_){
_start:
{
lean_object* v___f_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; uint8_t v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___f_2943_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___x_2944_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2944_, 0, lean_box(0));
lean_closure_set(v___x_2944_, 1, v_x_2940_);
v___x_2945_ = lean_io_as_task(v___x_2944_, v_prio_2941_);
v___x_2946_ = lean_unsigned_to_nat(0u);
v___x_2947_ = 1;
v___x_2948_ = lean_task_bind(v___x_2945_, v___f_2943_, v___x_2946_, v___x_2947_);
v___x_2949_ = lean_task_get_own(v___x_2948_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___x_2949_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2949_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2953_ == 0)
{
lean_ctor_set_tag(v___x_2952_, 1);
v___x_2955_ = v___x_2952_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2950_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
else
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2965_; 
v_a_2958_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2960_ = v___x_2949_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2949_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2963_; 
if (v_isShared_2961_ == 0)
{
lean_ctor_set_tag(v___x_2960_, 0);
v___x_2963_ = v___x_2960_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2958_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_block_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2940_ = stack[2].m_obj;
lean_object* v_prio_2941_ = stack[3].m_obj;
lean_object* v_res_2966_;
v_res_2966_ = l_Std_Async_EAsync_block(lean_box(0), lean_box(0), v_x_2940_, v_prio_2941_);
stack->m_obj
 = v_res_2966_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_block___boxed(lean_object* v_00_u03b5_2967_, lean_object* v_00_u03b1_2968_, lean_object* v_x_2969_, lean_object* v_prio_2970_, lean_object* v_a_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l_Std_Async_EAsync_block(v_00_u03b5_2967_, v_00_u03b1_2968_, v_x_2969_, v_prio_2970_);
return v_res_2972_;
}
}
lean_object* l_Std_Async_EAsync_throw___redArg(lean_object* v_e_2973_){
_start:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2975_, 0, v_e_2973_);
v___x_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2975_);
return v___x_2976_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_throw___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2973_ = stack[0].m_obj;
lean_object* v_res_2977_;
v_res_2977_ = l_Std_Async_EAsync_throw___redArg(v_e_2973_);
stack->m_obj
 = v_res_2977_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_throw___redArg___boxed(lean_object* v_e_2978_, lean_object* v_a_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l_Std_Async_EAsync_throw___redArg(v_e_2978_);
return v_res_2980_;
}
}
lean_object* l_Std_Async_EAsync_throw(lean_object* v_00_u03b5_2981_, lean_object* v_00_u03b1_2982_, lean_object* v_e_2983_){
_start:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2985_, 0, v_e_2983_);
v___x_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2985_);
return v___x_2986_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_throw_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2983_ = stack[2].m_obj;
lean_object* v_res_2987_;
v_res_2987_ = l_Std_Async_EAsync_throw(lean_box(0), lean_box(0), v_e_2983_);
stack->m_obj
 = v_res_2987_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_throw___boxed(lean_object* v_00_u03b5_2988_, lean_object* v_00_u03b1_2989_, lean_object* v_e_2990_, lean_object* v_a_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_Std_Async_EAsync_throw(v_00_u03b5_2988_, v_00_u03b1_2989_, v_e_2990_);
return v_res_2992_;
}
}
lean_object* l_Std_Async_EAsync_tryCatch___redArg___lam__0(lean_object* v_f_2993_, lean_object* v_x_2994_){
_start:
{
if (lean_obj_tag(v_x_2994_) == 0)
{
lean_object* v_a_2996_; lean_object* v___x_2997_; 
v_a_2996_ = lean_ctor_get(v_x_2994_, 0);
lean_inc(v_a_2996_);
lean_dec_ref_known(v_x_2994_, 1);
v___x_2997_ = lean_apply_2(v_f_2993_, v_a_2996_, lean_box(0));
return v___x_2997_;
}
else
{
lean_object* v___x_2998_; 
lean_dec_ref(v_f_2993_);
v___x_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2998_, 0, v_x_2994_);
return v___x_2998_;
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_tryCatch___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2993_ = stack[0].m_obj;
lean_object* v_x_2994_ = stack[1].m_obj;
lean_object* v_res_2999_;
v_res_2999_ = l_Std_Async_EAsync_tryCatch___redArg___lam__0(v_f_2993_, v_x_2994_);
stack->m_obj
 = v_res_2999_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch___redArg___lam__0___boxed(lean_object* v_f_3000_, lean_object* v_x_3001_, lean_object* v___y_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_Std_Async_EAsync_tryCatch___redArg___lam__0(v_f_3000_, v_x_3001_);
return v_res_3003_;
}
}
lean_object* l_Std_Async_EAsync_tryCatch___redArg(lean_object* v_x_3004_, lean_object* v_f_3005_, lean_object* v_prio_3006_, uint8_t v_sync_3007_){
_start:
{
lean_object* v___f_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___f_3009_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_tryCatch___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3009_, 0, v_f_3005_);
v___x_3010_ = lean_apply_1(v_x_3004_, lean_box(0));
v___x_3011_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_3006_, v_sync_3007_, v___x_3010_, v___f_3009_);
return v___x_3011_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_tryCatch___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3004_ = stack[0].m_obj;
lean_object* v_f_3005_ = stack[1].m_obj;
lean_object* v_prio_3006_ = stack[2].m_obj;
uint8_t v_sync_3007_ = stack[3].m_num;
lean_object* v_res_3012_;
v_res_3012_ = l_Std_Async_EAsync_tryCatch___redArg(v_x_3004_, v_f_3005_, v_prio_3006_, v_sync_3007_);
stack->m_obj
 = v_res_3012_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch___redArg___boxed(lean_object* v_x_3013_, lean_object* v_f_3014_, lean_object* v_prio_3015_, lean_object* v_sync_3016_, lean_object* v_a_3017_){
_start:
{
uint8_t v_sync_boxed_3018_; lean_object* v_res_3019_; 
v_sync_boxed_3018_ = lean_unbox(v_sync_3016_);
v_res_3019_ = l_Std_Async_EAsync_tryCatch___redArg(v_x_3013_, v_f_3014_, v_prio_3015_, v_sync_boxed_3018_);
return v_res_3019_;
}
}
lean_object* l_Std_Async_EAsync_tryCatch(lean_object* v_00_u03b5_3020_, lean_object* v_00_u03b1_3021_, lean_object* v_x_3022_, lean_object* v_f_3023_, lean_object* v_prio_3024_, uint8_t v_sync_3025_){
_start:
{
lean_object* v___f_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___f_3027_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_tryCatch___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3027_, 0, v_f_3023_);
v___x_3028_ = lean_apply_1(v_x_3022_, lean_box(0));
v___x_3029_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_3024_, v_sync_3025_, v___x_3028_, v___f_3027_);
return v___x_3029_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_tryCatch_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3022_ = stack[2].m_obj;
lean_object* v_f_3023_ = stack[3].m_obj;
lean_object* v_prio_3024_ = stack[4].m_obj;
uint8_t v_sync_3025_ = stack[5].m_num;
lean_object* v_res_3030_;
v_res_3030_ = l_Std_Async_EAsync_tryCatch(lean_box(0), lean_box(0), v_x_3022_, v_f_3023_, v_prio_3024_, v_sync_3025_);
stack->m_obj
 = v_res_3030_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch___boxed(lean_object* v_00_u03b5_3031_, lean_object* v_00_u03b1_3032_, lean_object* v_x_3033_, lean_object* v_f_3034_, lean_object* v_prio_3035_, lean_object* v_sync_3036_, lean_object* v_a_3037_){
_start:
{
uint8_t v_sync_boxed_3038_; lean_object* v_res_3039_; 
v_sync_boxed_3038_ = lean_unbox(v_sync_3036_);
v_res_3039_ = l_Std_Async_EAsync_tryCatch(v_00_u03b5_3031_, v_00_u03b1_3032_, v_x_3033_, v_f_3034_, v_prio_3035_, v_sync_boxed_3038_);
return v_res_3039_;
}
}
lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__0(lean_object* v_a_3040_, lean_object* v_____do__lift_3041_){
_start:
{
if (lean_obj_tag(v_____do__lift_3041_) == 0)
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3051_; 
lean_dec(v_a_3040_);
v_a_3043_ = lean_ctor_get(v_____do__lift_3041_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v_____do__lift_3041_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3045_ = v_____do__lift_3041_;
v_isShared_3046_ = v_isSharedCheck_3051_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v_____do__lift_3041_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3051_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3043_);
v___x_3048_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
lean_object* v___x_3049_; 
v___x_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
return v___x_3049_;
}
}
}
else
{
lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3059_; 
v_isSharedCheck_3059_ = !lean_is_exclusive(v_____do__lift_3041_);
if (v_isSharedCheck_3059_ == 0)
{
lean_object* v_unused_3060_; 
v_unused_3060_ = lean_ctor_get(v_____do__lift_3041_, 0);
lean_dec(v_unused_3060_);
v___x_3053_ = v_____do__lift_3041_;
v_isShared_3054_ = v_isSharedCheck_3059_;
goto v_resetjp_3052_;
}
else
{
lean_dec(v_____do__lift_3041_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3059_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
lean_ctor_set_tag(v___x_3053_, 0);
lean_ctor_set(v___x_3053_, 0, v_a_3040_);
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3040_);
v___x_3056_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
lean_object* v___x_3057_; 
v___x_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3056_);
return v___x_3057_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_tryFinally_x27___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3040_ = stack[0].m_obj;
lean_object* v_____do__lift_3041_ = stack[1].m_obj;
lean_object* v_res_3061_;
v_res_3061_ = l_Std_Async_EAsync_tryFinally_x27___redArg___lam__0(v_a_3040_, v_____do__lift_3041_);
stack->m_obj
 = v_res_3061_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__0___boxed(lean_object* v_a_3062_, lean_object* v_____do__lift_3063_, lean_object* v___y_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_Std_Async_EAsync_tryFinally_x27___redArg___lam__0(v_a_3062_, v_____do__lift_3063_);
return v_res_3065_;
}
}
lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__1(lean_object* v_a_3066_, lean_object* v_____do__lift_3067_){
_start:
{
if (lean_obj_tag(v_____do__lift_3067_) == 0)
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3077_; 
lean_dec(v_a_3066_);
v_a_3069_ = lean_ctor_get(v_____do__lift_3067_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v_____do__lift_3067_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3071_ = v_____do__lift_3067_;
v_isShared_3072_ = v_isSharedCheck_3077_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v_____do__lift_3067_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3077_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3069_);
v___x_3074_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
lean_object* v___x_3075_; 
v___x_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
return v___x_3075_;
}
}
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3087_; 
v_a_3078_ = lean_ctor_get(v_____do__lift_3067_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v_____do__lift_3067_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3080_ = v_____do__lift_3067_;
v_isShared_3081_ = v_isSharedCheck_3087_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v_____do__lift_3067_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3087_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3082_; lean_object* v___x_3084_; 
v___x_3082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3082_, 0, v_a_3066_);
lean_ctor_set(v___x_3082_, 1, v_a_3078_);
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 0, v___x_3082_);
v___x_3084_ = v___x_3080_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_3082_);
v___x_3084_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
lean_object* v___x_3085_; 
v___x_3085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
return v___x_3085_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_tryFinally_x27___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3066_ = stack[0].m_obj;
lean_object* v_____do__lift_3067_ = stack[1].m_obj;
lean_object* v_res_3088_;
v_res_3088_ = l_Std_Async_EAsync_tryFinally_x27___redArg___lam__1(v_a_3066_, v_____do__lift_3067_);
stack->m_obj
 = v_res_3088_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__1___boxed(lean_object* v_a_3089_, lean_object* v_____do__lift_3090_, lean_object* v___y_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l_Std_Async_EAsync_tryFinally_x27___redArg___lam__1(v_a_3089_, v_____do__lift_3090_);
return v_res_3092_;
}
}
lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__2(lean_object* v_f_3093_, lean_object* v_x_3094_){
_start:
{
if (lean_obj_tag(v_x_3094_) == 0)
{
lean_object* v_a_3096_; lean_object* v___f_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; uint8_t v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v_a_3096_ = lean_ctor_get(v_x_3094_, 0);
lean_inc(v_a_3096_);
lean_dec_ref_known(v_x_3094_, 1);
v___f_3097_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_tryFinally_x27___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3097_, 0, v_a_3096_);
v___x_3098_ = lean_box(0);
v___x_3099_ = lean_unsigned_to_nat(0u);
v___x_3100_ = 0;
v___x_3101_ = lean_apply_2(v_f_3093_, v___x_3098_, lean_box(0));
v___x_3102_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3099_, v___x_3100_, v___x_3101_, v___f_3097_);
return v___x_3102_;
}
else
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3115_; 
v_a_3103_ = lean_ctor_get(v_x_3094_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v_x_3094_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3105_ = v_x_3094_;
v_isShared_3106_ = v_isSharedCheck_3115_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v_x_3094_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3115_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___f_3107_; lean_object* v___x_3109_; 
lean_inc(v_a_3103_);
v___f_3107_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_tryFinally_x27___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3107_, 0, v_a_3103_);
if (v_isShared_3106_ == 0)
{
v___x_3109_ = v___x_3105_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3103_);
v___x_3109_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
lean_object* v___x_3110_; uint8_t v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3110_ = lean_unsigned_to_nat(0u);
v___x_3111_ = 0;
v___x_3112_ = lean_apply_2(v_f_3093_, v___x_3109_, lean_box(0));
v___x_3113_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3110_, v___x_3111_, v___x_3112_, v___f_3107_);
return v___x_3113_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_tryFinally_x27___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3093_ = stack[0].m_obj;
lean_object* v_x_3094_ = stack[1].m_obj;
lean_object* v_res_3116_;
v_res_3116_ = l_Std_Async_EAsync_tryFinally_x27___redArg___lam__2(v_f_3093_, v_x_3094_);
stack->m_obj
 = v_res_3116_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__2___boxed(lean_object* v_f_3117_, lean_object* v_x_3118_, lean_object* v___y_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l_Std_Async_EAsync_tryFinally_x27___redArg___lam__2(v_f_3117_, v_x_3118_);
return v_res_3120_;
}
}
lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg(lean_object* v_x_3121_, lean_object* v_f_3122_, lean_object* v_prio_3123_, uint8_t v_sync_3124_){
_start:
{
lean_object* v___f_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___f_3126_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_tryFinally_x27___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3126_, 0, v_f_3122_);
v___x_3127_ = lean_apply_1(v_x_3121_, lean_box(0));
v___x_3128_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_3123_, v_sync_3124_, v___x_3127_, v___f_3126_);
return v___x_3128_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_tryFinally_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3121_ = stack[0].m_obj;
lean_object* v_f_3122_ = stack[1].m_obj;
lean_object* v_prio_3123_ = stack[2].m_obj;
uint8_t v_sync_3124_ = stack[3].m_num;
lean_object* v_res_3129_;
v_res_3129_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v_x_3121_, v_f_3122_, v_prio_3123_, v_sync_3124_);
stack->m_obj
 = v_res_3129_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___boxed(lean_object* v_x_3130_, lean_object* v_f_3131_, lean_object* v_prio_3132_, lean_object* v_sync_3133_, lean_object* v_a_3134_){
_start:
{
uint8_t v_sync_boxed_3135_; lean_object* v_res_3136_; 
v_sync_boxed_3135_ = lean_unbox(v_sync_3133_);
v_res_3136_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v_x_3130_, v_f_3131_, v_prio_3132_, v_sync_boxed_3135_);
return v_res_3136_;
}
}
lean_object* l_Std_Async_EAsync_tryFinally_x27(lean_object* v_00_u03b5_3137_, lean_object* v_00_u03b1_3138_, lean_object* v_00_u03b2_3139_, lean_object* v_x_3140_, lean_object* v_f_3141_, lean_object* v_prio_3142_, uint8_t v_sync_3143_){
_start:
{
lean_object* v___x_3145_; 
v___x_3145_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v_x_3140_, v_f_3141_, v_prio_3142_, v_sync_3143_);
return v___x_3145_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_tryFinally_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3140_ = stack[3].m_obj;
lean_object* v_f_3141_ = stack[4].m_obj;
lean_object* v_prio_3142_ = stack[5].m_obj;
uint8_t v_sync_3143_ = stack[6].m_num;
lean_object* v_res_3146_;
v_res_3146_ = l_Std_Async_EAsync_tryFinally_x27(lean_box(0), lean_box(0), lean_box(0), v_x_3140_, v_f_3141_, v_prio_3142_, v_sync_3143_);
stack->m_obj
 = v_res_3146_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___boxed(lean_object* v_00_u03b5_3147_, lean_object* v_00_u03b1_3148_, lean_object* v_00_u03b2_3149_, lean_object* v_x_3150_, lean_object* v_f_3151_, lean_object* v_prio_3152_, lean_object* v_sync_3153_, lean_object* v_a_3154_){
_start:
{
uint8_t v_sync_boxed_3155_; lean_object* v_res_3156_; 
v_sync_boxed_3155_ = lean_unbox(v_sync_3153_);
v_res_3156_ = l_Std_Async_EAsync_tryFinally_x27(v_00_u03b5_3147_, v_00_u03b1_3148_, v_00_u03b2_3149_, v_x_3150_, v_f_3151_, v_prio_3152_, v_sync_boxed_3155_);
return v_res_3156_;
}
}
lean_object* l_Std_Async_EAsync_await___redArg(lean_object* v_x_3157_){
_start:
{
lean_object* v___x_3159_; 
v___x_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3159_, 0, v_x_3157_);
return v___x_3159_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_await___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3157_ = stack[0].m_obj;
lean_object* v_res_3160_;
v_res_3160_ = l_Std_Async_EAsync_await___redArg(v_x_3157_);
stack->m_obj
 = v_res_3160_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_await___redArg___boxed(lean_object* v_x_3161_, lean_object* v_a_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l_Std_Async_EAsync_await___redArg(v_x_3161_);
return v_res_3163_;
}
}
lean_object* l_Std_Async_EAsync_await(lean_object* v_00_u03b5_3164_, lean_object* v_00_u03b1_3165_, lean_object* v_x_3166_){
_start:
{
lean_object* v___x_3168_; 
v___x_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3168_, 0, v_x_3166_);
return v___x_3168_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_await_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3166_ = stack[2].m_obj;
lean_object* v_res_3169_;
v_res_3169_ = l_Std_Async_EAsync_await(lean_box(0), lean_box(0), v_x_3166_);
stack->m_obj
 = v_res_3169_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_await___boxed(lean_object* v_00_u03b5_3170_, lean_object* v_00_u03b1_3171_, lean_object* v_x_3172_, lean_object* v_a_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l_Std_Async_EAsync_await(v_00_u03b5_3170_, v_00_u03b1_3171_, v_x_3172_);
return v_res_3174_;
}
}
lean_object* l_Std_Async_EAsync_async___redArg(lean_object* v_self_3175_, lean_object* v_prio_3176_){
_start:
{
lean_object* v___f_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; uint8_t v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___f_3178_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___x_3179_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_3179_, 0, lean_box(0));
lean_closure_set(v___x_3179_, 1, v_self_3175_);
v___x_3180_ = lean_io_as_task(v___x_3179_, v_prio_3176_);
v___x_3181_ = lean_unsigned_to_nat(0u);
v___x_3182_ = 1;
v___x_3183_ = lean_task_bind(v___x_3180_, v___f_3178_, v___x_3181_, v___x_3182_);
v___x_3184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3183_);
v___x_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3184_);
return v___x_3185_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_async___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_3175_ = stack[0].m_obj;
lean_object* v_prio_3176_ = stack[1].m_obj;
lean_object* v_res_3186_;
v_res_3186_ = l_Std_Async_EAsync_async___redArg(v_self_3175_, v_prio_3176_);
stack->m_obj
 = v_res_3186_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_async___redArg___boxed(lean_object* v_self_3187_, lean_object* v_prio_3188_, lean_object* v_a_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l_Std_Async_EAsync_async___redArg(v_self_3187_, v_prio_3188_);
return v_res_3190_;
}
}
lean_object* l_Std_Async_EAsync_async(lean_object* v_00_u03b5_3191_, lean_object* v_00_u03b1_3192_, lean_object* v_self_3193_, lean_object* v_prio_3194_){
_start:
{
lean_object* v___f_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; uint8_t v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___f_3196_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___x_3197_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_3197_, 0, lean_box(0));
lean_closure_set(v___x_3197_, 1, v_self_3193_);
v___x_3198_ = lean_io_as_task(v___x_3197_, v_prio_3194_);
v___x_3199_ = lean_unsigned_to_nat(0u);
v___x_3200_ = 1;
v___x_3201_ = lean_task_bind(v___x_3198_, v___f_3196_, v___x_3199_, v___x_3200_);
v___x_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3201_);
v___x_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3202_);
return v___x_3203_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_async_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_3193_ = stack[2].m_obj;
lean_object* v_prio_3194_ = stack[3].m_obj;
lean_object* v_res_3204_;
v_res_3204_ = l_Std_Async_EAsync_async(lean_box(0), lean_box(0), v_self_3193_, v_prio_3194_);
stack->m_obj
 = v_res_3204_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_async___boxed(lean_object* v_00_u03b5_3205_, lean_object* v_00_u03b1_3206_, lean_object* v_self_3207_, lean_object* v_prio_3208_, lean_object* v_a_3209_){
_start:
{
lean_object* v_res_3210_; 
v_res_3210_ = l_Std_Async_EAsync_async(v_00_u03b5_3205_, v_00_u03b1_3206_, v_self_3207_, v_prio_3208_);
return v_res_3210_;
}
}
lean_object* l_Std_Async_EAsync_instFunctor___redArg___lam__0(lean_object* v_00_u03b1_3211_, lean_object* v_00_u03b2_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; uint8_t v___x_3218_; lean_object* v___x_3219_; lean_object* v___y_3221_; 
lean_inc(v___y_3213_);
v___x_3216_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_3216_, 0, lean_box(0));
lean_closure_set(v___x_3216_, 1, lean_box(0));
lean_closure_set(v___x_3216_, 2, lean_box(0));
lean_closure_set(v___x_3216_, 3, v___y_3213_);
v___x_3217_ = lean_unsigned_to_nat(0u);
v___x_3218_ = 0;
v___x_3219_ = lean_apply_1(v___y_3214_, lean_box(0));
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3223_; 
lean_dec_ref(v___x_3216_);
v_a_3223_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_a_3223_);
lean_dec_ref_known(v___x_3219_, 1);
if (lean_obj_tag(v_a_3223_) == 0)
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3231_; 
lean_dec(v___y_3213_);
v_a_3224_ = lean_ctor_get(v_a_3223_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v_a_3223_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3226_ = v_a_3223_;
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v_a_3223_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3224_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
v___y_3221_ = v___x_3229_;
goto v___jp_3220_;
}
}
}
else
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3240_; 
v_a_3232_ = lean_ctor_get(v_a_3223_, 0);
v_isSharedCheck_3240_ = !lean_is_exclusive(v_a_3223_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3234_ = v_a_3223_;
v_isShared_3235_ = v_isSharedCheck_3240_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v_a_3223_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3240_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3236_; lean_object* v___x_3238_; 
v___x_3236_ = lean_apply_1(v___y_3213_, v_a_3232_);
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 0, v___x_3236_);
v___x_3238_ = v___x_3234_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v___x_3236_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
v___y_3221_ = v___x_3238_;
goto v___jp_3220_;
}
}
}
}
else
{
lean_object* v_a_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3249_; 
lean_dec(v___y_3213_);
v_a_3241_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3243_ = v___x_3219_;
v_isShared_3244_ = v_isSharedCheck_3249_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_a_3241_);
lean_dec(v___x_3219_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3249_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3245_; lean_object* v___x_3247_; 
v___x_3245_ = lean_task_map(v___x_3216_, v_a_3241_, v___x_3217_, v___x_3218_);
if (v_isShared_3244_ == 0)
{
lean_ctor_set(v___x_3243_, 0, v___x_3245_);
v___x_3247_ = v___x_3243_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3245_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
v___jp_3220_:
{
lean_object* v___x_3222_; 
v___x_3222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3222_, 0, v___y_3221_);
return v___x_3222_;
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instFunctor___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3213_ = stack[2].m_obj;
lean_object* v___y_3214_ = stack[3].m_obj;
lean_object* v_res_3250_;
v_res_3250_ = l_Std_Async_EAsync_instFunctor___redArg___lam__0(lean_box(0), lean_box(0), v___y_3213_, v___y_3214_);
stack->m_obj
 = v_res_3250_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___redArg___lam__0___boxed(lean_object* v_00_u03b1_3251_, lean_object* v_00_u03b2_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
lean_object* v_res_3256_; 
v_res_3256_ = l_Std_Async_EAsync_instFunctor___redArg___lam__0(v_00_u03b1_3251_, v_00_u03b2_3252_, v___y_3253_, v___y_3254_);
return v_res_3256_;
}
}
lean_object* l_Std_Async_EAsync_instFunctor___redArg___lam__1(lean_object* v___f_3257_, lean_object* v_00_u03b1_3258_, lean_object* v_00_u03b2_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3263_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_3263_, 0, lean_box(0));
lean_closure_set(v___x_3263_, 1, lean_box(0));
lean_closure_set(v___x_3263_, 2, v___y_3260_);
v___x_3264_ = lean_apply_5(v___f_3257_, lean_box(0), lean_box(0), v___x_3263_, v___y_3261_, lean_box(0));
return v___x_3264_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instFunctor___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_3257_ = stack[0].m_obj;
lean_object* v___y_3260_ = stack[3].m_obj;
lean_object* v___y_3261_ = stack[4].m_obj;
lean_object* v_res_3265_;
v_res_3265_ = l_Std_Async_EAsync_instFunctor___redArg___lam__1(v___f_3257_, lean_box(0), lean_box(0), v___y_3260_, v___y_3261_);
stack->m_obj
 = v_res_3265_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___redArg___lam__1___boxed(lean_object* v___f_3266_, lean_object* v_00_u03b1_3267_, lean_object* v_00_u03b2_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l_Std_Async_EAsync_instFunctor___redArg___lam__1(v___f_3266_, v_00_u03b1_3267_, v_00_u03b2_3268_, v___y_3269_, v___y_3270_);
return v_res_3272_;
}
}
lean_object* l_Std_Async_EAsync_instFunctor___redArg(){
_start:
{
lean_object* v___x_3280_; 
v___x_3280_ = ((lean_object*)(l_Std_Async_EAsync_instFunctor___redArg___closed__2));
return v___x_3280_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instFunctor___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3281_;
v_res_3281_ = l_Std_Async_EAsync_instFunctor___redArg();
stack->m_obj
 = v_res_3281_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___redArg___boxed(lean_object* v___dummy_3282_){
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l_Std_Async_EAsync_instFunctor___redArg();
return v_res_3283_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instFunctor___closed__0(void){
_start:
{
lean_object* v___x_3284_; 
v___x_3284_ = l_Std_Async_EAsync_instFunctor___redArg();
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor(lean_object* v_00_u03b5_3285_){
_start:
{
lean_object* v___x_3286_; 
v___x_3286_ = lean_obj_once(&l_Std_Async_EAsync_instFunctor___closed__0, &l_Std_Async_EAsync_instFunctor___closed__0_once, _init_l_Std_Async_EAsync_instFunctor___closed__0);
return v___x_3286_;
}
}
lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__0(lean_object* v_00_u03b1_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3290_, 0, v___y_3288_);
v___x_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3290_);
return v___x_3291_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonad___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3288_ = stack[1].m_obj;
lean_object* v_res_3292_;
v_res_3292_ = l_Std_Async_EAsync_instMonad___redArg___lam__0(lean_box(0), v___y_3288_);
stack->m_obj
 = v_res_3292_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__0___boxed(lean_object* v_00_u03b1_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l_Std_Async_EAsync_instMonad___redArg___lam__0(v_00_u03b1_3293_, v___y_3294_);
return v_res_3296_;
}
}
lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__1(lean_object* v_x_3297_, lean_object* v_x_3298_){
_start:
{
if (lean_obj_tag(v_x_3298_) == 0)
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3308_; 
lean_dec_ref(v_x_3297_);
v_a_3300_ = lean_ctor_get(v_x_3298_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v_x_3298_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3302_ = v_x_3298_;
v_isShared_3303_ = v_isSharedCheck_3308_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v_x_3298_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3308_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3305_; 
if (v_isShared_3303_ == 0)
{
v___x_3305_ = v___x_3302_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_a_3300_);
v___x_3305_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
lean_object* v___x_3306_; 
v___x_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3305_);
return v___x_3306_;
}
}
}
else
{
lean_object* v_a_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; uint8_t v___x_3313_; lean_object* v___x_3314_; lean_object* v___y_3316_; 
v_a_3309_ = lean_ctor_get(v_x_3298_, 0);
lean_inc_n(v_a_3309_, 2);
lean_dec_ref_known(v_x_3298_, 1);
v___x_3310_ = lean_box(0);
v___x_3311_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_3311_, 0, lean_box(0));
lean_closure_set(v___x_3311_, 1, lean_box(0));
lean_closure_set(v___x_3311_, 2, lean_box(0));
lean_closure_set(v___x_3311_, 3, v_a_3309_);
v___x_3312_ = lean_unsigned_to_nat(0u);
v___x_3313_ = 0;
v___x_3314_ = lean_apply_2(v_x_3297_, v___x_3310_, lean_box(0));
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_object* v_a_3318_; 
lean_dec_ref(v___x_3311_);
v_a_3318_ = lean_ctor_get(v___x_3314_, 0);
lean_inc(v_a_3318_);
lean_dec_ref_known(v___x_3314_, 1);
if (lean_obj_tag(v_a_3318_) == 0)
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3326_; 
lean_dec(v_a_3309_);
v_a_3319_ = lean_ctor_get(v_a_3318_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v_a_3318_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3321_ = v_a_3318_;
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v_a_3318_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3324_; 
if (v_isShared_3322_ == 0)
{
v___x_3324_ = v___x_3321_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_a_3319_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
v___y_3316_ = v___x_3324_;
goto v___jp_3315_;
}
}
}
else
{
lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3335_; 
v_a_3327_ = lean_ctor_get(v_a_3318_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v_a_3318_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3329_ = v_a_3318_;
v_isShared_3330_ = v_isSharedCheck_3335_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v_a_3318_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3335_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3331_; lean_object* v___x_3333_; 
v___x_3331_ = lean_apply_1(v_a_3309_, v_a_3327_);
if (v_isShared_3330_ == 0)
{
lean_ctor_set(v___x_3329_, 0, v___x_3331_);
v___x_3333_ = v___x_3329_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v___x_3331_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
v___y_3316_ = v___x_3333_;
goto v___jp_3315_;
}
}
}
}
else
{
lean_object* v_a_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3344_; 
lean_dec(v_a_3309_);
v_a_3336_ = lean_ctor_get(v___x_3314_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3338_ = v___x_3314_;
v_isShared_3339_ = v_isSharedCheck_3344_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_a_3336_);
lean_dec(v___x_3314_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3344_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v___x_3340_; lean_object* v___x_3342_; 
v___x_3340_ = lean_task_map(v___x_3311_, v_a_3336_, v___x_3312_, v___x_3313_);
if (v_isShared_3339_ == 0)
{
lean_ctor_set(v___x_3338_, 0, v___x_3340_);
v___x_3342_ = v___x_3338_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v___x_3340_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
v___jp_3315_:
{
lean_object* v___x_3317_; 
v___x_3317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3317_, 0, v___y_3316_);
return v___x_3317_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonad___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3297_ = stack[0].m_obj;
lean_object* v_x_3298_ = stack[1].m_obj;
lean_object* v_res_3345_;
v_res_3345_ = l_Std_Async_EAsync_instMonad___redArg___lam__1(v_x_3297_, v_x_3298_);
stack->m_obj
 = v_res_3345_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__1___boxed(lean_object* v_x_3346_, lean_object* v_x_3347_, lean_object* v___y_3348_){
_start:
{
lean_object* v_res_3349_; 
v_res_3349_ = l_Std_Async_EAsync_instMonad___redArg___lam__1(v_x_3346_, v_x_3347_);
return v_res_3349_;
}
}
lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__2(lean_object* v_00_u03b1_3350_, lean_object* v_00_u03b2_3351_, lean_object* v_f_3352_, lean_object* v_x_3353_){
_start:
{
lean_object* v___f_3355_; lean_object* v___x_3356_; uint8_t v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___f_3355_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_instMonad___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3355_, 0, v_x_3353_);
v___x_3356_ = lean_unsigned_to_nat(0u);
v___x_3357_ = 0;
v___x_3358_ = lean_apply_1(v_f_3352_, lean_box(0));
v___x_3359_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3356_, v___x_3357_, v___x_3358_, v___f_3355_);
return v___x_3359_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonad___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3352_ = stack[2].m_obj;
lean_object* v_x_3353_ = stack[3].m_obj;
lean_object* v_res_3360_;
v_res_3360_ = l_Std_Async_EAsync_instMonad___redArg___lam__2(lean_box(0), lean_box(0), v_f_3352_, v_x_3353_);
stack->m_obj
 = v_res_3360_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__2___boxed(lean_object* v_00_u03b1_3361_, lean_object* v_00_u03b2_3362_, lean_object* v_f_3363_, lean_object* v_x_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v_res_3366_; 
v_res_3366_ = l_Std_Async_EAsync_instMonad___redArg___lam__2(v_00_u03b1_3361_, v_00_u03b2_3362_, v_f_3363_, v_x_3364_);
return v_res_3366_;
}
}
lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__3(lean_object* v___f_3367_, lean_object* v_a_3368_, lean_object* v_x_3369_){
_start:
{
if (lean_obj_tag(v_x_3369_) == 0)
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3379_; 
lean_dec(v_a_3368_);
lean_dec_ref(v___f_3367_);
v_a_3371_ = lean_ctor_get(v_x_3369_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v_x_3369_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3373_ = v_x_3369_;
v_isShared_3374_ = v_isSharedCheck_3379_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v_x_3369_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3379_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3376_; 
if (v_isShared_3374_ == 0)
{
v___x_3376_ = v___x_3373_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_a_3371_);
v___x_3376_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
lean_object* v___x_3377_; 
v___x_3377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3376_);
return v___x_3377_;
}
}
}
else
{
lean_object* v___x_3380_; 
lean_dec_ref_known(v_x_3369_, 1);
v___x_3380_ = lean_apply_3(v___f_3367_, lean_box(0), v_a_3368_, lean_box(0));
return v___x_3380_;
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonad___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_3367_ = stack[0].m_obj;
lean_object* v_a_3368_ = stack[1].m_obj;
lean_object* v_x_3369_ = stack[2].m_obj;
lean_object* v_res_3381_;
v_res_3381_ = l_Std_Async_EAsync_instMonad___redArg___lam__3(v___f_3367_, v_a_3368_, v_x_3369_);
stack->m_obj
 = v_res_3381_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__3___boxed(lean_object* v___f_3382_, lean_object* v_a_3383_, lean_object* v_x_3384_, lean_object* v___y_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l_Std_Async_EAsync_instMonad___redArg___lam__3(v___f_3382_, v_a_3383_, v_x_3384_);
return v_res_3386_;
}
}
lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__4(lean_object* v___f_3387_, lean_object* v_y_3388_, lean_object* v_x_3389_){
_start:
{
if (lean_obj_tag(v_x_3389_) == 0)
{
lean_object* v___x_3391_; 
lean_dec_ref(v_y_3388_);
lean_dec_ref(v___f_3387_);
v___x_3391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3391_, 0, v_x_3389_);
return v___x_3391_;
}
else
{
lean_object* v_a_3392_; lean_object* v___f_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; uint8_t v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v_a_3392_ = lean_ctor_get(v_x_3389_, 0);
lean_inc(v_a_3392_);
lean_dec_ref_known(v_x_3389_, 1);
v___f_3393_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_instMonad___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_3393_, 0, v___f_3387_);
lean_closure_set(v___f_3393_, 1, v_a_3392_);
v___x_3394_ = lean_box(0);
v___x_3395_ = lean_unsigned_to_nat(0u);
v___x_3396_ = 0;
v___x_3397_ = lean_apply_2(v_y_3388_, v___x_3394_, lean_box(0));
v___x_3398_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3395_, v___x_3396_, v___x_3397_, v___f_3393_);
return v___x_3398_;
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonad___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_3387_ = stack[0].m_obj;
lean_object* v_y_3388_ = stack[1].m_obj;
lean_object* v_x_3389_ = stack[2].m_obj;
lean_object* v_res_3399_;
v_res_3399_ = l_Std_Async_EAsync_instMonad___redArg___lam__4(v___f_3387_, v_y_3388_, v_x_3389_);
stack->m_obj
 = v_res_3399_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__4___boxed(lean_object* v___f_3400_, lean_object* v_y_3401_, lean_object* v_x_3402_, lean_object* v___y_3403_){
_start:
{
lean_object* v_res_3404_; 
v_res_3404_ = l_Std_Async_EAsync_instMonad___redArg___lam__4(v___f_3400_, v_y_3401_, v_x_3402_);
return v_res_3404_;
}
}
lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__5(lean_object* v___f_3405_, lean_object* v_00_u03b1_3406_, lean_object* v_00_u03b2_3407_, lean_object* v_x_3408_, lean_object* v_y_3409_){
_start:
{
lean_object* v___f_3411_; lean_object* v___x_3412_; uint8_t v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___f_3411_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_instMonad___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_3411_, 0, v___f_3405_);
lean_closure_set(v___f_3411_, 1, v_y_3409_);
v___x_3412_ = lean_unsigned_to_nat(0u);
v___x_3413_ = 0;
v___x_3414_ = lean_apply_1(v_x_3408_, lean_box(0));
v___x_3415_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3412_, v___x_3413_, v___x_3414_, v___f_3411_);
return v___x_3415_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonad___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_3405_ = stack[0].m_obj;
lean_object* v_x_3408_ = stack[3].m_obj;
lean_object* v_y_3409_ = stack[4].m_obj;
lean_object* v_res_3416_;
v_res_3416_ = l_Std_Async_EAsync_instMonad___redArg___lam__5(v___f_3405_, lean_box(0), lean_box(0), v_x_3408_, v_y_3409_);
stack->m_obj
 = v_res_3416_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__5___boxed(lean_object* v___f_3417_, lean_object* v_00_u03b1_3418_, lean_object* v_00_u03b2_3419_, lean_object* v_x_3420_, lean_object* v_y_3421_, lean_object* v___y_3422_){
_start:
{
lean_object* v_res_3423_; 
v_res_3423_ = l_Std_Async_EAsync_instMonad___redArg___lam__5(v___f_3417_, v_00_u03b1_3418_, v_00_u03b2_3419_, v_x_3420_, v_y_3421_);
return v_res_3423_;
}
}
lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__6(lean_object* v_y_3424_, lean_object* v_x_3425_){
_start:
{
if (lean_obj_tag(v_x_3425_) == 0)
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3435_; 
lean_dec_ref(v_y_3424_);
v_a_3427_ = lean_ctor_get(v_x_3425_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v_x_3425_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3429_ = v_x_3425_;
v_isShared_3430_ = v_isSharedCheck_3435_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v_x_3425_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3435_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_a_3427_);
v___x_3432_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
lean_object* v___x_3433_; 
v___x_3433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3432_);
return v___x_3433_;
}
}
}
else
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
lean_dec_ref_known(v_x_3425_, 1);
v___x_3436_ = lean_box(0);
v___x_3437_ = lean_apply_2(v_y_3424_, v___x_3436_, lean_box(0));
return v___x_3437_;
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonad___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_y_3424_ = stack[0].m_obj;
lean_object* v_x_3425_ = stack[1].m_obj;
lean_object* v_res_3438_;
v_res_3438_ = l_Std_Async_EAsync_instMonad___redArg___lam__6(v_y_3424_, v_x_3425_);
stack->m_obj
 = v_res_3438_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__6___boxed(lean_object* v_y_3439_, lean_object* v_x_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l_Std_Async_EAsync_instMonad___redArg___lam__6(v_y_3439_, v_x_3440_);
return v_res_3442_;
}
}
lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__7(lean_object* v_00_u03b1_3443_, lean_object* v_00_u03b2_3444_, lean_object* v_x_3445_, lean_object* v_y_3446_){
_start:
{
lean_object* v___f_3448_; lean_object* v___x_3449_; uint8_t v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v___f_3448_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_instMonad___redArg___lam__6___boxed), 3, 1);
lean_closure_set(v___f_3448_, 0, v_y_3446_);
v___x_3449_ = lean_unsigned_to_nat(0u);
v___x_3450_ = 0;
v___x_3451_ = lean_apply_1(v_x_3445_, lean_box(0));
v___x_3452_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3449_, v___x_3450_, v___x_3451_, v___f_3448_);
return v___x_3452_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonad___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3445_ = stack[2].m_obj;
lean_object* v_y_3446_ = stack[3].m_obj;
lean_object* v_res_3453_;
v_res_3453_ = l_Std_Async_EAsync_instMonad___redArg___lam__7(lean_box(0), lean_box(0), v_x_3445_, v_y_3446_);
stack->m_obj
 = v_res_3453_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__7___boxed(lean_object* v_00_u03b1_3454_, lean_object* v_00_u03b2_3455_, lean_object* v_x_3456_, lean_object* v_y_3457_, lean_object* v___y_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l_Std_Async_EAsync_instMonad___redArg___lam__7(v_00_u03b1_3454_, v_00_u03b2_3455_, v_x_3456_, v_y_3457_);
return v_res_3459_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonad___redArg___closed__4(void){
_start:
{
lean_object* v___f_3465_; lean_object* v___f_3466_; lean_object* v___f_3467_; lean_object* v___f_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___f_3465_ = ((lean_object*)(l_Std_Async_EAsync_instMonad___redArg___closed__3));
v___f_3466_ = ((lean_object*)(l_Std_Async_EAsync_instMonad___redArg___closed__2));
v___f_3467_ = ((lean_object*)(l_Std_Async_EAsync_instMonad___redArg___closed__1));
v___f_3468_ = ((lean_object*)(l_Std_Async_EAsync_instMonad___redArg___closed__0));
v___x_3469_ = lean_obj_once(&l_Std_Async_EAsync_instFunctor___closed__0, &l_Std_Async_EAsync_instFunctor___closed__0_once, _init_l_Std_Async_EAsync_instFunctor___closed__0);
v___x_3470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3469_);
lean_ctor_set(v___x_3470_, 1, v___f_3468_);
lean_ctor_set(v___x_3470_, 2, v___f_3467_);
lean_ctor_set(v___x_3470_, 3, v___f_3466_);
lean_ctor_set(v___x_3470_, 4, v___f_3465_);
return v___x_3470_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonad___redArg___closed__6(void){
_start:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3472_ = ((lean_object*)(l_Std_Async_EAsync_instMonad___redArg___closed__5));
v___x_3473_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___redArg___closed__4, &l_Std_Async_EAsync_instMonad___redArg___closed__4_once, _init_l_Std_Async_EAsync_instMonad___redArg___closed__4);
v___x_3474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3473_);
lean_ctor_set(v___x_3474_, 1, v___x_3472_);
return v___x_3474_;
}
}
lean_object* l_Std_Async_EAsync_instMonad___redArg(){
_start:
{
lean_object* v___x_3476_; 
v___x_3476_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___redArg___closed__6, &l_Std_Async_EAsync_instMonad___redArg___closed__6_once, _init_l_Std_Async_EAsync_instMonad___redArg___closed__6);
return v___x_3476_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonad___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3477_;
v_res_3477_ = l_Std_Async_EAsync_instMonad___redArg();
stack->m_obj
 = v_res_3477_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___boxed(lean_object* v___dummy_3478_){
_start:
{
lean_object* v_res_3479_; 
v_res_3479_ = l_Std_Async_EAsync_instMonad___redArg();
return v_res_3479_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonad___closed__0(void){
_start:
{
lean_object* v___x_3480_; 
v___x_3480_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad(lean_object* v_00_u03b5_3481_){
_start:
{
lean_object* v___x_3482_; 
v___x_3482_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___closed__0, &l_Std_Async_EAsync_instMonad___closed__0_once, _init_l_Std_Async_EAsync_instMonad___closed__0);
return v___x_3482_;
}
}
lean_object* l_Std_Async_EAsync_instMonadLiftEIO___redArg(){
_start:
{
lean_object* v___x_3485_; 
v___x_3485_ = ((lean_object*)(l_Std_Async_EAsync_instMonadLiftEIO___redArg___closed__0));
return v___x_3485_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonadLiftEIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3486_;
v_res_3486_ = l_Std_Async_EAsync_instMonadLiftEIO___redArg();
stack->m_obj
 = v_res_3486_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO___redArg___boxed(lean_object* v___dummy_3487_){
_start:
{
lean_object* v_res_3488_; 
v_res_3488_ = l_Std_Async_EAsync_instMonadLiftEIO___redArg();
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO(lean_object* v_00_u03b5_3489_){
_start:
{
lean_object* v___x_3490_; 
v___x_3490_ = ((lean_object*)(l_Std_Async_EAsync_instMonadLiftEIO___redArg___closed__0));
return v___x_3490_;
}
}
lean_object* l_Std_Async_EAsync_instMonadExcept___redArg___lam__1(lean_object* v_00_u03b1_3491_, lean_object* v_x_3492_, lean_object* v_f_3493_){
_start:
{
lean_object* v___f_3495_; lean_object* v___x_3496_; uint8_t v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___f_3495_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_tryCatch___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3495_, 0, v_f_3493_);
v___x_3496_ = lean_unsigned_to_nat(0u);
v___x_3497_ = 0;
v___x_3498_ = lean_apply_1(v_x_3492_, lean_box(0));
v___x_3499_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3496_, v___x_3497_, v___x_3498_, v___f_3495_);
return v___x_3499_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonadExcept___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3492_ = stack[1].m_obj;
lean_object* v_f_3493_ = stack[2].m_obj;
lean_object* v_res_3500_;
v_res_3500_ = l_Std_Async_EAsync_instMonadExcept___redArg___lam__1(lean_box(0), v_x_3492_, v_f_3493_);
stack->m_obj
 = v_res_3500_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExcept___redArg___lam__1___boxed(lean_object* v_00_u03b1_3501_, lean_object* v_x_3502_, lean_object* v_f_3503_, lean_object* v___y_3504_){
_start:
{
lean_object* v_res_3505_; 
v_res_3505_ = l_Std_Async_EAsync_instMonadExcept___redArg___lam__1(v_00_u03b1_3501_, v_x_3502_, v_f_3503_);
return v_res_3505_;
}
}
lean_object* l_Std_Async_EAsync_instMonadExcept___redArg(){
_start:
{
lean_object* v___x_3512_; 
v___x_3512_ = ((lean_object*)(l_Std_Async_EAsync_instMonadExcept___redArg___closed__2));
return v___x_3512_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonadExcept___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3513_;
v_res_3513_ = l_Std_Async_EAsync_instMonadExcept___redArg();
stack->m_obj
 = v_res_3513_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExcept___redArg___boxed(lean_object* v___dummy_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l_Std_Async_EAsync_instMonadExcept___redArg();
return v_res_3515_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonadExcept___closed__0(void){
_start:
{
lean_object* v___x_3516_; 
v___x_3516_ = l_Std_Async_EAsync_instMonadExcept___redArg();
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExcept(lean_object* v_00_u03b5_3517_){
_start:
{
lean_object* v___x_3518_; 
v___x_3518_ = lean_obj_once(&l_Std_Async_EAsync_instMonadExcept___closed__0, &l_Std_Async_EAsync_instMonadExcept___closed__0_once, _init_l_Std_Async_EAsync_instMonadExcept___closed__0);
return v___x_3518_;
}
}
lean_object* l_Std_Async_EAsync_instMonadExceptOf___redArg(){
_start:
{
lean_object* v___x_3523_; 
v___x_3523_ = ((lean_object*)(l_Std_Async_EAsync_instMonadExceptOf___redArg___closed__0));
return v___x_3523_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonadExceptOf___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3524_;
v_res_3524_ = l_Std_Async_EAsync_instMonadExceptOf___redArg();
stack->m_obj
 = v_res_3524_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExceptOf___redArg___boxed(lean_object* v___dummy_3525_){
_start:
{
lean_object* v_res_3526_; 
v_res_3526_ = l_Std_Async_EAsync_instMonadExceptOf___redArg();
return v_res_3526_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonadExceptOf___closed__0(void){
_start:
{
lean_object* v___x_3527_; 
v___x_3527_ = l_Std_Async_EAsync_instMonadExceptOf___redArg();
return v___x_3527_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExceptOf(lean_object* v_00_u03b5_3528_){
_start:
{
lean_object* v___x_3529_; 
v___x_3529_ = lean_obj_once(&l_Std_Async_EAsync_instMonadExceptOf___closed__0, &l_Std_Async_EAsync_instMonadExceptOf___closed__0_once, _init_l_Std_Async_EAsync_instMonadExceptOf___closed__0);
return v___x_3529_;
}
}
lean_object* l_Std_Async_EAsync_instMonadFinally___redArg___lam__0(lean_object* v_00_u03b1_3530_, lean_object* v_00_u03b2_3531_, lean_object* v_x_3532_, lean_object* v_f_3533_){
_start:
{
lean_object* v___x_3535_; uint8_t v___x_3536_; lean_object* v___x_3537_; 
v___x_3535_ = lean_unsigned_to_nat(0u);
v___x_3536_ = 0;
v___x_3537_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v_x_3532_, v_f_3533_, v___x_3535_, v___x_3536_);
return v___x_3537_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonadFinally___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3532_ = stack[2].m_obj;
lean_object* v_f_3533_ = stack[3].m_obj;
lean_object* v_res_3538_;
v_res_3538_ = l_Std_Async_EAsync_instMonadFinally___redArg___lam__0(lean_box(0), lean_box(0), v_x_3532_, v_f_3533_);
stack->m_obj
 = v_res_3538_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadFinally___redArg___lam__0___boxed(lean_object* v_00_u03b1_3539_, lean_object* v_00_u03b2_3540_, lean_object* v_x_3541_, lean_object* v_f_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_Std_Async_EAsync_instMonadFinally___redArg___lam__0(v_00_u03b1_3539_, v_00_u03b2_3540_, v_x_3541_, v_f_3542_);
return v_res_3544_;
}
}
lean_object* l_Std_Async_EAsync_instMonadFinally___redArg(){
_start:
{
lean_object* v___f_3547_; 
v___f_3547_ = ((lean_object*)(l_Std_Async_EAsync_instMonadFinally___redArg___closed__0));
return v___f_3547_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonadFinally___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3548_;
v_res_3548_ = l_Std_Async_EAsync_instMonadFinally___redArg();
stack->m_obj
 = v_res_3548_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadFinally___redArg___boxed(lean_object* v___dummy_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = l_Std_Async_EAsync_instMonadFinally___redArg();
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadFinally(lean_object* v_00_u03b5_3551_){
_start:
{
lean_object* v___f_3552_; 
v___f_3552_ = ((lean_object*)(l_Std_Async_EAsync_instMonadFinally___redArg___closed__0));
return v___f_3552_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instOrElse___redArg___closed__0(void){
_start:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3553_ = lean_obj_once(&l_Std_Async_EAsync_instMonadExcept___closed__0, &l_Std_Async_EAsync_instMonadExcept___closed__0_once, _init_l_Std_Async_EAsync_instMonadExcept___closed__0);
v___x_3554_ = lean_alloc_closure((void*)(l_MonadExcept_orElse), 6, 4);
lean_closure_set(v___x_3554_, 0, lean_box(0));
lean_closure_set(v___x_3554_, 1, lean_box(0));
lean_closure_set(v___x_3554_, 2, v___x_3553_);
lean_closure_set(v___x_3554_, 3, lean_box(0));
return v___x_3554_;
}
}
lean_object* l_Std_Async_EAsync_instOrElse___redArg(){
_start:
{
lean_object* v___x_3556_; 
v___x_3556_ = lean_obj_once(&l_Std_Async_EAsync_instOrElse___redArg___closed__0, &l_Std_Async_EAsync_instOrElse___redArg___closed__0_once, _init_l_Std_Async_EAsync_instOrElse___redArg___closed__0);
return v___x_3556_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instOrElse___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3557_;
v_res_3557_ = l_Std_Async_EAsync_instOrElse___redArg();
stack->m_obj
 = v_res_3557_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instOrElse___redArg___boxed(lean_object* v___dummy_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = l_Std_Async_EAsync_instOrElse___redArg();
return v_res_3559_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instOrElse___closed__0(void){
_start:
{
lean_object* v___x_3560_; 
v___x_3560_ = l_Std_Async_EAsync_instOrElse___redArg();
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instOrElse(lean_object* v_00_u03b5_3561_, lean_object* v_00_u03b1_3562_){
_start:
{
lean_object* v___x_3563_; 
v___x_3563_ = lean_obj_once(&l_Std_Async_EAsync_instOrElse___closed__0, &l_Std_Async_EAsync_instOrElse___closed__0_once, _init_l_Std_Async_EAsync_instOrElse___closed__0);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instInhabited___redArg(lean_object* v_inst_3564_){
_start:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3565_, 0, v_inst_3564_);
v___x_3566_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_pure___boxed), 3, 2);
lean_closure_set(v___x_3566_, 0, lean_box(0));
lean_closure_set(v___x_3566_, 1, v___x_3565_);
v___x_3567_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_mk___boxed), 3, 2);
lean_closure_set(v___x_3567_, 0, lean_box(0));
lean_closure_set(v___x_3567_, 1, v___x_3566_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instInhabited(lean_object* v_00_u03b5_3568_, lean_object* v_00_u03b1_3569_, lean_object* v_inst_3570_){
_start:
{
lean_object* v___x_3571_; 
v___x_3571_ = l_Std_Async_EAsync_instInhabited___redArg(v_inst_3570_);
return v___x_3571_;
}
}
lean_object* l_Std_Async_EAsync_instMonadAwaitETask___redArg___lam__0(lean_object* v_00_u03b1_3572_, lean_object* v_t_3573_){
_start:
{
lean_object* v___x_3575_; 
v___x_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3575_, 0, v_t_3573_);
return v___x_3575_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonadAwaitETask___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_3573_ = stack[1].m_obj;
lean_object* v_res_3576_;
v_res_3576_ = l_Std_Async_EAsync_instMonadAwaitETask___redArg___lam__0(lean_box(0), v_t_3573_);
stack->m_obj
 = v_res_3576_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitETask___redArg___lam__0___boxed(lean_object* v_00_u03b1_3577_, lean_object* v_t_3578_, lean_object* v___y_3579_){
_start:
{
lean_object* v_res_3580_; 
v_res_3580_ = l_Std_Async_EAsync_instMonadAwaitETask___redArg___lam__0(v_00_u03b1_3577_, v_t_3578_);
return v_res_3580_;
}
}
lean_object* l_Std_Async_EAsync_instMonadAwaitETask___redArg(){
_start:
{
lean_object* v___f_3583_; 
v___f_3583_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAwaitETask___redArg___closed__0));
return v___f_3583_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonadAwaitETask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3584_;
v_res_3584_ = l_Std_Async_EAsync_instMonadAwaitETask___redArg();
stack->m_obj
 = v_res_3584_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitETask___redArg___boxed(lean_object* v___dummy_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l_Std_Async_EAsync_instMonadAwaitETask___redArg();
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitETask(lean_object* v_00_u03b5_3587_){
_start:
{
lean_object* v___f_3588_; 
v___f_3588_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAwaitETask___redArg___closed__0));
return v___f_3588_;
}
}
lean_object* l_Std_Async_EAsync_instMonadAwaitTask___redArg___lam__1(lean_object* v___f_3589_, lean_object* v_00_u03b1_3590_, lean_object* v_t_3591_){
_start:
{
lean_object* v___x_3593_; uint8_t v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3593_ = lean_unsigned_to_nat(0u);
v___x_3594_ = 0;
v___x_3595_ = lean_task_map(v___f_3589_, v_t_3591_, v___x_3593_, v___x_3594_);
v___x_3596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3595_);
return v___x_3596_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonadAwaitTask___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_3589_ = stack[0].m_obj;
lean_object* v_t_3591_ = stack[2].m_obj;
lean_object* v_res_3597_;
v_res_3597_ = l_Std_Async_EAsync_instMonadAwaitTask___redArg___lam__1(v___f_3589_, lean_box(0), v_t_3591_);
stack->m_obj
 = v_res_3597_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitTask___redArg___lam__1___boxed(lean_object* v___f_3598_, lean_object* v_00_u03b1_3599_, lean_object* v_t_3600_, lean_object* v___y_3601_){
_start:
{
lean_object* v_res_3602_; 
v_res_3602_ = l_Std_Async_EAsync_instMonadAwaitTask___redArg___lam__1(v___f_3598_, v_00_u03b1_3599_, v_t_3600_);
return v_res_3602_;
}
}
lean_object* l_Std_Async_EAsync_instMonadAwaitTask___redArg(){
_start:
{
lean_object* v___f_3606_; 
v___f_3606_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAwaitTask___redArg___closed__0));
return v___f_3606_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonadAwaitTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3607_;
v_res_3607_ = l_Std_Async_EAsync_instMonadAwaitTask___redArg();
stack->m_obj
 = v_res_3607_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitTask___redArg___boxed(lean_object* v___dummy_3608_){
_start:
{
lean_object* v_res_3609_; 
v_res_3609_ = l_Std_Async_EAsync_instMonadAwaitTask___redArg();
return v_res_3609_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonadAwaitTask___closed__0(void){
_start:
{
lean_object* v___x_3610_; 
v___x_3610_ = l_Std_Async_EAsync_instMonadAwaitTask___redArg();
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitTask(lean_object* v_00_u03b5_3611_){
_start:
{
lean_object* v___x_3612_; 
v___x_3612_ = lean_obj_once(&l_Std_Async_EAsync_instMonadAwaitTask___closed__0, &l_Std_Async_EAsync_instMonadAwaitTask___closed__0_once, _init_l_Std_Async_EAsync_instMonadAwaitTask___closed__0);
return v___x_3612_;
}
}
lean_object* l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___lam__0(lean_object* v_00_u03b1_3613_, lean_object* v_t_3614_){
_start:
{
lean_object* v___x_3616_; 
v___x_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3616_, 0, v_t_3614_);
return v___x_3616_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_3614_ = stack[1].m_obj;
lean_object* v_res_3617_;
v_res_3617_ = l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___lam__0(lean_box(0), v_t_3614_);
stack->m_obj
 = v_res_3617_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___lam__0___boxed(lean_object* v_00_u03b1_3618_, lean_object* v_t_3619_, lean_object* v___y_3620_){
_start:
{
lean_object* v_res_3621_; 
v_res_3621_ = l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___lam__0(v_00_u03b1_3618_, v_t_3619_);
return v_res_3621_;
}
}
lean_object* l_Std_Async_EAsync_instMonadAwaitPromise___redArg___lam__1(lean_object* v___f_3624_, lean_object* v_00_u03b1_3625_, lean_object* v_t_3626_){
_start:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; uint8_t v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3628_ = l_IO_Promise_result_x21___redArg(v_t_3626_);
v___x_3629_ = lean_unsigned_to_nat(0u);
v___x_3630_ = 0;
v___x_3631_ = lean_task_map(v___f_3624_, v___x_3628_, v___x_3629_, v___x_3630_);
v___x_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonadAwaitPromise___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_3624_ = stack[0].m_obj;
lean_object* v_t_3626_ = stack[2].m_obj;
lean_object* v_res_3633_;
v_res_3633_ = l_Std_Async_EAsync_instMonadAwaitPromise___redArg___lam__1(v___f_3624_, lean_box(0), v_t_3626_);
stack->m_obj
 = v_res_3633_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitPromise___redArg___lam__1___boxed(lean_object* v___f_3634_, lean_object* v_00_u03b1_3635_, lean_object* v_t_3636_, lean_object* v___y_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l_Std_Async_EAsync_instMonadAwaitPromise___redArg___lam__1(v___f_3634_, v_00_u03b1_3635_, v_t_3636_);
lean_dec(v_t_3636_);
return v_res_3638_;
}
}
lean_object* l_Std_Async_EAsync_instMonadAwaitPromise___redArg(){
_start:
{
lean_object* v___f_3642_; 
v___f_3642_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAwaitPromise___redArg___closed__0));
return v___f_3642_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonadAwaitPromise___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3643_;
v_res_3643_ = l_Std_Async_EAsync_instMonadAwaitPromise___redArg();
stack->m_obj
 = v_res_3643_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitPromise___redArg___boxed(lean_object* v___dummy_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l_Std_Async_EAsync_instMonadAwaitPromise___redArg();
return v_res_3645_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonadAwaitPromise___closed__0(void){
_start:
{
lean_object* v___x_3646_; 
v___x_3646_ = l_Std_Async_EAsync_instMonadAwaitPromise___redArg();
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitPromise(lean_object* v_00_u03b5_3647_){
_start:
{
lean_object* v___x_3648_; 
v___x_3648_ = lean_obj_once(&l_Std_Async_EAsync_instMonadAwaitPromise___closed__0, &l_Std_Async_EAsync_instMonadAwaitPromise___closed__0_once, _init_l_Std_Async_EAsync_instMonadAwaitPromise___closed__0);
return v___x_3648_;
}
}
lean_object* l_Std_Async_EAsync_instMonadAsyncETask___redArg___lam__1(lean_object* v___f_3649_, lean_object* v_00_u03b1_3650_, lean_object* v_t_3651_, lean_object* v_prio_3652_){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; uint8_t v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3654_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_3654_, 0, lean_box(0));
lean_closure_set(v___x_3654_, 1, v_t_3651_);
v___x_3655_ = lean_io_as_task(v___x_3654_, v_prio_3652_);
v___x_3656_ = lean_unsigned_to_nat(0u);
v___x_3657_ = 1;
v___x_3658_ = lean_task_bind(v___x_3655_, v___f_3649_, v___x_3656_, v___x_3657_);
v___x_3659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3658_);
v___x_3660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3659_);
return v___x_3660_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonadAsyncETask___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_3649_ = stack[0].m_obj;
lean_object* v_t_3651_ = stack[2].m_obj;
lean_object* v_prio_3652_ = stack[3].m_obj;
lean_object* v_res_3661_;
v_res_3661_ = l_Std_Async_EAsync_instMonadAsyncETask___redArg___lam__1(v___f_3649_, lean_box(0), v_t_3651_, v_prio_3652_);
stack->m_obj
 = v_res_3661_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncETask___redArg___lam__1___boxed(lean_object* v___f_3662_, lean_object* v_00_u03b1_3663_, lean_object* v_t_3664_, lean_object* v_prio_3665_, lean_object* v___y_3666_){
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l_Std_Async_EAsync_instMonadAsyncETask___redArg___lam__1(v___f_3662_, v_00_u03b1_3663_, v_t_3664_, v_prio_3665_);
return v_res_3667_;
}
}
lean_object* l_Std_Async_EAsync_instMonadAsyncETask___redArg(){
_start:
{
lean_object* v___f_3671_; 
v___f_3671_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncETask___redArg___closed__0));
return v___f_3671_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonadAsyncETask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3672_;
v_res_3672_ = l_Std_Async_EAsync_instMonadAsyncETask___redArg();
stack->m_obj
 = v_res_3672_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncETask___redArg___boxed(lean_object* v___dummy_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l_Std_Async_EAsync_instMonadAsyncETask___redArg();
return v_res_3674_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonadAsyncETask___closed__0(void){
_start:
{
lean_object* v___x_3675_; 
v___x_3675_ = l_Std_Async_EAsync_instMonadAsyncETask___redArg();
return v___x_3675_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncETask(lean_object* v_00_u03b5_3676_){
_start:
{
lean_object* v___x_3677_; 
v___x_3677_ = lean_obj_once(&l_Std_Async_EAsync_instMonadAsyncETask___closed__0, &l_Std_Async_EAsync_instMonadAsyncETask___closed__0_once, _init_l_Std_Async_EAsync_instMonadAsyncETask___closed__0);
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__0(lean_object* v_x_3678_){
_start:
{
if (lean_obj_tag(v_x_3678_) == 0)
{
lean_object* v_a_3679_; lean_object* v___x_3680_; 
v_a_3679_ = lean_ctor_get(v_x_3678_, 0);
lean_inc(v_a_3679_);
lean_dec_ref_known(v_x_3678_, 1);
v___x_3680_ = lean_task_pure(v_a_3679_);
return v___x_3680_;
}
else
{
lean_object* v_a_3681_; 
v_a_3681_ = lean_ctor_get(v_x_3678_, 0);
lean_inc_ref(v_a_3681_);
lean_dec_ref_known(v_x_3678_, 1);
return v_a_3681_;
}
}
}
lean_object* l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__1(lean_object* v___f_3682_, lean_object* v_00_u03b1_3683_, lean_object* v_t_3684_, lean_object* v_prio_3685_){
_start:
{
lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; uint8_t v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3687_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_3687_, 0, lean_box(0));
lean_closure_set(v___x_3687_, 1, v_t_3684_);
v___x_3688_ = lean_io_as_task(v___x_3687_, v_prio_3685_);
v___x_3689_ = lean_unsigned_to_nat(0u);
v___x_3690_ = 1;
v___x_3691_ = lean_task_bind(v___x_3688_, v___f_3682_, v___x_3689_, v___x_3690_);
v___x_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3691_);
v___x_3693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3692_);
return v___x_3693_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_3682_ = stack[0].m_obj;
lean_object* v_t_3684_ = stack[2].m_obj;
lean_object* v_prio_3685_ = stack[3].m_obj;
lean_object* v_res_3694_;
v_res_3694_ = l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__1(v___f_3682_, lean_box(0), v_t_3684_, v_prio_3685_);
stack->m_obj
 = v_res_3694_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__1___boxed(lean_object* v___f_3695_, lean_object* v_00_u03b1_3696_, lean_object* v_t_3697_, lean_object* v_prio_3698_, lean_object* v___y_3699_){
_start:
{
lean_object* v_res_3700_; 
v_res_3700_ = l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__1(v___f_3695_, v_00_u03b1_3696_, v_t_3697_, v_prio_3698_);
return v_res_3700_;
}
}
lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___lam__0(lean_object* v_00_u03b1_3705_, lean_object* v_x_3706_){
_start:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3708_ = lean_apply_1(v_x_3706_, lean_box(0));
v___x_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3708_);
v___x_3710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3709_);
return v___x_3710_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3706_ = stack[1].m_obj;
lean_object* v_res_3711_;
v_res_3711_ = l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___lam__0(lean_box(0), v_x_3706_);
stack->m_obj
 = v_res_3711_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___lam__0___boxed(lean_object* v_00_u03b1_3712_, lean_object* v_x_3713_, lean_object* v___y_3714_){
_start:
{
lean_object* v_res_3715_; 
v_res_3715_ = l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___lam__0(v_00_u03b1_3712_, v_x_3713_);
return v_res_3715_;
}
}
lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO___redArg(){
_start:
{
lean_object* v___f_3718_; 
v___f_3718_ = ((lean_object*)(l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___closed__0));
return v___f_3718_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonadLiftBaseIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3719_;
v_res_3719_ = l_Std_Async_EAsync_instMonadLiftBaseIO___redArg();
stack->m_obj
 = v_res_3719_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___boxed(lean_object* v___dummy_3720_){
_start:
{
lean_object* v_res_3721_; 
v_res_3721_ = l_Std_Async_EAsync_instMonadLiftBaseIO___redArg();
return v_res_3721_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO(lean_object* v_00_u03b5_3722_){
_start:
{
lean_object* v___f_3723_; 
v___f_3723_ = ((lean_object*)(l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___closed__0));
return v___f_3723_;
}
}
lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___lam__0(lean_object* v_00_u03b1_3724_, lean_object* v_x_3725_){
_start:
{
lean_object* v_val_3728_; lean_object* v___x_3730_; 
v___x_3730_ = lean_apply_1(v_x_3725_, lean_box(0));
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3730_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3730_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
lean_ctor_set_tag(v___x_3733_, 1);
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
v_val_3728_ = v___x_3736_;
goto v___jp_3727_;
}
}
}
else
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
v_a_3739_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___x_3730_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3730_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
lean_ctor_set_tag(v___x_3741_, 0);
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3739_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
v_val_3728_ = v___x_3744_;
goto v___jp_3727_;
}
}
}
v___jp_3727_:
{
lean_object* v___x_3729_; 
v___x_3729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3729_, 0, v_val_3728_);
return v___x_3729_;
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3725_ = stack[1].m_obj;
lean_object* v_res_3747_;
v_res_3747_ = l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___lam__0(lean_box(0), v_x_3725_);
stack->m_obj
 = v_res_3747_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___lam__0___boxed(lean_object* v_00_u03b1_3748_, lean_object* v_x_3749_, lean_object* v___y_3750_){
_start:
{
lean_object* v_res_3751_; 
v_res_3751_ = l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___lam__0(v_00_u03b1_3748_, v_x_3749_);
return v_res_3751_;
}
}
lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1___redArg(){
_start:
{
lean_object* v___f_3754_; 
v___f_3754_ = ((lean_object*)(l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___closed__0));
return v___f_3754_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonadLiftEIO__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3755_;
v_res_3755_ = l_Std_Async_EAsync_instMonadLiftEIO__1___redArg();
stack->m_obj
 = v_res_3755_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___boxed(lean_object* v___dummy_3756_){
_start:
{
lean_object* v_res_3757_; 
v_res_3757_ = l_Std_Async_EAsync_instMonadLiftEIO__1___redArg();
return v_res_3757_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1(lean_object* v_00_u03b5_3758_){
_start:
{
lean_object* v___f_3759_; 
v___f_3759_ = ((lean_object*)(l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___closed__0));
return v___f_3759_;
}
}
lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg___lam__1(lean_object* v___f_3760_, lean_object* v_00_u03b1_3761_, lean_object* v_x_3762_){
_start:
{
lean_object* v___x_3764_; uint8_t v___x_3765_; lean_object* v___x_3766_; 
v___x_3764_ = lean_unsigned_to_nat(0u);
v___x_3765_ = 0;
v___x_3766_ = lean_apply_1(v_x_3762_, lean_box(0));
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3775_; 
lean_dec_ref(v___f_3760_);
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3769_ = v___x_3766_;
v_isShared_3770_ = v_isSharedCheck_3775_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3766_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3775_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3771_; lean_object* v___x_3773_; 
v___x_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3771_, 0, v_a_3767_);
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 0, v___x_3771_);
v___x_3773_ = v___x_3769_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3771_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
else
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3784_; 
v_a_3776_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3778_ = v___x_3766_;
v_isShared_3779_ = v_isSharedCheck_3784_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3766_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3784_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3780_; lean_object* v___x_3782_; 
v___x_3780_ = lean_task_map(v___f_3760_, v_a_3776_, v___x_3764_, v___x_3765_);
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 0, v___x_3780_);
v___x_3782_ = v___x_3778_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v___x_3780_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_3760_ = stack[0].m_obj;
lean_object* v_x_3762_ = stack[2].m_obj;
lean_object* v_res_3785_;
v_res_3785_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg___lam__1(v___f_3760_, lean_box(0), v_x_3762_);
stack->m_obj
 = v_res_3785_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg___lam__1___boxed(lean_object* v___f_3786_, lean_object* v_00_u03b1_3787_, lean_object* v_x_3788_, lean_object* v___y_3789_){
_start:
{
lean_object* v_res_3790_; 
v_res_3790_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg___lam__1(v___f_3786_, v_00_u03b1_3787_, v_x_3788_);
return v_res_3790_;
}
}
lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg(){
_start:
{
lean_object* v___f_3794_; 
v___f_3794_ = ((lean_object*)(l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg___closed__0));
return v___f_3794_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3795_;
v_res_3795_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
stack->m_obj
 = v_res_3795_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg___boxed(lean_object* v___dummy_3796_){
_start:
{
lean_object* v_res_3797_; 
v_res_3797_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
return v_res_3797_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonadLiftBaseAsync___closed__0(void){
_start:
{
lean_object* v___x_3798_; 
v___x_3798_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
return v___x_3798_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync(lean_object* v_00_u03b5_3799_){
_start:
{
lean_object* v___x_3800_; 
v___x_3800_ = lean_obj_once(&l_Std_Async_EAsync_instMonadLiftBaseAsync___closed__0, &l_Std_Async_EAsync_instMonadLiftBaseAsync___closed__0_once, _init_l_Std_Async_EAsync_instMonadLiftBaseAsync___closed__0);
return v___x_3800_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___lam__0___boxed(lean_object* v_promise_3801_, lean_object* v_f_3802_, lean_object* v_prio_3803_, lean_object* v_x_3804_, lean_object* v___y_3805_){
_start:
{
lean_object* v_res_3806_; 
v_res_3806_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___lam__0(v_promise_3801_, v_f_3802_, v_prio_3803_, v_x_3804_);
return v_res_3806_;
}
}
lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(lean_object* v_f_3807_, lean_object* v_prio_3808_, lean_object* v_promise_3809_, lean_object* v_b_3810_){
_start:
{
lean_object* v___f_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; 
lean_inc(v_prio_3808_);
lean_inc_ref_n(v_f_3807_, 2);
lean_inc(v_promise_3809_);
v___f_3812_ = lean_alloc_closure((void*)(l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3812_, 0, v_promise_3809_);
lean_closure_set(v___f_3812_, 1, v_f_3807_);
lean_closure_set(v___f_3812_, 2, v_prio_3808_);
v___x_3813_ = lean_box(0);
v___x_3814_ = lean_apply_3(v_f_3807_, v___x_3813_, v_b_3810_, lean_box(0));
if (lean_obj_tag(v___x_3814_) == 0)
{
lean_object* v_a_3815_; 
lean_dec_ref(v___f_3812_);
v_a_3815_ = lean_ctor_get(v___x_3814_, 0);
lean_inc(v_a_3815_);
lean_dec_ref_known(v___x_3814_, 1);
if (lean_obj_tag(v_a_3815_) == 0)
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3824_; 
lean_dec(v_prio_3808_);
lean_dec_ref(v_f_3807_);
v_a_3816_ = lean_ctor_get(v_a_3815_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v_a_3815_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3818_ = v_a_3815_;
v_isShared_3819_ = v_isSharedCheck_3824_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v_a_3815_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3824_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3821_; 
if (v_isShared_3819_ == 0)
{
v___x_3821_ = v___x_3818_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_a_3816_);
v___x_3821_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
lean_object* v___x_3822_; 
v___x_3822_ = lean_io_promise_resolve(v___x_3821_, v_promise_3809_);
lean_dec(v_promise_3809_);
return v___x_3822_;
}
}
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3836_; 
v_a_3825_ = lean_ctor_get(v_a_3815_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v_a_3815_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3827_ = v_a_3815_;
v_isShared_3828_ = v_isSharedCheck_3836_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v_a_3815_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3836_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
if (lean_obj_tag(v_a_3825_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3831_; 
lean_dec(v_prio_3808_);
lean_dec_ref(v_f_3807_);
v_a_3829_ = lean_ctor_get(v_a_3825_, 0);
lean_inc(v_a_3829_);
lean_dec_ref_known(v_a_3825_, 1);
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 0, v_a_3829_);
v___x_3831_ = v___x_3827_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_a_3829_);
v___x_3831_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
lean_object* v___x_3832_; 
v___x_3832_ = lean_io_promise_resolve(v___x_3831_, v_promise_3809_);
lean_dec(v_promise_3809_);
return v___x_3832_;
}
}
else
{
lean_object* v_a_3834_; 
lean_del_object(v___x_3827_);
v_a_3834_ = lean_ctor_get(v_a_3825_, 0);
lean_inc(v_a_3834_);
lean_dec_ref_known(v_a_3825_, 1);
v_b_3810_ = v_a_3834_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3837_; uint8_t v___x_3838_; lean_object* v___x_3839_; 
lean_dec(v_promise_3809_);
lean_dec_ref(v_f_3807_);
v_a_3837_ = lean_ctor_get(v___x_3814_, 0);
lean_inc_ref(v_a_3837_);
lean_dec_ref_known(v___x_3814_, 1);
v___x_3838_ = 0;
v___x_3839_ = l_BaseIO_chainTask___redArg(v_a_3837_, v___f_3812_, v_prio_3808_, v___x_3838_);
return v___x_3839_;
}
}
}
LEAN_EXPORT void l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3807_ = stack[0].m_obj;
lean_object* v_prio_3808_ = stack[1].m_obj;
lean_object* v_promise_3809_ = stack[2].m_obj;
lean_object* v_b_3810_ = stack[3].m_obj;
lean_object* v_res_3840_;
v_res_3840_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(v_f_3807_, v_prio_3808_, v_promise_3809_, v_b_3810_);
stack->m_obj
 = v_res_3840_;
}
lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___lam__0(lean_object* v_promise_3841_, lean_object* v_f_3842_, lean_object* v_prio_3843_, lean_object* v_x_3844_){
_start:
{
if (lean_obj_tag(v_x_3844_) == 0)
{
lean_object* v_a_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3854_; 
lean_dec(v_prio_3843_);
lean_dec_ref(v_f_3842_);
v_a_3846_ = lean_ctor_get(v_x_3844_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v_x_3844_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3848_ = v_x_3844_;
v_isShared_3849_ = v_isSharedCheck_3854_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_a_3846_);
lean_dec(v_x_3844_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3854_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3851_; 
if (v_isShared_3849_ == 0)
{
v___x_3851_ = v___x_3848_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_a_3846_);
v___x_3851_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
lean_object* v___x_3852_; 
v___x_3852_ = lean_io_promise_resolve(v___x_3851_, v_promise_3841_);
lean_dec(v_promise_3841_);
return v___x_3852_;
}
}
}
else
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3866_; 
v_a_3855_ = lean_ctor_get(v_x_3844_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v_x_3844_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3857_ = v_x_3844_;
v_isShared_3858_ = v_isSharedCheck_3866_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v_x_3844_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3866_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
if (lean_obj_tag(v_a_3855_) == 0)
{
lean_object* v_a_3859_; lean_object* v___x_3861_; 
lean_dec(v_prio_3843_);
lean_dec_ref(v_f_3842_);
v_a_3859_ = lean_ctor_get(v_a_3855_, 0);
lean_inc(v_a_3859_);
lean_dec_ref_known(v_a_3855_, 1);
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 0, v_a_3859_);
v___x_3861_ = v___x_3857_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_a_3859_);
v___x_3861_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
lean_object* v___x_3862_; 
v___x_3862_ = lean_io_promise_resolve(v___x_3861_, v_promise_3841_);
lean_dec(v_promise_3841_);
return v___x_3862_;
}
}
else
{
lean_object* v_a_3864_; lean_object* v___x_3865_; 
lean_del_object(v___x_3857_);
v_a_3864_ = lean_ctor_get(v_a_3855_, 0);
lean_inc(v_a_3864_);
lean_dec_ref_known(v_a_3855_, 1);
v___x_3865_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(v_f_3842_, v_prio_3843_, v_promise_3841_, v_a_3864_);
return v___x_3865_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_promise_3841_ = stack[0].m_obj;
lean_object* v_f_3842_ = stack[1].m_obj;
lean_object* v_prio_3843_ = stack[2].m_obj;
lean_object* v_x_3844_ = stack[3].m_obj;
lean_object* v_res_3867_;
v_res_3867_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___lam__0(v_promise_3841_, v_f_3842_, v_prio_3843_, v_x_3844_);
stack->m_obj
 = v_res_3867_;
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___boxed(lean_object* v_f_3868_, lean_object* v_prio_3869_, lean_object* v_promise_3870_, lean_object* v_b_3871_, lean_object* v_a_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(v_f_3868_, v_prio_3869_, v_promise_3870_, v_b_3871_);
return v_res_3873_;
}
}
lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_object* v_00_u03b5_3874_, lean_object* v_00_u03b2_3875_, lean_object* v_f_3876_, lean_object* v_prio_3877_, lean_object* v_promise_3878_, lean_object* v_b_3879_){
_start:
{
lean_object* v___x_3881_; 
v___x_3881_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(v_f_3876_, v_prio_3877_, v_promise_3878_, v_b_3879_);
return v___x_3881_;
}
}
LEAN_EXPORT void l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3876_ = stack[2].m_obj;
lean_object* v_prio_3877_ = stack[3].m_obj;
lean_object* v_promise_3878_ = stack[4].m_obj;
lean_object* v_b_3879_ = stack[5].m_obj;
lean_object* v_res_3882_;
v_res_3882_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v_f_3876_, v_prio_3877_, v_promise_3878_, v_b_3879_);
stack->m_obj
 = v_res_3882_;
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___boxed(lean_object* v_00_u03b5_3883_, lean_object* v_00_u03b2_3884_, lean_object* v_f_3885_, lean_object* v_prio_3886_, lean_object* v_promise_3887_, lean_object* v_b_3888_, lean_object* v_a_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(v_00_u03b5_3883_, v_00_u03b2_3884_, v_f_3885_, v_prio_3886_, v_promise_3887_, v_b_3888_);
return v_res_3890_;
}
}
lean_object* l_Std_Async_EAsync_forIn___redArg___lam__0(lean_object* v_a_3891_, lean_object* v_x_3892_){
_start:
{
if (lean_obj_tag(v_x_3892_) == 0)
{
lean_object* v_a_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3902_; 
v_a_3894_ = lean_ctor_get(v_x_3892_, 0);
v_isSharedCheck_3902_ = !lean_is_exclusive(v_x_3892_);
if (v_isSharedCheck_3902_ == 0)
{
v___x_3896_ = v_x_3892_;
v_isShared_3897_ = v_isSharedCheck_3902_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_a_3894_);
lean_dec(v_x_3892_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3902_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
lean_object* v___x_3899_; 
if (v_isShared_3897_ == 0)
{
v___x_3899_ = v___x_3896_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v_a_3894_);
v___x_3899_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
lean_object* v___x_3900_; 
v___x_3900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3899_);
return v___x_3900_;
}
}
}
else
{
lean_object* v___x_3903_; lean_object* v___x_3904_; 
lean_dec_ref_known(v_x_3892_, 1);
v___x_3903_ = l_IO_Promise_result_x21___redArg(v_a_3891_);
v___x_3904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3903_);
return v___x_3904_;
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_forIn___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3891_ = stack[0].m_obj;
lean_object* v_x_3892_ = stack[1].m_obj;
lean_object* v_res_3905_;
v_res_3905_ = l_Std_Async_EAsync_forIn___redArg___lam__0(v_a_3891_, v_x_3892_);
stack->m_obj
 = v_res_3905_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg___lam__0___boxed(lean_object* v_a_3906_, lean_object* v_x_3907_, lean_object* v___y_3908_){
_start:
{
lean_object* v_res_3909_; 
v_res_3909_ = l_Std_Async_EAsync_forIn___redArg___lam__0(v_a_3906_, v_x_3907_);
lean_dec(v_a_3906_);
return v_res_3909_;
}
}
lean_object* l_Std_Async_EAsync_forIn___redArg___lam__1(lean_object* v_f_3910_, lean_object* v_prio_3911_, lean_object* v_init_3912_, lean_object* v_x_3913_){
_start:
{
if (lean_obj_tag(v_x_3913_) == 0)
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3923_; 
lean_dec(v_init_3912_);
lean_dec(v_prio_3911_);
lean_dec_ref(v_f_3910_);
v_a_3915_ = lean_ctor_get(v_x_3913_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v_x_3913_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3917_ = v_x_3913_;
v_isShared_3918_ = v_isSharedCheck_3923_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v_x_3913_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3923_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_a_3915_);
v___x_3920_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
lean_object* v___x_3921_; 
v___x_3921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3920_);
return v___x_3921_;
}
}
}
else
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3937_; 
v_a_3924_ = lean_ctor_get(v_x_3913_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v_x_3913_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3926_ = v_x_3913_;
v_isShared_3927_ = v_isSharedCheck_3937_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v_x_3913_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3937_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___f_3928_; lean_object* v___x_3929_; uint8_t v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3933_; 
lean_inc(v_a_3924_);
v___f_3928_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_forIn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3928_, 0, v_a_3924_);
v___x_3929_ = lean_unsigned_to_nat(0u);
v___x_3930_ = 0;
v___x_3931_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(v_f_3910_, v_prio_3911_, v_a_3924_, v_init_3912_);
if (v_isShared_3927_ == 0)
{
lean_ctor_set(v___x_3926_, 0, v___x_3931_);
v___x_3933_ = v___x_3926_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v___x_3931_);
v___x_3933_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
lean_object* v___x_3934_; lean_object* v___x_3935_; 
v___x_3934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3933_);
v___x_3935_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3929_, v___x_3930_, v___x_3934_, v___f_3928_);
return v___x_3935_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_forIn___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3910_ = stack[0].m_obj;
lean_object* v_prio_3911_ = stack[1].m_obj;
lean_object* v_init_3912_ = stack[2].m_obj;
lean_object* v_x_3913_ = stack[3].m_obj;
lean_object* v_res_3938_;
v_res_3938_ = l_Std_Async_EAsync_forIn___redArg___lam__1(v_f_3910_, v_prio_3911_, v_init_3912_, v_x_3913_);
stack->m_obj
 = v_res_3938_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg___lam__1___boxed(lean_object* v_f_3939_, lean_object* v_prio_3940_, lean_object* v_init_3941_, lean_object* v_x_3942_, lean_object* v___y_3943_){
_start:
{
lean_object* v_res_3944_; 
v_res_3944_ = l_Std_Async_EAsync_forIn___redArg___lam__1(v_f_3939_, v_prio_3940_, v_init_3941_, v_x_3942_);
return v_res_3944_;
}
}
lean_object* l_Std_Async_EAsync_forIn___redArg(lean_object* v_init_3945_, lean_object* v_f_3946_, lean_object* v_prio_3947_){
_start:
{
lean_object* v___f_3949_; lean_object* v___x_3950_; uint8_t v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v___f_3949_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_forIn___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_3949_, 0, v_f_3946_);
lean_closure_set(v___f_3949_, 1, v_prio_3947_);
lean_closure_set(v___f_3949_, 2, v_init_3945_);
v___x_3950_ = lean_unsigned_to_nat(0u);
v___x_3951_ = 0;
v___x_3952_ = lean_io_promise_new();
v___x_3953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3952_);
v___x_3954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3953_);
v___x_3955_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3950_, v___x_3951_, v___x_3954_, v___f_3949_);
return v___x_3955_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_forIn___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_3945_ = stack[0].m_obj;
lean_object* v_f_3946_ = stack[1].m_obj;
lean_object* v_prio_3947_ = stack[2].m_obj;
lean_object* v_res_3956_;
v_res_3956_ = l_Std_Async_EAsync_forIn___redArg(v_init_3945_, v_f_3946_, v_prio_3947_);
stack->m_obj
 = v_res_3956_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg___boxed(lean_object* v_init_3957_, lean_object* v_f_3958_, lean_object* v_prio_3959_, lean_object* v_a_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_Std_Async_EAsync_forIn___redArg(v_init_3957_, v_f_3958_, v_prio_3959_);
return v_res_3961_;
}
}
lean_object* l_Std_Async_EAsync_forIn(lean_object* v_00_u03b5_3962_, lean_object* v_00_u03b2_3963_, lean_object* v_init_3964_, lean_object* v_f_3965_, lean_object* v_prio_3966_){
_start:
{
lean_object* v___f_3968_; lean_object* v___x_3969_; uint8_t v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___f_3968_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_forIn___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_3968_, 0, v_f_3965_);
lean_closure_set(v___f_3968_, 1, v_prio_3966_);
lean_closure_set(v___f_3968_, 2, v_init_3964_);
v___x_3969_ = lean_unsigned_to_nat(0u);
v___x_3970_ = 0;
v___x_3971_ = lean_io_promise_new();
v___x_3972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
v___x_3973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3972_);
v___x_3974_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3969_, v___x_3970_, v___x_3973_, v___f_3968_);
return v___x_3974_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_forIn_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_3964_ = stack[2].m_obj;
lean_object* v_f_3965_ = stack[3].m_obj;
lean_object* v_prio_3966_ = stack[4].m_obj;
lean_object* v_res_3975_;
v_res_3975_ = l_Std_Async_EAsync_forIn(lean_box(0), lean_box(0), v_init_3964_, v_f_3965_, v_prio_3966_);
stack->m_obj
 = v_res_3975_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___boxed(lean_object* v_00_u03b5_3976_, lean_object* v_00_u03b2_3977_, lean_object* v_init_3978_, lean_object* v_f_3979_, lean_object* v_prio_3980_, lean_object* v_a_3981_){
_start:
{
lean_object* v_res_3982_; 
v_res_3982_ = l_Std_Async_EAsync_forIn(v_00_u03b5_3976_, v_00_u03b2_3977_, v_init_3978_, v_f_3979_, v_prio_3980_);
return v_res_3982_;
}
}
lean_object* l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__1(lean_object* v_f_3983_, lean_object* v___x_3984_, lean_object* v_init_3985_, lean_object* v_x_3986_){
_start:
{
if (lean_obj_tag(v_x_3986_) == 0)
{
lean_object* v_a_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3996_; 
lean_dec(v_init_3985_);
lean_dec(v___x_3984_);
lean_dec_ref(v_f_3983_);
v_a_3988_ = lean_ctor_get(v_x_3986_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v_x_3986_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3990_ = v_x_3986_;
v_isShared_3991_ = v_isSharedCheck_3996_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_a_3988_);
lean_dec(v_x_3986_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3996_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3993_; 
if (v_isShared_3991_ == 0)
{
v___x_3993_ = v___x_3990_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_a_3988_);
v___x_3993_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
lean_object* v___x_3994_; 
v___x_3994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3993_);
return v___x_3994_;
}
}
}
else
{
lean_object* v_a_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4009_; 
v_a_3997_ = lean_ctor_get(v_x_3986_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v_x_3986_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_3999_ = v_x_3986_;
v_isShared_4000_ = v_isSharedCheck_4009_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_a_3997_);
lean_dec(v_x_3986_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4009_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___f_4001_; uint8_t v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4005_; 
lean_inc(v_a_3997_);
v___f_4001_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_forIn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4001_, 0, v_a_3997_);
v___x_4002_ = 0;
lean_inc(v___x_3984_);
v___x_4003_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(v_f_3983_, v___x_3984_, v_a_3997_, v_init_3985_);
if (v_isShared_4000_ == 0)
{
lean_ctor_set(v___x_3999_, 0, v___x_4003_);
v___x_4005_ = v___x_3999_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v___x_4003_);
v___x_4005_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_4006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4005_);
v___x_4007_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3984_, v___x_4002_, v___x_4006_, v___f_4001_);
return v___x_4007_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3983_ = stack[0].m_obj;
lean_object* v___x_3984_ = stack[1].m_obj;
lean_object* v_init_3985_ = stack[2].m_obj;
lean_object* v_x_3986_ = stack[3].m_obj;
lean_object* v_res_4010_;
v_res_4010_ = l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__1(v_f_3983_, v___x_3984_, v_init_3985_, v_x_3986_);
stack->m_obj
 = v_res_4010_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__1___boxed(lean_object* v_f_4011_, lean_object* v___x_4012_, lean_object* v_init_4013_, lean_object* v_x_4014_, lean_object* v___y_4015_){
_start:
{
lean_object* v_res_4016_; 
v_res_4016_ = l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__1(v_f_4011_, v___x_4012_, v_init_4013_, v_x_4014_);
return v_res_4016_;
}
}
lean_object* l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__0(lean_object* v_00_u03b2_4017_, lean_object* v_x_4018_, lean_object* v_init_4019_, lean_object* v_f_4020_){
_start:
{
lean_object* v___x_4022_; lean_object* v___f_4023_; uint8_t v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4022_ = lean_unsigned_to_nat(0u);
v___f_4023_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4023_, 0, v_f_4020_);
lean_closure_set(v___f_4023_, 1, v___x_4022_);
lean_closure_set(v___f_4023_, 2, v_init_4019_);
v___x_4024_ = 0;
v___x_4025_ = lean_io_promise_new();
v___x_4026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4026_, 0, v___x_4025_);
v___x_4027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4027_, 0, v___x_4026_);
v___x_4028_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4022_, v___x_4024_, v___x_4027_, v___f_4023_);
return v___x_4028_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4018_ = stack[1].m_obj;
lean_object* v_init_4019_ = stack[2].m_obj;
lean_object* v_f_4020_ = stack[3].m_obj;
lean_object* v_res_4029_;
v_res_4029_ = l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__0(lean_box(0), v_x_4018_, v_init_4019_, v_f_4020_);
stack->m_obj
 = v_res_4029_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__0___boxed(lean_object* v_00_u03b2_4030_, lean_object* v_x_4031_, lean_object* v_init_4032_, lean_object* v_f_4033_, lean_object* v___y_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__0(v_00_u03b2_4030_, v_x_4031_, v_init_4032_, v_f_4033_);
return v_res_4035_;
}
}
lean_object* l_Std_Async_EAsync_instForInLoopUnit___redArg(){
_start:
{
lean_object* v___f_4038_; 
v___f_4038_ = ((lean_object*)(l_Std_Async_EAsync_instForInLoopUnit___redArg___closed__0));
return v___f_4038_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_instForInLoopUnit___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4039_;
v_res_4039_ = l_Std_Async_EAsync_instForInLoopUnit___redArg();
stack->m_obj
 = v_res_4039_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___redArg___boxed(lean_object* v___dummy_4040_){
_start:
{
lean_object* v_res_4041_; 
v_res_4041_ = l_Std_Async_EAsync_instForInLoopUnit___redArg();
return v_res_4041_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit(lean_object* v_00_u03b5_4042_){
_start:
{
lean_object* v___f_4043_; 
v___f_4043_ = ((lean_object*)(l_Std_Async_EAsync_instForInLoopUnit___redArg___closed__0));
return v___f_4043_;
}
}
lean_object* l_Std_Async_EAsync_ofExcept___redArg(lean_object* v_except_4044_){
_start:
{
lean_object* v___x_4046_; 
v___x_4046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4046_, 0, v_except_4044_);
return v___x_4046_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_ofExcept___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_except_4044_ = stack[0].m_obj;
lean_object* v_res_4047_;
v_res_4047_ = l_Std_Async_EAsync_ofExcept___redArg(v_except_4044_);
stack->m_obj
 = v_res_4047_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofExcept___redArg___boxed(lean_object* v_except_4048_, lean_object* v_a_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l_Std_Async_EAsync_ofExcept___redArg(v_except_4048_);
return v_res_4050_;
}
}
lean_object* l_Std_Async_EAsync_ofExcept(lean_object* v_00_u03b5_4051_, lean_object* v_00_u03b1_4052_, lean_object* v_except_4053_){
_start:
{
lean_object* v___x_4055_; 
v___x_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4055_, 0, v_except_4053_);
return v___x_4055_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_ofExcept_0interp(lean_interpreter_value* stack)
{
lean_object* v_except_4053_ = stack[2].m_obj;
lean_object* v_res_4056_;
v_res_4056_ = l_Std_Async_EAsync_ofExcept(lean_box(0), lean_box(0), v_except_4053_);
stack->m_obj
 = v_res_4056_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofExcept___boxed(lean_object* v_00_u03b5_4057_, lean_object* v_00_u03b1_4058_, lean_object* v_except_4059_, lean_object* v_a_4060_){
_start:
{
lean_object* v_res_4061_; 
v_res_4061_ = l_Std_Async_EAsync_ofExcept(v_00_u03b5_4057_, v_00_u03b1_4058_, v_except_4059_);
return v_res_4061_;
}
}
lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__1(lean_object* v_a_4062_, lean_object* v_x_4063_){
_start:
{
if (lean_obj_tag(v_x_4063_) == 0)
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4073_; 
lean_dec(v_a_4062_);
v_a_4065_ = lean_ctor_get(v_x_4063_, 0);
v_isSharedCheck_4073_ = !lean_is_exclusive(v_x_4063_);
if (v_isSharedCheck_4073_ == 0)
{
v___x_4067_ = v_x_4063_;
v_isShared_4068_ = v_isSharedCheck_4073_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v_x_4063_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4073_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4070_; 
if (v_isShared_4068_ == 0)
{
v___x_4070_ = v___x_4067_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v_a_4065_);
v___x_4070_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
lean_object* v___x_4071_; 
v___x_4071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4071_, 0, v___x_4070_);
return v___x_4071_;
}
}
}
else
{
lean_object* v_a_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4083_; 
v_a_4074_ = lean_ctor_get(v_x_4063_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v_x_4063_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4076_ = v_x_4063_;
v_isShared_4077_ = v_isSharedCheck_4083_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_a_4074_);
lean_dec(v_x_4063_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4083_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v___x_4078_; lean_object* v___x_4080_; 
v___x_4078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4078_, 0, v_a_4062_);
lean_ctor_set(v___x_4078_, 1, v_a_4074_);
if (v_isShared_4077_ == 0)
{
lean_ctor_set(v___x_4076_, 0, v___x_4078_);
v___x_4080_ = v___x_4076_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v___x_4078_);
v___x_4080_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
lean_object* v___x_4081_; 
v___x_4081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4080_);
return v___x_4081_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_concurrently___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4062_ = stack[0].m_obj;
lean_object* v_x_4063_ = stack[1].m_obj;
lean_object* v_res_4084_;
v_res_4084_ = l_Std_Async_EAsync_concurrently___redArg___lam__1(v_a_4062_, v_x_4063_);
stack->m_obj
 = v_res_4084_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__1___boxed(lean_object* v_a_4085_, lean_object* v_x_4086_, lean_object* v___y_4087_){
_start:
{
lean_object* v_res_4088_; 
v_res_4088_ = l_Std_Async_EAsync_concurrently___redArg___lam__1(v_a_4085_, v_x_4086_);
return v_res_4088_;
}
}
lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__0(lean_object* v_a_4089_, lean_object* v_x_4090_){
_start:
{
if (lean_obj_tag(v_x_4090_) == 0)
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4100_; 
lean_dec_ref(v_a_4089_);
v_a_4092_ = lean_ctor_get(v_x_4090_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v_x_4090_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4094_ = v_x_4090_;
v_isShared_4095_ = v_isSharedCheck_4100_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v_x_4090_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4100_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4097_; 
if (v_isShared_4095_ == 0)
{
v___x_4097_ = v___x_4094_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_a_4092_);
v___x_4097_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
lean_object* v___x_4098_; 
v___x_4098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4097_);
return v___x_4098_;
}
}
}
else
{
lean_object* v_a_4101_; lean_object* v___f_4102_; lean_object* v___x_4103_; uint8_t v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; 
v_a_4101_ = lean_ctor_get(v_x_4090_, 0);
lean_inc(v_a_4101_);
lean_dec_ref_known(v_x_4090_, 1);
v___f_4102_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrently___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4102_, 0, v_a_4101_);
v___x_4103_ = lean_unsigned_to_nat(0u);
v___x_4104_ = 0;
v___x_4105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4105_, 0, v_a_4089_);
v___x_4106_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4103_, v___x_4104_, v___x_4105_, v___f_4102_);
return v___x_4106_;
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_concurrently___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4089_ = stack[0].m_obj;
lean_object* v_x_4090_ = stack[1].m_obj;
lean_object* v_res_4107_;
v_res_4107_ = l_Std_Async_EAsync_concurrently___redArg___lam__0(v_a_4089_, v_x_4090_);
stack->m_obj
 = v_res_4107_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__0___boxed(lean_object* v_a_4108_, lean_object* v_x_4109_, lean_object* v___y_4110_){
_start:
{
lean_object* v_res_4111_; 
v_res_4111_ = l_Std_Async_EAsync_concurrently___redArg___lam__0(v_a_4108_, v_x_4109_);
return v_res_4111_;
}
}
lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__2(lean_object* v_a_4112_, lean_object* v_x_4113_){
_start:
{
if (lean_obj_tag(v_x_4113_) == 0)
{
lean_object* v_a_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4123_; 
lean_dec_ref(v_a_4112_);
v_a_4115_ = lean_ctor_get(v_x_4113_, 0);
v_isSharedCheck_4123_ = !lean_is_exclusive(v_x_4113_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4117_ = v_x_4113_;
v_isShared_4118_ = v_isSharedCheck_4123_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_a_4115_);
lean_dec(v_x_4113_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4123_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4120_; 
if (v_isShared_4118_ == 0)
{
v___x_4120_ = v___x_4117_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_a_4115_);
v___x_4120_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
lean_object* v___x_4121_; 
v___x_4121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4120_);
return v___x_4121_;
}
}
}
else
{
lean_object* v_a_4124_; lean_object* v___f_4125_; lean_object* v___x_4126_; uint8_t v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
v_a_4124_ = lean_ctor_get(v_x_4113_, 0);
lean_inc(v_a_4124_);
lean_dec_ref_known(v_x_4113_, 1);
v___f_4125_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrently___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4125_, 0, v_a_4124_);
v___x_4126_ = lean_unsigned_to_nat(0u);
v___x_4127_ = 0;
v___x_4128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4128_, 0, v_a_4112_);
v___x_4129_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4126_, v___x_4127_, v___x_4128_, v___f_4125_);
return v___x_4129_;
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_concurrently___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4112_ = stack[0].m_obj;
lean_object* v_x_4113_ = stack[1].m_obj;
lean_object* v_res_4130_;
v_res_4130_ = l_Std_Async_EAsync_concurrently___redArg___lam__2(v_a_4112_, v_x_4113_);
stack->m_obj
 = v_res_4130_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__2___boxed(lean_object* v_a_4131_, lean_object* v_x_4132_, lean_object* v___y_4133_){
_start:
{
lean_object* v_res_4134_; 
v_res_4134_ = l_Std_Async_EAsync_concurrently___redArg___lam__2(v_a_4131_, v_x_4132_);
return v_res_4134_;
}
}
lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__3(lean_object* v_y_4135_, lean_object* v_prio_4136_, lean_object* v___f_4137_, lean_object* v_x_4138_){
_start:
{
if (lean_obj_tag(v_x_4138_) == 0)
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4148_; 
lean_dec_ref(v___f_4137_);
lean_dec(v_prio_4136_);
lean_dec_ref(v_y_4135_);
v_a_4140_ = lean_ctor_get(v_x_4138_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v_x_4138_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4142_ = v_x_4138_;
v_isShared_4143_ = v_isSharedCheck_4148_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v_x_4138_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4148_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4145_; 
if (v_isShared_4143_ == 0)
{
v___x_4145_ = v___x_4142_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4140_);
v___x_4145_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
lean_object* v___x_4146_; 
v___x_4146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4145_);
return v___x_4146_;
}
}
}
else
{
lean_object* v_a_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4165_; 
v_a_4149_ = lean_ctor_get(v_x_4138_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v_x_4138_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4151_ = v_x_4138_;
v_isShared_4152_ = v_isSharedCheck_4165_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_a_4149_);
lean_dec(v_x_4138_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4165_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___f_4153_; lean_object* v___x_4154_; uint8_t v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; uint8_t v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4161_; 
v___f_4153_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrently___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4153_, 0, v_a_4149_);
v___x_4154_ = lean_unsigned_to_nat(0u);
v___x_4155_ = 0;
v___x_4156_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4156_, 0, lean_box(0));
lean_closure_set(v___x_4156_, 1, v_y_4135_);
v___x_4157_ = lean_io_as_task(v___x_4156_, v_prio_4136_);
v___x_4158_ = 1;
v___x_4159_ = lean_task_bind(v___x_4157_, v___f_4137_, v___x_4154_, v___x_4158_);
if (v_isShared_4152_ == 0)
{
lean_ctor_set(v___x_4151_, 0, v___x_4159_);
v___x_4161_ = v___x_4151_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v___x_4159_);
v___x_4161_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
lean_object* v___x_4162_; lean_object* v___x_4163_; 
v___x_4162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4161_);
v___x_4163_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4154_, v___x_4155_, v___x_4162_, v___f_4153_);
return v___x_4163_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_concurrently___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_y_4135_ = stack[0].m_obj;
lean_object* v_prio_4136_ = stack[1].m_obj;
lean_object* v___f_4137_ = stack[2].m_obj;
lean_object* v_x_4138_ = stack[3].m_obj;
lean_object* v_res_4166_;
v_res_4166_ = l_Std_Async_EAsync_concurrently___redArg___lam__3(v_y_4135_, v_prio_4136_, v___f_4137_, v_x_4138_);
stack->m_obj
 = v_res_4166_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__3___boxed(lean_object* v_y_4167_, lean_object* v_prio_4168_, lean_object* v___f_4169_, lean_object* v_x_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v_res_4172_; 
v_res_4172_ = l_Std_Async_EAsync_concurrently___redArg___lam__3(v_y_4167_, v_prio_4168_, v___f_4169_, v_x_4170_);
return v_res_4172_;
}
}
lean_object* l_Std_Async_EAsync_concurrently___redArg(lean_object* v_x_4173_, lean_object* v_y_4174_, lean_object* v_prio_4175_){
_start:
{
lean_object* v___f_4177_; lean_object* v___f_4178_; lean_object* v___x_4179_; uint8_t v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; uint8_t v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; 
v___f_4177_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
lean_inc(v_prio_4175_);
v___f_4178_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrently___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_4178_, 0, v_y_4174_);
lean_closure_set(v___f_4178_, 1, v_prio_4175_);
lean_closure_set(v___f_4178_, 2, v___f_4177_);
v___x_4179_ = lean_unsigned_to_nat(0u);
v___x_4180_ = 0;
v___x_4181_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4181_, 0, lean_box(0));
lean_closure_set(v___x_4181_, 1, v_x_4173_);
v___x_4182_ = lean_io_as_task(v___x_4181_, v_prio_4175_);
v___x_4183_ = 1;
v___x_4184_ = lean_task_bind(v___x_4182_, v___f_4177_, v___x_4179_, v___x_4183_);
v___x_4185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4184_);
v___x_4186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4186_, 0, v___x_4185_);
v___x_4187_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4179_, v___x_4180_, v___x_4186_, v___f_4178_);
return v___x_4187_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_concurrently___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4173_ = stack[0].m_obj;
lean_object* v_y_4174_ = stack[1].m_obj;
lean_object* v_prio_4175_ = stack[2].m_obj;
lean_object* v_res_4188_;
v_res_4188_ = l_Std_Async_EAsync_concurrently___redArg(v_x_4173_, v_y_4174_, v_prio_4175_);
stack->m_obj
 = v_res_4188_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___boxed(lean_object* v_x_4189_, lean_object* v_y_4190_, lean_object* v_prio_4191_, lean_object* v_a_4192_){
_start:
{
lean_object* v_res_4193_; 
v_res_4193_ = l_Std_Async_EAsync_concurrently___redArg(v_x_4189_, v_y_4190_, v_prio_4191_);
return v_res_4193_;
}
}
lean_object* l_Std_Async_EAsync_concurrently(lean_object* v_00_u03b5_4194_, lean_object* v_00_u03b1_4195_, lean_object* v_00_u03b2_4196_, lean_object* v_x_4197_, lean_object* v_y_4198_, lean_object* v_prio_4199_){
_start:
{
lean_object* v___f_4201_; lean_object* v___f_4202_; lean_object* v___x_4203_; uint8_t v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; uint8_t v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___f_4201_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
lean_inc(v_prio_4199_);
v___f_4202_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrently___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_4202_, 0, v_y_4198_);
lean_closure_set(v___f_4202_, 1, v_prio_4199_);
lean_closure_set(v___f_4202_, 2, v___f_4201_);
v___x_4203_ = lean_unsigned_to_nat(0u);
v___x_4204_ = 0;
v___x_4205_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4205_, 0, lean_box(0));
lean_closure_set(v___x_4205_, 1, v_x_4197_);
v___x_4206_ = lean_io_as_task(v___x_4205_, v_prio_4199_);
v___x_4207_ = 1;
v___x_4208_ = lean_task_bind(v___x_4206_, v___f_4201_, v___x_4203_, v___x_4207_);
v___x_4209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4208_);
v___x_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4210_, 0, v___x_4209_);
v___x_4211_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4203_, v___x_4204_, v___x_4210_, v___f_4202_);
return v___x_4211_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_concurrently_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4197_ = stack[3].m_obj;
lean_object* v_y_4198_ = stack[4].m_obj;
lean_object* v_prio_4199_ = stack[5].m_obj;
lean_object* v_res_4212_;
v_res_4212_ = l_Std_Async_EAsync_concurrently(lean_box(0), lean_box(0), lean_box(0), v_x_4197_, v_y_4198_, v_prio_4199_);
stack->m_obj
 = v_res_4212_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___boxed(lean_object* v_00_u03b5_4213_, lean_object* v_00_u03b1_4214_, lean_object* v_00_u03b2_4215_, lean_object* v_x_4216_, lean_object* v_y_4217_, lean_object* v_prio_4218_, lean_object* v_a_4219_){
_start:
{
lean_object* v_res_4220_; 
v_res_4220_ = l_Std_Async_EAsync_concurrently(v_00_u03b5_4213_, v_00_u03b1_4214_, v_00_u03b2_4215_, v_x_4216_, v_y_4217_, v_prio_4218_);
return v_res_4220_;
}
}
lean_object* l_Std_Async_EAsync_race___redArg___lam__1(lean_object* v_x_4221_){
_start:
{
if (lean_obj_tag(v_x_4221_) == 0)
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4231_; 
v_a_4223_ = lean_ctor_get(v_x_4221_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v_x_4221_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4225_ = v_x_4221_;
v_isShared_4226_ = v_isSharedCheck_4231_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v_x_4221_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4231_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4228_; 
if (v_isShared_4226_ == 0)
{
v___x_4228_ = v___x_4225_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_a_4223_);
v___x_4228_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
lean_object* v___x_4229_; 
v___x_4229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4229_, 0, v___x_4228_);
return v___x_4229_;
}
}
}
else
{
lean_object* v_a_4232_; lean_object* v___x_4233_; 
v_a_4232_ = lean_ctor_get(v_x_4221_, 0);
lean_inc(v_a_4232_);
lean_dec_ref_known(v_x_4221_, 1);
v___x_4233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4233_, 0, v_a_4232_);
return v___x_4233_;
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_race___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4221_ = stack[0].m_obj;
lean_object* v_res_4234_;
v_res_4234_ = l_Std_Async_EAsync_race___redArg___lam__1(v_x_4221_);
stack->m_obj
 = v_res_4234_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__1___boxed(lean_object* v_x_4235_, lean_object* v___y_4236_){
_start:
{
lean_object* v_res_4237_; 
v_res_4237_ = l_Std_Async_EAsync_race___redArg___lam__1(v_x_4235_);
return v_res_4237_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__0(lean_object* v_a_4238_){
_start:
{
lean_object* v___x_4239_; 
v___x_4239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4239_, 0, v_a_4238_);
return v___x_4239_;
}
}
lean_object* l_Std_Async_EAsync_race___redArg___lam__3(lean_object* v_a_4240_, lean_object* v_value_4241_){
_start:
{
lean_object* v___x_4243_; 
v___x_4243_ = lean_io_promise_resolve(v_value_4241_, v_a_4240_);
return v___x_4243_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_race___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4240_ = stack[0].m_obj;
lean_object* v_value_4241_ = stack[1].m_obj;
lean_object* v_res_4244_;
v_res_4244_ = l_Std_Async_EAsync_race___redArg___lam__3(v_a_4240_, v_value_4241_);
stack->m_obj
 = v_res_4244_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__3___boxed(lean_object* v_a_4245_, lean_object* v_value_4246_, lean_object* v___y_4247_){
_start:
{
lean_object* v_res_4248_; 
v_res_4248_ = l_Std_Async_EAsync_race___redArg___lam__3(v_a_4245_, v_value_4246_);
lean_dec(v_a_4245_);
return v_res_4248_;
}
}
lean_object* l_Std_Async_EAsync_race___redArg___lam__2(lean_object* v_a_4249_, lean_object* v___f_4250_, lean_object* v___f_4251_, lean_object* v_x_4252_){
_start:
{
if (lean_obj_tag(v_x_4252_) == 0)
{
lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4262_; 
lean_dec_ref(v___f_4251_);
lean_dec_ref(v___f_4250_);
v_a_4254_ = lean_ctor_get(v_x_4252_, 0);
v_isSharedCheck_4262_ = !lean_is_exclusive(v_x_4252_);
if (v_isSharedCheck_4262_ == 0)
{
v___x_4256_ = v_x_4252_;
v_isShared_4257_ = v_isSharedCheck_4262_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v_x_4252_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4262_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v___x_4259_; 
if (v_isShared_4257_ == 0)
{
v___x_4259_ = v___x_4256_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v_a_4254_);
v___x_4259_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
lean_object* v___x_4260_; 
v___x_4260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4260_, 0, v___x_4259_);
return v___x_4260_;
}
}
}
else
{
lean_object* v___x_4263_; lean_object* v___x_4264_; uint8_t v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; 
lean_dec_ref_known(v_x_4252_, 1);
v___x_4263_ = l_IO_Promise_result_x21___redArg(v_a_4249_);
v___x_4264_ = lean_unsigned_to_nat(0u);
v___x_4265_ = 0;
v___x_4266_ = lean_task_map(v___f_4250_, v___x_4263_, v___x_4264_, v___x_4265_);
v___x_4267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4267_, 0, v___x_4266_);
v___x_4268_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4264_, v___x_4265_, v___x_4267_, v___f_4251_);
return v___x_4268_;
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_race___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4249_ = stack[0].m_obj;
lean_object* v___f_4250_ = stack[1].m_obj;
lean_object* v___f_4251_ = stack[2].m_obj;
lean_object* v_x_4252_ = stack[3].m_obj;
lean_object* v_res_4269_;
v_res_4269_ = l_Std_Async_EAsync_race___redArg___lam__2(v_a_4249_, v___f_4250_, v___f_4251_, v_x_4252_);
stack->m_obj
 = v_res_4269_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__2___boxed(lean_object* v_a_4270_, lean_object* v___f_4271_, lean_object* v___f_4272_, lean_object* v_x_4273_, lean_object* v___y_4274_){
_start:
{
lean_object* v_res_4275_; 
v_res_4275_ = l_Std_Async_EAsync_race___redArg___lam__2(v_a_4270_, v___f_4271_, v___f_4272_, v_x_4273_);
lean_dec(v_a_4270_);
return v_res_4275_;
}
}
lean_object* l_Std_Async_EAsync_race___redArg___lam__4(lean_object* v_a_4276_, lean_object* v___x_4277_, lean_object* v___x_4278_, uint8_t v___x_4279_, lean_object* v___f_4280_, lean_object* v_x_4281_){
_start:
{
if (lean_obj_tag(v_x_4281_) == 0)
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4291_; 
lean_dec_ref(v___f_4280_);
lean_dec(v___x_4278_);
lean_dec_ref(v___x_4277_);
lean_dec_ref(v_a_4276_);
v_a_4283_ = lean_ctor_get(v_x_4281_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v_x_4281_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4285_ = v_x_4281_;
v_isShared_4286_ = v_isSharedCheck_4291_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v_x_4281_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4291_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4288_; 
if (v_isShared_4286_ == 0)
{
v___x_4288_ = v___x_4285_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4283_);
v___x_4288_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
lean_object* v___x_4289_; 
v___x_4289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4289_, 0, v___x_4288_);
return v___x_4289_;
}
}
}
else
{
lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4301_; 
v_isSharedCheck_4301_ = !lean_is_exclusive(v_x_4281_);
if (v_isSharedCheck_4301_ == 0)
{
lean_object* v_unused_4302_; 
v_unused_4302_ = lean_ctor_get(v_x_4281_, 0);
lean_dec(v_unused_4302_);
v___x_4293_ = v_x_4281_;
v_isShared_4294_ = v_isSharedCheck_4301_;
goto v_resetjp_4292_;
}
else
{
lean_dec(v_x_4281_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4301_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v___x_4295_; lean_object* v___x_4297_; 
lean_inc(v___x_4278_);
v___x_4295_ = l_BaseIO_chainTask___redArg(v_a_4276_, v___x_4277_, v___x_4278_, v___x_4279_);
if (v_isShared_4294_ == 0)
{
lean_ctor_set(v___x_4293_, 0, v___x_4295_);
v___x_4297_ = v___x_4293_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v___x_4295_);
v___x_4297_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
lean_object* v___x_4298_; lean_object* v___x_4299_; 
v___x_4298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4297_);
v___x_4299_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4278_, v___x_4279_, v___x_4298_, v___f_4280_);
return v___x_4299_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_race___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4276_ = stack[0].m_obj;
lean_object* v___x_4277_ = stack[1].m_obj;
lean_object* v___x_4278_ = stack[2].m_obj;
uint8_t v___x_4279_ = stack[3].m_num;
lean_object* v___f_4280_ = stack[4].m_obj;
lean_object* v_x_4281_ = stack[5].m_obj;
lean_object* v_res_4303_;
v_res_4303_ = l_Std_Async_EAsync_race___redArg___lam__4(v_a_4276_, v___x_4277_, v___x_4278_, v___x_4279_, v___f_4280_, v_x_4281_);
stack->m_obj
 = v_res_4303_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__4___boxed(lean_object* v_a_4304_, lean_object* v___x_4305_, lean_object* v___x_4306_, lean_object* v___x_4307_, lean_object* v___f_4308_, lean_object* v_x_4309_, lean_object* v___y_4310_){
_start:
{
uint8_t v___x_1481__boxed_4311_; lean_object* v_res_4312_; 
v___x_1481__boxed_4311_ = lean_unbox(v___x_4307_);
v_res_4312_ = l_Std_Async_EAsync_race___redArg___lam__4(v_a_4304_, v___x_4305_, v___x_4306_, v___x_1481__boxed_4311_, v___f_4308_, v_x_4309_);
return v_res_4312_;
}
}
lean_object* l_Std_Async_EAsync_race___redArg___lam__5(lean_object* v___f_4313_, lean_object* v___f_4314_, lean_object* v___f_4315_, lean_object* v_a_4316_, lean_object* v_x_4317_){
_start:
{
if (lean_obj_tag(v_x_4317_) == 0)
{
lean_object* v_a_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4327_; 
lean_dec_ref(v_a_4316_);
lean_dec_ref(v___f_4315_);
lean_dec_ref(v___f_4314_);
lean_dec(v___f_4313_);
v_a_4319_ = lean_ctor_get(v_x_4317_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v_x_4317_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4321_ = v_x_4317_;
v_isShared_4322_ = v_isSharedCheck_4327_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_a_4319_);
lean_dec(v_x_4317_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4327_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v___x_4324_; 
if (v_isShared_4322_ == 0)
{
v___x_4324_ = v___x_4321_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_a_4319_);
v___x_4324_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
lean_object* v___x_4325_; 
v___x_4325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4325_, 0, v___x_4324_);
return v___x_4325_;
}
}
}
else
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4344_; 
v_a_4328_ = lean_ctor_get(v_x_4317_, 0);
v_isSharedCheck_4344_ = !lean_is_exclusive(v_x_4317_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4330_ = v_x_4317_;
v_isShared_4331_ = v_isSharedCheck_4344_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v_x_4317_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4344_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; uint8_t v___x_4335_; lean_object* v___x_4336_; lean_object* v___f_4337_; lean_object* v___x_4338_; lean_object* v___x_4340_; 
v___x_4332_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_4332_, 0, lean_box(0));
lean_closure_set(v___x_4332_, 1, lean_box(0));
lean_closure_set(v___x_4332_, 2, v___f_4313_);
lean_closure_set(v___x_4332_, 3, lean_box(0));
v___x_4333_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4333_, 0, lean_box(0));
lean_closure_set(v___x_4333_, 1, lean_box(0));
lean_closure_set(v___x_4333_, 2, lean_box(0));
lean_closure_set(v___x_4333_, 3, v___x_4332_);
lean_closure_set(v___x_4333_, 4, v___f_4314_);
v___x_4334_ = lean_unsigned_to_nat(0u);
v___x_4335_ = 0;
v___x_4336_ = lean_box(v___x_4335_);
lean_inc_ref(v___x_4333_);
v___f_4337_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__4___boxed), 7, 5);
lean_closure_set(v___f_4337_, 0, v_a_4328_);
lean_closure_set(v___f_4337_, 1, v___x_4333_);
lean_closure_set(v___f_4337_, 2, v___x_4334_);
lean_closure_set(v___f_4337_, 3, v___x_4336_);
lean_closure_set(v___f_4337_, 4, v___f_4315_);
v___x_4338_ = l_BaseIO_chainTask___redArg(v_a_4316_, v___x_4333_, v___x_4334_, v___x_4335_);
if (v_isShared_4331_ == 0)
{
lean_ctor_set(v___x_4330_, 0, v___x_4338_);
v___x_4340_ = v___x_4330_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v___x_4338_);
v___x_4340_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
lean_object* v___x_4341_; lean_object* v___x_4342_; 
v___x_4341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4341_, 0, v___x_4340_);
v___x_4342_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4334_, v___x_4335_, v___x_4341_, v___f_4337_);
return v___x_4342_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_race___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_4313_ = stack[0].m_obj;
lean_object* v___f_4314_ = stack[1].m_obj;
lean_object* v___f_4315_ = stack[2].m_obj;
lean_object* v_a_4316_ = stack[3].m_obj;
lean_object* v_x_4317_ = stack[4].m_obj;
lean_object* v_res_4345_;
v_res_4345_ = l_Std_Async_EAsync_race___redArg___lam__5(v___f_4313_, v___f_4314_, v___f_4315_, v_a_4316_, v_x_4317_);
stack->m_obj
 = v_res_4345_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__5___boxed(lean_object* v___f_4346_, lean_object* v___f_4347_, lean_object* v___f_4348_, lean_object* v_a_4349_, lean_object* v_x_4350_, lean_object* v___y_4351_){
_start:
{
lean_object* v_res_4352_; 
v_res_4352_ = l_Std_Async_EAsync_race___redArg___lam__5(v___f_4346_, v___f_4347_, v___f_4348_, v_a_4349_, v_x_4350_);
return v_res_4352_;
}
}
lean_object* l_Std_Async_EAsync_race___redArg___lam__6(lean_object* v___f_4353_, lean_object* v___f_4354_, lean_object* v___f_4355_, lean_object* v_y_4356_, lean_object* v_prio_4357_, lean_object* v___f_4358_, lean_object* v_x_4359_){
_start:
{
if (lean_obj_tag(v_x_4359_) == 0)
{
lean_object* v_a_4361_; lean_object* v___x_4363_; uint8_t v_isShared_4364_; uint8_t v_isSharedCheck_4369_; 
lean_dec_ref(v___f_4358_);
lean_dec(v_prio_4357_);
lean_dec_ref(v_y_4356_);
lean_dec_ref(v___f_4355_);
lean_dec_ref(v___f_4354_);
lean_dec(v___f_4353_);
v_a_4361_ = lean_ctor_get(v_x_4359_, 0);
v_isSharedCheck_4369_ = !lean_is_exclusive(v_x_4359_);
if (v_isSharedCheck_4369_ == 0)
{
v___x_4363_ = v_x_4359_;
v_isShared_4364_ = v_isSharedCheck_4369_;
goto v_resetjp_4362_;
}
else
{
lean_inc(v_a_4361_);
lean_dec(v_x_4359_);
v___x_4363_ = lean_box(0);
v_isShared_4364_ = v_isSharedCheck_4369_;
goto v_resetjp_4362_;
}
v_resetjp_4362_:
{
lean_object* v___x_4366_; 
if (v_isShared_4364_ == 0)
{
v___x_4366_ = v___x_4363_;
goto v_reusejp_4365_;
}
else
{
lean_object* v_reuseFailAlloc_4368_; 
v_reuseFailAlloc_4368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_a_4361_);
v___x_4366_ = v_reuseFailAlloc_4368_;
goto v_reusejp_4365_;
}
v_reusejp_4365_:
{
lean_object* v___x_4367_; 
v___x_4367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4367_, 0, v___x_4366_);
return v___x_4367_;
}
}
}
else
{
lean_object* v_a_4370_; lean_object* v___x_4372_; uint8_t v_isShared_4373_; uint8_t v_isSharedCheck_4386_; 
v_a_4370_ = lean_ctor_get(v_x_4359_, 0);
v_isSharedCheck_4386_ = !lean_is_exclusive(v_x_4359_);
if (v_isSharedCheck_4386_ == 0)
{
v___x_4372_ = v_x_4359_;
v_isShared_4373_ = v_isSharedCheck_4386_;
goto v_resetjp_4371_;
}
else
{
lean_inc(v_a_4370_);
lean_dec(v_x_4359_);
v___x_4372_ = lean_box(0);
v_isShared_4373_ = v_isSharedCheck_4386_;
goto v_resetjp_4371_;
}
v_resetjp_4371_:
{
lean_object* v___f_4374_; lean_object* v___x_4375_; uint8_t v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; uint8_t v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4382_; 
v___f_4374_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__5___boxed), 6, 4);
lean_closure_set(v___f_4374_, 0, v___f_4353_);
lean_closure_set(v___f_4374_, 1, v___f_4354_);
lean_closure_set(v___f_4374_, 2, v___f_4355_);
lean_closure_set(v___f_4374_, 3, v_a_4370_);
v___x_4375_ = lean_unsigned_to_nat(0u);
v___x_4376_ = 0;
v___x_4377_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4377_, 0, lean_box(0));
lean_closure_set(v___x_4377_, 1, v_y_4356_);
v___x_4378_ = lean_io_as_task(v___x_4377_, v_prio_4357_);
v___x_4379_ = 1;
v___x_4380_ = lean_task_bind(v___x_4378_, v___f_4358_, v___x_4375_, v___x_4379_);
if (v_isShared_4373_ == 0)
{
lean_ctor_set(v___x_4372_, 0, v___x_4380_);
v___x_4382_ = v___x_4372_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v___x_4380_);
v___x_4382_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
lean_object* v___x_4383_; lean_object* v___x_4384_; 
v___x_4383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4383_, 0, v___x_4382_);
v___x_4384_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4375_, v___x_4376_, v___x_4383_, v___f_4374_);
return v___x_4384_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_race___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_4353_ = stack[0].m_obj;
lean_object* v___f_4354_ = stack[1].m_obj;
lean_object* v___f_4355_ = stack[2].m_obj;
lean_object* v_y_4356_ = stack[3].m_obj;
lean_object* v_prio_4357_ = stack[4].m_obj;
lean_object* v___f_4358_ = stack[5].m_obj;
lean_object* v_x_4359_ = stack[6].m_obj;
lean_object* v_res_4387_;
v_res_4387_ = l_Std_Async_EAsync_race___redArg___lam__6(v___f_4353_, v___f_4354_, v___f_4355_, v_y_4356_, v_prio_4357_, v___f_4358_, v_x_4359_);
stack->m_obj
 = v_res_4387_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__6___boxed(lean_object* v___f_4388_, lean_object* v___f_4389_, lean_object* v___f_4390_, lean_object* v_y_4391_, lean_object* v_prio_4392_, lean_object* v___f_4393_, lean_object* v_x_4394_, lean_object* v___y_4395_){
_start:
{
lean_object* v_res_4396_; 
v_res_4396_ = l_Std_Async_EAsync_race___redArg___lam__6(v___f_4388_, v___f_4389_, v___f_4390_, v_y_4391_, v_prio_4392_, v___f_4393_, v_x_4394_);
return v_res_4396_;
}
}
lean_object* l_Std_Async_EAsync_race___redArg___lam__7(lean_object* v___f_4397_, lean_object* v___f_4398_, lean_object* v___f_4399_, lean_object* v_y_4400_, lean_object* v_prio_4401_, lean_object* v___f_4402_, lean_object* v_x_4403_, lean_object* v___f_4404_, lean_object* v_x_4405_){
_start:
{
if (lean_obj_tag(v_x_4405_) == 0)
{
lean_object* v_a_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4415_; 
lean_dec_ref(v___f_4404_);
lean_dec_ref(v_x_4403_);
lean_dec_ref(v___f_4402_);
lean_dec(v_prio_4401_);
lean_dec_ref(v_y_4400_);
lean_dec(v___f_4399_);
lean_dec_ref(v___f_4398_);
lean_dec_ref(v___f_4397_);
v_a_4407_ = lean_ctor_get(v_x_4405_, 0);
v_isSharedCheck_4415_ = !lean_is_exclusive(v_x_4405_);
if (v_isSharedCheck_4415_ == 0)
{
v___x_4409_ = v_x_4405_;
v_isShared_4410_ = v_isSharedCheck_4415_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_a_4407_);
lean_dec(v_x_4405_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4415_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
lean_object* v___x_4412_; 
if (v_isShared_4410_ == 0)
{
v___x_4412_ = v___x_4409_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_a_4407_);
v___x_4412_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
lean_object* v___x_4413_; 
v___x_4413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4413_, 0, v___x_4412_);
return v___x_4413_;
}
}
}
else
{
lean_object* v_a_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4434_; 
v_a_4416_ = lean_ctor_get(v_x_4405_, 0);
v_isSharedCheck_4434_ = !lean_is_exclusive(v_x_4405_);
if (v_isSharedCheck_4434_ == 0)
{
v___x_4418_ = v_x_4405_;
v_isShared_4419_ = v_isSharedCheck_4434_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_a_4416_);
lean_dec(v_x_4405_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4434_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v___f_4420_; lean_object* v___f_4421_; lean_object* v___f_4422_; lean_object* v___x_4423_; uint8_t v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; uint8_t v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4430_; 
lean_inc(v_a_4416_);
v___f_4420_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4420_, 0, v_a_4416_);
v___f_4421_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_4421_, 0, v_a_4416_);
lean_closure_set(v___f_4421_, 1, v___f_4397_);
lean_closure_set(v___f_4421_, 2, v___f_4398_);
lean_inc(v_prio_4401_);
v___f_4422_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__6___boxed), 8, 6);
lean_closure_set(v___f_4422_, 0, v___f_4399_);
lean_closure_set(v___f_4422_, 1, v___f_4420_);
lean_closure_set(v___f_4422_, 2, v___f_4421_);
lean_closure_set(v___f_4422_, 3, v_y_4400_);
lean_closure_set(v___f_4422_, 4, v_prio_4401_);
lean_closure_set(v___f_4422_, 5, v___f_4402_);
v___x_4423_ = lean_unsigned_to_nat(0u);
v___x_4424_ = 0;
v___x_4425_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4425_, 0, lean_box(0));
lean_closure_set(v___x_4425_, 1, v_x_4403_);
v___x_4426_ = lean_io_as_task(v___x_4425_, v_prio_4401_);
v___x_4427_ = 1;
v___x_4428_ = lean_task_bind(v___x_4426_, v___f_4404_, v___x_4423_, v___x_4427_);
if (v_isShared_4419_ == 0)
{
lean_ctor_set(v___x_4418_, 0, v___x_4428_);
v___x_4430_ = v___x_4418_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v___x_4428_);
v___x_4430_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; 
v___x_4431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4431_, 0, v___x_4430_);
v___x_4432_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4423_, v___x_4424_, v___x_4431_, v___f_4422_);
return v___x_4432_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_race___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_4397_ = stack[0].m_obj;
lean_object* v___f_4398_ = stack[1].m_obj;
lean_object* v___f_4399_ = stack[2].m_obj;
lean_object* v_y_4400_ = stack[3].m_obj;
lean_object* v_prio_4401_ = stack[4].m_obj;
lean_object* v___f_4402_ = stack[5].m_obj;
lean_object* v_x_4403_ = stack[6].m_obj;
lean_object* v___f_4404_ = stack[7].m_obj;
lean_object* v_x_4405_ = stack[8].m_obj;
lean_object* v_res_4435_;
v_res_4435_ = l_Std_Async_EAsync_race___redArg___lam__7(v___f_4397_, v___f_4398_, v___f_4399_, v_y_4400_, v_prio_4401_, v___f_4402_, v_x_4403_, v___f_4404_, v_x_4405_);
stack->m_obj
 = v_res_4435_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__7___boxed(lean_object* v___f_4436_, lean_object* v___f_4437_, lean_object* v___f_4438_, lean_object* v_y_4439_, lean_object* v_prio_4440_, lean_object* v___f_4441_, lean_object* v_x_4442_, lean_object* v___f_4443_, lean_object* v_x_4444_, lean_object* v___y_4445_){
_start:
{
lean_object* v_res_4446_; 
v_res_4446_ = l_Std_Async_EAsync_race___redArg___lam__7(v___f_4436_, v___f_4437_, v___f_4438_, v_y_4439_, v_prio_4440_, v___f_4441_, v_x_4442_, v___f_4443_, v_x_4444_);
return v_res_4446_;
}
}
lean_object* l_Std_Async_EAsync_race___redArg(lean_object* v_x_4449_, lean_object* v_y_4450_, lean_object* v_prio_4451_){
_start:
{
lean_object* v___f_4453_; lean_object* v___f_4454_; lean_object* v___f_4455_; lean_object* v___f_4456_; lean_object* v___f_4457_; lean_object* v___x_4458_; uint8_t v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; 
v___f_4453_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___f_4454_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__0));
v___f_4455_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__1));
v___f_4456_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_4457_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_4457_, 0, v___f_4455_);
lean_closure_set(v___f_4457_, 1, v___f_4454_);
lean_closure_set(v___f_4457_, 2, v___f_4456_);
lean_closure_set(v___f_4457_, 3, v_y_4450_);
lean_closure_set(v___f_4457_, 4, v_prio_4451_);
lean_closure_set(v___f_4457_, 5, v___f_4453_);
lean_closure_set(v___f_4457_, 6, v_x_4449_);
lean_closure_set(v___f_4457_, 7, v___f_4453_);
v___x_4458_ = lean_unsigned_to_nat(0u);
v___x_4459_ = 0;
v___x_4460_ = lean_io_promise_new();
v___x_4461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4461_, 0, v___x_4460_);
v___x_4462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4462_, 0, v___x_4461_);
v___x_4463_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4458_, v___x_4459_, v___x_4462_, v___f_4457_);
return v___x_4463_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_race___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4449_ = stack[0].m_obj;
lean_object* v_y_4450_ = stack[1].m_obj;
lean_object* v_prio_4451_ = stack[2].m_obj;
lean_object* v_res_4464_;
v_res_4464_ = l_Std_Async_EAsync_race___redArg(v_x_4449_, v_y_4450_, v_prio_4451_);
stack->m_obj
 = v_res_4464_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___boxed(lean_object* v_x_4465_, lean_object* v_y_4466_, lean_object* v_prio_4467_, lean_object* v_a_4468_){
_start:
{
lean_object* v_res_4469_; 
v_res_4469_ = l_Std_Async_EAsync_race___redArg(v_x_4465_, v_y_4466_, v_prio_4467_);
return v_res_4469_;
}
}
lean_object* l_Std_Async_EAsync_race(lean_object* v_00_u03b1_4470_, lean_object* v_00_u03b5_4471_, lean_object* v_inst_4472_, lean_object* v_x_4473_, lean_object* v_y_4474_, lean_object* v_prio_4475_){
_start:
{
lean_object* v___f_4477_; lean_object* v___f_4478_; lean_object* v___f_4479_; lean_object* v___f_4480_; lean_object* v___f_4481_; lean_object* v___x_4482_; uint8_t v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; 
v___f_4477_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___f_4478_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__0));
v___f_4479_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__1));
v___f_4480_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_4481_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_4481_, 0, v___f_4479_);
lean_closure_set(v___f_4481_, 1, v___f_4478_);
lean_closure_set(v___f_4481_, 2, v___f_4480_);
lean_closure_set(v___f_4481_, 3, v_y_4474_);
lean_closure_set(v___f_4481_, 4, v_prio_4475_);
lean_closure_set(v___f_4481_, 5, v___f_4477_);
lean_closure_set(v___f_4481_, 6, v_x_4473_);
lean_closure_set(v___f_4481_, 7, v___f_4477_);
v___x_4482_ = lean_unsigned_to_nat(0u);
v___x_4483_ = 0;
v___x_4484_ = lean_io_promise_new();
v___x_4485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4485_, 0, v___x_4484_);
v___x_4486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4486_, 0, v___x_4485_);
v___x_4487_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4482_, v___x_4483_, v___x_4486_, v___f_4481_);
return v___x_4487_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_race_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4472_ = stack[2].m_obj;
lean_object* v_x_4473_ = stack[3].m_obj;
lean_object* v_y_4474_ = stack[4].m_obj;
lean_object* v_prio_4475_ = stack[5].m_obj;
lean_object* v_res_4488_;
v_res_4488_ = l_Std_Async_EAsync_race(lean_box(0), lean_box(0), v_inst_4472_, v_x_4473_, v_y_4474_, v_prio_4475_);
stack->m_obj
 = v_res_4488_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___boxed(lean_object* v_00_u03b1_4489_, lean_object* v_00_u03b5_4490_, lean_object* v_inst_4491_, lean_object* v_x_4492_, lean_object* v_y_4493_, lean_object* v_prio_4494_, lean_object* v_a_4495_){
_start:
{
lean_object* v_res_4496_; 
v_res_4496_ = l_Std_Async_EAsync_race(v_00_u03b1_4489_, v_00_u03b5_4490_, v_inst_4491_, v_x_4492_, v_y_4493_, v_prio_4494_);
lean_dec(v_inst_4491_);
return v_res_4496_;
}
}
lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1(lean_object* v_prio_4497_, lean_object* v___f_4498_, lean_object* v_x_4499_){
_start:
{
lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; uint8_t v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; 
v___x_4501_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4501_, 0, lean_box(0));
lean_closure_set(v___x_4501_, 1, v_x_4499_);
v___x_4502_ = lean_io_as_task(v___x_4501_, v_prio_4497_);
v___x_4503_ = lean_unsigned_to_nat(0u);
v___x_4504_ = 1;
v___x_4505_ = lean_task_bind(v___x_4502_, v___f_4498_, v___x_4503_, v___x_4504_);
v___x_4506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4506_, 0, v___x_4505_);
v___x_4507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4507_, 0, v___x_4506_);
return v___x_4507_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_prio_4497_ = stack[0].m_obj;
lean_object* v___f_4498_ = stack[1].m_obj;
lean_object* v_x_4499_ = stack[2].m_obj;
lean_object* v_res_4508_;
v_res_4508_ = l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1(v_prio_4497_, v___f_4498_, v_x_4499_);
stack->m_obj
 = v_res_4508_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1___boxed(lean_object* v_prio_4509_, lean_object* v___f_4510_, lean_object* v_x_4511_, lean_object* v___y_4512_){
_start:
{
lean_object* v_res_4513_; 
v_res_4513_ = l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1(v_prio_4509_, v___f_4510_, v_x_4511_);
return v_res_4513_;
}
}
lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__0(lean_object* v___y_4514_){
_start:
{
lean_object* v___x_4516_; 
v___x_4516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4516_, 0, v___y_4514_);
return v___x_4516_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_concurrentlyAll___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4514_ = stack[0].m_obj;
lean_object* v_res_4517_;
v_res_4517_ = l_Std_Async_EAsync_concurrentlyAll___redArg___lam__0(v___y_4514_);
stack->m_obj
 = v_res_4517_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__0___boxed(lean_object* v___y_4518_, lean_object* v___y_4519_){
_start:
{
lean_object* v_res_4520_; 
v_res_4520_ = l_Std_Async_EAsync_concurrentlyAll___redArg___lam__0(v___y_4518_);
return v_res_4520_;
}
}
lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__2(lean_object* v___x_4521_, lean_object* v___f_4522_, lean_object* v_x_4523_){
_start:
{
if (lean_obj_tag(v_x_4523_) == 0)
{
lean_object* v_a_4525_; lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4533_; 
lean_dec_ref(v___f_4522_);
lean_dec_ref(v___x_4521_);
v_a_4525_ = lean_ctor_get(v_x_4523_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v_x_4523_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4527_ = v_x_4523_;
v_isShared_4528_ = v_isSharedCheck_4533_;
goto v_resetjp_4526_;
}
else
{
lean_inc(v_a_4525_);
lean_dec(v_x_4523_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4533_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v___x_4530_; 
if (v_isShared_4528_ == 0)
{
v___x_4530_ = v___x_4527_;
goto v_reusejp_4529_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v_a_4525_);
v___x_4530_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4529_;
}
v_reusejp_4529_:
{
lean_object* v___x_4531_; 
v___x_4531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4530_);
return v___x_4531_;
}
}
}
else
{
lean_object* v_a_4534_; size_t v_sz_4535_; size_t v___x_4536_; lean_object* v___x_292__overap_4537_; lean_object* v___x_4538_; 
v_a_4534_ = lean_ctor_get(v_x_4523_, 0);
lean_inc(v_a_4534_);
lean_dec_ref_known(v_x_4523_, 1);
v_sz_4535_ = lean_array_size(v_a_4534_);
v___x_4536_ = ((size_t)0ULL);
v___x_292__overap_4537_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_4521_, v___f_4522_, v_sz_4535_, v___x_4536_, v_a_4534_);
v___x_4538_ = lean_apply_1(v___x_292__overap_4537_, lean_box(0));
return v___x_4538_;
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_concurrentlyAll___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4521_ = stack[0].m_obj;
lean_object* v___f_4522_ = stack[1].m_obj;
lean_object* v_x_4523_ = stack[2].m_obj;
lean_object* v_res_4539_;
v_res_4539_ = l_Std_Async_EAsync_concurrentlyAll___redArg___lam__2(v___x_4521_, v___f_4522_, v_x_4523_);
stack->m_obj
 = v_res_4539_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__2___boxed(lean_object* v___x_4540_, lean_object* v___f_4541_, lean_object* v_x_4542_, lean_object* v___y_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Std_Async_EAsync_concurrentlyAll___redArg___lam__2(v___x_4540_, v___f_4541_, v_x_4542_);
return v_res_4544_;
}
}
static lean_object* _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1(void){
_start:
{
lean_object* v___f_4546_; lean_object* v___x_4547_; lean_object* v___f_4548_; 
v___f_4546_ = ((lean_object*)(l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0));
v___x_4547_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___closed__0, &l_Std_Async_EAsync_instMonad___closed__0_once, _init_l_Std_Async_EAsync_instMonad___closed__0);
v___f_4548_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrentlyAll___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4548_, 0, v___x_4547_);
lean_closure_set(v___f_4548_, 1, v___f_4546_);
return v___f_4548_;
}
}
lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg(lean_object* v_xs_4549_, lean_object* v_prio_4550_){
_start:
{
lean_object* v___f_4552_; lean_object* v___f_4553_; lean_object* v___x_4554_; lean_object* v___f_4555_; lean_object* v___x_4556_; uint8_t v___x_4557_; size_t v_sz_4558_; size_t v___x_4559_; lean_object* v___x_217__overap_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; 
v___f_4552_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___f_4553_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4553_, 0, v_prio_4550_);
lean_closure_set(v___f_4553_, 1, v___f_4552_);
v___x_4554_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___closed__0, &l_Std_Async_EAsync_instMonad___closed__0_once, _init_l_Std_Async_EAsync_instMonad___closed__0);
v___f_4555_ = lean_obj_once(&l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1, &l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1_once, _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1);
v___x_4556_ = lean_unsigned_to_nat(0u);
v___x_4557_ = 0;
v_sz_4558_ = lean_array_size(v_xs_4549_);
v___x_4559_ = ((size_t)0ULL);
v___x_217__overap_4560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_4554_, v___f_4553_, v_sz_4558_, v___x_4559_, v_xs_4549_);
v___x_4561_ = lean_apply_1(v___x_217__overap_4560_, lean_box(0));
v___x_4562_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4556_, v___x_4557_, v___x_4561_, v___f_4555_);
return v___x_4562_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_concurrentlyAll___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_4549_ = stack[0].m_obj;
lean_object* v_prio_4550_ = stack[1].m_obj;
lean_object* v_res_4563_;
v_res_4563_ = l_Std_Async_EAsync_concurrentlyAll___redArg(v_xs_4549_, v_prio_4550_);
stack->m_obj
 = v_res_4563_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___boxed(lean_object* v_xs_4564_, lean_object* v_prio_4565_, lean_object* v_a_4566_){
_start:
{
lean_object* v_res_4567_; 
v_res_4567_ = l_Std_Async_EAsync_concurrentlyAll___redArg(v_xs_4564_, v_prio_4565_);
return v_res_4567_;
}
}
lean_object* l_Std_Async_EAsync_concurrentlyAll(lean_object* v_00_u03b5_4568_, lean_object* v_00_u03b1_4569_, lean_object* v_xs_4570_, lean_object* v_prio_4571_){
_start:
{
lean_object* v___f_4573_; lean_object* v___f_4574_; lean_object* v___x_4575_; lean_object* v___f_4576_; lean_object* v___x_4577_; uint8_t v___x_4578_; size_t v_sz_4579_; size_t v___x_4580_; lean_object* v___x_258__overap_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; 
v___f_4573_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___f_4574_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4574_, 0, v_prio_4571_);
lean_closure_set(v___f_4574_, 1, v___f_4573_);
v___x_4575_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___closed__0, &l_Std_Async_EAsync_instMonad___closed__0_once, _init_l_Std_Async_EAsync_instMonad___closed__0);
v___f_4576_ = lean_obj_once(&l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1, &l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1_once, _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1);
v___x_4577_ = lean_unsigned_to_nat(0u);
v___x_4578_ = 0;
v_sz_4579_ = lean_array_size(v_xs_4570_);
v___x_4580_ = ((size_t)0ULL);
v___x_258__overap_4581_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_4575_, v___f_4574_, v_sz_4579_, v___x_4580_, v_xs_4570_);
v___x_4582_ = lean_apply_1(v___x_258__overap_4581_, lean_box(0));
v___x_4583_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4577_, v___x_4578_, v___x_4582_, v___f_4576_);
return v___x_4583_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_concurrentlyAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_4570_ = stack[2].m_obj;
lean_object* v_prio_4571_ = stack[3].m_obj;
lean_object* v_res_4584_;
v_res_4584_ = l_Std_Async_EAsync_concurrentlyAll(lean_box(0), lean_box(0), v_xs_4570_, v_prio_4571_);
stack->m_obj
 = v_res_4584_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___boxed(lean_object* v_00_u03b5_4585_, lean_object* v_00_u03b1_4586_, lean_object* v_xs_4587_, lean_object* v_prio_4588_, lean_object* v_a_4589_){
_start:
{
lean_object* v_res_4590_; 
v_res_4590_ = l_Std_Async_EAsync_concurrentlyAll(v_00_u03b5_4585_, v_00_u03b1_4586_, v_xs_4587_, v_prio_4588_);
return v_res_4590_;
}
}
lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__4(lean_object* v___f_4591_, lean_object* v___f_4592_, lean_object* v_x_4593_){
_start:
{
if (lean_obj_tag(v_x_4593_) == 0)
{
lean_object* v_a_4595_; lean_object* v___x_4597_; uint8_t v_isShared_4598_; uint8_t v_isSharedCheck_4603_; 
lean_dec_ref(v___f_4592_);
lean_dec(v___f_4591_);
v_a_4595_ = lean_ctor_get(v_x_4593_, 0);
v_isSharedCheck_4603_ = !lean_is_exclusive(v_x_4593_);
if (v_isSharedCheck_4603_ == 0)
{
v___x_4597_ = v_x_4593_;
v_isShared_4598_ = v_isSharedCheck_4603_;
goto v_resetjp_4596_;
}
else
{
lean_inc(v_a_4595_);
lean_dec(v_x_4593_);
v___x_4597_ = lean_box(0);
v_isShared_4598_ = v_isSharedCheck_4603_;
goto v_resetjp_4596_;
}
v_resetjp_4596_:
{
lean_object* v___x_4600_; 
if (v_isShared_4598_ == 0)
{
v___x_4600_ = v___x_4597_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_a_4595_);
v___x_4600_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
lean_object* v___x_4601_; 
v___x_4601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4601_, 0, v___x_4600_);
return v___x_4601_;
}
}
}
else
{
lean_object* v_a_4604_; lean_object* v___x_4606_; uint8_t v_isShared_4607_; uint8_t v_isSharedCheck_4617_; 
v_a_4604_ = lean_ctor_get(v_x_4593_, 0);
v_isSharedCheck_4617_ = !lean_is_exclusive(v_x_4593_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4606_ = v_x_4593_;
v_isShared_4607_ = v_isSharedCheck_4617_;
goto v_resetjp_4605_;
}
else
{
lean_inc(v_a_4604_);
lean_dec(v_x_4593_);
v___x_4606_ = lean_box(0);
v_isShared_4607_ = v_isSharedCheck_4617_;
goto v_resetjp_4605_;
}
v_resetjp_4605_:
{
lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; uint8_t v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4614_; 
v___x_4608_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_4608_, 0, lean_box(0));
lean_closure_set(v___x_4608_, 1, lean_box(0));
lean_closure_set(v___x_4608_, 2, v___f_4591_);
lean_closure_set(v___x_4608_, 3, lean_box(0));
v___x_4609_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4609_, 0, lean_box(0));
lean_closure_set(v___x_4609_, 1, lean_box(0));
lean_closure_set(v___x_4609_, 2, lean_box(0));
lean_closure_set(v___x_4609_, 3, v___x_4608_);
lean_closure_set(v___x_4609_, 4, v___f_4592_);
v___x_4610_ = lean_unsigned_to_nat(0u);
v___x_4611_ = 0;
v___x_4612_ = l_BaseIO_chainTask___redArg(v_a_4604_, v___x_4609_, v___x_4610_, v___x_4611_);
if (v_isShared_4607_ == 0)
{
lean_ctor_set(v___x_4606_, 0, v___x_4612_);
v___x_4614_ = v___x_4606_;
goto v_reusejp_4613_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v___x_4612_);
v___x_4614_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4613_;
}
v_reusejp_4613_:
{
lean_object* v___x_4615_; 
v___x_4615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4615_, 0, v___x_4614_);
return v___x_4615_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_raceAll___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_4591_ = stack[0].m_obj;
lean_object* v___f_4592_ = stack[1].m_obj;
lean_object* v_x_4593_ = stack[2].m_obj;
lean_object* v_res_4618_;
v_res_4618_ = l_Std_Async_EAsync_raceAll___redArg___lam__4(v___f_4591_, v___f_4592_, v_x_4593_);
stack->m_obj
 = v_res_4618_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__4___boxed(lean_object* v___f_4619_, lean_object* v___f_4620_, lean_object* v_x_4621_, lean_object* v___y_4622_){
_start:
{
lean_object* v_res_4623_; 
v_res_4623_ = l_Std_Async_EAsync_raceAll___redArg___lam__4(v___f_4619_, v___f_4620_, v_x_4621_);
return v_res_4623_;
}
}
lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__0(lean_object* v_prio_4624_, lean_object* v___f_4625_, lean_object* v___f_4626_, lean_object* v_x_4627_){
_start:
{
lean_object* v___x_4629_; uint8_t v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; uint8_t v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; 
v___x_4629_ = lean_unsigned_to_nat(0u);
v___x_4630_ = 0;
v___x_4631_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4631_, 0, lean_box(0));
lean_closure_set(v___x_4631_, 1, v_x_4627_);
v___x_4632_ = lean_io_as_task(v___x_4631_, v_prio_4624_);
v___x_4633_ = 1;
v___x_4634_ = lean_task_bind(v___x_4632_, v___f_4625_, v___x_4629_, v___x_4633_);
v___x_4635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4635_, 0, v___x_4634_);
v___x_4636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4636_, 0, v___x_4635_);
v___x_4637_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4629_, v___x_4630_, v___x_4636_, v___f_4626_);
return v___x_4637_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_raceAll___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_prio_4624_ = stack[0].m_obj;
lean_object* v___f_4625_ = stack[1].m_obj;
lean_object* v___f_4626_ = stack[2].m_obj;
lean_object* v_x_4627_ = stack[3].m_obj;
lean_object* v_res_4638_;
v_res_4638_ = l_Std_Async_EAsync_raceAll___redArg___lam__0(v_prio_4624_, v___f_4625_, v___f_4626_, v_x_4627_);
stack->m_obj
 = v_res_4638_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__0___boxed(lean_object* v_prio_4639_, lean_object* v___f_4640_, lean_object* v___f_4641_, lean_object* v_x_4642_, lean_object* v___y_4643_){
_start:
{
lean_object* v_res_4644_; 
v_res_4644_ = l_Std_Async_EAsync_raceAll___redArg___lam__0(v_prio_4639_, v___f_4640_, v___f_4641_, v_x_4642_);
return v_res_4644_;
}
}
lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__2(lean_object* v___f_4645_, lean_object* v_prio_4646_, lean_object* v___f_4647_, lean_object* v___f_4648_, lean_object* v___f_4649_, lean_object* v_inst_4650_, lean_object* v_xs_4651_, lean_object* v_x_4652_){
_start:
{
if (lean_obj_tag(v_x_4652_) == 0)
{
lean_object* v_a_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4662_; 
lean_dec(v_xs_4651_);
lean_dec_ref(v_inst_4650_);
lean_dec_ref(v___f_4649_);
lean_dec_ref(v___f_4648_);
lean_dec_ref(v___f_4647_);
lean_dec(v_prio_4646_);
lean_dec(v___f_4645_);
v_a_4654_ = lean_ctor_get(v_x_4652_, 0);
v_isSharedCheck_4662_ = !lean_is_exclusive(v_x_4652_);
if (v_isSharedCheck_4662_ == 0)
{
v___x_4656_ = v_x_4652_;
v_isShared_4657_ = v_isSharedCheck_4662_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_a_4654_);
lean_dec(v_x_4652_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4662_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
lean_object* v___x_4659_; 
if (v_isShared_4657_ == 0)
{
v___x_4659_ = v___x_4656_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_a_4654_);
v___x_4659_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
lean_object* v___x_4660_; 
v___x_4660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4660_, 0, v___x_4659_);
return v___x_4660_;
}
}
}
else
{
lean_object* v_a_4663_; lean_object* v___f_4664_; lean_object* v___f_4665_; lean_object* v___f_4666_; lean_object* v___f_4667_; lean_object* v___x_4668_; uint8_t v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; 
v_a_4663_ = lean_ctor_get(v_x_4652_, 0);
lean_inc_n(v_a_4663_, 2);
lean_dec_ref_known(v_x_4652_, 1);
v___f_4664_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4664_, 0, v_a_4663_);
v___f_4665_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_raceAll___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_4665_, 0, v___f_4645_);
lean_closure_set(v___f_4665_, 1, v___f_4664_);
v___f_4666_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_raceAll___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4666_, 0, v_prio_4646_);
lean_closure_set(v___f_4666_, 1, v___f_4647_);
lean_closure_set(v___f_4666_, 2, v___f_4665_);
v___f_4667_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_4667_, 0, v_a_4663_);
lean_closure_set(v___f_4667_, 1, v___f_4648_);
lean_closure_set(v___f_4667_, 2, v___f_4649_);
v___x_4668_ = lean_unsigned_to_nat(0u);
v___x_4669_ = 0;
v___x_4670_ = lean_apply_3(v_inst_4650_, v_xs_4651_, v___f_4666_, lean_box(0));
v___x_4671_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4668_, v___x_4669_, v___x_4670_, v___f_4667_);
return v___x_4671_;
}
}
}
LEAN_EXPORT void l_Std_Async_EAsync_raceAll___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_4645_ = stack[0].m_obj;
lean_object* v_prio_4646_ = stack[1].m_obj;
lean_object* v___f_4647_ = stack[2].m_obj;
lean_object* v___f_4648_ = stack[3].m_obj;
lean_object* v___f_4649_ = stack[4].m_obj;
lean_object* v_inst_4650_ = stack[5].m_obj;
lean_object* v_xs_4651_ = stack[6].m_obj;
lean_object* v_x_4652_ = stack[7].m_obj;
lean_object* v_res_4672_;
v_res_4672_ = l_Std_Async_EAsync_raceAll___redArg___lam__2(v___f_4645_, v_prio_4646_, v___f_4647_, v___f_4648_, v___f_4649_, v_inst_4650_, v_xs_4651_, v_x_4652_);
stack->m_obj
 = v_res_4672_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__2___boxed(lean_object* v___f_4673_, lean_object* v_prio_4674_, lean_object* v___f_4675_, lean_object* v___f_4676_, lean_object* v___f_4677_, lean_object* v_inst_4678_, lean_object* v_xs_4679_, lean_object* v_x_4680_, lean_object* v___y_4681_){
_start:
{
lean_object* v_res_4682_; 
v_res_4682_ = l_Std_Async_EAsync_raceAll___redArg___lam__2(v___f_4673_, v_prio_4674_, v___f_4675_, v___f_4676_, v___f_4677_, v_inst_4678_, v_xs_4679_, v_x_4680_);
return v_res_4682_;
}
}
lean_object* l_Std_Async_EAsync_raceAll___redArg(lean_object* v_inst_4683_, lean_object* v_xs_4684_, lean_object* v_prio_4685_){
_start:
{
lean_object* v___f_4687_; lean_object* v___f_4688_; lean_object* v___f_4689_; lean_object* v___f_4690_; lean_object* v___f_4691_; lean_object* v___x_4692_; uint8_t v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; 
v___f_4687_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__1));
v___f_4688_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__0));
v___f_4689_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___f_4690_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_4691_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_raceAll___redArg___lam__2___boxed), 9, 7);
lean_closure_set(v___f_4691_, 0, v___f_4690_);
lean_closure_set(v___f_4691_, 1, v_prio_4685_);
lean_closure_set(v___f_4691_, 2, v___f_4689_);
lean_closure_set(v___f_4691_, 3, v___f_4687_);
lean_closure_set(v___f_4691_, 4, v___f_4688_);
lean_closure_set(v___f_4691_, 5, v_inst_4683_);
lean_closure_set(v___f_4691_, 6, v_xs_4684_);
v___x_4692_ = lean_unsigned_to_nat(0u);
v___x_4693_ = 0;
v___x_4694_ = lean_io_promise_new();
v___x_4695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4695_, 0, v___x_4694_);
v___x_4696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4696_, 0, v___x_4695_);
v___x_4697_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4692_, v___x_4693_, v___x_4696_, v___f_4691_);
return v___x_4697_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_raceAll___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4683_ = stack[0].m_obj;
lean_object* v_xs_4684_ = stack[1].m_obj;
lean_object* v_prio_4685_ = stack[2].m_obj;
lean_object* v_res_4698_;
v_res_4698_ = l_Std_Async_EAsync_raceAll___redArg(v_inst_4683_, v_xs_4684_, v_prio_4685_);
stack->m_obj
 = v_res_4698_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___boxed(lean_object* v_inst_4699_, lean_object* v_xs_4700_, lean_object* v_prio_4701_, lean_object* v_a_4702_){
_start:
{
lean_object* v_res_4703_; 
v_res_4703_ = l_Std_Async_EAsync_raceAll___redArg(v_inst_4699_, v_xs_4700_, v_prio_4701_);
return v_res_4703_;
}
}
lean_object* l_Std_Async_EAsync_raceAll(lean_object* v_00_u03b1_4704_, lean_object* v_00_u03b5_4705_, lean_object* v_c_4706_, lean_object* v_inst_4707_, lean_object* v_inst_4708_, lean_object* v_xs_4709_, lean_object* v_prio_4710_){
_start:
{
lean_object* v___f_4712_; lean_object* v___f_4713_; lean_object* v___f_4714_; lean_object* v___f_4715_; lean_object* v___f_4716_; lean_object* v___x_4717_; uint8_t v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; 
v___f_4712_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__1));
v___f_4713_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__0));
v___f_4714_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___f_4715_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_4716_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_raceAll___redArg___lam__2___boxed), 9, 7);
lean_closure_set(v___f_4716_, 0, v___f_4715_);
lean_closure_set(v___f_4716_, 1, v_prio_4710_);
lean_closure_set(v___f_4716_, 2, v___f_4714_);
lean_closure_set(v___f_4716_, 3, v___f_4712_);
lean_closure_set(v___f_4716_, 4, v___f_4713_);
lean_closure_set(v___f_4716_, 5, v_inst_4708_);
lean_closure_set(v___f_4716_, 6, v_xs_4709_);
v___x_4717_ = lean_unsigned_to_nat(0u);
v___x_4718_ = 0;
v___x_4719_ = lean_io_promise_new();
v___x_4720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4720_, 0, v___x_4719_);
v___x_4721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4721_, 0, v___x_4720_);
v___x_4722_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4717_, v___x_4718_, v___x_4721_, v___f_4716_);
return v___x_4722_;
}
}
LEAN_EXPORT void l_Std_Async_EAsync_raceAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4707_ = stack[3].m_obj;
lean_object* v_inst_4708_ = stack[4].m_obj;
lean_object* v_xs_4709_ = stack[5].m_obj;
lean_object* v_prio_4710_ = stack[6].m_obj;
lean_object* v_res_4723_;
v_res_4723_ = l_Std_Async_EAsync_raceAll(lean_box(0), lean_box(0), lean_box(0), v_inst_4707_, v_inst_4708_, v_xs_4709_, v_prio_4710_);
stack->m_obj
 = v_res_4723_;
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___boxed(lean_object* v_00_u03b1_4724_, lean_object* v_00_u03b5_4725_, lean_object* v_c_4726_, lean_object* v_inst_4727_, lean_object* v_inst_4728_, lean_object* v_xs_4729_, lean_object* v_prio_4730_, lean_object* v_a_4731_){
_start:
{
lean_object* v_res_4732_; 
v_res_4732_ = l_Std_Async_EAsync_raceAll(v_00_u03b1_4724_, v_00_u03b5_4725_, v_c_4726_, v_inst_4727_, v_inst_4728_, v_xs_4729_, v_prio_4730_);
lean_dec(v_inst_4727_);
return v_res_4732_;
}
}
lean_object* l_Std_Async_Async_toIO___redArg(lean_object* v_x_4733_){
_start:
{
lean_object* v___x_4735_; 
v___x_4735_ = lean_apply_1(v_x_4733_, lean_box(0));
if (lean_obj_tag(v___x_4735_) == 0)
{
lean_object* v_a_4736_; lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4744_; 
v_a_4736_ = lean_ctor_get(v___x_4735_, 0);
v_isSharedCheck_4744_ = !lean_is_exclusive(v___x_4735_);
if (v_isSharedCheck_4744_ == 0)
{
v___x_4738_ = v___x_4735_;
v_isShared_4739_ = v_isSharedCheck_4744_;
goto v_resetjp_4737_;
}
else
{
lean_inc(v_a_4736_);
lean_dec(v___x_4735_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4744_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
lean_object* v___x_4740_; lean_object* v___x_4742_; 
v___x_4740_ = lean_task_pure(v_a_4736_);
if (v_isShared_4739_ == 0)
{
lean_ctor_set(v___x_4738_, 0, v___x_4740_);
v___x_4742_ = v___x_4738_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v___x_4740_);
v___x_4742_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
return v___x_4742_;
}
}
}
else
{
lean_object* v_a_4745_; lean_object* v___x_4747_; uint8_t v_isShared_4748_; uint8_t v_isSharedCheck_4752_; 
v_a_4745_ = lean_ctor_get(v___x_4735_, 0);
v_isSharedCheck_4752_ = !lean_is_exclusive(v___x_4735_);
if (v_isSharedCheck_4752_ == 0)
{
v___x_4747_ = v___x_4735_;
v_isShared_4748_ = v_isSharedCheck_4752_;
goto v_resetjp_4746_;
}
else
{
lean_inc(v_a_4745_);
lean_dec(v___x_4735_);
v___x_4747_ = lean_box(0);
v_isShared_4748_ = v_isSharedCheck_4752_;
goto v_resetjp_4746_;
}
v_resetjp_4746_:
{
lean_object* v___x_4750_; 
if (v_isShared_4748_ == 0)
{
lean_ctor_set_tag(v___x_4747_, 0);
v___x_4750_ = v___x_4747_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v_a_4745_);
v___x_4750_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
return v___x_4750_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Async_toIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4733_ = stack[0].m_obj;
lean_object* v_res_4753_;
v_res_4753_ = l_Std_Async_Async_toIO___redArg(v_x_4733_);
stack->m_obj
 = v_res_4753_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_toIO___redArg___boxed(lean_object* v_x_4754_, lean_object* v_a_4755_){
_start:
{
lean_object* v_res_4756_; 
v_res_4756_ = l_Std_Async_Async_toIO___redArg(v_x_4754_);
return v_res_4756_;
}
}
lean_object* l_Std_Async_Async_toIO(lean_object* v_00_u03b1_4757_, lean_object* v_x_4758_){
_start:
{
lean_object* v___x_4760_; 
v___x_4760_ = lean_apply_1(v_x_4758_, lean_box(0));
if (lean_obj_tag(v___x_4760_) == 0)
{
lean_object* v_a_4761_; lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4769_; 
v_a_4761_ = lean_ctor_get(v___x_4760_, 0);
v_isSharedCheck_4769_ = !lean_is_exclusive(v___x_4760_);
if (v_isSharedCheck_4769_ == 0)
{
v___x_4763_ = v___x_4760_;
v_isShared_4764_ = v_isSharedCheck_4769_;
goto v_resetjp_4762_;
}
else
{
lean_inc(v_a_4761_);
lean_dec(v___x_4760_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4769_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
lean_object* v___x_4765_; lean_object* v___x_4767_; 
v___x_4765_ = lean_task_pure(v_a_4761_);
if (v_isShared_4764_ == 0)
{
lean_ctor_set(v___x_4763_, 0, v___x_4765_);
v___x_4767_ = v___x_4763_;
goto v_reusejp_4766_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v___x_4765_);
v___x_4767_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4766_;
}
v_reusejp_4766_:
{
return v___x_4767_;
}
}
}
else
{
lean_object* v_a_4770_; lean_object* v___x_4772_; uint8_t v_isShared_4773_; uint8_t v_isSharedCheck_4777_; 
v_a_4770_ = lean_ctor_get(v___x_4760_, 0);
v_isSharedCheck_4777_ = !lean_is_exclusive(v___x_4760_);
if (v_isSharedCheck_4777_ == 0)
{
v___x_4772_ = v___x_4760_;
v_isShared_4773_ = v_isSharedCheck_4777_;
goto v_resetjp_4771_;
}
else
{
lean_inc(v_a_4770_);
lean_dec(v___x_4760_);
v___x_4772_ = lean_box(0);
v_isShared_4773_ = v_isSharedCheck_4777_;
goto v_resetjp_4771_;
}
v_resetjp_4771_:
{
lean_object* v___x_4775_; 
if (v_isShared_4773_ == 0)
{
lean_ctor_set_tag(v___x_4772_, 0);
v___x_4775_ = v___x_4772_;
goto v_reusejp_4774_;
}
else
{
lean_object* v_reuseFailAlloc_4776_; 
v_reuseFailAlloc_4776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4776_, 0, v_a_4770_);
v___x_4775_ = v_reuseFailAlloc_4776_;
goto v_reusejp_4774_;
}
v_reusejp_4774_:
{
return v___x_4775_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Async_toIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4758_ = stack[1].m_obj;
lean_object* v_res_4778_;
v_res_4778_ = l_Std_Async_Async_toIO(lean_box(0), v_x_4758_);
stack->m_obj
 = v_res_4778_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_toIO___boxed(lean_object* v_00_u03b1_4779_, lean_object* v_x_4780_, lean_object* v_a_4781_){
_start:
{
lean_object* v_res_4782_; 
v_res_4782_ = l_Std_Async_Async_toIO(v_00_u03b1_4779_, v_x_4780_);
return v_res_4782_;
}
}
lean_object* l_Std_Async_Async_block___redArg(lean_object* v_x_4783_, lean_object* v_prio_4784_){
_start:
{
lean_object* v___f_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; uint8_t v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; 
v___f_4786_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___x_4787_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4787_, 0, lean_box(0));
lean_closure_set(v___x_4787_, 1, v_x_4783_);
v___x_4788_ = lean_io_as_task(v___x_4787_, v_prio_4784_);
v___x_4789_ = lean_unsigned_to_nat(0u);
v___x_4790_ = 1;
v___x_4791_ = lean_task_bind(v___x_4788_, v___f_4786_, v___x_4789_, v___x_4790_);
v___x_4792_ = lean_task_get_own(v___x_4791_);
if (lean_obj_tag(v___x_4792_) == 0)
{
lean_object* v_a_4793_; lean_object* v___x_4795_; uint8_t v_isShared_4796_; uint8_t v_isSharedCheck_4800_; 
v_a_4793_ = lean_ctor_get(v___x_4792_, 0);
v_isSharedCheck_4800_ = !lean_is_exclusive(v___x_4792_);
if (v_isSharedCheck_4800_ == 0)
{
v___x_4795_ = v___x_4792_;
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
else
{
lean_inc(v_a_4793_);
lean_dec(v___x_4792_);
v___x_4795_ = lean_box(0);
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
v_resetjp_4794_:
{
lean_object* v___x_4798_; 
if (v_isShared_4796_ == 0)
{
lean_ctor_set_tag(v___x_4795_, 1);
v___x_4798_ = v___x_4795_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_a_4793_);
v___x_4798_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
return v___x_4798_;
}
}
}
else
{
lean_object* v_a_4801_; lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4808_; 
v_a_4801_ = lean_ctor_get(v___x_4792_, 0);
v_isSharedCheck_4808_ = !lean_is_exclusive(v___x_4792_);
if (v_isSharedCheck_4808_ == 0)
{
v___x_4803_ = v___x_4792_;
v_isShared_4804_ = v_isSharedCheck_4808_;
goto v_resetjp_4802_;
}
else
{
lean_inc(v_a_4801_);
lean_dec(v___x_4792_);
v___x_4803_ = lean_box(0);
v_isShared_4804_ = v_isSharedCheck_4808_;
goto v_resetjp_4802_;
}
v_resetjp_4802_:
{
lean_object* v___x_4806_; 
if (v_isShared_4804_ == 0)
{
lean_ctor_set_tag(v___x_4803_, 0);
v___x_4806_ = v___x_4803_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_a_4801_);
v___x_4806_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4805_;
}
v_reusejp_4805_:
{
return v___x_4806_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Async_block___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4783_ = stack[0].m_obj;
lean_object* v_prio_4784_ = stack[1].m_obj;
lean_object* v_res_4809_;
v_res_4809_ = l_Std_Async_Async_block___redArg(v_x_4783_, v_prio_4784_);
stack->m_obj
 = v_res_4809_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_block___redArg___boxed(lean_object* v_x_4810_, lean_object* v_prio_4811_, lean_object* v_a_4812_){
_start:
{
lean_object* v_res_4813_; 
v_res_4813_ = l_Std_Async_Async_block___redArg(v_x_4810_, v_prio_4811_);
return v_res_4813_;
}
}
lean_object* l_Std_Async_Async_block(lean_object* v_00_u03b1_4814_, lean_object* v_x_4815_, lean_object* v_prio_4816_){
_start:
{
lean_object* v___f_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; uint8_t v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; 
v___f_4818_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___x_4819_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4819_, 0, lean_box(0));
lean_closure_set(v___x_4819_, 1, v_x_4815_);
v___x_4820_ = lean_io_as_task(v___x_4819_, v_prio_4816_);
v___x_4821_ = lean_unsigned_to_nat(0u);
v___x_4822_ = 1;
v___x_4823_ = lean_task_bind(v___x_4820_, v___f_4818_, v___x_4821_, v___x_4822_);
v___x_4824_ = lean_task_get_own(v___x_4823_);
if (lean_obj_tag(v___x_4824_) == 0)
{
lean_object* v_a_4825_; lean_object* v___x_4827_; uint8_t v_isShared_4828_; uint8_t v_isSharedCheck_4832_; 
v_a_4825_ = lean_ctor_get(v___x_4824_, 0);
v_isSharedCheck_4832_ = !lean_is_exclusive(v___x_4824_);
if (v_isSharedCheck_4832_ == 0)
{
v___x_4827_ = v___x_4824_;
v_isShared_4828_ = v_isSharedCheck_4832_;
goto v_resetjp_4826_;
}
else
{
lean_inc(v_a_4825_);
lean_dec(v___x_4824_);
v___x_4827_ = lean_box(0);
v_isShared_4828_ = v_isSharedCheck_4832_;
goto v_resetjp_4826_;
}
v_resetjp_4826_:
{
lean_object* v___x_4830_; 
if (v_isShared_4828_ == 0)
{
lean_ctor_set_tag(v___x_4827_, 1);
v___x_4830_ = v___x_4827_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4831_; 
v_reuseFailAlloc_4831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4831_, 0, v_a_4825_);
v___x_4830_ = v_reuseFailAlloc_4831_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
return v___x_4830_;
}
}
}
else
{
lean_object* v_a_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4840_; 
v_a_4833_ = lean_ctor_get(v___x_4824_, 0);
v_isSharedCheck_4840_ = !lean_is_exclusive(v___x_4824_);
if (v_isSharedCheck_4840_ == 0)
{
v___x_4835_ = v___x_4824_;
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_a_4833_);
lean_dec(v___x_4824_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
lean_object* v___x_4838_; 
if (v_isShared_4836_ == 0)
{
lean_ctor_set_tag(v___x_4835_, 0);
v___x_4838_ = v___x_4835_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v_a_4833_);
v___x_4838_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
return v___x_4838_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Async_block_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4815_ = stack[1].m_obj;
lean_object* v_prio_4816_ = stack[2].m_obj;
lean_object* v_res_4841_;
v_res_4841_ = l_Std_Async_Async_block(lean_box(0), v_x_4815_, v_prio_4816_);
stack->m_obj
 = v_res_4841_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_block___boxed(lean_object* v_00_u03b1_4842_, lean_object* v_x_4843_, lean_object* v_prio_4844_, lean_object* v_a_4845_){
_start:
{
lean_object* v_res_4846_; 
v_res_4846_ = l_Std_Async_Async_block(v_00_u03b1_4842_, v_x_4843_, v_prio_4844_);
return v_res_4846_;
}
}
lean_object* l_Std_Async_Async_ofPromise___redArg___lam__1(lean_object* v___f_4847_, lean_object* v_x_4848_){
_start:
{
if (lean_obj_tag(v_x_4848_) == 0)
{
lean_object* v_a_4850_; lean_object* v___x_4852_; uint8_t v_isShared_4853_; uint8_t v_isSharedCheck_4858_; 
lean_dec_ref(v___f_4847_);
v_a_4850_ = lean_ctor_get(v_x_4848_, 0);
v_isSharedCheck_4858_ = !lean_is_exclusive(v_x_4848_);
if (v_isSharedCheck_4858_ == 0)
{
v___x_4852_ = v_x_4848_;
v_isShared_4853_ = v_isSharedCheck_4858_;
goto v_resetjp_4851_;
}
else
{
lean_inc(v_a_4850_);
lean_dec(v_x_4848_);
v___x_4852_ = lean_box(0);
v_isShared_4853_ = v_isSharedCheck_4858_;
goto v_resetjp_4851_;
}
v_resetjp_4851_:
{
lean_object* v___x_4855_; 
if (v_isShared_4853_ == 0)
{
v___x_4855_ = v___x_4852_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4857_; 
v_reuseFailAlloc_4857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4857_, 0, v_a_4850_);
v___x_4855_ = v_reuseFailAlloc_4857_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
lean_object* v___x_4856_; 
v___x_4856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4856_, 0, v___x_4855_);
return v___x_4856_;
}
}
}
else
{
lean_object* v_a_4859_; 
v_a_4859_ = lean_ctor_get(v_x_4848_, 0);
lean_inc(v_a_4859_);
lean_dec_ref_known(v_x_4848_, 1);
if (lean_obj_tag(v_a_4859_) == 0)
{
lean_object* v_a_4860_; lean_object* v___x_4862_; uint8_t v_isShared_4863_; uint8_t v_isSharedCheck_4868_; 
lean_dec_ref(v___f_4847_);
v_a_4860_ = lean_ctor_get(v_a_4859_, 0);
v_isSharedCheck_4868_ = !lean_is_exclusive(v_a_4859_);
if (v_isSharedCheck_4868_ == 0)
{
v___x_4862_ = v_a_4859_;
v_isShared_4863_ = v_isSharedCheck_4868_;
goto v_resetjp_4861_;
}
else
{
lean_inc(v_a_4860_);
lean_dec(v_a_4859_);
v___x_4862_ = lean_box(0);
v_isShared_4863_ = v_isSharedCheck_4868_;
goto v_resetjp_4861_;
}
v_resetjp_4861_:
{
lean_object* v___x_4865_; 
if (v_isShared_4863_ == 0)
{
v___x_4865_ = v___x_4862_;
goto v_reusejp_4864_;
}
else
{
lean_object* v_reuseFailAlloc_4867_; 
v_reuseFailAlloc_4867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4867_, 0, v_a_4860_);
v___x_4865_ = v_reuseFailAlloc_4867_;
goto v_reusejp_4864_;
}
v_reusejp_4864_:
{
lean_object* v___x_4866_; 
v___x_4866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4866_, 0, v___x_4865_);
return v___x_4866_;
}
}
}
else
{
lean_object* v_a_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; uint8_t v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; 
v_a_4869_ = lean_ctor_get(v_a_4859_, 0);
lean_inc(v_a_4869_);
lean_dec_ref_known(v_a_4859_, 1);
v___x_4870_ = lean_io_promise_result_opt(v_a_4869_);
lean_dec(v_a_4869_);
v___x_4871_ = lean_unsigned_to_nat(0u);
v___x_4872_ = 0;
v___x_4873_ = lean_task_map(v___f_4847_, v___x_4870_, v___x_4871_, v___x_4872_);
v___x_4874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4874_, 0, v___x_4873_);
return v___x_4874_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_Async_ofPromise___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_4847_ = stack[0].m_obj;
lean_object* v_x_4848_ = stack[1].m_obj;
lean_object* v_res_4875_;
v_res_4875_ = l_Std_Async_Async_ofPromise___redArg___lam__1(v___f_4847_, v_x_4848_);
stack->m_obj
 = v_res_4875_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise___redArg___lam__1___boxed(lean_object* v___f_4876_, lean_object* v_x_4877_, lean_object* v___y_4878_){
_start:
{
lean_object* v_res_4879_; 
v_res_4879_ = l_Std_Async_Async_ofPromise___redArg___lam__1(v___f_4876_, v_x_4877_);
return v_res_4879_;
}
}
lean_object* l_Std_Async_Async_ofPromise___redArg(lean_object* v_task_4880_, lean_object* v_error_4881_){
_start:
{
lean_object* v___f_4883_; lean_object* v___f_4884_; lean_object* v___x_4885_; uint8_t v___x_4886_; lean_object* v_val_4888_; lean_object* v___x_4892_; 
v___f_4883_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPromise___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4883_, 0, v_error_4881_);
v___f_4884_ = lean_alloc_closure((void*)(l_Std_Async_Async_ofPromise___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4884_, 0, v___f_4883_);
v___x_4885_ = lean_unsigned_to_nat(0u);
v___x_4886_ = 0;
v___x_4892_ = lean_apply_1(v_task_4880_, lean_box(0));
if (lean_obj_tag(v___x_4892_) == 0)
{
lean_object* v_a_4893_; lean_object* v___x_4895_; uint8_t v_isShared_4896_; uint8_t v_isSharedCheck_4900_; 
v_a_4893_ = lean_ctor_get(v___x_4892_, 0);
v_isSharedCheck_4900_ = !lean_is_exclusive(v___x_4892_);
if (v_isSharedCheck_4900_ == 0)
{
v___x_4895_ = v___x_4892_;
v_isShared_4896_ = v_isSharedCheck_4900_;
goto v_resetjp_4894_;
}
else
{
lean_inc(v_a_4893_);
lean_dec(v___x_4892_);
v___x_4895_ = lean_box(0);
v_isShared_4896_ = v_isSharedCheck_4900_;
goto v_resetjp_4894_;
}
v_resetjp_4894_:
{
lean_object* v___x_4898_; 
if (v_isShared_4896_ == 0)
{
lean_ctor_set_tag(v___x_4895_, 1);
v___x_4898_ = v___x_4895_;
goto v_reusejp_4897_;
}
else
{
lean_object* v_reuseFailAlloc_4899_; 
v_reuseFailAlloc_4899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4899_, 0, v_a_4893_);
v___x_4898_ = v_reuseFailAlloc_4899_;
goto v_reusejp_4897_;
}
v_reusejp_4897_:
{
v_val_4888_ = v___x_4898_;
goto v___jp_4887_;
}
}
}
else
{
lean_object* v_a_4901_; lean_object* v___x_4903_; uint8_t v_isShared_4904_; uint8_t v_isSharedCheck_4908_; 
v_a_4901_ = lean_ctor_get(v___x_4892_, 0);
v_isSharedCheck_4908_ = !lean_is_exclusive(v___x_4892_);
if (v_isSharedCheck_4908_ == 0)
{
v___x_4903_ = v___x_4892_;
v_isShared_4904_ = v_isSharedCheck_4908_;
goto v_resetjp_4902_;
}
else
{
lean_inc(v_a_4901_);
lean_dec(v___x_4892_);
v___x_4903_ = lean_box(0);
v_isShared_4904_ = v_isSharedCheck_4908_;
goto v_resetjp_4902_;
}
v_resetjp_4902_:
{
lean_object* v___x_4906_; 
if (v_isShared_4904_ == 0)
{
lean_ctor_set_tag(v___x_4903_, 0);
v___x_4906_ = v___x_4903_;
goto v_reusejp_4905_;
}
else
{
lean_object* v_reuseFailAlloc_4907_; 
v_reuseFailAlloc_4907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4907_, 0, v_a_4901_);
v___x_4906_ = v_reuseFailAlloc_4907_;
goto v_reusejp_4905_;
}
v_reusejp_4905_:
{
v_val_4888_ = v___x_4906_;
goto v___jp_4887_;
}
}
}
v___jp_4887_:
{
lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; 
v___x_4889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4889_, 0, v_val_4888_);
v___x_4890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4890_, 0, v___x_4889_);
v___x_4891_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4885_, v___x_4886_, v___x_4890_, v___f_4884_);
return v___x_4891_;
}
}
}
LEAN_EXPORT void l_Std_Async_Async_ofPromise___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_task_4880_ = stack[0].m_obj;
lean_object* v_error_4881_ = stack[1].m_obj;
lean_object* v_res_4909_;
v_res_4909_ = l_Std_Async_Async_ofPromise___redArg(v_task_4880_, v_error_4881_);
stack->m_obj
 = v_res_4909_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise___redArg___boxed(lean_object* v_task_4910_, lean_object* v_error_4911_, lean_object* v_a_4912_){
_start:
{
lean_object* v_res_4913_; 
v_res_4913_ = l_Std_Async_Async_ofPromise___redArg(v_task_4910_, v_error_4911_);
return v_res_4913_;
}
}
lean_object* l_Std_Async_Async_ofPromise(lean_object* v_00_u03b1_4914_, lean_object* v_task_4915_, lean_object* v_error_4916_){
_start:
{
lean_object* v___f_4918_; lean_object* v___f_4919_; lean_object* v___x_4920_; uint8_t v___x_4921_; lean_object* v_val_4923_; lean_object* v___x_4927_; 
v___f_4918_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPromise___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4918_, 0, v_error_4916_);
v___f_4919_ = lean_alloc_closure((void*)(l_Std_Async_Async_ofPromise___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4919_, 0, v___f_4918_);
v___x_4920_ = lean_unsigned_to_nat(0u);
v___x_4921_ = 0;
v___x_4927_ = lean_apply_1(v_task_4915_, lean_box(0));
if (lean_obj_tag(v___x_4927_) == 0)
{
lean_object* v_a_4928_; lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4935_; 
v_a_4928_ = lean_ctor_get(v___x_4927_, 0);
v_isSharedCheck_4935_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_4935_ == 0)
{
v___x_4930_ = v___x_4927_;
v_isShared_4931_ = v_isSharedCheck_4935_;
goto v_resetjp_4929_;
}
else
{
lean_inc(v_a_4928_);
lean_dec(v___x_4927_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4935_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
lean_object* v___x_4933_; 
if (v_isShared_4931_ == 0)
{
lean_ctor_set_tag(v___x_4930_, 1);
v___x_4933_ = v___x_4930_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v_a_4928_);
v___x_4933_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
v_val_4923_ = v___x_4933_;
goto v___jp_4922_;
}
}
}
else
{
lean_object* v_a_4936_; lean_object* v___x_4938_; uint8_t v_isShared_4939_; uint8_t v_isSharedCheck_4943_; 
v_a_4936_ = lean_ctor_get(v___x_4927_, 0);
v_isSharedCheck_4943_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_4943_ == 0)
{
v___x_4938_ = v___x_4927_;
v_isShared_4939_ = v_isSharedCheck_4943_;
goto v_resetjp_4937_;
}
else
{
lean_inc(v_a_4936_);
lean_dec(v___x_4927_);
v___x_4938_ = lean_box(0);
v_isShared_4939_ = v_isSharedCheck_4943_;
goto v_resetjp_4937_;
}
v_resetjp_4937_:
{
lean_object* v___x_4941_; 
if (v_isShared_4939_ == 0)
{
lean_ctor_set_tag(v___x_4938_, 0);
v___x_4941_ = v___x_4938_;
goto v_reusejp_4940_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v_a_4936_);
v___x_4941_ = v_reuseFailAlloc_4942_;
goto v_reusejp_4940_;
}
v_reusejp_4940_:
{
v_val_4923_ = v___x_4941_;
goto v___jp_4922_;
}
}
}
v___jp_4922_:
{
lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; 
v___x_4924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4924_, 0, v_val_4923_);
v___x_4925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4925_, 0, v___x_4924_);
v___x_4926_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4920_, v___x_4921_, v___x_4925_, v___f_4919_);
return v___x_4926_;
}
}
}
LEAN_EXPORT void l_Std_Async_Async_ofPromise_0interp(lean_interpreter_value* stack)
{
lean_object* v_task_4915_ = stack[1].m_obj;
lean_object* v_error_4916_ = stack[2].m_obj;
lean_object* v_res_4944_;
v_res_4944_ = l_Std_Async_Async_ofPromise(lean_box(0), v_task_4915_, v_error_4916_);
stack->m_obj
 = v_res_4944_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise___boxed(lean_object* v_00_u03b1_4945_, lean_object* v_task_4946_, lean_object* v_error_4947_, lean_object* v_a_4948_){
_start:
{
lean_object* v_res_4949_; 
v_res_4949_ = l_Std_Async_Async_ofPromise(v_00_u03b1_4945_, v_task_4946_, v_error_4947_);
return v_res_4949_;
}
}
lean_object* l_Std_Async_Async_ofAsyncTask___redArg(lean_object* v_task_4950_){
_start:
{
lean_object* v___x_4952_; 
v___x_4952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4952_, 0, v_task_4950_);
return v___x_4952_;
}
}
LEAN_EXPORT void l_Std_Async_Async_ofAsyncTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_task_4950_ = stack[0].m_obj;
lean_object* v_res_4953_;
v_res_4953_ = l_Std_Async_Async_ofAsyncTask___redArg(v_task_4950_);
stack->m_obj
 = v_res_4953_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofAsyncTask___redArg___boxed(lean_object* v_task_4954_, lean_object* v_a_4955_){
_start:
{
lean_object* v_res_4956_; 
v_res_4956_ = l_Std_Async_Async_ofAsyncTask___redArg(v_task_4954_);
return v_res_4956_;
}
}
lean_object* l_Std_Async_Async_ofAsyncTask(lean_object* v_00_u03b1_4957_, lean_object* v_task_4958_){
_start:
{
lean_object* v___x_4960_; 
v___x_4960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4960_, 0, v_task_4958_);
return v___x_4960_;
}
}
LEAN_EXPORT void l_Std_Async_Async_ofAsyncTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_task_4958_ = stack[1].m_obj;
lean_object* v_res_4961_;
v_res_4961_ = l_Std_Async_Async_ofAsyncTask(lean_box(0), v_task_4958_);
stack->m_obj
 = v_res_4961_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofAsyncTask___boxed(lean_object* v_00_u03b1_4962_, lean_object* v_task_4963_, lean_object* v_a_4964_){
_start:
{
lean_object* v_res_4965_; 
v_res_4965_ = l_Std_Async_Async_ofAsyncTask(v_00_u03b1_4962_, v_task_4963_);
return v_res_4965_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___redArg___lam__0(lean_object* v_a_4966_){
_start:
{
lean_object* v___x_4967_; 
v___x_4967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4967_, 0, v_a_4966_);
return v___x_4967_;
}
}
lean_object* l_Std_Async_Async_ofIOTask___redArg___lam__1(lean_object* v___f_4968_, lean_object* v_x_4969_){
_start:
{
if (lean_obj_tag(v_x_4969_) == 0)
{
lean_object* v_a_4971_; lean_object* v___x_4973_; uint8_t v_isShared_4974_; uint8_t v_isSharedCheck_4979_; 
lean_dec_ref(v___f_4968_);
v_a_4971_ = lean_ctor_get(v_x_4969_, 0);
v_isSharedCheck_4979_ = !lean_is_exclusive(v_x_4969_);
if (v_isSharedCheck_4979_ == 0)
{
v___x_4973_ = v_x_4969_;
v_isShared_4974_ = v_isSharedCheck_4979_;
goto v_resetjp_4972_;
}
else
{
lean_inc(v_a_4971_);
lean_dec(v_x_4969_);
v___x_4973_ = lean_box(0);
v_isShared_4974_ = v_isSharedCheck_4979_;
goto v_resetjp_4972_;
}
v_resetjp_4972_:
{
lean_object* v___x_4976_; 
if (v_isShared_4974_ == 0)
{
v___x_4976_ = v___x_4973_;
goto v_reusejp_4975_;
}
else
{
lean_object* v_reuseFailAlloc_4978_; 
v_reuseFailAlloc_4978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4978_, 0, v_a_4971_);
v___x_4976_ = v_reuseFailAlloc_4978_;
goto v_reusejp_4975_;
}
v_reusejp_4975_:
{
lean_object* v___x_4977_; 
v___x_4977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4977_, 0, v___x_4976_);
return v___x_4977_;
}
}
}
else
{
lean_object* v_a_4980_; 
v_a_4980_ = lean_ctor_get(v_x_4969_, 0);
lean_inc(v_a_4980_);
lean_dec_ref_known(v_x_4969_, 1);
if (lean_obj_tag(v_a_4980_) == 0)
{
lean_object* v_a_4981_; lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_4989_; 
lean_dec_ref(v___f_4968_);
v_a_4981_ = lean_ctor_get(v_a_4980_, 0);
v_isSharedCheck_4989_ = !lean_is_exclusive(v_a_4980_);
if (v_isSharedCheck_4989_ == 0)
{
v___x_4983_ = v_a_4980_;
v_isShared_4984_ = v_isSharedCheck_4989_;
goto v_resetjp_4982_;
}
else
{
lean_inc(v_a_4981_);
lean_dec(v_a_4980_);
v___x_4983_ = lean_box(0);
v_isShared_4984_ = v_isSharedCheck_4989_;
goto v_resetjp_4982_;
}
v_resetjp_4982_:
{
lean_object* v___x_4986_; 
if (v_isShared_4984_ == 0)
{
v___x_4986_ = v___x_4983_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4988_; 
v_reuseFailAlloc_4988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4988_, 0, v_a_4981_);
v___x_4986_ = v_reuseFailAlloc_4988_;
goto v_reusejp_4985_;
}
v_reusejp_4985_:
{
lean_object* v___x_4987_; 
v___x_4987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4987_, 0, v___x_4986_);
return v___x_4987_;
}
}
}
else
{
lean_object* v_a_4990_; lean_object* v___x_4991_; uint8_t v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
v_a_4990_ = lean_ctor_get(v_a_4980_, 0);
lean_inc(v_a_4990_);
lean_dec_ref_known(v_a_4980_, 1);
v___x_4991_ = lean_unsigned_to_nat(0u);
v___x_4992_ = 0;
v___x_4993_ = lean_task_map(v___f_4968_, v_a_4990_, v___x_4991_, v___x_4992_);
v___x_4994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4994_, 0, v___x_4993_);
return v___x_4994_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_Async_ofIOTask___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_4968_ = stack[0].m_obj;
lean_object* v_x_4969_ = stack[1].m_obj;
lean_object* v_res_4995_;
v_res_4995_ = l_Std_Async_Async_ofIOTask___redArg___lam__1(v___f_4968_, v_x_4969_);
stack->m_obj
 = v_res_4995_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___redArg___lam__1___boxed(lean_object* v___f_4996_, lean_object* v_x_4997_, lean_object* v___y_4998_){
_start:
{
lean_object* v_res_4999_; 
v_res_4999_ = l_Std_Async_Async_ofIOTask___redArg___lam__1(v___f_4996_, v_x_4997_);
return v_res_4999_;
}
}
lean_object* l_Std_Async_Async_ofIOTask___redArg(lean_object* v_task_5003_){
_start:
{
lean_object* v___f_5005_; lean_object* v___x_5006_; uint8_t v___x_5007_; lean_object* v_val_5009_; lean_object* v___x_5013_; 
v___f_5005_ = ((lean_object*)(l_Std_Async_Async_ofIOTask___redArg___closed__1));
v___x_5006_ = lean_unsigned_to_nat(0u);
v___x_5007_ = 0;
v___x_5013_ = lean_apply_1(v_task_5003_, lean_box(0));
if (lean_obj_tag(v___x_5013_) == 0)
{
lean_object* v_a_5014_; lean_object* v___x_5016_; uint8_t v_isShared_5017_; uint8_t v_isSharedCheck_5021_; 
v_a_5014_ = lean_ctor_get(v___x_5013_, 0);
v_isSharedCheck_5021_ = !lean_is_exclusive(v___x_5013_);
if (v_isSharedCheck_5021_ == 0)
{
v___x_5016_ = v___x_5013_;
v_isShared_5017_ = v_isSharedCheck_5021_;
goto v_resetjp_5015_;
}
else
{
lean_inc(v_a_5014_);
lean_dec(v___x_5013_);
v___x_5016_ = lean_box(0);
v_isShared_5017_ = v_isSharedCheck_5021_;
goto v_resetjp_5015_;
}
v_resetjp_5015_:
{
lean_object* v___x_5019_; 
if (v_isShared_5017_ == 0)
{
lean_ctor_set_tag(v___x_5016_, 1);
v___x_5019_ = v___x_5016_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v_a_5014_);
v___x_5019_ = v_reuseFailAlloc_5020_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
v_val_5009_ = v___x_5019_;
goto v___jp_5008_;
}
}
}
else
{
lean_object* v_a_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5029_; 
v_a_5022_ = lean_ctor_get(v___x_5013_, 0);
v_isSharedCheck_5029_ = !lean_is_exclusive(v___x_5013_);
if (v_isSharedCheck_5029_ == 0)
{
v___x_5024_ = v___x_5013_;
v_isShared_5025_ = v_isSharedCheck_5029_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_a_5022_);
lean_dec(v___x_5013_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5029_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v___x_5027_; 
if (v_isShared_5025_ == 0)
{
lean_ctor_set_tag(v___x_5024_, 0);
v___x_5027_ = v___x_5024_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v_a_5022_);
v___x_5027_ = v_reuseFailAlloc_5028_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
v_val_5009_ = v___x_5027_;
goto v___jp_5008_;
}
}
}
v___jp_5008_:
{
lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; 
v___x_5010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5010_, 0, v_val_5009_);
v___x_5011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5011_, 0, v___x_5010_);
v___x_5012_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5006_, v___x_5007_, v___x_5011_, v___f_5005_);
return v___x_5012_;
}
}
}
LEAN_EXPORT void l_Std_Async_Async_ofIOTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_task_5003_ = stack[0].m_obj;
lean_object* v_res_5030_;
v_res_5030_ = l_Std_Async_Async_ofIOTask___redArg(v_task_5003_);
stack->m_obj
 = v_res_5030_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___redArg___boxed(lean_object* v_task_5031_, lean_object* v_a_5032_){
_start:
{
lean_object* v_res_5033_; 
v_res_5033_ = l_Std_Async_Async_ofIOTask___redArg(v_task_5031_);
return v_res_5033_;
}
}
lean_object* l_Std_Async_Async_ofIOTask(lean_object* v_00_u03b1_5034_, lean_object* v_task_5035_){
_start:
{
lean_object* v___f_5037_; lean_object* v___x_5038_; uint8_t v___x_5039_; lean_object* v_val_5041_; lean_object* v___x_5045_; 
v___f_5037_ = ((lean_object*)(l_Std_Async_Async_ofIOTask___redArg___closed__1));
v___x_5038_ = lean_unsigned_to_nat(0u);
v___x_5039_ = 0;
v___x_5045_ = lean_apply_1(v_task_5035_, lean_box(0));
if (lean_obj_tag(v___x_5045_) == 0)
{
lean_object* v_a_5046_; lean_object* v___x_5048_; uint8_t v_isShared_5049_; uint8_t v_isSharedCheck_5053_; 
v_a_5046_ = lean_ctor_get(v___x_5045_, 0);
v_isSharedCheck_5053_ = !lean_is_exclusive(v___x_5045_);
if (v_isSharedCheck_5053_ == 0)
{
v___x_5048_ = v___x_5045_;
v_isShared_5049_ = v_isSharedCheck_5053_;
goto v_resetjp_5047_;
}
else
{
lean_inc(v_a_5046_);
lean_dec(v___x_5045_);
v___x_5048_ = lean_box(0);
v_isShared_5049_ = v_isSharedCheck_5053_;
goto v_resetjp_5047_;
}
v_resetjp_5047_:
{
lean_object* v___x_5051_; 
if (v_isShared_5049_ == 0)
{
lean_ctor_set_tag(v___x_5048_, 1);
v___x_5051_ = v___x_5048_;
goto v_reusejp_5050_;
}
else
{
lean_object* v_reuseFailAlloc_5052_; 
v_reuseFailAlloc_5052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5052_, 0, v_a_5046_);
v___x_5051_ = v_reuseFailAlloc_5052_;
goto v_reusejp_5050_;
}
v_reusejp_5050_:
{
v_val_5041_ = v___x_5051_;
goto v___jp_5040_;
}
}
}
else
{
lean_object* v_a_5054_; lean_object* v___x_5056_; uint8_t v_isShared_5057_; uint8_t v_isSharedCheck_5061_; 
v_a_5054_ = lean_ctor_get(v___x_5045_, 0);
v_isSharedCheck_5061_ = !lean_is_exclusive(v___x_5045_);
if (v_isSharedCheck_5061_ == 0)
{
v___x_5056_ = v___x_5045_;
v_isShared_5057_ = v_isSharedCheck_5061_;
goto v_resetjp_5055_;
}
else
{
lean_inc(v_a_5054_);
lean_dec(v___x_5045_);
v___x_5056_ = lean_box(0);
v_isShared_5057_ = v_isSharedCheck_5061_;
goto v_resetjp_5055_;
}
v_resetjp_5055_:
{
lean_object* v___x_5059_; 
if (v_isShared_5057_ == 0)
{
lean_ctor_set_tag(v___x_5056_, 0);
v___x_5059_ = v___x_5056_;
goto v_reusejp_5058_;
}
else
{
lean_object* v_reuseFailAlloc_5060_; 
v_reuseFailAlloc_5060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5060_, 0, v_a_5054_);
v___x_5059_ = v_reuseFailAlloc_5060_;
goto v_reusejp_5058_;
}
v_reusejp_5058_:
{
v_val_5041_ = v___x_5059_;
goto v___jp_5040_;
}
}
}
v___jp_5040_:
{
lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; 
v___x_5042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5042_, 0, v_val_5041_);
v___x_5043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5043_, 0, v___x_5042_);
v___x_5044_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5038_, v___x_5039_, v___x_5043_, v___f_5037_);
return v___x_5044_;
}
}
}
LEAN_EXPORT void l_Std_Async_Async_ofIOTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_task_5035_ = stack[1].m_obj;
lean_object* v_res_5062_;
v_res_5062_ = l_Std_Async_Async_ofIOTask(lean_box(0), v_task_5035_);
stack->m_obj
 = v_res_5062_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___boxed(lean_object* v_00_u03b1_5063_, lean_object* v_task_5064_, lean_object* v_a_5065_){
_start:
{
lean_object* v_res_5066_; 
v_res_5066_ = l_Std_Async_Async_ofIOTask(v_00_u03b1_5063_, v_task_5064_);
return v_res_5066_;
}
}
lean_object* l_Std_Async_Async_ofExcept___redArg(lean_object* v_except_5067_){
_start:
{
lean_object* v___x_5069_; 
v___x_5069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5069_, 0, v_except_5067_);
return v___x_5069_;
}
}
LEAN_EXPORT void l_Std_Async_Async_ofExcept___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_except_5067_ = stack[0].m_obj;
lean_object* v_res_5070_;
v_res_5070_ = l_Std_Async_Async_ofExcept___redArg(v_except_5067_);
stack->m_obj
 = v_res_5070_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofExcept___redArg___boxed(lean_object* v_except_5071_, lean_object* v_a_5072_){
_start:
{
lean_object* v_res_5073_; 
v_res_5073_ = l_Std_Async_Async_ofExcept___redArg(v_except_5071_);
return v_res_5073_;
}
}
lean_object* l_Std_Async_Async_ofExcept(lean_object* v_00_u03b1_5074_, lean_object* v_except_5075_){
_start:
{
lean_object* v___x_5077_; 
v___x_5077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5077_, 0, v_except_5075_);
return v___x_5077_;
}
}
LEAN_EXPORT void l_Std_Async_Async_ofExcept_0interp(lean_interpreter_value* stack)
{
lean_object* v_except_5075_ = stack[1].m_obj;
lean_object* v_res_5078_;
v_res_5078_ = l_Std_Async_Async_ofExcept(lean_box(0), v_except_5075_);
stack->m_obj
 = v_res_5078_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofExcept___boxed(lean_object* v_00_u03b1_5079_, lean_object* v_except_5080_, lean_object* v_a_5081_){
_start:
{
lean_object* v_res_5082_; 
v_res_5082_ = l_Std_Async_Async_ofExcept(v_00_u03b1_5079_, v_except_5080_);
return v_res_5082_;
}
}
lean_object* l_Std_Async_Async_ofTask___redArg(lean_object* v_task_5083_){
_start:
{
lean_object* v___f_5085_; lean_object* v___x_5086_; uint8_t v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; 
v___f_5085_ = ((lean_object*)(l_Std_Async_Async_ofIOTask___redArg___closed__0));
v___x_5086_ = lean_unsigned_to_nat(0u);
v___x_5087_ = 0;
v___x_5088_ = lean_task_map(v___f_5085_, v_task_5083_, v___x_5086_, v___x_5087_);
v___x_5089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5089_, 0, v___x_5088_);
return v___x_5089_;
}
}
LEAN_EXPORT void l_Std_Async_Async_ofTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_task_5083_ = stack[0].m_obj;
lean_object* v_res_5090_;
v_res_5090_ = l_Std_Async_Async_ofTask___redArg(v_task_5083_);
stack->m_obj
 = v_res_5090_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofTask___redArg___boxed(lean_object* v_task_5091_, lean_object* v_a_5092_){
_start:
{
lean_object* v_res_5093_; 
v_res_5093_ = l_Std_Async_Async_ofTask___redArg(v_task_5091_);
return v_res_5093_;
}
}
lean_object* l_Std_Async_Async_ofTask(lean_object* v_00_u03b1_5094_, lean_object* v_task_5095_){
_start:
{
lean_object* v___f_5097_; lean_object* v___x_5098_; uint8_t v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; 
v___f_5097_ = ((lean_object*)(l_Std_Async_Async_ofIOTask___redArg___closed__0));
v___x_5098_ = lean_unsigned_to_nat(0u);
v___x_5099_ = 0;
v___x_5100_ = lean_task_map(v___f_5097_, v_task_5095_, v___x_5098_, v___x_5099_);
v___x_5101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5101_, 0, v___x_5100_);
return v___x_5101_;
}
}
LEAN_EXPORT void l_Std_Async_Async_ofTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_task_5095_ = stack[1].m_obj;
lean_object* v_res_5102_;
v_res_5102_ = l_Std_Async_Async_ofTask(lean_box(0), v_task_5095_);
stack->m_obj
 = v_res_5102_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofTask___boxed(lean_object* v_00_u03b1_5103_, lean_object* v_task_5104_, lean_object* v_a_5105_){
_start:
{
lean_object* v_res_5106_; 
v_res_5106_ = l_Std_Async_Async_ofTask(v_00_u03b1_5103_, v_task_5104_);
return v_res_5106_;
}
}
lean_object* l_Std_Async_Async_ofPurePromise___redArg(lean_object* v_task_5107_, lean_object* v_error_5108_){
_start:
{
lean_object* v___f_5110_; lean_object* v___x_5111_; 
v___f_5110_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPurePromise___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5110_, 0, v_error_5108_);
v___x_5111_ = lean_apply_1(v_task_5107_, lean_box(0));
if (lean_obj_tag(v___x_5111_) == 0)
{
lean_object* v_a_5112_; lean_object* v___x_5114_; uint8_t v_isShared_5115_; uint8_t v_isSharedCheck_5123_; 
v_a_5112_ = lean_ctor_get(v___x_5111_, 0);
v_isSharedCheck_5123_ = !lean_is_exclusive(v___x_5111_);
if (v_isSharedCheck_5123_ == 0)
{
v___x_5114_ = v___x_5111_;
v_isShared_5115_ = v_isSharedCheck_5123_;
goto v_resetjp_5113_;
}
else
{
lean_inc(v_a_5112_);
lean_dec(v___x_5111_);
v___x_5114_ = lean_box(0);
v_isShared_5115_ = v_isSharedCheck_5123_;
goto v_resetjp_5113_;
}
v_resetjp_5113_:
{
lean_object* v___x_5116_; lean_object* v___x_5117_; uint8_t v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5121_; 
v___x_5116_ = lean_io_promise_result_opt(v_a_5112_);
lean_dec(v_a_5112_);
v___x_5117_ = lean_unsigned_to_nat(0u);
v___x_5118_ = 0;
v___x_5119_ = lean_task_map(v___f_5110_, v___x_5116_, v___x_5117_, v___x_5118_);
if (v_isShared_5115_ == 0)
{
lean_ctor_set_tag(v___x_5114_, 1);
lean_ctor_set(v___x_5114_, 0, v___x_5119_);
v___x_5121_ = v___x_5114_;
goto v_reusejp_5120_;
}
else
{
lean_object* v_reuseFailAlloc_5122_; 
v_reuseFailAlloc_5122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5122_, 0, v___x_5119_);
v___x_5121_ = v_reuseFailAlloc_5122_;
goto v_reusejp_5120_;
}
v_reusejp_5120_:
{
return v___x_5121_;
}
}
}
else
{
lean_object* v_a_5124_; lean_object* v___x_5126_; uint8_t v_isShared_5127_; uint8_t v_isSharedCheck_5132_; 
lean_dec_ref(v___f_5110_);
v_a_5124_ = lean_ctor_get(v___x_5111_, 0);
v_isSharedCheck_5132_ = !lean_is_exclusive(v___x_5111_);
if (v_isSharedCheck_5132_ == 0)
{
v___x_5126_ = v___x_5111_;
v_isShared_5127_ = v_isSharedCheck_5132_;
goto v_resetjp_5125_;
}
else
{
lean_inc(v_a_5124_);
lean_dec(v___x_5111_);
v___x_5126_ = lean_box(0);
v_isShared_5127_ = v_isSharedCheck_5132_;
goto v_resetjp_5125_;
}
v_resetjp_5125_:
{
lean_object* v___x_5129_; 
if (v_isShared_5127_ == 0)
{
lean_ctor_set_tag(v___x_5126_, 0);
v___x_5129_ = v___x_5126_;
goto v_reusejp_5128_;
}
else
{
lean_object* v_reuseFailAlloc_5131_; 
v_reuseFailAlloc_5131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5131_, 0, v_a_5124_);
v___x_5129_ = v_reuseFailAlloc_5131_;
goto v_reusejp_5128_;
}
v_reusejp_5128_:
{
lean_object* v___x_5130_; 
v___x_5130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5130_, 0, v___x_5129_);
return v___x_5130_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Async_ofPurePromise___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_task_5107_ = stack[0].m_obj;
lean_object* v_error_5108_ = stack[1].m_obj;
lean_object* v_res_5133_;
v_res_5133_ = l_Std_Async_Async_ofPurePromise___redArg(v_task_5107_, v_error_5108_);
stack->m_obj
 = v_res_5133_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPurePromise___redArg___boxed(lean_object* v_task_5134_, lean_object* v_error_5135_, lean_object* v_a_5136_){
_start:
{
lean_object* v_res_5137_; 
v_res_5137_ = l_Std_Async_Async_ofPurePromise___redArg(v_task_5134_, v_error_5135_);
return v_res_5137_;
}
}
lean_object* l_Std_Async_Async_ofPurePromise(lean_object* v_00_u03b1_5138_, lean_object* v_task_5139_, lean_object* v_error_5140_){
_start:
{
lean_object* v___f_5142_; lean_object* v___x_5143_; 
v___f_5142_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPurePromise___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5142_, 0, v_error_5140_);
v___x_5143_ = lean_apply_1(v_task_5139_, lean_box(0));
if (lean_obj_tag(v___x_5143_) == 0)
{
lean_object* v_a_5144_; lean_object* v___x_5146_; uint8_t v_isShared_5147_; uint8_t v_isSharedCheck_5155_; 
v_a_5144_ = lean_ctor_get(v___x_5143_, 0);
v_isSharedCheck_5155_ = !lean_is_exclusive(v___x_5143_);
if (v_isSharedCheck_5155_ == 0)
{
v___x_5146_ = v___x_5143_;
v_isShared_5147_ = v_isSharedCheck_5155_;
goto v_resetjp_5145_;
}
else
{
lean_inc(v_a_5144_);
lean_dec(v___x_5143_);
v___x_5146_ = lean_box(0);
v_isShared_5147_ = v_isSharedCheck_5155_;
goto v_resetjp_5145_;
}
v_resetjp_5145_:
{
lean_object* v___x_5148_; lean_object* v___x_5149_; uint8_t v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5153_; 
v___x_5148_ = lean_io_promise_result_opt(v_a_5144_);
lean_dec(v_a_5144_);
v___x_5149_ = lean_unsigned_to_nat(0u);
v___x_5150_ = 0;
v___x_5151_ = lean_task_map(v___f_5142_, v___x_5148_, v___x_5149_, v___x_5150_);
if (v_isShared_5147_ == 0)
{
lean_ctor_set_tag(v___x_5146_, 1);
lean_ctor_set(v___x_5146_, 0, v___x_5151_);
v___x_5153_ = v___x_5146_;
goto v_reusejp_5152_;
}
else
{
lean_object* v_reuseFailAlloc_5154_; 
v_reuseFailAlloc_5154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5154_, 0, v___x_5151_);
v___x_5153_ = v_reuseFailAlloc_5154_;
goto v_reusejp_5152_;
}
v_reusejp_5152_:
{
return v___x_5153_;
}
}
}
else
{
lean_object* v_a_5156_; lean_object* v___x_5158_; uint8_t v_isShared_5159_; uint8_t v_isSharedCheck_5164_; 
lean_dec_ref(v___f_5142_);
v_a_5156_ = lean_ctor_get(v___x_5143_, 0);
v_isSharedCheck_5164_ = !lean_is_exclusive(v___x_5143_);
if (v_isSharedCheck_5164_ == 0)
{
v___x_5158_ = v___x_5143_;
v_isShared_5159_ = v_isSharedCheck_5164_;
goto v_resetjp_5157_;
}
else
{
lean_inc(v_a_5156_);
lean_dec(v___x_5143_);
v___x_5158_ = lean_box(0);
v_isShared_5159_ = v_isSharedCheck_5164_;
goto v_resetjp_5157_;
}
v_resetjp_5157_:
{
lean_object* v___x_5161_; 
if (v_isShared_5159_ == 0)
{
lean_ctor_set_tag(v___x_5158_, 0);
v___x_5161_ = v___x_5158_;
goto v_reusejp_5160_;
}
else
{
lean_object* v_reuseFailAlloc_5163_; 
v_reuseFailAlloc_5163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5163_, 0, v_a_5156_);
v___x_5161_ = v_reuseFailAlloc_5163_;
goto v_reusejp_5160_;
}
v_reusejp_5160_:
{
lean_object* v___x_5162_; 
v___x_5162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5162_, 0, v___x_5161_);
return v___x_5162_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Async_ofPurePromise_0interp(lean_interpreter_value* stack)
{
lean_object* v_task_5139_ = stack[1].m_obj;
lean_object* v_error_5140_ = stack[2].m_obj;
lean_object* v_res_5165_;
v_res_5165_ = l_Std_Async_Async_ofPurePromise(lean_box(0), v_task_5139_, v_error_5140_);
stack->m_obj
 = v_res_5165_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPurePromise___boxed(lean_object* v_00_u03b1_5166_, lean_object* v_task_5167_, lean_object* v_error_5168_, lean_object* v_a_5169_){
_start:
{
lean_object* v_res_5170_; 
v_res_5170_ = l_Std_Async_Async_ofPurePromise(v_00_u03b1_5166_, v_task_5167_, v_error_5168_);
return v_res_5170_;
}
}
lean_object* l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___redArg(lean_object* v_t_5172_){
_start:
{
lean_object* v___x_5174_; 
v___x_5174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5174_, 0, v_t_5172_);
return v___x_5174_;
}
}
LEAN_EXPORT void l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_5172_ = stack[0].m_obj;
lean_object* v_res_5175_;
v_res_5175_ = l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___redArg(v_t_5172_);
stack->m_obj
 = v_res_5175_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___redArg___boxed(lean_object* v_t_5176_, lean_object* v_a_5177_){
_start:
{
lean_object* v_res_5178_; 
v_res_5178_ = l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___redArg(v_t_5176_);
return v_res_5178_;
}
}
lean_object* l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1(lean_object* v_00_u03b1_5179_, lean_object* v_t_5180_){
_start:
{
lean_object* v___x_5182_; 
v___x_5182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5182_, 0, v_t_5180_);
return v___x_5182_;
}
}
LEAN_EXPORT void l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_5180_ = stack[1].m_obj;
lean_object* v_res_5183_;
v_res_5183_ = l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1(lean_box(0), v_t_5180_);
stack->m_obj
 = v_res_5183_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___boxed(lean_object* v_00_u03b1_5184_, lean_object* v_t_5185_, lean_object* v_a_5186_){
_start:
{
lean_object* v_res_5187_; 
v_res_5187_ = l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1(v_00_u03b1_5184_, v_t_5185_);
return v_res_5187_;
}
}
lean_object* l_Std_Async_Async_instMonadAwaitPromise___aux__1___redArg(lean_object* v_t_5190_){
_start:
{
lean_object* v___f_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; uint8_t v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; 
v___f_5192_ = ((lean_object*)(l_Std_Async_Async_ofIOTask___redArg___closed__0));
v___x_5193_ = l_IO_Promise_result_x21___redArg(v_t_5190_);
v___x_5194_ = lean_unsigned_to_nat(0u);
v___x_5195_ = 0;
v___x_5196_ = lean_task_map(v___f_5192_, v___x_5193_, v___x_5194_, v___x_5195_);
v___x_5197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5197_, 0, v___x_5196_);
return v___x_5197_;
}
}
LEAN_EXPORT void l_Std_Async_Async_instMonadAwaitPromise___aux__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_5190_ = stack[0].m_obj;
lean_object* v_res_5198_;
v_res_5198_ = l_Std_Async_Async_instMonadAwaitPromise___aux__1___redArg(v_t_5190_);
stack->m_obj
 = v_res_5198_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitPromise___aux__1___redArg___boxed(lean_object* v_t_5199_, lean_object* v_a_5200_){
_start:
{
lean_object* v_res_5201_; 
v_res_5201_ = l_Std_Async_Async_instMonadAwaitPromise___aux__1___redArg(v_t_5199_);
lean_dec(v_t_5199_);
return v_res_5201_;
}
}
lean_object* l_Std_Async_Async_instMonadAwaitPromise___aux__1(lean_object* v_00_u03b1_5202_, lean_object* v_t_5203_){
_start:
{
lean_object* v___f_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; uint8_t v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; 
v___f_5205_ = ((lean_object*)(l_Std_Async_Async_ofIOTask___redArg___closed__0));
v___x_5206_ = l_IO_Promise_result_x21___redArg(v_t_5203_);
v___x_5207_ = lean_unsigned_to_nat(0u);
v___x_5208_ = 0;
v___x_5209_ = lean_task_map(v___f_5205_, v___x_5206_, v___x_5207_, v___x_5208_);
v___x_5210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5210_, 0, v___x_5209_);
return v___x_5210_;
}
}
LEAN_EXPORT void l_Std_Async_Async_instMonadAwaitPromise___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_5203_ = stack[1].m_obj;
lean_object* v_res_5211_;
v_res_5211_ = l_Std_Async_Async_instMonadAwaitPromise___aux__1(lean_box(0), v_t_5203_);
stack->m_obj
 = v_res_5211_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitPromise___aux__1___boxed(lean_object* v_00_u03b1_5212_, lean_object* v_t_5213_, lean_object* v_a_5214_){
_start:
{
lean_object* v_res_5215_; 
v_res_5215_ = l_Std_Async_Async_instMonadAwaitPromise___aux__1(v_00_u03b1_5212_, v_t_5213_);
lean_dec(v_t_5213_);
return v_res_5215_;
}
}
lean_object* l_Std_Async_Async_concurrently___redArg___lam__1(lean_object* v_a_5218_, lean_object* v_x_5219_){
_start:
{
if (lean_obj_tag(v_x_5219_) == 0)
{
lean_object* v_a_5221_; lean_object* v___x_5223_; uint8_t v_isShared_5224_; uint8_t v_isSharedCheck_5229_; 
lean_dec(v_a_5218_);
v_a_5221_ = lean_ctor_get(v_x_5219_, 0);
v_isSharedCheck_5229_ = !lean_is_exclusive(v_x_5219_);
if (v_isSharedCheck_5229_ == 0)
{
v___x_5223_ = v_x_5219_;
v_isShared_5224_ = v_isSharedCheck_5229_;
goto v_resetjp_5222_;
}
else
{
lean_inc(v_a_5221_);
lean_dec(v_x_5219_);
v___x_5223_ = lean_box(0);
v_isShared_5224_ = v_isSharedCheck_5229_;
goto v_resetjp_5222_;
}
v_resetjp_5222_:
{
lean_object* v___x_5226_; 
if (v_isShared_5224_ == 0)
{
v___x_5226_ = v___x_5223_;
goto v_reusejp_5225_;
}
else
{
lean_object* v_reuseFailAlloc_5228_; 
v_reuseFailAlloc_5228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5228_, 0, v_a_5221_);
v___x_5226_ = v_reuseFailAlloc_5228_;
goto v_reusejp_5225_;
}
v_reusejp_5225_:
{
lean_object* v___x_5227_; 
v___x_5227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5227_, 0, v___x_5226_);
return v___x_5227_;
}
}
}
else
{
lean_object* v_a_5230_; lean_object* v___x_5232_; uint8_t v_isShared_5233_; uint8_t v_isSharedCheck_5239_; 
v_a_5230_ = lean_ctor_get(v_x_5219_, 0);
v_isSharedCheck_5239_ = !lean_is_exclusive(v_x_5219_);
if (v_isSharedCheck_5239_ == 0)
{
v___x_5232_ = v_x_5219_;
v_isShared_5233_ = v_isSharedCheck_5239_;
goto v_resetjp_5231_;
}
else
{
lean_inc(v_a_5230_);
lean_dec(v_x_5219_);
v___x_5232_ = lean_box(0);
v_isShared_5233_ = v_isSharedCheck_5239_;
goto v_resetjp_5231_;
}
v_resetjp_5231_:
{
lean_object* v___x_5234_; lean_object* v___x_5236_; 
v___x_5234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5234_, 0, v_a_5218_);
lean_ctor_set(v___x_5234_, 1, v_a_5230_);
if (v_isShared_5233_ == 0)
{
lean_ctor_set(v___x_5232_, 0, v___x_5234_);
v___x_5236_ = v___x_5232_;
goto v_reusejp_5235_;
}
else
{
lean_object* v_reuseFailAlloc_5238_; 
v_reuseFailAlloc_5238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5238_, 0, v___x_5234_);
v___x_5236_ = v_reuseFailAlloc_5238_;
goto v_reusejp_5235_;
}
v_reusejp_5235_:
{
lean_object* v___x_5237_; 
v___x_5237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5237_, 0, v___x_5236_);
return v___x_5237_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Async_concurrently___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5218_ = stack[0].m_obj;
lean_object* v_x_5219_ = stack[1].m_obj;
lean_object* v_res_5240_;
v_res_5240_ = l_Std_Async_Async_concurrently___redArg___lam__1(v_a_5218_, v_x_5219_);
stack->m_obj
 = v_res_5240_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__1___boxed(lean_object* v_a_5241_, lean_object* v_x_5242_, lean_object* v___y_5243_){
_start:
{
lean_object* v_res_5244_; 
v_res_5244_ = l_Std_Async_Async_concurrently___redArg___lam__1(v_a_5241_, v_x_5242_);
return v_res_5244_;
}
}
lean_object* l_Std_Async_Async_concurrently___redArg___lam__0(lean_object* v_a_5245_, lean_object* v_x_5246_){
_start:
{
if (lean_obj_tag(v_x_5246_) == 0)
{
lean_object* v_a_5248_; lean_object* v___x_5250_; uint8_t v_isShared_5251_; uint8_t v_isSharedCheck_5256_; 
lean_dec_ref(v_a_5245_);
v_a_5248_ = lean_ctor_get(v_x_5246_, 0);
v_isSharedCheck_5256_ = !lean_is_exclusive(v_x_5246_);
if (v_isSharedCheck_5256_ == 0)
{
v___x_5250_ = v_x_5246_;
v_isShared_5251_ = v_isSharedCheck_5256_;
goto v_resetjp_5249_;
}
else
{
lean_inc(v_a_5248_);
lean_dec(v_x_5246_);
v___x_5250_ = lean_box(0);
v_isShared_5251_ = v_isSharedCheck_5256_;
goto v_resetjp_5249_;
}
v_resetjp_5249_:
{
lean_object* v___x_5253_; 
if (v_isShared_5251_ == 0)
{
v___x_5253_ = v___x_5250_;
goto v_reusejp_5252_;
}
else
{
lean_object* v_reuseFailAlloc_5255_; 
v_reuseFailAlloc_5255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5255_, 0, v_a_5248_);
v___x_5253_ = v_reuseFailAlloc_5255_;
goto v_reusejp_5252_;
}
v_reusejp_5252_:
{
lean_object* v___x_5254_; 
v___x_5254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5254_, 0, v___x_5253_);
return v___x_5254_;
}
}
}
else
{
lean_object* v_a_5257_; lean_object* v___f_5258_; lean_object* v___x_5259_; uint8_t v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; 
v_a_5257_ = lean_ctor_get(v_x_5246_, 0);
lean_inc(v_a_5257_);
lean_dec_ref_known(v_x_5246_, 1);
v___f_5258_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrently___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_5258_, 0, v_a_5257_);
v___x_5259_ = lean_unsigned_to_nat(0u);
v___x_5260_ = 0;
v___x_5261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5261_, 0, v_a_5245_);
v___x_5262_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5259_, v___x_5260_, v___x_5261_, v___f_5258_);
return v___x_5262_;
}
}
}
LEAN_EXPORT void l_Std_Async_Async_concurrently___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5245_ = stack[0].m_obj;
lean_object* v_x_5246_ = stack[1].m_obj;
lean_object* v_res_5263_;
v_res_5263_ = l_Std_Async_Async_concurrently___redArg___lam__0(v_a_5245_, v_x_5246_);
stack->m_obj
 = v_res_5263_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__0___boxed(lean_object* v_a_5264_, lean_object* v_x_5265_, lean_object* v___y_5266_){
_start:
{
lean_object* v_res_5267_; 
v_res_5267_ = l_Std_Async_Async_concurrently___redArg___lam__0(v_a_5264_, v_x_5265_);
return v_res_5267_;
}
}
lean_object* l_Std_Async_Async_concurrently___redArg___lam__2(lean_object* v_a_5268_, lean_object* v_x_5269_){
_start:
{
if (lean_obj_tag(v_x_5269_) == 0)
{
lean_object* v_a_5271_; lean_object* v___x_5273_; uint8_t v_isShared_5274_; uint8_t v_isSharedCheck_5279_; 
lean_dec_ref(v_a_5268_);
v_a_5271_ = lean_ctor_get(v_x_5269_, 0);
v_isSharedCheck_5279_ = !lean_is_exclusive(v_x_5269_);
if (v_isSharedCheck_5279_ == 0)
{
v___x_5273_ = v_x_5269_;
v_isShared_5274_ = v_isSharedCheck_5279_;
goto v_resetjp_5272_;
}
else
{
lean_inc(v_a_5271_);
lean_dec(v_x_5269_);
v___x_5273_ = lean_box(0);
v_isShared_5274_ = v_isSharedCheck_5279_;
goto v_resetjp_5272_;
}
v_resetjp_5272_:
{
lean_object* v___x_5276_; 
if (v_isShared_5274_ == 0)
{
v___x_5276_ = v___x_5273_;
goto v_reusejp_5275_;
}
else
{
lean_object* v_reuseFailAlloc_5278_; 
v_reuseFailAlloc_5278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5278_, 0, v_a_5271_);
v___x_5276_ = v_reuseFailAlloc_5278_;
goto v_reusejp_5275_;
}
v_reusejp_5275_:
{
lean_object* v___x_5277_; 
v___x_5277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5277_, 0, v___x_5276_);
return v___x_5277_;
}
}
}
else
{
lean_object* v_a_5280_; lean_object* v___f_5281_; lean_object* v___x_5282_; uint8_t v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; 
v_a_5280_ = lean_ctor_get(v_x_5269_, 0);
lean_inc(v_a_5280_);
lean_dec_ref_known(v_x_5269_, 1);
v___f_5281_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrently___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5281_, 0, v_a_5280_);
v___x_5282_ = lean_unsigned_to_nat(0u);
v___x_5283_ = 0;
v___x_5284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5284_, 0, v_a_5268_);
v___x_5285_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5282_, v___x_5283_, v___x_5284_, v___f_5281_);
return v___x_5285_;
}
}
}
LEAN_EXPORT void l_Std_Async_Async_concurrently___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5268_ = stack[0].m_obj;
lean_object* v_x_5269_ = stack[1].m_obj;
lean_object* v_res_5286_;
v_res_5286_ = l_Std_Async_Async_concurrently___redArg___lam__2(v_a_5268_, v_x_5269_);
stack->m_obj
 = v_res_5286_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__2___boxed(lean_object* v_a_5287_, lean_object* v_x_5288_, lean_object* v___y_5289_){
_start:
{
lean_object* v_res_5290_; 
v_res_5290_ = l_Std_Async_Async_concurrently___redArg___lam__2(v_a_5287_, v_x_5288_);
return v_res_5290_;
}
}
lean_object* l_Std_Async_Async_concurrently___redArg___lam__3(lean_object* v_y_5291_, lean_object* v_prio_5292_, lean_object* v___f_5293_, lean_object* v_x_5294_){
_start:
{
if (lean_obj_tag(v_x_5294_) == 0)
{
lean_object* v_a_5296_; lean_object* v___x_5298_; uint8_t v_isShared_5299_; uint8_t v_isSharedCheck_5304_; 
lean_dec_ref(v___f_5293_);
lean_dec(v_prio_5292_);
lean_dec_ref(v_y_5291_);
v_a_5296_ = lean_ctor_get(v_x_5294_, 0);
v_isSharedCheck_5304_ = !lean_is_exclusive(v_x_5294_);
if (v_isSharedCheck_5304_ == 0)
{
v___x_5298_ = v_x_5294_;
v_isShared_5299_ = v_isSharedCheck_5304_;
goto v_resetjp_5297_;
}
else
{
lean_inc(v_a_5296_);
lean_dec(v_x_5294_);
v___x_5298_ = lean_box(0);
v_isShared_5299_ = v_isSharedCheck_5304_;
goto v_resetjp_5297_;
}
v_resetjp_5297_:
{
lean_object* v___x_5301_; 
if (v_isShared_5299_ == 0)
{
v___x_5301_ = v___x_5298_;
goto v_reusejp_5300_;
}
else
{
lean_object* v_reuseFailAlloc_5303_; 
v_reuseFailAlloc_5303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5303_, 0, v_a_5296_);
v___x_5301_ = v_reuseFailAlloc_5303_;
goto v_reusejp_5300_;
}
v_reusejp_5300_:
{
lean_object* v___x_5302_; 
v___x_5302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5302_, 0, v___x_5301_);
return v___x_5302_;
}
}
}
else
{
lean_object* v_a_5305_; lean_object* v___x_5307_; uint8_t v_isShared_5308_; uint8_t v_isSharedCheck_5321_; 
v_a_5305_ = lean_ctor_get(v_x_5294_, 0);
v_isSharedCheck_5321_ = !lean_is_exclusive(v_x_5294_);
if (v_isSharedCheck_5321_ == 0)
{
v___x_5307_ = v_x_5294_;
v_isShared_5308_ = v_isSharedCheck_5321_;
goto v_resetjp_5306_;
}
else
{
lean_inc(v_a_5305_);
lean_dec(v_x_5294_);
v___x_5307_ = lean_box(0);
v_isShared_5308_ = v_isSharedCheck_5321_;
goto v_resetjp_5306_;
}
v_resetjp_5306_:
{
lean_object* v___f_5309_; lean_object* v___x_5310_; uint8_t v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; uint8_t v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5317_; 
v___f_5309_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrently___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_5309_, 0, v_a_5305_);
v___x_5310_ = lean_unsigned_to_nat(0u);
v___x_5311_ = 0;
v___x_5312_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5312_, 0, lean_box(0));
lean_closure_set(v___x_5312_, 1, v_y_5291_);
v___x_5313_ = lean_io_as_task(v___x_5312_, v_prio_5292_);
v___x_5314_ = 1;
v___x_5315_ = lean_task_bind(v___x_5313_, v___f_5293_, v___x_5310_, v___x_5314_);
if (v_isShared_5308_ == 0)
{
lean_ctor_set(v___x_5307_, 0, v___x_5315_);
v___x_5317_ = v___x_5307_;
goto v_reusejp_5316_;
}
else
{
lean_object* v_reuseFailAlloc_5320_; 
v_reuseFailAlloc_5320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5320_, 0, v___x_5315_);
v___x_5317_ = v_reuseFailAlloc_5320_;
goto v_reusejp_5316_;
}
v_reusejp_5316_:
{
lean_object* v___x_5318_; lean_object* v___x_5319_; 
v___x_5318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5318_, 0, v___x_5317_);
v___x_5319_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5310_, v___x_5311_, v___x_5318_, v___f_5309_);
return v___x_5319_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Async_concurrently___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_y_5291_ = stack[0].m_obj;
lean_object* v_prio_5292_ = stack[1].m_obj;
lean_object* v___f_5293_ = stack[2].m_obj;
lean_object* v_x_5294_ = stack[3].m_obj;
lean_object* v_res_5322_;
v_res_5322_ = l_Std_Async_Async_concurrently___redArg___lam__3(v_y_5291_, v_prio_5292_, v___f_5293_, v_x_5294_);
stack->m_obj
 = v_res_5322_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__3___boxed(lean_object* v_y_5323_, lean_object* v_prio_5324_, lean_object* v___f_5325_, lean_object* v_x_5326_, lean_object* v___y_5327_){
_start:
{
lean_object* v_res_5328_; 
v_res_5328_ = l_Std_Async_Async_concurrently___redArg___lam__3(v_y_5323_, v_prio_5324_, v___f_5325_, v_x_5326_);
return v_res_5328_;
}
}
lean_object* l_Std_Async_Async_concurrently___redArg(lean_object* v_x_5329_, lean_object* v_y_5330_, lean_object* v_prio_5331_){
_start:
{
lean_object* v___f_5333_; lean_object* v___f_5334_; lean_object* v___x_5335_; uint8_t v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; uint8_t v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; 
v___f_5333_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
lean_inc(v_prio_5331_);
v___f_5334_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrently___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_5334_, 0, v_y_5330_);
lean_closure_set(v___f_5334_, 1, v_prio_5331_);
lean_closure_set(v___f_5334_, 2, v___f_5333_);
v___x_5335_ = lean_unsigned_to_nat(0u);
v___x_5336_ = 0;
v___x_5337_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5337_, 0, lean_box(0));
lean_closure_set(v___x_5337_, 1, v_x_5329_);
v___x_5338_ = lean_io_as_task(v___x_5337_, v_prio_5331_);
v___x_5339_ = 1;
v___x_5340_ = lean_task_bind(v___x_5338_, v___f_5333_, v___x_5335_, v___x_5339_);
v___x_5341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5341_, 0, v___x_5340_);
v___x_5342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5342_, 0, v___x_5341_);
v___x_5343_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5335_, v___x_5336_, v___x_5342_, v___f_5334_);
return v___x_5343_;
}
}
LEAN_EXPORT void l_Std_Async_Async_concurrently___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5329_ = stack[0].m_obj;
lean_object* v_y_5330_ = stack[1].m_obj;
lean_object* v_prio_5331_ = stack[2].m_obj;
lean_object* v_res_5344_;
v_res_5344_ = l_Std_Async_Async_concurrently___redArg(v_x_5329_, v_y_5330_, v_prio_5331_);
stack->m_obj
 = v_res_5344_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___boxed(lean_object* v_x_5345_, lean_object* v_y_5346_, lean_object* v_prio_5347_, lean_object* v_a_5348_){
_start:
{
lean_object* v_res_5349_; 
v_res_5349_ = l_Std_Async_Async_concurrently___redArg(v_x_5345_, v_y_5346_, v_prio_5347_);
return v_res_5349_;
}
}
lean_object* l_Std_Async_Async_concurrently(lean_object* v_00_u03b1_5350_, lean_object* v_00_u03b2_5351_, lean_object* v_x_5352_, lean_object* v_y_5353_, lean_object* v_prio_5354_){
_start:
{
lean_object* v___f_5356_; lean_object* v___f_5357_; lean_object* v___x_5358_; uint8_t v___x_5359_; lean_object* v___x_5360_; lean_object* v___x_5361_; uint8_t v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; 
v___f_5356_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
lean_inc(v_prio_5354_);
v___f_5357_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrently___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_5357_, 0, v_y_5353_);
lean_closure_set(v___f_5357_, 1, v_prio_5354_);
lean_closure_set(v___f_5357_, 2, v___f_5356_);
v___x_5358_ = lean_unsigned_to_nat(0u);
v___x_5359_ = 0;
v___x_5360_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5360_, 0, lean_box(0));
lean_closure_set(v___x_5360_, 1, v_x_5352_);
v___x_5361_ = lean_io_as_task(v___x_5360_, v_prio_5354_);
v___x_5362_ = 1;
v___x_5363_ = lean_task_bind(v___x_5361_, v___f_5356_, v___x_5358_, v___x_5362_);
v___x_5364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5364_, 0, v___x_5363_);
v___x_5365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5365_, 0, v___x_5364_);
v___x_5366_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5358_, v___x_5359_, v___x_5365_, v___f_5357_);
return v___x_5366_;
}
}
LEAN_EXPORT void l_Std_Async_Async_concurrently_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5352_ = stack[2].m_obj;
lean_object* v_y_5353_ = stack[3].m_obj;
lean_object* v_prio_5354_ = stack[4].m_obj;
lean_object* v_res_5367_;
v_res_5367_ = l_Std_Async_Async_concurrently(lean_box(0), lean_box(0), v_x_5352_, v_y_5353_, v_prio_5354_);
stack->m_obj
 = v_res_5367_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___boxed(lean_object* v_00_u03b1_5368_, lean_object* v_00_u03b2_5369_, lean_object* v_x_5370_, lean_object* v_y_5371_, lean_object* v_prio_5372_, lean_object* v_a_5373_){
_start:
{
lean_object* v_res_5374_; 
v_res_5374_ = l_Std_Async_Async_concurrently(v_00_u03b1_5368_, v_00_u03b2_5369_, v_x_5370_, v_y_5371_, v_prio_5372_);
return v_res_5374_;
}
}
lean_object* l_Std_Async_Async_race___redArg___lam__1(lean_object* v_x_5375_){
_start:
{
if (lean_obj_tag(v_x_5375_) == 0)
{
lean_object* v_a_5377_; lean_object* v___x_5379_; uint8_t v_isShared_5380_; uint8_t v_isSharedCheck_5385_; 
v_a_5377_ = lean_ctor_get(v_x_5375_, 0);
v_isSharedCheck_5385_ = !lean_is_exclusive(v_x_5375_);
if (v_isSharedCheck_5385_ == 0)
{
v___x_5379_ = v_x_5375_;
v_isShared_5380_ = v_isSharedCheck_5385_;
goto v_resetjp_5378_;
}
else
{
lean_inc(v_a_5377_);
lean_dec(v_x_5375_);
v___x_5379_ = lean_box(0);
v_isShared_5380_ = v_isSharedCheck_5385_;
goto v_resetjp_5378_;
}
v_resetjp_5378_:
{
lean_object* v___x_5382_; 
if (v_isShared_5380_ == 0)
{
v___x_5382_ = v___x_5379_;
goto v_reusejp_5381_;
}
else
{
lean_object* v_reuseFailAlloc_5384_; 
v_reuseFailAlloc_5384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5384_, 0, v_a_5377_);
v___x_5382_ = v_reuseFailAlloc_5384_;
goto v_reusejp_5381_;
}
v_reusejp_5381_:
{
lean_object* v___x_5383_; 
v___x_5383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5383_, 0, v___x_5382_);
return v___x_5383_;
}
}
}
else
{
lean_object* v_a_5386_; lean_object* v___x_5387_; 
v_a_5386_ = lean_ctor_get(v_x_5375_, 0);
lean_inc(v_a_5386_);
lean_dec_ref_known(v_x_5375_, 1);
v___x_5387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5387_, 0, v_a_5386_);
return v___x_5387_;
}
}
}
LEAN_EXPORT void l_Std_Async_Async_race___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5375_ = stack[0].m_obj;
lean_object* v_res_5388_;
v_res_5388_ = l_Std_Async_Async_race___redArg___lam__1(v_x_5375_);
stack->m_obj
 = v_res_5388_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__1___boxed(lean_object* v_x_5389_, lean_object* v___y_5390_){
_start:
{
lean_object* v_res_5391_; 
v_res_5391_ = l_Std_Async_Async_race___redArg___lam__1(v_x_5389_);
return v_res_5391_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__0(lean_object* v_a_5392_){
_start:
{
lean_object* v___x_5393_; 
v___x_5393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5393_, 0, v_a_5392_);
return v___x_5393_;
}
}
lean_object* l_Std_Async_Async_race___redArg___lam__3(lean_object* v_a_5394_, lean_object* v_value_5395_){
_start:
{
lean_object* v___x_5397_; 
v___x_5397_ = lean_io_promise_resolve(v_value_5395_, v_a_5394_);
return v___x_5397_;
}
}
LEAN_EXPORT void l_Std_Async_Async_race___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5394_ = stack[0].m_obj;
lean_object* v_value_5395_ = stack[1].m_obj;
lean_object* v_res_5398_;
v_res_5398_ = l_Std_Async_Async_race___redArg___lam__3(v_a_5394_, v_value_5395_);
stack->m_obj
 = v_res_5398_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__3___boxed(lean_object* v_a_5399_, lean_object* v_value_5400_, lean_object* v___y_5401_){
_start:
{
lean_object* v_res_5402_; 
v_res_5402_ = l_Std_Async_Async_race___redArg___lam__3(v_a_5399_, v_value_5400_);
lean_dec(v_a_5399_);
return v_res_5402_;
}
}
lean_object* l_Std_Async_Async_race___redArg___lam__2(lean_object* v_a_5403_, lean_object* v___f_5404_, lean_object* v___f_5405_, lean_object* v_x_5406_){
_start:
{
if (lean_obj_tag(v_x_5406_) == 0)
{
lean_object* v_a_5408_; lean_object* v___x_5410_; uint8_t v_isShared_5411_; uint8_t v_isSharedCheck_5416_; 
lean_dec_ref(v___f_5405_);
lean_dec_ref(v___f_5404_);
v_a_5408_ = lean_ctor_get(v_x_5406_, 0);
v_isSharedCheck_5416_ = !lean_is_exclusive(v_x_5406_);
if (v_isSharedCheck_5416_ == 0)
{
v___x_5410_ = v_x_5406_;
v_isShared_5411_ = v_isSharedCheck_5416_;
goto v_resetjp_5409_;
}
else
{
lean_inc(v_a_5408_);
lean_dec(v_x_5406_);
v___x_5410_ = lean_box(0);
v_isShared_5411_ = v_isSharedCheck_5416_;
goto v_resetjp_5409_;
}
v_resetjp_5409_:
{
lean_object* v___x_5413_; 
if (v_isShared_5411_ == 0)
{
v___x_5413_ = v___x_5410_;
goto v_reusejp_5412_;
}
else
{
lean_object* v_reuseFailAlloc_5415_; 
v_reuseFailAlloc_5415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5415_, 0, v_a_5408_);
v___x_5413_ = v_reuseFailAlloc_5415_;
goto v_reusejp_5412_;
}
v_reusejp_5412_:
{
lean_object* v___x_5414_; 
v___x_5414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5414_, 0, v___x_5413_);
return v___x_5414_;
}
}
}
else
{
lean_object* v___x_5417_; uint8_t v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; 
lean_dec_ref_known(v_x_5406_, 1);
v___x_5417_ = lean_unsigned_to_nat(0u);
v___x_5418_ = 0;
v___x_5419_ = l_IO_Promise_result_x21___redArg(v_a_5403_);
v___x_5420_ = lean_task_map(v___f_5404_, v___x_5419_, v___x_5417_, v___x_5418_);
v___x_5421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5421_, 0, v___x_5420_);
v___x_5422_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5417_, v___x_5418_, v___x_5421_, v___f_5405_);
return v___x_5422_;
}
}
}
LEAN_EXPORT void l_Std_Async_Async_race___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5403_ = stack[0].m_obj;
lean_object* v___f_5404_ = stack[1].m_obj;
lean_object* v___f_5405_ = stack[2].m_obj;
lean_object* v_x_5406_ = stack[3].m_obj;
lean_object* v_res_5423_;
v_res_5423_ = l_Std_Async_Async_race___redArg___lam__2(v_a_5403_, v___f_5404_, v___f_5405_, v_x_5406_);
stack->m_obj
 = v_res_5423_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__2___boxed(lean_object* v_a_5424_, lean_object* v___f_5425_, lean_object* v___f_5426_, lean_object* v_x_5427_, lean_object* v___y_5428_){
_start:
{
lean_object* v_res_5429_; 
v_res_5429_ = l_Std_Async_Async_race___redArg___lam__2(v_a_5424_, v___f_5425_, v___f_5426_, v_x_5427_);
lean_dec(v_a_5424_);
return v_res_5429_;
}
}
lean_object* l_Std_Async_Async_race___redArg___lam__4(lean_object* v_a_5430_, lean_object* v___x_5431_, lean_object* v___x_5432_, uint8_t v___x_5433_, lean_object* v___f_5434_, lean_object* v_x_5435_){
_start:
{
if (lean_obj_tag(v_x_5435_) == 0)
{
lean_object* v_a_5437_; lean_object* v___x_5439_; uint8_t v_isShared_5440_; uint8_t v_isSharedCheck_5445_; 
lean_dec_ref(v___f_5434_);
lean_dec(v___x_5432_);
lean_dec_ref(v___x_5431_);
lean_dec_ref(v_a_5430_);
v_a_5437_ = lean_ctor_get(v_x_5435_, 0);
v_isSharedCheck_5445_ = !lean_is_exclusive(v_x_5435_);
if (v_isSharedCheck_5445_ == 0)
{
v___x_5439_ = v_x_5435_;
v_isShared_5440_ = v_isSharedCheck_5445_;
goto v_resetjp_5438_;
}
else
{
lean_inc(v_a_5437_);
lean_dec(v_x_5435_);
v___x_5439_ = lean_box(0);
v_isShared_5440_ = v_isSharedCheck_5445_;
goto v_resetjp_5438_;
}
v_resetjp_5438_:
{
lean_object* v___x_5442_; 
if (v_isShared_5440_ == 0)
{
v___x_5442_ = v___x_5439_;
goto v_reusejp_5441_;
}
else
{
lean_object* v_reuseFailAlloc_5444_; 
v_reuseFailAlloc_5444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5444_, 0, v_a_5437_);
v___x_5442_ = v_reuseFailAlloc_5444_;
goto v_reusejp_5441_;
}
v_reusejp_5441_:
{
lean_object* v___x_5443_; 
v___x_5443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5443_, 0, v___x_5442_);
return v___x_5443_;
}
}
}
else
{
lean_object* v___x_5447_; uint8_t v_isShared_5448_; uint8_t v_isSharedCheck_5455_; 
v_isSharedCheck_5455_ = !lean_is_exclusive(v_x_5435_);
if (v_isSharedCheck_5455_ == 0)
{
lean_object* v_unused_5456_; 
v_unused_5456_ = lean_ctor_get(v_x_5435_, 0);
lean_dec(v_unused_5456_);
v___x_5447_ = v_x_5435_;
v_isShared_5448_ = v_isSharedCheck_5455_;
goto v_resetjp_5446_;
}
else
{
lean_dec(v_x_5435_);
v___x_5447_ = lean_box(0);
v_isShared_5448_ = v_isSharedCheck_5455_;
goto v_resetjp_5446_;
}
v_resetjp_5446_:
{
lean_object* v___x_5449_; lean_object* v___x_5451_; 
lean_inc(v___x_5432_);
v___x_5449_ = l_BaseIO_chainTask___redArg(v_a_5430_, v___x_5431_, v___x_5432_, v___x_5433_);
if (v_isShared_5448_ == 0)
{
lean_ctor_set(v___x_5447_, 0, v___x_5449_);
v___x_5451_ = v___x_5447_;
goto v_reusejp_5450_;
}
else
{
lean_object* v_reuseFailAlloc_5454_; 
v_reuseFailAlloc_5454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5454_, 0, v___x_5449_);
v___x_5451_ = v_reuseFailAlloc_5454_;
goto v_reusejp_5450_;
}
v_reusejp_5450_:
{
lean_object* v___x_5452_; lean_object* v___x_5453_; 
v___x_5452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5452_, 0, v___x_5451_);
v___x_5453_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5432_, v___x_5433_, v___x_5452_, v___f_5434_);
return v___x_5453_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Async_race___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5430_ = stack[0].m_obj;
lean_object* v___x_5431_ = stack[1].m_obj;
lean_object* v___x_5432_ = stack[2].m_obj;
uint8_t v___x_5433_ = stack[3].m_num;
lean_object* v___f_5434_ = stack[4].m_obj;
lean_object* v_x_5435_ = stack[5].m_obj;
lean_object* v_res_5457_;
v_res_5457_ = l_Std_Async_Async_race___redArg___lam__4(v_a_5430_, v___x_5431_, v___x_5432_, v___x_5433_, v___f_5434_, v_x_5435_);
stack->m_obj
 = v_res_5457_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__4___boxed(lean_object* v_a_5458_, lean_object* v___x_5459_, lean_object* v___x_5460_, lean_object* v___x_5461_, lean_object* v___f_5462_, lean_object* v_x_5463_, lean_object* v___y_5464_){
_start:
{
uint8_t v___x_1461__boxed_5465_; lean_object* v_res_5466_; 
v___x_1461__boxed_5465_ = lean_unbox(v___x_5461_);
v_res_5466_ = l_Std_Async_Async_race___redArg___lam__4(v_a_5458_, v___x_5459_, v___x_5460_, v___x_1461__boxed_5465_, v___f_5462_, v_x_5463_);
return v_res_5466_;
}
}
lean_object* l_Std_Async_Async_race___redArg___lam__5(lean_object* v___f_5467_, lean_object* v___f_5468_, lean_object* v___f_5469_, lean_object* v_a_5470_, lean_object* v_x_5471_){
_start:
{
if (lean_obj_tag(v_x_5471_) == 0)
{
lean_object* v_a_5473_; lean_object* v___x_5475_; uint8_t v_isShared_5476_; uint8_t v_isSharedCheck_5481_; 
lean_dec_ref(v_a_5470_);
lean_dec_ref(v___f_5469_);
lean_dec_ref(v___f_5468_);
lean_dec(v___f_5467_);
v_a_5473_ = lean_ctor_get(v_x_5471_, 0);
v_isSharedCheck_5481_ = !lean_is_exclusive(v_x_5471_);
if (v_isSharedCheck_5481_ == 0)
{
v___x_5475_ = v_x_5471_;
v_isShared_5476_ = v_isSharedCheck_5481_;
goto v_resetjp_5474_;
}
else
{
lean_inc(v_a_5473_);
lean_dec(v_x_5471_);
v___x_5475_ = lean_box(0);
v_isShared_5476_ = v_isSharedCheck_5481_;
goto v_resetjp_5474_;
}
v_resetjp_5474_:
{
lean_object* v___x_5478_; 
if (v_isShared_5476_ == 0)
{
v___x_5478_ = v___x_5475_;
goto v_reusejp_5477_;
}
else
{
lean_object* v_reuseFailAlloc_5480_; 
v_reuseFailAlloc_5480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5480_, 0, v_a_5473_);
v___x_5478_ = v_reuseFailAlloc_5480_;
goto v_reusejp_5477_;
}
v_reusejp_5477_:
{
lean_object* v___x_5479_; 
v___x_5479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5479_, 0, v___x_5478_);
return v___x_5479_;
}
}
}
else
{
lean_object* v_a_5482_; lean_object* v___x_5484_; uint8_t v_isShared_5485_; uint8_t v_isSharedCheck_5498_; 
v_a_5482_ = lean_ctor_get(v_x_5471_, 0);
v_isSharedCheck_5498_ = !lean_is_exclusive(v_x_5471_);
if (v_isSharedCheck_5498_ == 0)
{
v___x_5484_ = v_x_5471_;
v_isShared_5485_ = v_isSharedCheck_5498_;
goto v_resetjp_5483_;
}
else
{
lean_inc(v_a_5482_);
lean_dec(v_x_5471_);
v___x_5484_ = lean_box(0);
v_isShared_5485_ = v_isSharedCheck_5498_;
goto v_resetjp_5483_;
}
v_resetjp_5483_:
{
lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; uint8_t v___x_5489_; lean_object* v___x_5490_; lean_object* v___f_5491_; lean_object* v___x_5492_; lean_object* v___x_5494_; 
v___x_5486_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_5486_, 0, lean_box(0));
lean_closure_set(v___x_5486_, 1, lean_box(0));
lean_closure_set(v___x_5486_, 2, v___f_5467_);
lean_closure_set(v___x_5486_, 3, lean_box(0));
v___x_5487_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_5487_, 0, lean_box(0));
lean_closure_set(v___x_5487_, 1, lean_box(0));
lean_closure_set(v___x_5487_, 2, lean_box(0));
lean_closure_set(v___x_5487_, 3, v___x_5486_);
lean_closure_set(v___x_5487_, 4, v___f_5468_);
v___x_5488_ = lean_unsigned_to_nat(0u);
v___x_5489_ = 0;
v___x_5490_ = lean_box(v___x_5489_);
lean_inc_ref(v___x_5487_);
v___f_5491_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__4___boxed), 7, 5);
lean_closure_set(v___f_5491_, 0, v_a_5482_);
lean_closure_set(v___f_5491_, 1, v___x_5487_);
lean_closure_set(v___f_5491_, 2, v___x_5488_);
lean_closure_set(v___f_5491_, 3, v___x_5490_);
lean_closure_set(v___f_5491_, 4, v___f_5469_);
v___x_5492_ = l_BaseIO_chainTask___redArg(v_a_5470_, v___x_5487_, v___x_5488_, v___x_5489_);
if (v_isShared_5485_ == 0)
{
lean_ctor_set(v___x_5484_, 0, v___x_5492_);
v___x_5494_ = v___x_5484_;
goto v_reusejp_5493_;
}
else
{
lean_object* v_reuseFailAlloc_5497_; 
v_reuseFailAlloc_5497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5497_, 0, v___x_5492_);
v___x_5494_ = v_reuseFailAlloc_5497_;
goto v_reusejp_5493_;
}
v_reusejp_5493_:
{
lean_object* v___x_5495_; lean_object* v___x_5496_; 
v___x_5495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5495_, 0, v___x_5494_);
v___x_5496_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5488_, v___x_5489_, v___x_5495_, v___f_5491_);
return v___x_5496_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Async_race___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_5467_ = stack[0].m_obj;
lean_object* v___f_5468_ = stack[1].m_obj;
lean_object* v___f_5469_ = stack[2].m_obj;
lean_object* v_a_5470_ = stack[3].m_obj;
lean_object* v_x_5471_ = stack[4].m_obj;
lean_object* v_res_5499_;
v_res_5499_ = l_Std_Async_Async_race___redArg___lam__5(v___f_5467_, v___f_5468_, v___f_5469_, v_a_5470_, v_x_5471_);
stack->m_obj
 = v_res_5499_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__5___boxed(lean_object* v___f_5500_, lean_object* v___f_5501_, lean_object* v___f_5502_, lean_object* v_a_5503_, lean_object* v_x_5504_, lean_object* v___y_5505_){
_start:
{
lean_object* v_res_5506_; 
v_res_5506_ = l_Std_Async_Async_race___redArg___lam__5(v___f_5500_, v___f_5501_, v___f_5502_, v_a_5503_, v_x_5504_);
return v_res_5506_;
}
}
lean_object* l_Std_Async_Async_race___redArg___lam__6(lean_object* v___f_5507_, lean_object* v___f_5508_, lean_object* v___f_5509_, lean_object* v_y_5510_, lean_object* v_prio_5511_, lean_object* v___f_5512_, lean_object* v_x_5513_){
_start:
{
if (lean_obj_tag(v_x_5513_) == 0)
{
lean_object* v_a_5515_; lean_object* v___x_5517_; uint8_t v_isShared_5518_; uint8_t v_isSharedCheck_5523_; 
lean_dec_ref(v___f_5512_);
lean_dec(v_prio_5511_);
lean_dec_ref(v_y_5510_);
lean_dec_ref(v___f_5509_);
lean_dec_ref(v___f_5508_);
lean_dec(v___f_5507_);
v_a_5515_ = lean_ctor_get(v_x_5513_, 0);
v_isSharedCheck_5523_ = !lean_is_exclusive(v_x_5513_);
if (v_isSharedCheck_5523_ == 0)
{
v___x_5517_ = v_x_5513_;
v_isShared_5518_ = v_isSharedCheck_5523_;
goto v_resetjp_5516_;
}
else
{
lean_inc(v_a_5515_);
lean_dec(v_x_5513_);
v___x_5517_ = lean_box(0);
v_isShared_5518_ = v_isSharedCheck_5523_;
goto v_resetjp_5516_;
}
v_resetjp_5516_:
{
lean_object* v___x_5520_; 
if (v_isShared_5518_ == 0)
{
v___x_5520_ = v___x_5517_;
goto v_reusejp_5519_;
}
else
{
lean_object* v_reuseFailAlloc_5522_; 
v_reuseFailAlloc_5522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5522_, 0, v_a_5515_);
v___x_5520_ = v_reuseFailAlloc_5522_;
goto v_reusejp_5519_;
}
v_reusejp_5519_:
{
lean_object* v___x_5521_; 
v___x_5521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5521_, 0, v___x_5520_);
return v___x_5521_;
}
}
}
else
{
lean_object* v_a_5524_; lean_object* v___x_5526_; uint8_t v_isShared_5527_; uint8_t v_isSharedCheck_5540_; 
v_a_5524_ = lean_ctor_get(v_x_5513_, 0);
v_isSharedCheck_5540_ = !lean_is_exclusive(v_x_5513_);
if (v_isSharedCheck_5540_ == 0)
{
v___x_5526_ = v_x_5513_;
v_isShared_5527_ = v_isSharedCheck_5540_;
goto v_resetjp_5525_;
}
else
{
lean_inc(v_a_5524_);
lean_dec(v_x_5513_);
v___x_5526_ = lean_box(0);
v_isShared_5527_ = v_isSharedCheck_5540_;
goto v_resetjp_5525_;
}
v_resetjp_5525_:
{
lean_object* v___f_5528_; lean_object* v___x_5529_; uint8_t v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; uint8_t v___x_5533_; lean_object* v___x_5534_; lean_object* v___x_5536_; 
v___f_5528_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__5___boxed), 6, 4);
lean_closure_set(v___f_5528_, 0, v___f_5507_);
lean_closure_set(v___f_5528_, 1, v___f_5508_);
lean_closure_set(v___f_5528_, 2, v___f_5509_);
lean_closure_set(v___f_5528_, 3, v_a_5524_);
v___x_5529_ = lean_unsigned_to_nat(0u);
v___x_5530_ = 0;
v___x_5531_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5531_, 0, lean_box(0));
lean_closure_set(v___x_5531_, 1, v_y_5510_);
v___x_5532_ = lean_io_as_task(v___x_5531_, v_prio_5511_);
v___x_5533_ = 1;
v___x_5534_ = lean_task_bind(v___x_5532_, v___f_5512_, v___x_5529_, v___x_5533_);
if (v_isShared_5527_ == 0)
{
lean_ctor_set(v___x_5526_, 0, v___x_5534_);
v___x_5536_ = v___x_5526_;
goto v_reusejp_5535_;
}
else
{
lean_object* v_reuseFailAlloc_5539_; 
v_reuseFailAlloc_5539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5539_, 0, v___x_5534_);
v___x_5536_ = v_reuseFailAlloc_5539_;
goto v_reusejp_5535_;
}
v_reusejp_5535_:
{
lean_object* v___x_5537_; lean_object* v___x_5538_; 
v___x_5537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5537_, 0, v___x_5536_);
v___x_5538_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5529_, v___x_5530_, v___x_5537_, v___f_5528_);
return v___x_5538_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Async_race___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_5507_ = stack[0].m_obj;
lean_object* v___f_5508_ = stack[1].m_obj;
lean_object* v___f_5509_ = stack[2].m_obj;
lean_object* v_y_5510_ = stack[3].m_obj;
lean_object* v_prio_5511_ = stack[4].m_obj;
lean_object* v___f_5512_ = stack[5].m_obj;
lean_object* v_x_5513_ = stack[6].m_obj;
lean_object* v_res_5541_;
v_res_5541_ = l_Std_Async_Async_race___redArg___lam__6(v___f_5507_, v___f_5508_, v___f_5509_, v_y_5510_, v_prio_5511_, v___f_5512_, v_x_5513_);
stack->m_obj
 = v_res_5541_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__6___boxed(lean_object* v___f_5542_, lean_object* v___f_5543_, lean_object* v___f_5544_, lean_object* v_y_5545_, lean_object* v_prio_5546_, lean_object* v___f_5547_, lean_object* v_x_5548_, lean_object* v___y_5549_){
_start:
{
lean_object* v_res_5550_; 
v_res_5550_ = l_Std_Async_Async_race___redArg___lam__6(v___f_5542_, v___f_5543_, v___f_5544_, v_y_5545_, v_prio_5546_, v___f_5547_, v_x_5548_);
return v_res_5550_;
}
}
lean_object* l_Std_Async_Async_race___redArg___lam__7(lean_object* v___f_5551_, lean_object* v___f_5552_, lean_object* v___f_5553_, lean_object* v_y_5554_, lean_object* v_prio_5555_, lean_object* v___f_5556_, lean_object* v_x_5557_, lean_object* v___f_5558_, lean_object* v_x_5559_){
_start:
{
if (lean_obj_tag(v_x_5559_) == 0)
{
lean_object* v_a_5561_; lean_object* v___x_5563_; uint8_t v_isShared_5564_; uint8_t v_isSharedCheck_5569_; 
lean_dec_ref(v___f_5558_);
lean_dec_ref(v_x_5557_);
lean_dec_ref(v___f_5556_);
lean_dec(v_prio_5555_);
lean_dec_ref(v_y_5554_);
lean_dec(v___f_5553_);
lean_dec_ref(v___f_5552_);
lean_dec_ref(v___f_5551_);
v_a_5561_ = lean_ctor_get(v_x_5559_, 0);
v_isSharedCheck_5569_ = !lean_is_exclusive(v_x_5559_);
if (v_isSharedCheck_5569_ == 0)
{
v___x_5563_ = v_x_5559_;
v_isShared_5564_ = v_isSharedCheck_5569_;
goto v_resetjp_5562_;
}
else
{
lean_inc(v_a_5561_);
lean_dec(v_x_5559_);
v___x_5563_ = lean_box(0);
v_isShared_5564_ = v_isSharedCheck_5569_;
goto v_resetjp_5562_;
}
v_resetjp_5562_:
{
lean_object* v___x_5566_; 
if (v_isShared_5564_ == 0)
{
v___x_5566_ = v___x_5563_;
goto v_reusejp_5565_;
}
else
{
lean_object* v_reuseFailAlloc_5568_; 
v_reuseFailAlloc_5568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5568_, 0, v_a_5561_);
v___x_5566_ = v_reuseFailAlloc_5568_;
goto v_reusejp_5565_;
}
v_reusejp_5565_:
{
lean_object* v___x_5567_; 
v___x_5567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5567_, 0, v___x_5566_);
return v___x_5567_;
}
}
}
else
{
lean_object* v_a_5570_; lean_object* v___x_5572_; uint8_t v_isShared_5573_; uint8_t v_isSharedCheck_5588_; 
v_a_5570_ = lean_ctor_get(v_x_5559_, 0);
v_isSharedCheck_5588_ = !lean_is_exclusive(v_x_5559_);
if (v_isSharedCheck_5588_ == 0)
{
v___x_5572_ = v_x_5559_;
v_isShared_5573_ = v_isSharedCheck_5588_;
goto v_resetjp_5571_;
}
else
{
lean_inc(v_a_5570_);
lean_dec(v_x_5559_);
v___x_5572_ = lean_box(0);
v_isShared_5573_ = v_isSharedCheck_5588_;
goto v_resetjp_5571_;
}
v_resetjp_5571_:
{
lean_object* v___f_5574_; lean_object* v___f_5575_; lean_object* v___f_5576_; lean_object* v___x_5577_; uint8_t v___x_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; uint8_t v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5584_; 
lean_inc(v_a_5570_);
v___f_5574_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_5574_, 0, v_a_5570_);
v___f_5575_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_5575_, 0, v_a_5570_);
lean_closure_set(v___f_5575_, 1, v___f_5551_);
lean_closure_set(v___f_5575_, 2, v___f_5552_);
lean_inc(v_prio_5555_);
v___f_5576_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__6___boxed), 8, 6);
lean_closure_set(v___f_5576_, 0, v___f_5553_);
lean_closure_set(v___f_5576_, 1, v___f_5574_);
lean_closure_set(v___f_5576_, 2, v___f_5575_);
lean_closure_set(v___f_5576_, 3, v_y_5554_);
lean_closure_set(v___f_5576_, 4, v_prio_5555_);
lean_closure_set(v___f_5576_, 5, v___f_5556_);
v___x_5577_ = lean_unsigned_to_nat(0u);
v___x_5578_ = 0;
v___x_5579_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5579_, 0, lean_box(0));
lean_closure_set(v___x_5579_, 1, v_x_5557_);
v___x_5580_ = lean_io_as_task(v___x_5579_, v_prio_5555_);
v___x_5581_ = 1;
v___x_5582_ = lean_task_bind(v___x_5580_, v___f_5558_, v___x_5577_, v___x_5581_);
if (v_isShared_5573_ == 0)
{
lean_ctor_set(v___x_5572_, 0, v___x_5582_);
v___x_5584_ = v___x_5572_;
goto v_reusejp_5583_;
}
else
{
lean_object* v_reuseFailAlloc_5587_; 
v_reuseFailAlloc_5587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5587_, 0, v___x_5582_);
v___x_5584_ = v_reuseFailAlloc_5587_;
goto v_reusejp_5583_;
}
v_reusejp_5583_:
{
lean_object* v___x_5585_; lean_object* v___x_5586_; 
v___x_5585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5585_, 0, v___x_5584_);
v___x_5586_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5577_, v___x_5578_, v___x_5585_, v___f_5576_);
return v___x_5586_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Async_race___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_5551_ = stack[0].m_obj;
lean_object* v___f_5552_ = stack[1].m_obj;
lean_object* v___f_5553_ = stack[2].m_obj;
lean_object* v_y_5554_ = stack[3].m_obj;
lean_object* v_prio_5555_ = stack[4].m_obj;
lean_object* v___f_5556_ = stack[5].m_obj;
lean_object* v_x_5557_ = stack[6].m_obj;
lean_object* v___f_5558_ = stack[7].m_obj;
lean_object* v_x_5559_ = stack[8].m_obj;
lean_object* v_res_5589_;
v_res_5589_ = l_Std_Async_Async_race___redArg___lam__7(v___f_5551_, v___f_5552_, v___f_5553_, v_y_5554_, v_prio_5555_, v___f_5556_, v_x_5557_, v___f_5558_, v_x_5559_);
stack->m_obj
 = v_res_5589_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__7___boxed(lean_object* v___f_5590_, lean_object* v___f_5591_, lean_object* v___f_5592_, lean_object* v_y_5593_, lean_object* v_prio_5594_, lean_object* v___f_5595_, lean_object* v_x_5596_, lean_object* v___f_5597_, lean_object* v_x_5598_, lean_object* v___y_5599_){
_start:
{
lean_object* v_res_5600_; 
v_res_5600_ = l_Std_Async_Async_race___redArg___lam__7(v___f_5590_, v___f_5591_, v___f_5592_, v_y_5593_, v_prio_5594_, v___f_5595_, v_x_5596_, v___f_5597_, v_x_5598_);
return v_res_5600_;
}
}
lean_object* l_Std_Async_Async_race___redArg(lean_object* v_x_5603_, lean_object* v_y_5604_, lean_object* v_prio_5605_){
_start:
{
lean_object* v___f_5607_; lean_object* v___f_5608_; lean_object* v___f_5609_; lean_object* v___f_5610_; lean_object* v___f_5611_; lean_object* v___x_5612_; uint8_t v___x_5613_; lean_object* v___x_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; 
v___f_5607_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___f_5608_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__0));
v___f_5609_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__1));
v___f_5610_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_5611_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_5611_, 0, v___f_5609_);
lean_closure_set(v___f_5611_, 1, v___f_5608_);
lean_closure_set(v___f_5611_, 2, v___f_5610_);
lean_closure_set(v___f_5611_, 3, v_y_5604_);
lean_closure_set(v___f_5611_, 4, v_prio_5605_);
lean_closure_set(v___f_5611_, 5, v___f_5607_);
lean_closure_set(v___f_5611_, 6, v_x_5603_);
lean_closure_set(v___f_5611_, 7, v___f_5607_);
v___x_5612_ = lean_unsigned_to_nat(0u);
v___x_5613_ = 0;
v___x_5614_ = lean_io_promise_new();
v___x_5615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5615_, 0, v___x_5614_);
v___x_5616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5616_, 0, v___x_5615_);
v___x_5617_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5612_, v___x_5613_, v___x_5616_, v___f_5611_);
return v___x_5617_;
}
}
LEAN_EXPORT void l_Std_Async_Async_race___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5603_ = stack[0].m_obj;
lean_object* v_y_5604_ = stack[1].m_obj;
lean_object* v_prio_5605_ = stack[2].m_obj;
lean_object* v_res_5618_;
v_res_5618_ = l_Std_Async_Async_race___redArg(v_x_5603_, v_y_5604_, v_prio_5605_);
stack->m_obj
 = v_res_5618_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___boxed(lean_object* v_x_5619_, lean_object* v_y_5620_, lean_object* v_prio_5621_, lean_object* v_a_5622_){
_start:
{
lean_object* v_res_5623_; 
v_res_5623_ = l_Std_Async_Async_race___redArg(v_x_5619_, v_y_5620_, v_prio_5621_);
return v_res_5623_;
}
}
lean_object* l_Std_Async_Async_race(lean_object* v_00_u03b1_5624_, lean_object* v_inst_5625_, lean_object* v_x_5626_, lean_object* v_y_5627_, lean_object* v_prio_5628_){
_start:
{
lean_object* v___f_5630_; lean_object* v___f_5631_; lean_object* v___f_5632_; lean_object* v___f_5633_; lean_object* v___f_5634_; lean_object* v___x_5635_; uint8_t v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; 
v___f_5630_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___f_5631_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__0));
v___f_5632_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__1));
v___f_5633_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_5634_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_5634_, 0, v___f_5632_);
lean_closure_set(v___f_5634_, 1, v___f_5631_);
lean_closure_set(v___f_5634_, 2, v___f_5633_);
lean_closure_set(v___f_5634_, 3, v_y_5627_);
lean_closure_set(v___f_5634_, 4, v_prio_5628_);
lean_closure_set(v___f_5634_, 5, v___f_5630_);
lean_closure_set(v___f_5634_, 6, v_x_5626_);
lean_closure_set(v___f_5634_, 7, v___f_5630_);
v___x_5635_ = lean_unsigned_to_nat(0u);
v___x_5636_ = 0;
v___x_5637_ = lean_io_promise_new();
v___x_5638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5638_, 0, v___x_5637_);
v___x_5639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5639_, 0, v___x_5638_);
v___x_5640_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5635_, v___x_5636_, v___x_5639_, v___f_5634_);
return v___x_5640_;
}
}
LEAN_EXPORT void l_Std_Async_Async_race_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_5625_ = stack[1].m_obj;
lean_object* v_x_5626_ = stack[2].m_obj;
lean_object* v_y_5627_ = stack[3].m_obj;
lean_object* v_prio_5628_ = stack[4].m_obj;
lean_object* v_res_5641_;
v_res_5641_ = l_Std_Async_Async_race(lean_box(0), v_inst_5625_, v_x_5626_, v_y_5627_, v_prio_5628_);
stack->m_obj
 = v_res_5641_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___boxed(lean_object* v_00_u03b1_5642_, lean_object* v_inst_5643_, lean_object* v_x_5644_, lean_object* v_y_5645_, lean_object* v_prio_5646_, lean_object* v_a_5647_){
_start:
{
lean_object* v_res_5648_; 
v_res_5648_ = l_Std_Async_Async_race(v_00_u03b1_5642_, v_inst_5643_, v_x_5644_, v_y_5645_, v_prio_5646_);
lean_dec(v_inst_5643_);
return v_res_5648_;
}
}
lean_object* l_Std_Async_Async_concurrentlyAll___redArg___lam__1(lean_object* v_prio_5649_, lean_object* v___f_5650_, lean_object* v_x_5651_){
_start:
{
lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; uint8_t v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; 
v___x_5653_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5653_, 0, lean_box(0));
lean_closure_set(v___x_5653_, 1, v_x_5651_);
v___x_5654_ = lean_io_as_task(v___x_5653_, v_prio_5649_);
v___x_5655_ = lean_unsigned_to_nat(0u);
v___x_5656_ = 1;
v___x_5657_ = lean_task_bind(v___x_5654_, v___f_5650_, v___x_5655_, v___x_5656_);
v___x_5658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5658_, 0, v___x_5657_);
v___x_5659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5659_, 0, v___x_5658_);
return v___x_5659_;
}
}
LEAN_EXPORT void l_Std_Async_Async_concurrentlyAll___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_prio_5649_ = stack[0].m_obj;
lean_object* v___f_5650_ = stack[1].m_obj;
lean_object* v_x_5651_ = stack[2].m_obj;
lean_object* v_res_5660_;
v_res_5660_ = l_Std_Async_Async_concurrentlyAll___redArg___lam__1(v_prio_5649_, v___f_5650_, v_x_5651_);
stack->m_obj
 = v_res_5660_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg___lam__1___boxed(lean_object* v_prio_5661_, lean_object* v___f_5662_, lean_object* v_x_5663_, lean_object* v___y_5664_){
_start:
{
lean_object* v_res_5665_; 
v_res_5665_ = l_Std_Async_Async_concurrentlyAll___redArg___lam__1(v_prio_5661_, v___f_5662_, v_x_5663_);
return v_res_5665_;
}
}
lean_object* l_Std_Async_Async_concurrentlyAll___redArg___lam__0(lean_object* v___x_5667_, lean_object* v_x_5668_){
_start:
{
if (lean_obj_tag(v_x_5668_) == 0)
{
lean_object* v_a_5670_; lean_object* v___x_5672_; uint8_t v_isShared_5673_; uint8_t v_isSharedCheck_5678_; 
lean_dec_ref(v___x_5667_);
v_a_5670_ = lean_ctor_get(v_x_5668_, 0);
v_isSharedCheck_5678_ = !lean_is_exclusive(v_x_5668_);
if (v_isSharedCheck_5678_ == 0)
{
v___x_5672_ = v_x_5668_;
v_isShared_5673_ = v_isSharedCheck_5678_;
goto v_resetjp_5671_;
}
else
{
lean_inc(v_a_5670_);
lean_dec(v_x_5668_);
v___x_5672_ = lean_box(0);
v_isShared_5673_ = v_isSharedCheck_5678_;
goto v_resetjp_5671_;
}
v_resetjp_5671_:
{
lean_object* v___x_5675_; 
if (v_isShared_5673_ == 0)
{
v___x_5675_ = v___x_5672_;
goto v_reusejp_5674_;
}
else
{
lean_object* v_reuseFailAlloc_5677_; 
v_reuseFailAlloc_5677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5677_, 0, v_a_5670_);
v___x_5675_ = v_reuseFailAlloc_5677_;
goto v_reusejp_5674_;
}
v_reusejp_5674_:
{
lean_object* v___x_5676_; 
v___x_5676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5676_, 0, v___x_5675_);
return v___x_5676_;
}
}
}
else
{
lean_object* v_a_5679_; lean_object* v___x_5680_; size_t v_sz_5681_; size_t v___x_5682_; lean_object* v___x_271__overap_5683_; lean_object* v___x_5684_; 
v_a_5679_ = lean_ctor_get(v_x_5668_, 0);
lean_inc(v_a_5679_);
lean_dec_ref_known(v_x_5668_, 1);
v___x_5680_ = ((lean_object*)(l_Std_Async_Async_concurrentlyAll___redArg___lam__0___closed__0));
v_sz_5681_ = lean_array_size(v_a_5679_);
v___x_5682_ = ((size_t)0ULL);
v___x_271__overap_5683_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_5667_, v___x_5680_, v_sz_5681_, v___x_5682_, v_a_5679_);
v___x_5684_ = lean_apply_1(v___x_271__overap_5683_, lean_box(0));
return v___x_5684_;
}
}
}
LEAN_EXPORT void l_Std_Async_Async_concurrentlyAll___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_5667_ = stack[0].m_obj;
lean_object* v_x_5668_ = stack[1].m_obj;
lean_object* v_res_5685_;
v_res_5685_ = l_Std_Async_Async_concurrentlyAll___redArg___lam__0(v___x_5667_, v_x_5668_);
stack->m_obj
 = v_res_5685_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg___lam__0___boxed(lean_object* v___x_5686_, lean_object* v_x_5687_, lean_object* v___y_5688_){
_start:
{
lean_object* v_res_5689_; 
v_res_5689_ = l_Std_Async_Async_concurrentlyAll___redArg___lam__0(v___x_5686_, v_x_5687_);
return v_res_5689_;
}
}
static lean_object* _init_l_Std_Async_Async_concurrentlyAll___redArg___closed__0(void){
_start:
{
lean_object* v___x_5690_; lean_object* v___f_5691_; 
v___x_5690_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___closed__0, &l_Std_Async_EAsync_instMonad___closed__0_once, _init_l_Std_Async_EAsync_instMonad___closed__0);
v___f_5691_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrentlyAll___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5691_, 0, v___x_5690_);
return v___f_5691_;
}
}
lean_object* l_Std_Async_Async_concurrentlyAll___redArg(lean_object* v_xs_5692_, lean_object* v_prio_5693_){
_start:
{
lean_object* v___f_5695_; lean_object* v___f_5696_; lean_object* v___x_5697_; lean_object* v___f_5698_; lean_object* v___x_5699_; uint8_t v___x_5700_; size_t v_sz_5701_; size_t v___x_5702_; lean_object* v___x_204__overap_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; 
v___f_5695_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___f_5696_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrentlyAll___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_5696_, 0, v_prio_5693_);
lean_closure_set(v___f_5696_, 1, v___f_5695_);
v___x_5697_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___closed__0, &l_Std_Async_EAsync_instMonad___closed__0_once, _init_l_Std_Async_EAsync_instMonad___closed__0);
v___f_5698_ = lean_obj_once(&l_Std_Async_Async_concurrentlyAll___redArg___closed__0, &l_Std_Async_Async_concurrentlyAll___redArg___closed__0_once, _init_l_Std_Async_Async_concurrentlyAll___redArg___closed__0);
v___x_5699_ = lean_unsigned_to_nat(0u);
v___x_5700_ = 0;
v_sz_5701_ = lean_array_size(v_xs_5692_);
v___x_5702_ = ((size_t)0ULL);
v___x_204__overap_5703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_5697_, v___f_5696_, v_sz_5701_, v___x_5702_, v_xs_5692_);
v___x_5704_ = lean_apply_1(v___x_204__overap_5703_, lean_box(0));
v___x_5705_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5699_, v___x_5700_, v___x_5704_, v___f_5698_);
return v___x_5705_;
}
}
LEAN_EXPORT void l_Std_Async_Async_concurrentlyAll___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_5692_ = stack[0].m_obj;
lean_object* v_prio_5693_ = stack[1].m_obj;
lean_object* v_res_5706_;
v_res_5706_ = l_Std_Async_Async_concurrentlyAll___redArg(v_xs_5692_, v_prio_5693_);
stack->m_obj
 = v_res_5706_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg___boxed(lean_object* v_xs_5707_, lean_object* v_prio_5708_, lean_object* v_a_5709_){
_start:
{
lean_object* v_res_5710_; 
v_res_5710_ = l_Std_Async_Async_concurrentlyAll___redArg(v_xs_5707_, v_prio_5708_);
return v_res_5710_;
}
}
lean_object* l_Std_Async_Async_concurrentlyAll(lean_object* v_00_u03b1_5711_, lean_object* v_xs_5712_, lean_object* v_prio_5713_){
_start:
{
lean_object* v___f_5715_; lean_object* v___f_5716_; lean_object* v___x_5717_; lean_object* v___f_5718_; lean_object* v___x_5719_; uint8_t v___x_5720_; size_t v_sz_5721_; size_t v___x_5722_; lean_object* v___x_241__overap_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; 
v___f_5715_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___f_5716_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrentlyAll___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_5716_, 0, v_prio_5713_);
lean_closure_set(v___f_5716_, 1, v___f_5715_);
v___x_5717_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___closed__0, &l_Std_Async_EAsync_instMonad___closed__0_once, _init_l_Std_Async_EAsync_instMonad___closed__0);
v___f_5718_ = lean_obj_once(&l_Std_Async_Async_concurrentlyAll___redArg___closed__0, &l_Std_Async_Async_concurrentlyAll___redArg___closed__0_once, _init_l_Std_Async_Async_concurrentlyAll___redArg___closed__0);
v___x_5719_ = lean_unsigned_to_nat(0u);
v___x_5720_ = 0;
v_sz_5721_ = lean_array_size(v_xs_5712_);
v___x_5722_ = ((size_t)0ULL);
v___x_241__overap_5723_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_5717_, v___f_5716_, v_sz_5721_, v___x_5722_, v_xs_5712_);
v___x_5724_ = lean_apply_1(v___x_241__overap_5723_, lean_box(0));
v___x_5725_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5719_, v___x_5720_, v___x_5724_, v___f_5718_);
return v___x_5725_;
}
}
LEAN_EXPORT void l_Std_Async_Async_concurrentlyAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_5712_ = stack[1].m_obj;
lean_object* v_prio_5713_ = stack[2].m_obj;
lean_object* v_res_5726_;
v_res_5726_ = l_Std_Async_Async_concurrentlyAll(lean_box(0), v_xs_5712_, v_prio_5713_);
stack->m_obj
 = v_res_5726_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___boxed(lean_object* v_00_u03b1_5727_, lean_object* v_xs_5728_, lean_object* v_prio_5729_, lean_object* v_a_5730_){
_start:
{
lean_object* v_res_5731_; 
v_res_5731_ = l_Std_Async_Async_concurrentlyAll(v_00_u03b1_5727_, v_xs_5728_, v_prio_5729_);
return v_res_5731_;
}
}
lean_object* l_Std_Async_Async_raceAll___redArg___lam__4(lean_object* v___f_5732_, lean_object* v___f_5733_, lean_object* v_x_5734_){
_start:
{
if (lean_obj_tag(v_x_5734_) == 0)
{
lean_object* v_a_5736_; lean_object* v___x_5738_; uint8_t v_isShared_5739_; uint8_t v_isSharedCheck_5744_; 
lean_dec_ref(v___f_5733_);
lean_dec(v___f_5732_);
v_a_5736_ = lean_ctor_get(v_x_5734_, 0);
v_isSharedCheck_5744_ = !lean_is_exclusive(v_x_5734_);
if (v_isSharedCheck_5744_ == 0)
{
v___x_5738_ = v_x_5734_;
v_isShared_5739_ = v_isSharedCheck_5744_;
goto v_resetjp_5737_;
}
else
{
lean_inc(v_a_5736_);
lean_dec(v_x_5734_);
v___x_5738_ = lean_box(0);
v_isShared_5739_ = v_isSharedCheck_5744_;
goto v_resetjp_5737_;
}
v_resetjp_5737_:
{
lean_object* v___x_5741_; 
if (v_isShared_5739_ == 0)
{
v___x_5741_ = v___x_5738_;
goto v_reusejp_5740_;
}
else
{
lean_object* v_reuseFailAlloc_5743_; 
v_reuseFailAlloc_5743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5743_, 0, v_a_5736_);
v___x_5741_ = v_reuseFailAlloc_5743_;
goto v_reusejp_5740_;
}
v_reusejp_5740_:
{
lean_object* v___x_5742_; 
v___x_5742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5742_, 0, v___x_5741_);
return v___x_5742_;
}
}
}
else
{
lean_object* v_a_5745_; lean_object* v___x_5747_; uint8_t v_isShared_5748_; uint8_t v_isSharedCheck_5758_; 
v_a_5745_ = lean_ctor_get(v_x_5734_, 0);
v_isSharedCheck_5758_ = !lean_is_exclusive(v_x_5734_);
if (v_isSharedCheck_5758_ == 0)
{
v___x_5747_ = v_x_5734_;
v_isShared_5748_ = v_isSharedCheck_5758_;
goto v_resetjp_5746_;
}
else
{
lean_inc(v_a_5745_);
lean_dec(v_x_5734_);
v___x_5747_ = lean_box(0);
v_isShared_5748_ = v_isSharedCheck_5758_;
goto v_resetjp_5746_;
}
v_resetjp_5746_:
{
lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; uint8_t v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5755_; 
v___x_5749_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_5749_, 0, lean_box(0));
lean_closure_set(v___x_5749_, 1, lean_box(0));
lean_closure_set(v___x_5749_, 2, v___f_5732_);
lean_closure_set(v___x_5749_, 3, lean_box(0));
v___x_5750_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_5750_, 0, lean_box(0));
lean_closure_set(v___x_5750_, 1, lean_box(0));
lean_closure_set(v___x_5750_, 2, lean_box(0));
lean_closure_set(v___x_5750_, 3, v___x_5749_);
lean_closure_set(v___x_5750_, 4, v___f_5733_);
v___x_5751_ = lean_unsigned_to_nat(0u);
v___x_5752_ = 0;
v___x_5753_ = l_BaseIO_chainTask___redArg(v_a_5745_, v___x_5750_, v___x_5751_, v___x_5752_);
if (v_isShared_5748_ == 0)
{
lean_ctor_set(v___x_5747_, 0, v___x_5753_);
v___x_5755_ = v___x_5747_;
goto v_reusejp_5754_;
}
else
{
lean_object* v_reuseFailAlloc_5757_; 
v_reuseFailAlloc_5757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5757_, 0, v___x_5753_);
v___x_5755_ = v_reuseFailAlloc_5757_;
goto v_reusejp_5754_;
}
v_reusejp_5754_:
{
lean_object* v___x_5756_; 
v___x_5756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5756_, 0, v___x_5755_);
return v___x_5756_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Async_raceAll___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_5732_ = stack[0].m_obj;
lean_object* v___f_5733_ = stack[1].m_obj;
lean_object* v_x_5734_ = stack[2].m_obj;
lean_object* v_res_5759_;
v_res_5759_ = l_Std_Async_Async_raceAll___redArg___lam__4(v___f_5732_, v___f_5733_, v_x_5734_);
stack->m_obj
 = v_res_5759_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__4___boxed(lean_object* v___f_5760_, lean_object* v___f_5761_, lean_object* v_x_5762_, lean_object* v___y_5763_){
_start:
{
lean_object* v_res_5764_; 
v_res_5764_ = l_Std_Async_Async_raceAll___redArg___lam__4(v___f_5760_, v___f_5761_, v_x_5762_);
return v_res_5764_;
}
}
lean_object* l_Std_Async_Async_raceAll___redArg___lam__0(lean_object* v_prio_5765_, lean_object* v___f_5766_, lean_object* v___f_5767_, lean_object* v_x_5768_){
_start:
{
lean_object* v___x_5770_; uint8_t v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; uint8_t v___x_5774_; lean_object* v___x_5775_; lean_object* v___x_5776_; lean_object* v___x_5777_; lean_object* v___x_5778_; 
v___x_5770_ = lean_unsigned_to_nat(0u);
v___x_5771_ = 0;
v___x_5772_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5772_, 0, lean_box(0));
lean_closure_set(v___x_5772_, 1, v_x_5768_);
v___x_5773_ = lean_io_as_task(v___x_5772_, v_prio_5765_);
v___x_5774_ = 1;
v___x_5775_ = lean_task_bind(v___x_5773_, v___f_5766_, v___x_5770_, v___x_5774_);
v___x_5776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5776_, 0, v___x_5775_);
v___x_5777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5777_, 0, v___x_5776_);
v___x_5778_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5770_, v___x_5771_, v___x_5777_, v___f_5767_);
return v___x_5778_;
}
}
LEAN_EXPORT void l_Std_Async_Async_raceAll___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_prio_5765_ = stack[0].m_obj;
lean_object* v___f_5766_ = stack[1].m_obj;
lean_object* v___f_5767_ = stack[2].m_obj;
lean_object* v_x_5768_ = stack[3].m_obj;
lean_object* v_res_5779_;
v_res_5779_ = l_Std_Async_Async_raceAll___redArg___lam__0(v_prio_5765_, v___f_5766_, v___f_5767_, v_x_5768_);
stack->m_obj
 = v_res_5779_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__0___boxed(lean_object* v_prio_5780_, lean_object* v___f_5781_, lean_object* v___f_5782_, lean_object* v_x_5783_, lean_object* v___y_5784_){
_start:
{
lean_object* v_res_5785_; 
v_res_5785_ = l_Std_Async_Async_raceAll___redArg___lam__0(v_prio_5780_, v___f_5781_, v___f_5782_, v_x_5783_);
return v_res_5785_;
}
}
lean_object* l_Std_Async_Async_raceAll___redArg___lam__2(lean_object* v___f_5786_, lean_object* v_prio_5787_, lean_object* v___f_5788_, lean_object* v___f_5789_, lean_object* v___f_5790_, lean_object* v_inst_5791_, lean_object* v_xs_5792_, lean_object* v_x_5793_){
_start:
{
if (lean_obj_tag(v_x_5793_) == 0)
{
lean_object* v_a_5795_; lean_object* v___x_5797_; uint8_t v_isShared_5798_; uint8_t v_isSharedCheck_5803_; 
lean_dec(v_xs_5792_);
lean_dec_ref(v_inst_5791_);
lean_dec_ref(v___f_5790_);
lean_dec_ref(v___f_5789_);
lean_dec_ref(v___f_5788_);
lean_dec(v_prio_5787_);
lean_dec(v___f_5786_);
v_a_5795_ = lean_ctor_get(v_x_5793_, 0);
v_isSharedCheck_5803_ = !lean_is_exclusive(v_x_5793_);
if (v_isSharedCheck_5803_ == 0)
{
v___x_5797_ = v_x_5793_;
v_isShared_5798_ = v_isSharedCheck_5803_;
goto v_resetjp_5796_;
}
else
{
lean_inc(v_a_5795_);
lean_dec(v_x_5793_);
v___x_5797_ = lean_box(0);
v_isShared_5798_ = v_isSharedCheck_5803_;
goto v_resetjp_5796_;
}
v_resetjp_5796_:
{
lean_object* v___x_5800_; 
if (v_isShared_5798_ == 0)
{
v___x_5800_ = v___x_5797_;
goto v_reusejp_5799_;
}
else
{
lean_object* v_reuseFailAlloc_5802_; 
v_reuseFailAlloc_5802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5802_, 0, v_a_5795_);
v___x_5800_ = v_reuseFailAlloc_5802_;
goto v_reusejp_5799_;
}
v_reusejp_5799_:
{
lean_object* v___x_5801_; 
v___x_5801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5801_, 0, v___x_5800_);
return v___x_5801_;
}
}
}
else
{
lean_object* v_a_5804_; lean_object* v___f_5805_; lean_object* v___f_5806_; lean_object* v___f_5807_; lean_object* v___f_5808_; lean_object* v___x_5809_; uint8_t v___x_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; 
v_a_5804_ = lean_ctor_get(v_x_5793_, 0);
lean_inc_n(v_a_5804_, 2);
lean_dec_ref_known(v_x_5793_, 1);
v___f_5805_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_5805_, 0, v_a_5804_);
v___f_5806_ = lean_alloc_closure((void*)(l_Std_Async_Async_raceAll___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_5806_, 0, v___f_5786_);
lean_closure_set(v___f_5806_, 1, v___f_5805_);
v___f_5807_ = lean_alloc_closure((void*)(l_Std_Async_Async_raceAll___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_5807_, 0, v_prio_5787_);
lean_closure_set(v___f_5807_, 1, v___f_5788_);
lean_closure_set(v___f_5807_, 2, v___f_5806_);
v___f_5808_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_5808_, 0, v_a_5804_);
lean_closure_set(v___f_5808_, 1, v___f_5789_);
lean_closure_set(v___f_5808_, 2, v___f_5790_);
v___x_5809_ = lean_unsigned_to_nat(0u);
v___x_5810_ = 0;
v___x_5811_ = lean_apply_3(v_inst_5791_, v_xs_5792_, v___f_5807_, lean_box(0));
v___x_5812_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5809_, v___x_5810_, v___x_5811_, v___f_5808_);
return v___x_5812_;
}
}
}
LEAN_EXPORT void l_Std_Async_Async_raceAll___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_5786_ = stack[0].m_obj;
lean_object* v_prio_5787_ = stack[1].m_obj;
lean_object* v___f_5788_ = stack[2].m_obj;
lean_object* v___f_5789_ = stack[3].m_obj;
lean_object* v___f_5790_ = stack[4].m_obj;
lean_object* v_inst_5791_ = stack[5].m_obj;
lean_object* v_xs_5792_ = stack[6].m_obj;
lean_object* v_x_5793_ = stack[7].m_obj;
lean_object* v_res_5813_;
v_res_5813_ = l_Std_Async_Async_raceAll___redArg___lam__2(v___f_5786_, v_prio_5787_, v___f_5788_, v___f_5789_, v___f_5790_, v_inst_5791_, v_xs_5792_, v_x_5793_);
stack->m_obj
 = v_res_5813_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__2___boxed(lean_object* v___f_5814_, lean_object* v_prio_5815_, lean_object* v___f_5816_, lean_object* v___f_5817_, lean_object* v___f_5818_, lean_object* v_inst_5819_, lean_object* v_xs_5820_, lean_object* v_x_5821_, lean_object* v___y_5822_){
_start:
{
lean_object* v_res_5823_; 
v_res_5823_ = l_Std_Async_Async_raceAll___redArg___lam__2(v___f_5814_, v_prio_5815_, v___f_5816_, v___f_5817_, v___f_5818_, v_inst_5819_, v_xs_5820_, v_x_5821_);
return v_res_5823_;
}
}
lean_object* l_Std_Async_Async_raceAll___redArg(lean_object* v_inst_5824_, lean_object* v_xs_5825_, lean_object* v_prio_5826_){
_start:
{
lean_object* v___f_5828_; lean_object* v___f_5829_; lean_object* v___f_5830_; lean_object* v___f_5831_; lean_object* v___f_5832_; lean_object* v___x_5833_; uint8_t v___x_5834_; lean_object* v___x_5835_; lean_object* v___x_5836_; lean_object* v___x_5837_; lean_object* v___x_5838_; 
v___f_5828_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__1));
v___f_5829_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__0));
v___f_5830_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___f_5831_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_5832_ = lean_alloc_closure((void*)(l_Std_Async_Async_raceAll___redArg___lam__2___boxed), 9, 7);
lean_closure_set(v___f_5832_, 0, v___f_5831_);
lean_closure_set(v___f_5832_, 1, v_prio_5826_);
lean_closure_set(v___f_5832_, 2, v___f_5830_);
lean_closure_set(v___f_5832_, 3, v___f_5828_);
lean_closure_set(v___f_5832_, 4, v___f_5829_);
lean_closure_set(v___f_5832_, 5, v_inst_5824_);
lean_closure_set(v___f_5832_, 6, v_xs_5825_);
v___x_5833_ = lean_unsigned_to_nat(0u);
v___x_5834_ = 0;
v___x_5835_ = lean_io_promise_new();
v___x_5836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5836_, 0, v___x_5835_);
v___x_5837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5837_, 0, v___x_5836_);
v___x_5838_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5833_, v___x_5834_, v___x_5837_, v___f_5832_);
return v___x_5838_;
}
}
LEAN_EXPORT void l_Std_Async_Async_raceAll___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_5824_ = stack[0].m_obj;
lean_object* v_xs_5825_ = stack[1].m_obj;
lean_object* v_prio_5826_ = stack[2].m_obj;
lean_object* v_res_5839_;
v_res_5839_ = l_Std_Async_Async_raceAll___redArg(v_inst_5824_, v_xs_5825_, v_prio_5826_);
stack->m_obj
 = v_res_5839_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___boxed(lean_object* v_inst_5840_, lean_object* v_xs_5841_, lean_object* v_prio_5842_, lean_object* v_a_5843_){
_start:
{
lean_object* v_res_5844_; 
v_res_5844_ = l_Std_Async_Async_raceAll___redArg(v_inst_5840_, v_xs_5841_, v_prio_5842_);
return v_res_5844_;
}
}
lean_object* l_Std_Async_Async_raceAll(lean_object* v_c_5845_, lean_object* v_00_u03b1_5846_, lean_object* v_inst_5847_, lean_object* v_xs_5848_, lean_object* v_prio_5849_){
_start:
{
lean_object* v___f_5851_; lean_object* v___f_5852_; lean_object* v___f_5853_; lean_object* v___f_5854_; lean_object* v___f_5855_; lean_object* v___x_5856_; uint8_t v___x_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; lean_object* v___x_5860_; lean_object* v___x_5861_; 
v___f_5851_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__1));
v___f_5852_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__0));
v___f_5853_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___f_5854_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_5855_ = lean_alloc_closure((void*)(l_Std_Async_Async_raceAll___redArg___lam__2___boxed), 9, 7);
lean_closure_set(v___f_5855_, 0, v___f_5854_);
lean_closure_set(v___f_5855_, 1, v_prio_5849_);
lean_closure_set(v___f_5855_, 2, v___f_5853_);
lean_closure_set(v___f_5855_, 3, v___f_5851_);
lean_closure_set(v___f_5855_, 4, v___f_5852_);
lean_closure_set(v___f_5855_, 5, v_inst_5847_);
lean_closure_set(v___f_5855_, 6, v_xs_5848_);
v___x_5856_ = lean_unsigned_to_nat(0u);
v___x_5857_ = 0;
v___x_5858_ = lean_io_promise_new();
v___x_5859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5859_, 0, v___x_5858_);
v___x_5860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5860_, 0, v___x_5859_);
v___x_5861_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5856_, v___x_5857_, v___x_5860_, v___f_5855_);
return v___x_5861_;
}
}
LEAN_EXPORT void l_Std_Async_Async_raceAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_5847_ = stack[2].m_obj;
lean_object* v_xs_5848_ = stack[3].m_obj;
lean_object* v_prio_5849_ = stack[4].m_obj;
lean_object* v_res_5862_;
v_res_5862_ = l_Std_Async_Async_raceAll(lean_box(0), lean_box(0), v_inst_5847_, v_xs_5848_, v_prio_5849_);
stack->m_obj
 = v_res_5862_;
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___boxed(lean_object* v_c_5863_, lean_object* v_00_u03b1_5864_, lean_object* v_inst_5865_, lean_object* v_xs_5866_, lean_object* v_prio_5867_, lean_object* v_a_5868_){
_start:
{
lean_object* v_res_5869_; 
v_res_5869_ = l_Std_Async_Async_raceAll(v_c_5863_, v_00_u03b1_5864_, v_inst_5865_, v_xs_5866_, v_prio_5867_);
return v_res_5869_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_background___redArg(lean_object* v_inst_5870_, lean_object* v_inst_5871_, lean_object* v_action_5872_, lean_object* v_prio_5873_){
_start:
{
lean_object* v_toApplicative_5874_; lean_object* v_toFunctor_5875_; lean_object* v_mapConst_5876_; lean_object* v___x_5877_; lean_object* v___x_5878_; lean_object* v___x_5879_; 
v_toApplicative_5874_ = lean_ctor_get(v_inst_5870_, 0);
lean_inc_ref(v_toApplicative_5874_);
lean_dec_ref(v_inst_5870_);
v_toFunctor_5875_ = lean_ctor_get(v_toApplicative_5874_, 0);
lean_inc_ref(v_toFunctor_5875_);
lean_dec_ref(v_toApplicative_5874_);
v_mapConst_5876_ = lean_ctor_get(v_toFunctor_5875_, 1);
lean_inc(v_mapConst_5876_);
lean_dec_ref(v_toFunctor_5875_);
v___x_5877_ = lean_apply_3(v_inst_5871_, lean_box(0), v_action_5872_, v_prio_5873_);
v___x_5878_ = lean_box(0);
v___x_5879_ = lean_apply_4(v_mapConst_5876_, lean_box(0), lean_box(0), v___x_5878_, v___x_5877_);
return v___x_5879_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_background(lean_object* v_m_5880_, lean_object* v_t_5881_, lean_object* v_00_u03b1_5882_, lean_object* v_inst_5883_, lean_object* v_inst_5884_, lean_object* v_action_5885_, lean_object* v_prio_5886_){
_start:
{
lean_object* v_toApplicative_5887_; lean_object* v_toFunctor_5888_; lean_object* v_mapConst_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; 
v_toApplicative_5887_ = lean_ctor_get(v_inst_5883_, 0);
lean_inc_ref(v_toApplicative_5887_);
lean_dec_ref(v_inst_5883_);
v_toFunctor_5888_ = lean_ctor_get(v_toApplicative_5887_, 0);
lean_inc_ref(v_toFunctor_5888_);
lean_dec_ref(v_toApplicative_5887_);
v_mapConst_5889_ = lean_ctor_get(v_toFunctor_5888_, 1);
lean_inc(v_mapConst_5889_);
lean_dec_ref(v_toFunctor_5888_);
v___x_5890_ = lean_apply_3(v_inst_5884_, lean_box(0), v_action_5885_, v_prio_5886_);
v___x_5891_ = lean_box(0);
v___x_5892_ = lean_apply_4(v_mapConst_5889_, lean_box(0), lean_box(0), v___x_5891_, v___x_5890_);
return v___x_5892_;
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
