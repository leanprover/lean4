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
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorIdx___impl___redArg(lean_object* v_x_952_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = lean_obj_tag_nat(v_x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorIdx___impl___redArg___boxed(lean_object* v_x_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Std_Async_MaybeTask_ctorIdx___impl___redArg(v_x_954_);
lean_dec_ref(v_x_954_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorIdx___impl(lean_object* v_00_u03b1_956_, lean_object* v_x_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = lean_obj_tag_nat(v_x_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorIdx___impl___boxed(lean_object* v_00_u03b1_959_, lean_object* v_x_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Std_Async_MaybeTask_ctorIdx___impl(v_00_u03b1_959_, v_x_960_);
lean_dec_ref(v_x_960_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorElim___redArg(lean_object* v_t_962_, lean_object* v_k_963_){
_start:
{
if (lean_obj_tag(v_t_962_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_965_; 
v_a_964_ = lean_ctor_get(v_t_962_, 0);
lean_inc(v_a_964_);
lean_dec_ref_known(v_t_962_, 1);
v___x_965_ = lean_apply_1(v_k_963_, v_a_964_);
return v___x_965_;
}
else
{
lean_object* v_a_966_; lean_object* v___x_967_; 
v_a_966_ = lean_ctor_get(v_t_962_, 0);
lean_inc_ref(v_a_966_);
lean_dec_ref_known(v_t_962_, 1);
v___x_967_ = lean_apply_1(v_k_963_, v_a_966_);
return v___x_967_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorElim(lean_object* v_00_u03b1_968_, lean_object* v_motive_969_, lean_object* v_ctorIdx_970_, lean_object* v_t_971_, lean_object* v_h_972_, lean_object* v_k_973_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_Std_Async_MaybeTask_ctorElim___redArg(v_t_971_, v_k_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ctorElim___boxed(lean_object* v_00_u03b1_975_, lean_object* v_motive_976_, lean_object* v_ctorIdx_977_, lean_object* v_t_978_, lean_object* v_h_979_, lean_object* v_k_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Std_Async_MaybeTask_ctorElim(v_00_u03b1_975_, v_motive_976_, v_ctorIdx_977_, v_t_978_, v_h_979_, v_k_980_);
lean_dec(v_ctorIdx_977_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_pure_elim___redArg(lean_object* v_t_982_, lean_object* v_pure_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Std_Async_MaybeTask_ctorElim___redArg(v_t_982_, v_pure_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_pure_elim(lean_object* v_00_u03b1_985_, lean_object* v_motive_986_, lean_object* v_t_987_, lean_object* v_h_988_, lean_object* v_pure_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_Std_Async_MaybeTask_ctorElim___redArg(v_t_987_, v_pure_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ofTask_elim___redArg(lean_object* v_t_991_, lean_object* v_ofTask_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Std_Async_MaybeTask_ctorElim___redArg(v_t_991_, v_ofTask_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_ofTask_elim(lean_object* v_00_u03b1_994_, lean_object* v_motive_995_, lean_object* v_t_996_, lean_object* v_h_997_, lean_object* v_ofTask_998_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l_Std_Async_MaybeTask_ctorElim___redArg(v_t_996_, v_ofTask_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_toTask___redArg(lean_object* v_x_1000_){
_start:
{
if (lean_obj_tag(v_x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; 
v_a_1001_ = lean_ctor_get(v_x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v_x_1000_, 1);
v___x_1002_ = lean_task_pure(v_a_1001_);
return v___x_1002_;
}
else
{
lean_object* v_a_1003_; 
v_a_1003_ = lean_ctor_get(v_x_1000_, 0);
lean_inc_ref(v_a_1003_);
lean_dec_ref_known(v_x_1000_, 1);
return v_a_1003_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_toTask(lean_object* v_00_u03b1_1004_, lean_object* v_x_1005_){
_start:
{
if (lean_obj_tag(v_x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1007_; 
v_a_1006_ = lean_ctor_get(v_x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v_x_1005_, 1);
v___x_1007_ = lean_task_pure(v_a_1006_);
return v___x_1007_;
}
else
{
lean_object* v_a_1008_; 
v_a_1008_ = lean_ctor_get(v_x_1005_, 0);
lean_inc_ref(v_a_1008_);
lean_dec_ref_known(v_x_1005_, 1);
return v_a_1008_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_get___redArg(lean_object* v_x_1009_){
_start:
{
if (lean_obj_tag(v_x_1009_) == 0)
{
lean_object* v_a_1010_; 
v_a_1010_ = lean_ctor_get(v_x_1009_, 0);
lean_inc(v_a_1010_);
lean_dec_ref_known(v_x_1009_, 1);
return v_a_1010_;
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1012_; 
v_a_1011_ = lean_ctor_get(v_x_1009_, 0);
lean_inc_ref(v_a_1011_);
lean_dec_ref_known(v_x_1009_, 1);
v___x_1012_ = lean_task_get_own(v_a_1011_);
return v___x_1012_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_get(lean_object* v_00_u03b1_1013_, lean_object* v_x_1014_){
_start:
{
if (lean_obj_tag(v_x_1014_) == 0)
{
lean_object* v_a_1015_; 
v_a_1015_ = lean_ctor_get(v_x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref_known(v_x_1014_, 1);
return v_a_1015_;
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1017_; 
v_a_1016_ = lean_ctor_get(v_x_1014_, 0);
lean_inc_ref(v_a_1016_);
lean_dec_ref_known(v_x_1014_, 1);
v___x_1017_ = lean_task_get_own(v_a_1016_);
return v___x_1017_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_map___redArg(lean_object* v_f_1018_, lean_object* v_prio_1019_, uint8_t v_sync_1020_, lean_object* v_x_1021_){
_start:
{
if (lean_obj_tag(v_x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1030_; 
lean_dec(v_prio_1019_);
v_a_1022_ = lean_ctor_get(v_x_1021_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_x_1021_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1024_ = v_x_1021_;
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v_x_1021_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1026_ = lean_apply_1(v_f_1018_, v_a_1022_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v___x_1026_);
v___x_1028_ = v___x_1024_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1039_; 
v_a_1031_ = lean_ctor_get(v_x_1021_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_x_1021_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1033_ = v_x_1021_;
v_isShared_1034_ = v_isSharedCheck_1039_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v_x_1021_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1039_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1035_ = lean_task_map(v_f_1018_, v_a_1031_, v_prio_1019_, v_sync_1020_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1035_);
v___x_1037_ = v___x_1033_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_map___redArg___boxed(lean_object* v_f_1040_, lean_object* v_prio_1041_, lean_object* v_sync_1042_, lean_object* v_x_1043_){
_start:
{
uint8_t v_sync_boxed_1044_; lean_object* v_res_1045_; 
v_sync_boxed_1044_ = lean_unbox(v_sync_1042_);
v_res_1045_ = l_Std_Async_MaybeTask_map___redArg(v_f_1040_, v_prio_1041_, v_sync_boxed_1044_, v_x_1043_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_map(lean_object* v_00_u03b1_1046_, lean_object* v_00_u03b2_1047_, lean_object* v_f_1048_, lean_object* v_prio_1049_, uint8_t v_sync_1050_, lean_object* v_x_1051_){
_start:
{
if (lean_obj_tag(v_x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1060_; 
lean_dec(v_prio_1049_);
v_a_1052_ = lean_ctor_get(v_x_1051_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_x_1051_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1054_ = v_x_1051_;
v_isShared_1055_ = v_isSharedCheck_1060_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v_x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1060_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1058_; 
v___x_1056_ = lean_apply_1(v_f_1048_, v_a_1052_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v___x_1056_);
v___x_1058_ = v___x_1054_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1056_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1069_; 
v_a_1061_ = lean_ctor_get(v_x_1051_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_x_1051_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1063_ = v_x_1051_;
v_isShared_1064_ = v_isSharedCheck_1069_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v_x_1051_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1069_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1065_ = lean_task_map(v_f_1048_, v_a_1061_, v_prio_1049_, v_sync_1050_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1065_);
v___x_1067_ = v___x_1063_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_map___boxed(lean_object* v_00_u03b1_1070_, lean_object* v_00_u03b2_1071_, lean_object* v_f_1072_, lean_object* v_prio_1073_, lean_object* v_sync_1074_, lean_object* v_x_1075_){
_start:
{
uint8_t v_sync_boxed_1076_; lean_object* v_res_1077_; 
v_sync_boxed_1076_ = lean_unbox(v_sync_1074_);
v_res_1077_ = l_Std_Async_MaybeTask_map(v_00_u03b1_1070_, v_00_u03b2_1071_, v_f_1072_, v_prio_1073_, v_sync_boxed_1076_, v_x_1075_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_bind___redArg___lam__0(lean_object* v_f_1078_, lean_object* v_x_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_apply_1(v_f_1078_, v_x_1079_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1082_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
lean_dec_ref_known(v___x_1080_, 1);
v___x_1082_ = lean_task_pure(v_a_1081_);
return v___x_1082_;
}
else
{
lean_object* v_a_1083_; 
v_a_1083_ = lean_ctor_get(v___x_1080_, 0);
lean_inc_ref(v_a_1083_);
lean_dec_ref_known(v___x_1080_, 1);
return v_a_1083_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_bind___redArg(lean_object* v_t_1084_, lean_object* v_f_1085_, lean_object* v_prio_1086_, uint8_t v_sync_1087_){
_start:
{
if (lean_obj_tag(v_t_1084_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1089_; 
lean_dec(v_prio_1086_);
v_a_1088_ = lean_ctor_get(v_t_1084_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v_t_1084_, 1);
v___x_1089_ = lean_apply_1(v_f_1085_, v_a_1088_);
return v___x_1089_;
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1099_; 
v_a_1090_ = lean_ctor_get(v_t_1084_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_t_1084_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1092_ = v_t_1084_;
v_isShared_1093_ = v_isSharedCheck_1099_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v_t_1084_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1099_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___f_1094_; lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___f_1094_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1094_, 0, v_f_1085_);
v___x_1095_ = lean_task_bind(v_a_1090_, v___f_1094_, v_prio_1086_, v_sync_1087_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1095_);
v___x_1097_ = v___x_1092_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_bind___redArg___boxed(lean_object* v_t_1100_, lean_object* v_f_1101_, lean_object* v_prio_1102_, lean_object* v_sync_1103_){
_start:
{
uint8_t v_sync_boxed_1104_; lean_object* v_res_1105_; 
v_sync_boxed_1104_ = lean_unbox(v_sync_1103_);
v_res_1105_ = l_Std_Async_MaybeTask_bind___redArg(v_t_1100_, v_f_1101_, v_prio_1102_, v_sync_boxed_1104_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_bind(lean_object* v_00_u03b1_1106_, lean_object* v_00_u03b2_1107_, lean_object* v_t_1108_, lean_object* v_f_1109_, lean_object* v_prio_1110_, uint8_t v_sync_1111_){
_start:
{
if (lean_obj_tag(v_t_1108_) == 0)
{
lean_object* v_a_1112_; lean_object* v___x_1113_; 
lean_dec(v_prio_1110_);
v_a_1112_ = lean_ctor_get(v_t_1108_, 0);
lean_inc(v_a_1112_);
lean_dec_ref_known(v_t_1108_, 1);
v___x_1113_ = lean_apply_1(v_f_1109_, v_a_1112_);
return v___x_1113_;
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1123_; 
v_a_1114_ = lean_ctor_get(v_t_1108_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_t_1108_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1116_ = v_t_1108_;
v_isShared_1117_ = v_isSharedCheck_1123_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v_t_1108_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1123_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___f_1118_; lean_object* v___x_1119_; lean_object* v___x_1121_; 
v___f_1118_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1118_, 0, v_f_1109_);
v___x_1119_ = lean_task_bind(v_a_1114_, v___f_1118_, v_prio_1110_, v_sync_1111_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 0, v___x_1119_);
v___x_1121_ = v___x_1116_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_bind___boxed(lean_object* v_00_u03b1_1124_, lean_object* v_00_u03b2_1125_, lean_object* v_t_1126_, lean_object* v_f_1127_, lean_object* v_prio_1128_, lean_object* v_sync_1129_){
_start:
{
uint8_t v_sync_boxed_1130_; lean_object* v_res_1131_; 
v_sync_boxed_1130_ = lean_unbox(v_sync_1129_);
v_res_1131_ = l_Std_Async_MaybeTask_bind(v_00_u03b1_1124_, v_00_u03b2_1125_, v_t_1126_, v_f_1127_, v_prio_1128_, v_sync_boxed_1130_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_joinTask___redArg___lam__0(lean_object* v_x_1132_){
_start:
{
if (lean_obj_tag(v_x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1134_; 
v_a_1133_ = lean_ctor_get(v_x_1132_, 0);
lean_inc(v_a_1133_);
lean_dec_ref_known(v_x_1132_, 1);
v___x_1134_ = lean_task_pure(v_a_1133_);
return v___x_1134_;
}
else
{
lean_object* v_a_1135_; 
v_a_1135_ = lean_ctor_get(v_x_1132_, 0);
lean_inc_ref(v_a_1135_);
lean_dec_ref_known(v_x_1132_, 1);
return v_a_1135_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_joinTask___redArg(lean_object* v_t_1137_){
_start:
{
lean_object* v___f_1138_; lean_object* v___x_1139_; uint8_t v___x_1140_; lean_object* v___x_1141_; 
v___f_1138_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___x_1139_ = lean_unsigned_to_nat(0u);
v___x_1140_ = 1;
v___x_1141_ = lean_task_bind(v_t_1137_, v___f_1138_, v___x_1139_, v___x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_joinTask(lean_object* v_00_u03b1_1142_, lean_object* v_t_1143_){
_start:
{
lean_object* v___f_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; lean_object* v___x_1147_; 
v___f_1144_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___x_1145_ = lean_unsigned_to_nat(0u);
v___x_1146_ = 1;
v___x_1147_ = lean_task_bind(v_t_1143_, v___f_1144_, v___x_1145_, v___x_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instFunctor___lam__0(lean_object* v_00_u03b1_1148_, lean_object* v_00_u03b2_1149_, lean_object* v_f_1150_, lean_object* v___y_1151_){
_start:
{
if (lean_obj_tag(v___y_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1160_; 
v_a_1152_ = lean_ctor_get(v___y_1151_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___y_1151_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1154_ = v___y_1151_;
v_isShared_1155_ = v_isSharedCheck_1160_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___y_1151_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1160_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1156_ = lean_apply_1(v_f_1150_, v_a_1152_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v___x_1156_);
v___x_1158_ = v___x_1154_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
else
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1171_; 
v_a_1161_ = lean_ctor_get(v___y_1151_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___y_1151_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1163_ = v___y_1151_;
v_isShared_1164_ = v_isSharedCheck_1171_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___y_1151_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1171_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; uint8_t v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1165_ = lean_unsigned_to_nat(0u);
v___x_1166_ = 0;
v___x_1167_ = lean_task_map(v_f_1150_, v_a_1161_, v___x_1165_, v___x_1166_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 0, v___x_1167_);
v___x_1169_ = v___x_1163_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instFunctor___lam__1(lean_object* v___f_1172_, lean_object* v_00_u03b1_1173_, lean_object* v_00_u03b2_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_1177_, 0, lean_box(0));
lean_closure_set(v___x_1177_, 1, lean_box(0));
lean_closure_set(v___x_1177_, 2, v___y_1175_);
v___x_1178_ = lean_apply_4(v___f_1172_, lean_box(0), lean_box(0), v___x_1177_, v___y_1176_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__0(lean_object* v_00_u03b1_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1188_, 0, v___y_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__1(lean_object* v_x_1189_, lean_object* v_y_1190_){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_box(0);
v___x_1192_ = lean_apply_1(v_x_1189_, v___x_1191_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1201_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1201_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1201_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1197_ = lean_apply_1(v_y_1190_, v_a_1193_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1197_);
v___x_1199_ = v___x_1195_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1212_; 
v_a_1202_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1204_ = v___x_1192_;
v_isShared_1205_ = v_isSharedCheck_1212_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1192_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1212_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; uint8_t v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1210_; 
v___x_1206_ = lean_unsigned_to_nat(0u);
v___x_1207_ = 0;
v___x_1208_ = lean_task_map(v_y_1190_, v_a_1202_, v___x_1206_, v___x_1207_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v___x_1208_);
v___x_1210_ = v___x_1204_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__2(lean_object* v___f_1213_, lean_object* v_x_1214_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_apply_1(v___f_1213_, v_x_1214_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1217_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref_known(v___x_1215_, 1);
v___x_1217_ = lean_task_pure(v_a_1216_);
return v___x_1217_;
}
else
{
lean_object* v_a_1218_; 
v_a_1218_ = lean_ctor_get(v___x_1215_, 0);
lean_inc_ref(v_a_1218_);
lean_dec_ref_known(v___x_1215_, 1);
return v_a_1218_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__3(lean_object* v_00_u03b1_1219_, lean_object* v_00_u03b2_1220_, lean_object* v_f_1221_, lean_object* v_x_1222_){
_start:
{
lean_object* v___f_1223_; 
lean_inc_ref(v_x_1222_);
v___f_1223_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_instMonad___lam__1), 2, 1);
lean_closure_set(v___f_1223_, 0, v_x_1222_);
if (lean_obj_tag(v_f_1221_) == 0)
{
lean_object* v_a_1224_; lean_object* v___x_1225_; 
lean_dec_ref(v___f_1223_);
v_a_1224_ = lean_ctor_get(v_f_1221_, 0);
lean_inc(v_a_1224_);
lean_dec_ref_known(v_f_1221_, 1);
v___x_1225_ = l_Std_Async_MaybeTask_instMonad___lam__1(v_x_1222_, v_a_1224_);
return v___x_1225_;
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1237_; 
lean_dec_ref(v_x_1222_);
v_a_1226_ = lean_ctor_get(v_f_1221_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_f_1221_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1228_ = v_f_1221_;
v_isShared_1229_ = v_isSharedCheck_1237_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v_f_1221_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1237_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___f_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___f_1230_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_instMonad___lam__2), 2, 1);
lean_closure_set(v___f_1230_, 0, v___f_1223_);
v___x_1231_ = lean_unsigned_to_nat(0u);
v___x_1232_ = 0;
v___x_1233_ = lean_task_bind(v_a_1226_, v___f_1230_, v___x_1231_, v___x_1232_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v___x_1233_);
v___x_1235_ = v___x_1228_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__5(lean_object* v_00_u03b1_1238_, lean_object* v_00_u03b2_1239_, lean_object* v_t_1240_, lean_object* v_f_1241_){
_start:
{
if (lean_obj_tag(v_t_1240_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1243_; 
v_a_1242_ = lean_ctor_get(v_t_1240_, 0);
lean_inc(v_a_1242_);
lean_dec_ref_known(v_t_1240_, 1);
v___x_1243_ = lean_apply_1(v_f_1241_, v_a_1242_);
return v___x_1243_;
}
else
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1255_; 
v_a_1244_ = lean_ctor_get(v_t_1240_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v_t_1240_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1246_ = v_t_1240_;
v_isShared_1247_ = v_isSharedCheck_1255_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v_t_1240_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1255_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___f_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___f_1248_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_bind___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1248_, 0, v_f_1241_);
v___x_1249_ = lean_unsigned_to_nat(0u);
v___x_1250_ = 0;
v___x_1251_ = lean_task_bind(v_a_1244_, v___f_1248_, v___x_1249_, v___x_1250_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1251_);
v___x_1253_ = v___x_1246_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__4(lean_object* v_a_1256_, lean_object* v_x_1257_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1258_, 0, v_a_1256_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__4___boxed(lean_object* v_a_1259_, lean_object* v_x_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Std_Async_MaybeTask_instMonad___lam__4(v_a_1259_, v_x_1260_);
lean_dec(v_x_1260_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__6(lean_object* v_y_1262_, lean_object* v___f_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v___f_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___f_1265_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_instMonad___lam__4___boxed), 2, 1);
lean_closure_set(v___f_1265_, 0, v_a_1264_);
v___x_1266_ = lean_box(0);
v___x_1267_ = lean_apply_1(v_y_1262_, v___x_1266_);
v___x_1268_ = lean_apply_4(v___f_1263_, lean_box(0), lean_box(0), v___x_1267_, v___f_1265_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__7(lean_object* v___f_1269_, lean_object* v_00_u03b1_1270_, lean_object* v_00_u03b2_1271_, lean_object* v_x_1272_, lean_object* v_y_1273_){
_start:
{
lean_object* v___f_1274_; lean_object* v___x_1275_; 
lean_inc_ref(v___f_1269_);
v___f_1274_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_instMonad___lam__6), 3, 2);
lean_closure_set(v___f_1274_, 0, v_y_1273_);
lean_closure_set(v___f_1274_, 1, v___f_1269_);
v___x_1275_ = lean_apply_4(v___f_1269_, lean_box(0), lean_box(0), v_x_1272_, v___f_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__8(lean_object* v_y_1276_, lean_object* v_x_1277_){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = lean_box(0);
v___x_1279_ = lean_apply_1(v_y_1276_, v___x_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__8___boxed(lean_object* v_y_1280_, lean_object* v_x_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Std_Async_MaybeTask_instMonad___lam__8(v_y_1280_, v_x_1281_);
lean_dec(v_x_1281_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__9(lean_object* v___f_1283_, lean_object* v_x_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = lean_apply_1(v___f_1283_, v_x_1284_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1287_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1286_);
lean_dec_ref_known(v___x_1285_, 1);
v___x_1287_ = lean_task_pure(v_a_1286_);
return v___x_1287_;
}
else
{
lean_object* v_a_1288_; 
v_a_1288_ = lean_ctor_get(v___x_1285_, 0);
lean_inc_ref(v_a_1288_);
lean_dec_ref_known(v___x_1285_, 1);
return v_a_1288_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_MaybeTask_instMonad___lam__10(lean_object* v_00_u03b1_1289_, lean_object* v_00_u03b2_1290_, lean_object* v_x_1291_, lean_object* v_y_1292_){
_start:
{
lean_object* v___f_1293_; 
lean_inc_ref(v_y_1292_);
v___f_1293_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_instMonad___lam__8___boxed), 2, 1);
lean_closure_set(v___f_1293_, 0, v_y_1292_);
if (lean_obj_tag(v_x_1291_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1295_; 
lean_dec_ref(v___f_1293_);
v_a_1294_ = lean_ctor_get(v_x_1291_, 0);
lean_inc(v_a_1294_);
lean_dec_ref_known(v_x_1291_, 1);
v___x_1295_ = l_Std_Async_MaybeTask_instMonad___lam__8(v_y_1292_, v_a_1294_);
lean_dec(v_a_1294_);
return v___x_1295_;
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1307_; 
lean_dec_ref(v_y_1292_);
v_a_1296_ = lean_ctor_get(v_x_1291_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v_x_1291_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1298_ = v_x_1291_;
v_isShared_1299_ = v_isSharedCheck_1307_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v_x_1291_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1307_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___f_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___f_1300_ = lean_alloc_closure((void*)(l_Std_Async_MaybeTask_instMonad___lam__9), 2, 1);
lean_closure_set(v___f_1300_, 0, v___f_1293_);
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1302_ = 0;
v___x_1303_ = lean_task_bind(v_a_1296_, v___f_1300_, v___x_1301_, v___x_1302_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 0, v___x_1303_);
v___x_1305_ = v___x_1298_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_mk___redArg(lean_object* v_x_1324_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = lean_apply_1(v_x_1324_, lean_box(0));
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_mk___redArg___boxed(lean_object* v_x_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Std_Async_BaseAsync_mk___redArg(v_x_1327_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_mk(lean_object* v_00_u03b1_1330_, lean_object* v_x_1331_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = lean_apply_1(v_x_1331_, lean_box(0));
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_mk___boxed(lean_object* v_00_u03b1_1334_, lean_object* v_x_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Std_Async_BaseAsync_mk(v_00_u03b1_1334_, v_x_1335_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toRawBaseIO___redArg(lean_object* v_x_1338_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = lean_apply_1(v_x_1338_, lean_box(0));
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toRawBaseIO___redArg___boxed(lean_object* v_x_1341_, lean_object* v_a_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Std_Async_BaseAsync_toRawBaseIO___redArg(v_x_1341_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toRawBaseIO(lean_object* v_00_u03b1_1344_, lean_object* v_x_1345_){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = lean_apply_1(v_x_1345_, lean_box(0));
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toRawBaseIO___boxed(lean_object* v_00_u03b1_1348_, lean_object* v_x_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Std_Async_BaseAsync_toRawBaseIO(v_00_u03b1_1348_, v_x_1349_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toBaseIO___redArg(lean_object* v_x_1352_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = lean_apply_1(v_x_1352_, lean_box(0));
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v___x_1356_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
lean_dec_ref_known(v___x_1354_, 1);
v___x_1356_ = lean_task_pure(v_a_1355_);
return v___x_1356_;
}
else
{
lean_object* v_a_1357_; 
v_a_1357_ = lean_ctor_get(v___x_1354_, 0);
lean_inc_ref(v_a_1357_);
lean_dec_ref_known(v___x_1354_, 1);
return v_a_1357_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toBaseIO___redArg___boxed(lean_object* v_x_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Std_Async_BaseAsync_toBaseIO___redArg(v_x_1358_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toBaseIO(lean_object* v_00_u03b1_1361_, lean_object* v_x_1362_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_apply_1(v_x_1362_, lean_box(0));
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1366_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref_known(v___x_1364_, 1);
v___x_1366_ = lean_task_pure(v_a_1365_);
return v___x_1366_;
}
else
{
lean_object* v_a_1367_; 
v_a_1367_ = lean_ctor_get(v___x_1364_, 0);
lean_inc_ref(v_a_1367_);
lean_dec_ref_known(v___x_1364_, 1);
return v_a_1367_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_toBaseIO___boxed(lean_object* v_00_u03b1_1368_, lean_object* v_x_1369_, lean_object* v_a_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Std_Async_BaseAsync_toBaseIO(v_00_u03b1_1368_, v_x_1369_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofTask___redArg(lean_object* v_x_1372_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1374_, 0, v_x_1372_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofTask___redArg___boxed(lean_object* v_x_1375_, lean_object* v_a_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Std_Async_BaseAsync_ofTask___redArg(v_x_1375_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofTask(lean_object* v_00_u03b1_1378_, lean_object* v_x_1379_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1381_, 0, v_x_1379_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofTask___boxed(lean_object* v_00_u03b1_1382_, lean_object* v_x_1383_, lean_object* v_a_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Std_Async_BaseAsync_ofTask(v_00_u03b1_1382_, v_x_1383_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_pure___redArg(lean_object* v_a_1386_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1388_, 0, v_a_1386_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_pure___redArg___boxed(lean_object* v_a_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Std_Async_BaseAsync_pure___redArg(v_a_1389_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_pure(lean_object* v_00_u03b1_1392_, lean_object* v_a_1393_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1395_, 0, v_a_1393_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_pure___boxed(lean_object* v_00_u03b1_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Std_Async_BaseAsync_pure(v_00_u03b1_1396_, v_a_1397_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_map___redArg(lean_object* v_f_1400_, lean_object* v_self_1401_, lean_object* v_prio_1402_, uint8_t v_sync_1403_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = lean_apply_1(v_self_1401_, lean_box(0));
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1414_; 
lean_dec(v_prio_1402_);
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1414_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1414_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1410_ = lean_apply_1(v_f_1400_, v_a_1406_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1410_);
v___x_1412_ = v___x_1408_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1423_; 
v_a_1415_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1417_ = v___x_1405_;
v_isShared_1418_ = v_isSharedCheck_1423_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1405_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1423_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1419_ = lean_task_map(v_f_1400_, v_a_1415_, v_prio_1402_, v_sync_1403_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1419_);
v___x_1421_ = v___x_1417_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_map___redArg___boxed(lean_object* v_f_1424_, lean_object* v_self_1425_, lean_object* v_prio_1426_, lean_object* v_sync_1427_, lean_object* v_a_1428_){
_start:
{
uint8_t v_sync_boxed_1429_; lean_object* v_res_1430_; 
v_sync_boxed_1429_ = lean_unbox(v_sync_1427_);
v_res_1430_ = l_Std_Async_BaseAsync_map___redArg(v_f_1424_, v_self_1425_, v_prio_1426_, v_sync_boxed_1429_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_map(lean_object* v_00_u03b1_1431_, lean_object* v_00_u03b2_1432_, lean_object* v_f_1433_, lean_object* v_self_1434_, lean_object* v_prio_1435_, uint8_t v_sync_1436_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = lean_apply_1(v_self_1434_, lean_box(0));
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1447_; 
lean_dec(v_prio_1435_);
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1441_ = v___x_1438_;
v_isShared_1442_ = v_isSharedCheck_1447_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1438_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1447_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1443_; lean_object* v___x_1445_; 
v___x_1443_ = lean_apply_1(v_f_1433_, v_a_1439_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v___x_1443_);
v___x_1445_ = v___x_1441_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1443_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1456_; 
v_a_1448_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1450_ = v___x_1438_;
v_isShared_1451_ = v_isSharedCheck_1456_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1438_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1456_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; lean_object* v___x_1454_; 
v___x_1452_ = lean_task_map(v_f_1433_, v_a_1448_, v_prio_1435_, v_sync_1436_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1452_);
v___x_1454_ = v___x_1450_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1452_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_map___boxed(lean_object* v_00_u03b1_1457_, lean_object* v_00_u03b2_1458_, lean_object* v_f_1459_, lean_object* v_self_1460_, lean_object* v_prio_1461_, lean_object* v_sync_1462_, lean_object* v_a_1463_){
_start:
{
uint8_t v_sync_boxed_1464_; lean_object* v_res_1465_; 
v_sync_boxed_1464_ = lean_unbox(v_sync_1462_);
v_res_1465_ = l_Std_Async_BaseAsync_map(v_00_u03b1_1457_, v_00_u03b2_1458_, v_f_1459_, v_self_1460_, v_prio_1461_, v_sync_boxed_1464_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___lam__0(lean_object* v_f_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v___x_1469_; 
v___x_1469_ = lean_apply_2(v_f_1466_, v_a_1467_, lean_box(0));
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1471_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_a_1470_);
lean_dec_ref_known(v___x_1469_, 1);
v___x_1471_ = lean_task_pure(v_a_1470_);
return v___x_1471_;
}
else
{
lean_object* v_a_1472_; 
v_a_1472_ = lean_ctor_get(v___x_1469_, 0);
lean_inc_ref(v_a_1472_);
lean_dec_ref_known(v___x_1469_, 1);
return v_a_1472_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___lam__0___boxed(lean_object* v_f_1473_, lean_object* v_a_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___lam__0(v_f_1473_, v_a_1474_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(lean_object* v_prio_1477_, uint8_t v_sync_1478_, lean_object* v_t_1479_, lean_object* v_f_1480_){
_start:
{
if (lean_obj_tag(v_t_1479_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1483_; 
lean_dec(v_prio_1477_);
v_a_1482_ = lean_ctor_get(v_t_1479_, 0);
lean_inc(v_a_1482_);
lean_dec_ref_known(v_t_1479_, 1);
v___x_1483_ = lean_apply_2(v_f_1480_, v_a_1482_, lean_box(0));
return v___x_1483_;
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1493_; 
v_a_1484_ = lean_ctor_get(v_t_1479_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_t_1479_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1486_ = v_t_1479_;
v_isShared_1487_ = v_isSharedCheck_1493_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v_t_1479_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1493_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___f_1488_; lean_object* v___x_1489_; lean_object* v___x_1491_; 
v___f_1488_ = lean_alloc_closure((void*)(l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1488_, 0, v_f_1480_);
v___x_1489_ = lean_io_bind_task(v_a_1484_, v___f_1488_, v_prio_1477_, v_sync_1478_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v___x_1489_);
v___x_1491_ = v___x_1486_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1489_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___boxed(lean_object* v_prio_1494_, lean_object* v_sync_1495_, lean_object* v_t_1496_, lean_object* v_f_1497_, lean_object* v_a_1498_){
_start:
{
uint8_t v_sync_boxed_1499_; lean_object* v_res_1500_; 
v_sync_boxed_1499_ = lean_unbox(v_sync_1495_);
v_res_1500_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_1494_, v_sync_boxed_1499_, v_t_1496_, v_f_1497_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object* v_00_u03b1_1501_, lean_object* v_00_u03b2_1502_, lean_object* v_prio_1503_, uint8_t v_sync_1504_, lean_object* v_t_1505_, lean_object* v_f_1506_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_1503_, v_sync_1504_, v_t_1505_, v_f_1506_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___boxed(lean_object* v_00_u03b1_1509_, lean_object* v_00_u03b2_1510_, lean_object* v_prio_1511_, lean_object* v_sync_1512_, lean_object* v_t_1513_, lean_object* v_f_1514_, lean_object* v_a_1515_){
_start:
{
uint8_t v_sync_boxed_1516_; lean_object* v_res_1517_; 
v_sync_boxed_1516_ = lean_unbox(v_sync_1512_);
v_res_1517_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(v_00_u03b1_1509_, v_00_u03b2_1510_, v_prio_1511_, v_sync_boxed_1516_, v_t_1513_, v_f_1514_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_bind___redArg(lean_object* v_self_1518_, lean_object* v_f_1519_, lean_object* v_prio_1520_, uint8_t v_sync_1521_){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = lean_apply_1(v_self_1518_, lean_box(0));
v___x_1524_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_1520_, v_sync_1521_, v___x_1523_, v_f_1519_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_bind___redArg___boxed(lean_object* v_self_1525_, lean_object* v_f_1526_, lean_object* v_prio_1527_, lean_object* v_sync_1528_, lean_object* v_a_1529_){
_start:
{
uint8_t v_sync_boxed_1530_; lean_object* v_res_1531_; 
v_sync_boxed_1530_ = lean_unbox(v_sync_1528_);
v_res_1531_ = l_Std_Async_BaseAsync_bind___redArg(v_self_1525_, v_f_1526_, v_prio_1527_, v_sync_boxed_1530_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_bind(lean_object* v_00_u03b1_1532_, lean_object* v_00_u03b2_1533_, lean_object* v_self_1534_, lean_object* v_f_1535_, lean_object* v_prio_1536_, uint8_t v_sync_1537_){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = lean_apply_1(v_self_1534_, lean_box(0));
v___x_1540_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_1536_, v_sync_1537_, v___x_1539_, v_f_1535_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_bind___boxed(lean_object* v_00_u03b1_1541_, lean_object* v_00_u03b2_1542_, lean_object* v_self_1543_, lean_object* v_f_1544_, lean_object* v_prio_1545_, lean_object* v_sync_1546_, lean_object* v_a_1547_){
_start:
{
uint8_t v_sync_boxed_1548_; lean_object* v_res_1549_; 
v_sync_boxed_1548_ = lean_unbox(v_sync_1546_);
v_res_1549_ = l_Std_Async_BaseAsync_bind(v_00_u03b1_1541_, v_00_u03b2_1542_, v_self_1543_, v_f_1544_, v_prio_1545_, v_sync_boxed_1548_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_lift___redArg(lean_object* v_x_1550_){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = lean_apply_1(v_x_1550_, lean_box(0));
v___x_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_lift___redArg___boxed(lean_object* v_x_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Std_Async_BaseAsync_lift___redArg(v_x_1554_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_lift(lean_object* v_00_u03b1_1557_, lean_object* v_x_1558_){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = lean_apply_1(v_x_1558_, lean_box(0));
v___x_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_lift___boxed(lean_object* v_00_u03b1_1562_, lean_object* v_x_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Std_Async_BaseAsync_lift(v_00_u03b1_1562_, v_x_1563_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_wait___redArg(lean_object* v_self_1566_){
_start:
{
lean_object* v_val_1569_; lean_object* v___x_1571_; 
v___x_1571_ = lean_apply_1(v_self_1566_, lean_box(0));
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v___x_1573_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1572_);
lean_dec_ref_known(v___x_1571_, 1);
v___x_1573_ = lean_task_pure(v_a_1572_);
v_val_1569_ = v___x_1573_;
goto v___jp_1568_;
}
else
{
lean_object* v_a_1574_; 
v_a_1574_ = lean_ctor_get(v___x_1571_, 0);
lean_inc_ref(v_a_1574_);
lean_dec_ref_known(v___x_1571_, 1);
v_val_1569_ = v_a_1574_;
goto v___jp_1568_;
}
v___jp_1568_:
{
lean_object* v___x_1570_; 
v___x_1570_ = lean_task_get_own(v_val_1569_);
return v___x_1570_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_wait___redArg___boxed(lean_object* v_self_1575_, lean_object* v_a_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l_Std_Async_BaseAsync_wait___redArg(v_self_1575_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_wait(lean_object* v_00_u03b1_1578_, lean_object* v_self_1579_){
_start:
{
lean_object* v_val_1582_; lean_object* v___x_1584_; 
v___x_1584_ = lean_apply_1(v_self_1579_, lean_box(0));
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1586_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
v___x_1586_ = lean_task_pure(v_a_1585_);
v_val_1582_ = v___x_1586_;
goto v___jp_1581_;
}
else
{
lean_object* v_a_1587_; 
v_a_1587_ = lean_ctor_get(v___x_1584_, 0);
lean_inc_ref(v_a_1587_);
lean_dec_ref_known(v___x_1584_, 1);
v_val_1582_ = v_a_1587_;
goto v___jp_1581_;
}
v___jp_1581_:
{
lean_object* v___x_1583_; 
v___x_1583_ = lean_task_get_own(v_val_1582_);
return v___x_1583_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_wait___boxed(lean_object* v_00_u03b1_1588_, lean_object* v_self_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Std_Async_BaseAsync_wait(v_00_u03b1_1588_, v_self_1589_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_asTask___redArg(lean_object* v_x_1592_, lean_object* v_prio_1593_){
_start:
{
lean_object* v___f_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; uint8_t v___x_1599_; lean_object* v___x_1600_; 
v___f_1595_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___x_1596_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1596_, 0, lean_box(0));
lean_closure_set(v___x_1596_, 1, v_x_1592_);
v___x_1597_ = lean_io_as_task(v___x_1596_, v_prio_1593_);
v___x_1598_ = lean_unsigned_to_nat(0u);
v___x_1599_ = 1;
v___x_1600_ = lean_task_bind(v___x_1597_, v___f_1595_, v___x_1598_, v___x_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_asTask___redArg___boxed(lean_object* v_x_1601_, lean_object* v_prio_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Std_Async_BaseAsync_asTask___redArg(v_x_1601_, v_prio_1602_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_asTask(lean_object* v_00_u03b1_1605_, lean_object* v_x_1606_, lean_object* v_prio_1607_){
_start:
{
lean_object* v___f_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; lean_object* v___x_1614_; 
v___f_1609_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___x_1610_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1610_, 0, lean_box(0));
lean_closure_set(v___x_1610_, 1, v_x_1606_);
v___x_1611_ = lean_io_as_task(v___x_1610_, v_prio_1607_);
v___x_1612_ = lean_unsigned_to_nat(0u);
v___x_1613_ = 1;
v___x_1614_ = lean_task_bind(v___x_1611_, v___f_1609_, v___x_1612_, v___x_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_asTask___boxed(lean_object* v_00_u03b1_1615_, lean_object* v_x_1616_, lean_object* v_prio_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Std_Async_BaseAsync_asTask(v_00_u03b1_1615_, v_x_1616_, v_prio_1617_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_await___redArg(lean_object* v_t_1620_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1622_, 0, v_t_1620_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_await___redArg___boxed(lean_object* v_t_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Std_Async_BaseAsync_await___redArg(v_t_1623_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_await(lean_object* v_00_u03b1_1626_, lean_object* v_t_1627_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1629_, 0, v_t_1627_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_await___boxed(lean_object* v_00_u03b1_1630_, lean_object* v_t_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Std_Async_BaseAsync_await(v_00_u03b1_1630_, v_t_1631_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_async___redArg(lean_object* v_self_1634_, lean_object* v_prio_1635_){
_start:
{
lean_object* v___f_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; uint8_t v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___f_1637_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___x_1638_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1638_, 0, lean_box(0));
lean_closure_set(v___x_1638_, 1, v_self_1634_);
v___x_1639_ = lean_io_as_task(v___x_1638_, v_prio_1635_);
v___x_1640_ = lean_unsigned_to_nat(0u);
v___x_1641_ = 1;
v___x_1642_ = lean_task_bind(v___x_1639_, v___f_1637_, v___x_1640_, v___x_1641_);
v___x_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_async___redArg___boxed(lean_object* v_self_1644_, lean_object* v_prio_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Std_Async_BaseAsync_async___redArg(v_self_1644_, v_prio_1645_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_async(lean_object* v_00_u03b1_1648_, lean_object* v_self_1649_, lean_object* v_prio_1650_){
_start:
{
lean_object* v___f_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___f_1652_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___x_1653_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1653_, 0, lean_box(0));
lean_closure_set(v___x_1653_, 1, v_self_1649_);
v___x_1654_ = lean_io_as_task(v___x_1653_, v_prio_1650_);
v___x_1655_ = lean_unsigned_to_nat(0u);
v___x_1656_ = 1;
v___x_1657_ = lean_task_bind(v___x_1654_, v___f_1652_, v___x_1655_, v___x_1656_);
v___x_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_async___boxed(lean_object* v_00_u03b1_1659_, lean_object* v_self_1660_, lean_object* v_prio_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Std_Async_BaseAsync_async(v_00_u03b1_1659_, v_self_1660_, v_prio_1661_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instFunctor___lam__0(lean_object* v_00_u03b1_1664_, lean_object* v_00_u03b2_1665_, lean_object* v_f_1666_, lean_object* v_self_1667_){
_start:
{
lean_object* v___x_1669_; uint8_t v___x_1670_; lean_object* v___x_1671_; 
v___x_1669_ = lean_unsigned_to_nat(0u);
v___x_1670_ = 0;
v___x_1671_ = lean_apply_1(v_self_1667_, lean_box(0));
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1680_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1674_ = v___x_1671_;
v_isShared_1675_ = v_isSharedCheck_1680_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1671_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1680_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; lean_object* v___x_1678_; 
v___x_1676_ = lean_apply_1(v_f_1666_, v_a_1672_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 0, v___x_1676_);
v___x_1678_ = v___x_1674_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1689_; 
v_a_1681_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1683_ = v___x_1671_;
v_isShared_1684_ = v_isSharedCheck_1689_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1671_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1689_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1685_; lean_object* v___x_1687_; 
v___x_1685_ = lean_task_map(v_f_1666_, v_a_1681_, v___x_1669_, v___x_1670_);
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 0, v___x_1685_);
v___x_1687_ = v___x_1683_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instFunctor___lam__0___boxed(lean_object* v_00_u03b1_1690_, lean_object* v_00_u03b2_1691_, lean_object* v_f_1692_, lean_object* v_self_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Std_Async_BaseAsync_instFunctor___lam__0(v_00_u03b1_1690_, v_00_u03b2_1691_, v_f_1692_, v_self_1693_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instFunctor___lam__1(lean_object* v___f_1696_, lean_object* v_00_u03b1_1697_, lean_object* v_00_u03b2_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1702_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_1702_, 0, lean_box(0));
lean_closure_set(v___x_1702_, 1, lean_box(0));
lean_closure_set(v___x_1702_, 2, v___y_1699_);
v___x_1703_ = lean_apply_5(v___f_1696_, lean_box(0), lean_box(0), v___x_1702_, v___y_1700_, lean_box(0));
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instFunctor___lam__1___boxed(lean_object* v___f_1704_, lean_object* v_00_u03b1_1705_, lean_object* v_00_u03b2_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Std_Async_BaseAsync_instFunctor___lam__1(v___f_1704_, v_00_u03b1_1705_, v_00_u03b2_1706_, v___y_1707_, v___y_1708_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__0(lean_object* v_x_1718_, lean_object* v_y_1719_){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; uint8_t v___x_1723_; lean_object* v___x_1724_; 
v___x_1721_ = lean_box(0);
v___x_1722_ = lean_unsigned_to_nat(0u);
v___x_1723_ = 0;
v___x_1724_ = lean_apply_2(v_x_1718_, v___x_1721_, lean_box(0));
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1733_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1727_ = v___x_1724_;
v_isShared_1728_ = v_isSharedCheck_1733_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1724_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1733_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1729_ = lean_apply_1(v_y_1719_, v_a_1725_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 0, v___x_1729_);
v___x_1731_ = v___x_1727_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
else
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1742_; 
v_a_1734_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1736_ = v___x_1724_;
v_isShared_1737_ = v_isSharedCheck_1742_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1724_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1742_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; lean_object* v___x_1740_; 
v___x_1738_ = lean_task_map(v_y_1719_, v_a_1734_, v___x_1722_, v___x_1723_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v___x_1738_);
v___x_1740_ = v___x_1736_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__0___boxed(lean_object* v_x_1743_, lean_object* v_y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Std_Async_BaseAsync_instMonad___lam__0(v_x_1743_, v_y_1744_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__1(lean_object* v_00_u03b1_1747_, lean_object* v_00_u03b2_1748_, lean_object* v_f_1749_, lean_object* v_x_1750_){
_start:
{
lean_object* v___f_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___f_1752_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_instMonad___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1752_, 0, v_x_1750_);
v___x_1753_ = lean_unsigned_to_nat(0u);
v___x_1754_ = 0;
v___x_1755_ = lean_apply_1(v_f_1749_, lean_box(0));
v___x_1756_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_1753_, v___x_1754_, v___x_1755_, v___f_1752_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__1___boxed(lean_object* v_00_u03b1_1757_, lean_object* v_00_u03b2_1758_, lean_object* v_f_1759_, lean_object* v_x_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Std_Async_BaseAsync_instMonad___lam__1(v_00_u03b1_1757_, v_00_u03b2_1758_, v_f_1759_, v_x_1760_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__2(lean_object* v_00_u03b1_1763_, lean_object* v_00_u03b2_1764_, lean_object* v_self_1765_, lean_object* v_f_1766_){
_start:
{
lean_object* v___x_1768_; uint8_t v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1768_ = lean_unsigned_to_nat(0u);
v___x_1769_ = 0;
v___x_1770_ = lean_apply_1(v_self_1765_, lean_box(0));
v___x_1771_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_1768_, v___x_1769_, v___x_1770_, v_f_1766_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__2___boxed(lean_object* v_00_u03b1_1772_, lean_object* v_00_u03b2_1773_, lean_object* v_self_1774_, lean_object* v_f_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Std_Async_BaseAsync_instMonad___lam__2(v_00_u03b1_1772_, v_00_u03b2_1773_, v_self_1774_, v_f_1775_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__3(lean_object* v_a_1778_, lean_object* v_x_1779_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1781_, 0, v_a_1778_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__3___boxed(lean_object* v_a_1782_, lean_object* v_x_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Std_Async_BaseAsync_instMonad___lam__3(v_a_1782_, v_x_1783_);
lean_dec(v_x_1783_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__4(lean_object* v_y_1786_, lean_object* v___f_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v___f_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___f_1790_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_instMonad___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1790_, 0, v_a_1788_);
v___x_1791_ = lean_box(0);
v___x_1792_ = lean_apply_1(v_y_1786_, v___x_1791_);
v___x_1793_ = lean_apply_5(v___f_1787_, lean_box(0), lean_box(0), v___x_1792_, v___f_1790_, lean_box(0));
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__4___boxed(lean_object* v_y_1794_, lean_object* v___f_1795_, lean_object* v_a_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Std_Async_BaseAsync_instMonad___lam__4(v_y_1794_, v___f_1795_, v_a_1796_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__5(lean_object* v___f_1799_, lean_object* v_00_u03b1_1800_, lean_object* v_00_u03b2_1801_, lean_object* v_x_1802_, lean_object* v_y_1803_){
_start:
{
lean_object* v___f_1805_; lean_object* v___x_1806_; 
lean_inc_ref(v___f_1799_);
v___f_1805_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_instMonad___lam__4___boxed), 4, 2);
lean_closure_set(v___f_1805_, 0, v_y_1803_);
lean_closure_set(v___f_1805_, 1, v___f_1799_);
v___x_1806_ = lean_apply_5(v___f_1799_, lean_box(0), lean_box(0), v_x_1802_, v___f_1805_, lean_box(0));
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__5___boxed(lean_object* v___f_1807_, lean_object* v_00_u03b1_1808_, lean_object* v_00_u03b2_1809_, lean_object* v_x_1810_, lean_object* v_y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Std_Async_BaseAsync_instMonad___lam__5(v___f_1807_, v_00_u03b1_1808_, v_00_u03b2_1809_, v_x_1810_, v_y_1811_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__6(lean_object* v_y_1814_, lean_object* v_x_1815_){
_start:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1817_ = lean_box(0);
v___x_1818_ = lean_apply_2(v_y_1814_, v___x_1817_, lean_box(0));
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__6___boxed(lean_object* v_y_1819_, lean_object* v_x_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Std_Async_BaseAsync_instMonad___lam__6(v_y_1819_, v_x_1820_);
lean_dec(v_x_1820_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__7(lean_object* v_00_u03b1_1823_, lean_object* v_00_u03b2_1824_, lean_object* v_x_1825_, lean_object* v_y_1826_){
_start:
{
lean_object* v___f_1828_; lean_object* v___x_1829_; uint8_t v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___f_1828_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_instMonad___lam__6___boxed), 3, 1);
lean_closure_set(v___f_1828_, 0, v_y_1826_);
v___x_1829_ = lean_unsigned_to_nat(0u);
v___x_1830_ = 0;
v___x_1831_ = lean_apply_1(v_x_1825_, lean_box(0));
v___x_1832_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_1829_, v___x_1830_, v___x_1831_, v___f_1828_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonad___lam__7___boxed(lean_object* v_00_u03b1_1833_, lean_object* v_00_u03b2_1834_, lean_object* v_x_1835_, lean_object* v_y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Std_Async_BaseAsync_instMonad___lam__7(v_00_u03b1_1833_, v_00_u03b2_1834_, v_x_1835_, v_y_1836_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadAsyncTask___lam__1(lean_object* v___f_1859_, lean_object* v_00_u03b1_1860_, lean_object* v_t_1861_, lean_object* v_prio_1862_){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1864_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1864_, 0, lean_box(0));
lean_closure_set(v___x_1864_, 1, v_t_1861_);
v___x_1865_ = lean_io_as_task(v___x_1864_, v_prio_1862_);
v___x_1866_ = lean_unsigned_to_nat(0u);
v___x_1867_ = 1;
v___x_1868_ = lean_task_bind(v___x_1865_, v___f_1859_, v___x_1866_, v___x_1867_);
v___x_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadAsyncTask___lam__1___boxed(lean_object* v___f_1870_, lean_object* v_00_u03b1_1871_, lean_object* v_t_1872_, lean_object* v_prio_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Std_Async_BaseAsync_instMonadAsyncTask___lam__1(v___f_1870_, v_00_u03b1_1871_, v_t_1872_, v_prio_1873_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instInhabited___redArg(lean_object* v_inst_1879_){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1880_, 0, v_inst_1879_);
v___x_1881_ = lean_alloc_closure((void*)(l_instMonadBaseIO___aux__5___boxed), 3, 2);
lean_closure_set(v___x_1881_, 0, lean_box(0));
lean_closure_set(v___x_1881_, 1, v___x_1880_);
v___x_1882_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_mk___boxed), 3, 2);
lean_closure_set(v___x_1882_, 0, lean_box(0));
lean_closure_set(v___x_1882_, 1, v___x_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instInhabited(lean_object* v_00_u03b1_1883_, lean_object* v_inst_1884_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Std_Async_BaseAsync_instInhabited___redArg(v_inst_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadFinally___lam__0(lean_object* v_res_1886_, lean_object* v_snd_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1888_, 0, v_res_1886_);
lean_ctor_set(v___x_1888_, 1, v_snd_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadFinally___lam__1(lean_object* v_f_1889_, lean_object* v_res_1890_){
_start:
{
lean_object* v___f_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; lean_object* v___x_1896_; 
lean_inc_n(v_res_1890_, 2);
v___f_1892_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_instMonadFinally___lam__0), 2, 1);
lean_closure_set(v___f_1892_, 0, v_res_1890_);
v___x_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1893_, 0, v_res_1890_);
v___x_1894_ = lean_unsigned_to_nat(0u);
v___x_1895_ = 0;
v___x_1896_ = lean_apply_2(v_f_1889_, v___x_1893_, lean_box(0));
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1905_; 
lean_dec_ref(v___f_1892_);
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1899_ = v___x_1896_;
v_isShared_1900_ = v_isSharedCheck_1905_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1896_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1905_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1901_, 0, v_res_1890_);
lean_ctor_set(v___x_1901_, 1, v_a_1897_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v___x_1901_);
v___x_1903_ = v___x_1899_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1901_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1914_; 
lean_dec(v_res_1890_);
v_a_1906_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1908_ = v___x_1896_;
v_isShared_1909_ = v_isSharedCheck_1914_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1896_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1914_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1910_; lean_object* v___x_1912_; 
v___x_1910_ = lean_task_map(v___f_1892_, v_a_1906_, v___x_1894_, v___x_1895_);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 0, v___x_1910_);
v___x_1912_ = v___x_1908_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadFinally___lam__1___boxed(lean_object* v_f_1915_, lean_object* v_res_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Std_Async_BaseAsync_instMonadFinally___lam__1(v_f_1915_, v_res_1916_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadFinally___lam__2(lean_object* v_00_u03b1_1919_, lean_object* v_00_u03b2_1920_, lean_object* v_x_1921_, lean_object* v_f_1922_){
_start:
{
lean_object* v___f_1924_; lean_object* v___x_1925_; uint8_t v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___f_1924_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_instMonadFinally___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1924_, 0, v_f_1922_);
v___x_1925_ = lean_unsigned_to_nat(0u);
v___x_1926_ = 0;
v___x_1927_ = lean_apply_1(v_x_1921_, lean_box(0));
v___x_1928_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_1925_, v___x_1926_, v___x_1927_, v___f_1924_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_instMonadFinally___lam__2___boxed(lean_object* v_00_u03b1_1929_, lean_object* v_00_u03b2_1930_, lean_object* v_x_1931_, lean_object* v_f_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Std_Async_BaseAsync_instMonadFinally___lam__2(v_00_u03b1_1929_, v_00_u03b2_1930_, v_x_1931_, v_f_1932_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofExcept___redArg(lean_object* v_except_1937_){
_start:
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
v_a_1939_ = lean_ctor_get(v_except_1937_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v_except_1937_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v_except_1937_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v_except_1937_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
lean_ctor_set_tag(v___x_1941_, 0);
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofExcept___redArg___boxed(lean_object* v_except_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Std_Async_BaseAsync_ofExcept___redArg(v_except_1947_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofExcept(lean_object* v_00_u03b1_1950_, lean_object* v_except_1951_){
_start:
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
v_a_1953_ = lean_ctor_get(v_except_1951_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v_except_1951_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v_except_1951_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v_except_1951_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
lean_ctor_set_tag(v___x_1955_, 0);
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_ofExcept___boxed(lean_object* v_00_u03b1_1961_, lean_object* v_except_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Std_Async_BaseAsync_ofExcept(v_00_u03b1_1961_, v_except_1962_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__1(lean_object* v_resultX_1965_, lean_object* v_resultY_1966_){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1968_, 0, v_resultX_1965_);
lean_ctor_set(v___x_1968_, 1, v_resultY_1966_);
v___x_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__1___boxed(lean_object* v_resultX_1970_, lean_object* v_resultY_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Std_Async_BaseAsync_concurrently___redArg___lam__1(v_resultX_1970_, v_resultY_1971_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__0(lean_object* v_taskY_1974_, lean_object* v_resultX_1975_){
_start:
{
lean_object* v___f_1977_; lean_object* v___x_1978_; uint8_t v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___f_1977_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrently___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1977_, 0, v_resultX_1975_);
v___x_1978_ = lean_unsigned_to_nat(0u);
v___x_1979_ = 0;
v___x_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1980_, 0, v_taskY_1974_);
v___x_1981_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_1978_, v___x_1979_, v___x_1980_, v___f_1977_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__0___boxed(lean_object* v_taskY_1982_, lean_object* v_resultX_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Std_Async_BaseAsync_concurrently___redArg___lam__0(v_taskY_1982_, v_resultX_1983_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__2(lean_object* v_taskX_1986_, lean_object* v_taskY_1987_){
_start:
{
lean_object* v___f_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___f_1989_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrently___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1989_, 0, v_taskY_1987_);
v___x_1990_ = lean_unsigned_to_nat(0u);
v___x_1991_ = 0;
v___x_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1992_, 0, v_taskX_1986_);
v___x_1993_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_1990_, v___x_1991_, v___x_1992_, v___f_1989_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__2___boxed(lean_object* v_taskX_1994_, lean_object* v_taskY_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Std_Async_BaseAsync_concurrently___redArg___lam__2(v_taskX_1994_, v_taskY_1995_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__3(lean_object* v_y_1998_, lean_object* v_prio_1999_, lean_object* v___f_2000_, lean_object* v_taskX_2001_){
_start:
{
lean_object* v___f_2003_; lean_object* v___x_2004_; uint8_t v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; uint8_t v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___f_2003_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrently___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2003_, 0, v_taskX_2001_);
v___x_2004_ = lean_unsigned_to_nat(0u);
v___x_2005_ = 0;
v___x_2006_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2006_, 0, lean_box(0));
lean_closure_set(v___x_2006_, 1, v_y_1998_);
v___x_2007_ = lean_io_as_task(v___x_2006_, v_prio_1999_);
v___x_2008_ = 1;
v___x_2009_ = lean_task_bind(v___x_2007_, v___f_2000_, v___x_2004_, v___x_2008_);
v___x_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
v___x_2011_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2004_, v___x_2005_, v___x_2010_, v___f_2003_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___lam__3___boxed(lean_object* v_y_2012_, lean_object* v_prio_2013_, lean_object* v___f_2014_, lean_object* v_taskX_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_Std_Async_BaseAsync_concurrently___redArg___lam__3(v_y_2012_, v_prio_2013_, v___f_2014_, v_taskX_2015_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg(lean_object* v_x_2018_, lean_object* v_y_2019_, lean_object* v_prio_2020_){
_start:
{
lean_object* v___f_2022_; lean_object* v___f_2023_; lean_object* v___x_2024_; uint8_t v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; uint8_t v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___f_2022_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
lean_inc(v_prio_2020_);
v___f_2023_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrently___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2023_, 0, v_y_2019_);
lean_closure_set(v___f_2023_, 1, v_prio_2020_);
lean_closure_set(v___f_2023_, 2, v___f_2022_);
v___x_2024_ = lean_unsigned_to_nat(0u);
v___x_2025_ = 0;
v___x_2026_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2026_, 0, lean_box(0));
lean_closure_set(v___x_2026_, 1, v_x_2018_);
v___x_2027_ = lean_io_as_task(v___x_2026_, v_prio_2020_);
v___x_2028_ = 1;
v___x_2029_ = lean_task_bind(v___x_2027_, v___f_2022_, v___x_2024_, v___x_2028_);
v___x_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
v___x_2031_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2024_, v___x_2025_, v___x_2030_, v___f_2023_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___redArg___boxed(lean_object* v_x_2032_, lean_object* v_y_2033_, lean_object* v_prio_2034_, lean_object* v_a_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_Std_Async_BaseAsync_concurrently___redArg(v_x_2032_, v_y_2033_, v_prio_2034_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently(lean_object* v_00_u03b1_2037_, lean_object* v_00_u03b2_2038_, lean_object* v_x_2039_, lean_object* v_y_2040_, lean_object* v_prio_2041_){
_start:
{
lean_object* v___f_2043_; lean_object* v___f_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___f_2043_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
lean_inc(v_prio_2041_);
v___f_2044_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrently___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2044_, 0, v_y_2040_);
lean_closure_set(v___f_2044_, 1, v_prio_2041_);
lean_closure_set(v___f_2044_, 2, v___f_2043_);
v___x_2045_ = lean_unsigned_to_nat(0u);
v___x_2046_ = 0;
v___x_2047_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2047_, 0, lean_box(0));
lean_closure_set(v___x_2047_, 1, v_x_2039_);
v___x_2048_ = lean_io_as_task(v___x_2047_, v_prio_2041_);
v___x_2049_ = 1;
v___x_2050_ = lean_task_bind(v___x_2048_, v___f_2043_, v___x_2045_, v___x_2049_);
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
v___x_2052_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2045_, v___x_2046_, v___x_2051_, v___f_2044_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrently___boxed(lean_object* v_00_u03b1_2053_, lean_object* v_00_u03b2_2054_, lean_object* v_x_2055_, lean_object* v_y_2056_, lean_object* v_prio_2057_, lean_object* v_a_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Std_Async_BaseAsync_concurrently(v_00_u03b1_2053_, v_00_u03b2_2054_, v_x_2055_, v_y_2056_, v_prio_2057_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__2(lean_object* v_promise_2060_, lean_object* v_value_2061_){
_start:
{
lean_object* v___x_2063_; 
v___x_2063_ = lean_io_promise_resolve(v_value_2061_, v_promise_2060_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__2___boxed(lean_object* v_promise_2064_, lean_object* v_value_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_Std_Async_BaseAsync_race___redArg___lam__2(v_promise_2064_, v_value_2065_);
lean_dec(v_promise_2064_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__0(lean_object* v_promise_2068_, lean_object* v_____r_2069_){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2071_ = l_IO_Promise_result_x21___redArg(v_promise_2068_);
v___x_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__0___boxed(lean_object* v_promise_2073_, lean_object* v_____r_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Std_Async_BaseAsync_race___redArg___lam__0(v_promise_2073_, v_____r_2074_);
lean_dec(v_promise_2073_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__1(lean_object* v_task_u2082_2077_, lean_object* v___x_2078_, lean_object* v___x_2079_, uint8_t v___x_2080_, lean_object* v___f_2081_, lean_object* v_____r_2082_){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
lean_inc(v___x_2079_);
v___x_2084_ = l_BaseIO_chainTask___redArg(v_task_u2082_2077_, v___x_2078_, v___x_2079_, v___x_2080_);
v___x_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
v___x_2086_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2079_, v___x_2080_, v___x_2085_, v___f_2081_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__1___boxed(lean_object* v_task_u2082_2087_, lean_object* v___x_2088_, lean_object* v___x_2089_, lean_object* v___x_2090_, lean_object* v___f_2091_, lean_object* v_____r_2092_, lean_object* v___y_2093_){
_start:
{
uint8_t v___x_624__boxed_2094_; lean_object* v_res_2095_; 
v___x_624__boxed_2094_ = lean_unbox(v___x_2090_);
v_res_2095_ = l_Std_Async_BaseAsync_race___redArg___lam__1(v_task_u2082_2087_, v___x_2088_, v___x_2089_, v___x_624__boxed_2094_, v___f_2091_, v_____r_2092_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__3(lean_object* v___f_2096_, lean_object* v___f_2097_, lean_object* v___f_2098_, lean_object* v_task_u2081_2099_, lean_object* v_task_u2082_2100_){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; uint8_t v___x_2105_; lean_object* v___x_2106_; lean_object* v___f_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2102_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_2102_, 0, lean_box(0));
lean_closure_set(v___x_2102_, 1, lean_box(0));
lean_closure_set(v___x_2102_, 2, v___f_2096_);
lean_closure_set(v___x_2102_, 3, lean_box(0));
v___x_2103_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_2103_, 0, lean_box(0));
lean_closure_set(v___x_2103_, 1, lean_box(0));
lean_closure_set(v___x_2103_, 2, lean_box(0));
lean_closure_set(v___x_2103_, 3, v___x_2102_);
lean_closure_set(v___x_2103_, 4, v___f_2097_);
v___x_2104_ = lean_unsigned_to_nat(0u);
v___x_2105_ = 0;
v___x_2106_ = lean_box(v___x_2105_);
lean_inc_ref(v___x_2103_);
v___f_2107_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2107_, 0, v_task_u2082_2100_);
lean_closure_set(v___f_2107_, 1, v___x_2103_);
lean_closure_set(v___f_2107_, 2, v___x_2104_);
lean_closure_set(v___f_2107_, 3, v___x_2106_);
lean_closure_set(v___f_2107_, 4, v___f_2098_);
v___x_2108_ = l_BaseIO_chainTask___redArg(v_task_u2081_2099_, v___x_2103_, v___x_2104_, v___x_2105_);
v___x_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
v___x_2110_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2104_, v___x_2105_, v___x_2109_, v___f_2107_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__3___boxed(lean_object* v___f_2111_, lean_object* v___f_2112_, lean_object* v___f_2113_, lean_object* v_task_u2081_2114_, lean_object* v_task_u2082_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Std_Async_BaseAsync_race___redArg___lam__3(v___f_2111_, v___f_2112_, v___f_2113_, v_task_u2081_2114_, v_task_u2082_2115_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__4(lean_object* v___f_2118_, lean_object* v___f_2119_, lean_object* v___f_2120_, lean_object* v_y_2121_, lean_object* v_prio_2122_, lean_object* v___f_2123_, lean_object* v_task_u2081_2124_){
_start:
{
lean_object* v___f_2126_; lean_object* v___x_2127_; uint8_t v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___f_2126_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_2126_, 0, v___f_2118_);
lean_closure_set(v___f_2126_, 1, v___f_2119_);
lean_closure_set(v___f_2126_, 2, v___f_2120_);
lean_closure_set(v___f_2126_, 3, v_task_u2081_2124_);
v___x_2127_ = lean_unsigned_to_nat(0u);
v___x_2128_ = 0;
v___x_2129_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2129_, 0, lean_box(0));
lean_closure_set(v___x_2129_, 1, v_y_2121_);
v___x_2130_ = lean_io_as_task(v___x_2129_, v_prio_2122_);
v___x_2131_ = 1;
v___x_2132_ = lean_task_bind(v___x_2130_, v___f_2123_, v___x_2127_, v___x_2131_);
v___x_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
v___x_2134_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2127_, v___x_2128_, v___x_2133_, v___f_2126_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__4___boxed(lean_object* v___f_2135_, lean_object* v___f_2136_, lean_object* v___f_2137_, lean_object* v_y_2138_, lean_object* v_prio_2139_, lean_object* v___f_2140_, lean_object* v_task_u2081_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_Std_Async_BaseAsync_race___redArg___lam__4(v___f_2135_, v___f_2136_, v___f_2137_, v_y_2138_, v_prio_2139_, v___f_2140_, v_task_u2081_2141_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__5(lean_object* v___f_2144_, lean_object* v_y_2145_, lean_object* v_prio_2146_, lean_object* v___f_2147_, lean_object* v_x_2148_, lean_object* v___f_2149_, lean_object* v_promise_2150_){
_start:
{
lean_object* v___f_2152_; lean_object* v___f_2153_; lean_object* v___f_2154_; lean_object* v___x_2155_; uint8_t v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
lean_inc(v_promise_2150_);
v___f_2152_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2152_, 0, v_promise_2150_);
v___f_2153_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2153_, 0, v_promise_2150_);
lean_inc(v_prio_2146_);
v___f_2154_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__4___boxed), 8, 6);
lean_closure_set(v___f_2154_, 0, v___f_2144_);
lean_closure_set(v___f_2154_, 1, v___f_2152_);
lean_closure_set(v___f_2154_, 2, v___f_2153_);
lean_closure_set(v___f_2154_, 3, v_y_2145_);
lean_closure_set(v___f_2154_, 4, v_prio_2146_);
lean_closure_set(v___f_2154_, 5, v___f_2147_);
v___x_2155_ = lean_unsigned_to_nat(0u);
v___x_2156_ = 0;
v___x_2157_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2157_, 0, lean_box(0));
lean_closure_set(v___x_2157_, 1, v_x_2148_);
v___x_2158_ = lean_io_as_task(v___x_2157_, v_prio_2146_);
v___x_2159_ = 1;
v___x_2160_ = lean_task_bind(v___x_2158_, v___f_2149_, v___x_2155_, v___x_2159_);
v___x_2161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
v___x_2162_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2155_, v___x_2156_, v___x_2161_, v___f_2154_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___lam__5___boxed(lean_object* v___f_2163_, lean_object* v_y_2164_, lean_object* v_prio_2165_, lean_object* v___f_2166_, lean_object* v_x_2167_, lean_object* v___f_2168_, lean_object* v_promise_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Std_Async_BaseAsync_race___redArg___lam__5(v___f_2163_, v_y_2164_, v_prio_2165_, v___f_2166_, v_x_2167_, v___f_2168_, v_promise_2169_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg(lean_object* v_x_2173_, lean_object* v_y_2174_, lean_object* v_prio_2175_){
_start:
{
lean_object* v___f_2177_; lean_object* v___f_2178_; lean_object* v___f_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___f_2177_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___f_2178_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_2179_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__5___boxed), 8, 6);
lean_closure_set(v___f_2179_, 0, v___f_2178_);
lean_closure_set(v___f_2179_, 1, v_y_2174_);
lean_closure_set(v___f_2179_, 2, v_prio_2175_);
lean_closure_set(v___f_2179_, 3, v___f_2177_);
lean_closure_set(v___f_2179_, 4, v_x_2173_);
lean_closure_set(v___f_2179_, 5, v___f_2177_);
v___x_2180_ = lean_unsigned_to_nat(0u);
v___x_2181_ = 0;
v___x_2182_ = lean_io_promise_new();
v___x_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2182_);
v___x_2184_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2180_, v___x_2181_, v___x_2183_, v___f_2179_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___redArg___boxed(lean_object* v_x_2185_, lean_object* v_y_2186_, lean_object* v_prio_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Std_Async_BaseAsync_race___redArg(v_x_2185_, v_y_2186_, v_prio_2187_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race(lean_object* v_00_u03b1_2190_, lean_object* v_inst_2191_, lean_object* v_x_2192_, lean_object* v_y_2193_, lean_object* v_prio_2194_){
_start:
{
lean_object* v___f_2196_; lean_object* v___f_2197_; lean_object* v___f_2198_; lean_object* v___x_2199_; uint8_t v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___f_2196_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___f_2197_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_2198_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__5___boxed), 8, 6);
lean_closure_set(v___f_2198_, 0, v___f_2197_);
lean_closure_set(v___f_2198_, 1, v_y_2193_);
lean_closure_set(v___f_2198_, 2, v_prio_2194_);
lean_closure_set(v___f_2198_, 3, v___f_2196_);
lean_closure_set(v___f_2198_, 4, v_x_2192_);
lean_closure_set(v___f_2198_, 5, v___f_2196_);
v___x_2199_ = lean_unsigned_to_nat(0u);
v___x_2200_ = 0;
v___x_2201_ = lean_io_promise_new();
v___x_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
v___x_2203_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2199_, v___x_2200_, v___x_2202_, v___f_2198_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_race___boxed(lean_object* v_00_u03b1_2204_, lean_object* v_inst_2205_, lean_object* v_x_2206_, lean_object* v_y_2207_, lean_object* v_prio_2208_, lean_object* v_a_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Std_Async_BaseAsync_race(v_00_u03b1_2204_, v_inst_2205_, v_x_2206_, v_y_2207_, v_prio_2208_);
lean_dec(v_inst_2205_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1(lean_object* v_prio_2211_, lean_object* v___f_2212_, lean_object* v_x_2213_){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; uint8_t v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2215_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2215_, 0, lean_box(0));
lean_closure_set(v___x_2215_, 1, v_x_2213_);
v___x_2216_ = lean_io_as_task(v___x_2215_, v_prio_2211_);
v___x_2217_ = lean_unsigned_to_nat(0u);
v___x_2218_ = 1;
v___x_2219_ = lean_task_bind(v___x_2216_, v___f_2212_, v___x_2217_, v___x_2218_);
v___x_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1___boxed(lean_object* v_prio_2221_, lean_object* v___f_2222_, lean_object* v_x_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1(v_prio_2221_, v___f_2222_, v_x_2223_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0(lean_object* v___x_2227_, lean_object* v_tasks_2228_){
_start:
{
lean_object* v___x_2230_; size_t v_sz_2231_; size_t v___x_2232_; lean_object* v___x_219__overap_2233_; lean_object* v___x_2234_; 
v___x_2230_ = ((lean_object*)(l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0___closed__0));
v_sz_2231_ = lean_array_size(v_tasks_2228_);
v___x_2232_ = ((size_t)0ULL);
v___x_219__overap_2233_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2227_, v___x_2230_, v_sz_2231_, v___x_2232_, v_tasks_2228_);
v___x_2234_ = lean_apply_1(v___x_219__overap_2233_, lean_box(0));
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0___boxed(lean_object* v___x_2235_, lean_object* v_tasks_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0(v___x_2235_, v_tasks_2236_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg(lean_object* v_xs_2241_, lean_object* v_prio_2242_){
_start:
{
lean_object* v___f_2244_; lean_object* v___f_2245_; lean_object* v___x_2246_; lean_object* v___f_2247_; lean_object* v___x_2248_; uint8_t v___x_2249_; size_t v_sz_2250_; size_t v___x_2251_; lean_object* v___x_167__overap_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___f_2244_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___f_2245_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2245_, 0, v_prio_2242_);
lean_closure_set(v___f_2245_, 1, v___f_2244_);
v___x_2246_ = ((lean_object*)(l_Std_Async_BaseAsync_instMonad));
v___f_2247_ = ((lean_object*)(l_Std_Async_BaseAsync_concurrentlyAll___redArg___closed__0));
v___x_2248_ = lean_unsigned_to_nat(0u);
v___x_2249_ = 0;
v_sz_2250_ = lean_array_size(v_xs_2241_);
v___x_2251_ = ((size_t)0ULL);
v___x_167__overap_2252_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2246_, v___f_2245_, v_sz_2250_, v___x_2251_, v_xs_2241_);
v___x_2253_ = lean_apply_1(v___x_167__overap_2252_, lean_box(0));
v___x_2254_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2248_, v___x_2249_, v___x_2253_, v___f_2247_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___redArg___boxed(lean_object* v_xs_2255_, lean_object* v_prio_2256_, lean_object* v_a_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Std_Async_BaseAsync_concurrentlyAll___redArg(v_xs_2255_, v_prio_2256_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll(lean_object* v_00_u03b1_2259_, lean_object* v_xs_2260_, lean_object* v_prio_2261_){
_start:
{
lean_object* v___f_2263_; lean_object* v___f_2264_; lean_object* v___x_2265_; lean_object* v___f_2266_; lean_object* v___x_2267_; uint8_t v___x_2268_; size_t v_sz_2269_; size_t v___x_2270_; lean_object* v___x_196__overap_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___f_2263_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___f_2264_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2264_, 0, v_prio_2261_);
lean_closure_set(v___f_2264_, 1, v___f_2263_);
v___x_2265_ = ((lean_object*)(l_Std_Async_BaseAsync_instMonad));
v___f_2266_ = ((lean_object*)(l_Std_Async_BaseAsync_concurrentlyAll___redArg___closed__0));
v___x_2267_ = lean_unsigned_to_nat(0u);
v___x_2268_ = 0;
v_sz_2269_ = lean_array_size(v_xs_2260_);
v___x_2270_ = ((size_t)0ULL);
v___x_196__overap_2271_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2265_, v___f_2264_, v_sz_2269_, v___x_2270_, v_xs_2260_);
v___x_2272_ = lean_apply_1(v___x_196__overap_2271_, lean_box(0));
v___x_2273_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2267_, v___x_2268_, v___x_2272_, v___f_2266_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_concurrentlyAll___boxed(lean_object* v_00_u03b1_2274_, lean_object* v_xs_2275_, lean_object* v_prio_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Std_Async_BaseAsync_concurrentlyAll(v_00_u03b1_2274_, v_xs_2275_, v_prio_2276_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__2(lean_object* v___f_2279_, lean_object* v___f_2280_, lean_object* v_task_u2081_2281_){
_start:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; uint8_t v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2283_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_2283_, 0, lean_box(0));
lean_closure_set(v___x_2283_, 1, lean_box(0));
lean_closure_set(v___x_2283_, 2, v___f_2279_);
lean_closure_set(v___x_2283_, 3, lean_box(0));
v___x_2284_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_2284_, 0, lean_box(0));
lean_closure_set(v___x_2284_, 1, lean_box(0));
lean_closure_set(v___x_2284_, 2, lean_box(0));
lean_closure_set(v___x_2284_, 3, v___x_2283_);
lean_closure_set(v___x_2284_, 4, v___f_2280_);
v___x_2285_ = lean_unsigned_to_nat(0u);
v___x_2286_ = 0;
v___x_2287_ = l_BaseIO_chainTask___redArg(v_task_u2081_2281_, v___x_2284_, v___x_2285_, v___x_2286_);
v___x_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__2___boxed(lean_object* v___f_2289_, lean_object* v___f_2290_, lean_object* v_task_u2081_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Std_Async_BaseAsync_raceAll___redArg___lam__2(v___f_2289_, v___f_2290_, v_task_u2081_2291_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__0(lean_object* v_prio_2294_, lean_object* v___f_2295_, lean_object* v___f_2296_, lean_object* v_x_2297_){
_start:
{
lean_object* v___x_2299_; uint8_t v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; uint8_t v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2299_ = lean_unsigned_to_nat(0u);
v___x_2300_ = 0;
v___x_2301_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2301_, 0, lean_box(0));
lean_closure_set(v___x_2301_, 1, v_x_2297_);
v___x_2302_ = lean_io_as_task(v___x_2301_, v_prio_2294_);
v___x_2303_ = 1;
v___x_2304_ = lean_task_bind(v___x_2302_, v___f_2295_, v___x_2299_, v___x_2303_);
v___x_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2304_);
v___x_2306_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2299_, v___x_2300_, v___x_2305_, v___f_2296_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__0___boxed(lean_object* v_prio_2307_, lean_object* v___f_2308_, lean_object* v___f_2309_, lean_object* v_x_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Std_Async_BaseAsync_raceAll___redArg___lam__0(v_prio_2307_, v___f_2308_, v___f_2309_, v_x_2310_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__3(lean_object* v___f_2313_, lean_object* v_prio_2314_, lean_object* v___f_2315_, lean_object* v_inst_2316_, lean_object* v_xs_2317_, lean_object* v_promise_2318_){
_start:
{
lean_object* v___f_2320_; lean_object* v___f_2321_; lean_object* v___f_2322_; lean_object* v___f_2323_; lean_object* v___x_2324_; uint8_t v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
lean_inc(v_promise_2318_);
v___f_2320_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2320_, 0, v_promise_2318_);
v___f_2321_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_raceAll___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2321_, 0, v___f_2313_);
lean_closure_set(v___f_2321_, 1, v___f_2320_);
v___f_2322_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_raceAll___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2322_, 0, v_prio_2314_);
lean_closure_set(v___f_2322_, 1, v___f_2315_);
lean_closure_set(v___f_2322_, 2, v___f_2321_);
v___f_2323_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_race___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2323_, 0, v_promise_2318_);
v___x_2324_ = lean_unsigned_to_nat(0u);
v___x_2325_ = 0;
v___x_2326_ = lean_apply_3(v_inst_2316_, v_xs_2317_, v___f_2322_, lean_box(0));
v___x_2327_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2324_, v___x_2325_, v___x_2326_, v___f_2323_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___lam__3___boxed(lean_object* v___f_2328_, lean_object* v_prio_2329_, lean_object* v___f_2330_, lean_object* v_inst_2331_, lean_object* v_xs_2332_, lean_object* v_promise_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Std_Async_BaseAsync_raceAll___redArg___lam__3(v___f_2328_, v_prio_2329_, v___f_2330_, v_inst_2331_, v_xs_2332_, v_promise_2333_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg(lean_object* v_inst_2336_, lean_object* v_xs_2337_, lean_object* v_prio_2338_){
_start:
{
lean_object* v___f_2340_; lean_object* v___f_2341_; lean_object* v___f_2342_; lean_object* v___x_2343_; uint8_t v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___f_2340_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___f_2341_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_2342_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_raceAll___redArg___lam__3___boxed), 7, 5);
lean_closure_set(v___f_2342_, 0, v___f_2341_);
lean_closure_set(v___f_2342_, 1, v_prio_2338_);
lean_closure_set(v___f_2342_, 2, v___f_2340_);
lean_closure_set(v___f_2342_, 3, v_inst_2336_);
lean_closure_set(v___f_2342_, 4, v_xs_2337_);
v___x_2343_ = lean_unsigned_to_nat(0u);
v___x_2344_ = 0;
v___x_2345_ = lean_io_promise_new();
v___x_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2345_);
v___x_2347_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2343_, v___x_2344_, v___x_2346_, v___f_2342_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___redArg___boxed(lean_object* v_inst_2348_, lean_object* v_xs_2349_, lean_object* v_prio_2350_, lean_object* v_a_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Std_Async_BaseAsync_raceAll___redArg(v_inst_2348_, v_xs_2349_, v_prio_2350_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll(lean_object* v_00_u03b1_2353_, lean_object* v_c_2354_, lean_object* v_inst_2355_, lean_object* v_inst_2356_, lean_object* v_xs_2357_, lean_object* v_prio_2358_){
_start:
{
lean_object* v___f_2360_; lean_object* v___f_2361_; lean_object* v___f_2362_; lean_object* v___x_2363_; uint8_t v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___f_2360_ = ((lean_object*)(l_Std_Async_MaybeTask_joinTask___redArg___closed__0));
v___f_2361_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_2362_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_raceAll___redArg___lam__3___boxed), 7, 5);
lean_closure_set(v___f_2362_, 0, v___f_2361_);
lean_closure_set(v___f_2362_, 1, v_prio_2358_);
lean_closure_set(v___f_2362_, 2, v___f_2360_);
lean_closure_set(v___f_2362_, 3, v_inst_2356_);
lean_closure_set(v___f_2362_, 4, v_xs_2357_);
v___x_2363_ = lean_unsigned_to_nat(0u);
v___x_2364_ = 0;
v___x_2365_ = lean_io_promise_new();
v___x_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
v___x_2367_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2363_, v___x_2364_, v___x_2366_, v___f_2362_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_BaseAsync_raceAll___boxed(lean_object* v_00_u03b1_2368_, lean_object* v_c_2369_, lean_object* v_inst_2370_, lean_object* v_inst_2371_, lean_object* v_xs_2372_, lean_object* v_prio_2373_, lean_object* v_a_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Std_Async_BaseAsync_raceAll(v_00_u03b1_2368_, v_c_2369_, v_inst_2370_, v_inst_2371_, v_xs_2372_, v_prio_2373_);
lean_dec(v_inst_2370_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toBaseIO___redArg(lean_object* v_x_2376_){
_start:
{
lean_object* v___x_2378_; 
v___x_2378_ = lean_apply_1(v_x_2376_, lean_box(0));
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; lean_object* v___x_2380_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2379_);
lean_dec_ref_known(v___x_2378_, 1);
v___x_2380_ = lean_task_pure(v_a_2379_);
return v___x_2380_;
}
else
{
lean_object* v_a_2381_; 
v_a_2381_ = lean_ctor_get(v___x_2378_, 0);
lean_inc_ref(v_a_2381_);
lean_dec_ref_known(v___x_2378_, 1);
return v_a_2381_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toBaseIO___redArg___boxed(lean_object* v_x_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Std_Async_EAsync_toBaseIO___redArg(v_x_2382_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toBaseIO(lean_object* v_00_u03b5_2385_, lean_object* v_00_u03b1_2386_, lean_object* v_x_2387_){
_start:
{
lean_object* v___x_2389_; 
v___x_2389_ = lean_apply_1(v_x_2387_, lean_box(0));
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; lean_object* v___x_2391_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
lean_inc(v_a_2390_);
lean_dec_ref_known(v___x_2389_, 1);
v___x_2391_ = lean_task_pure(v_a_2390_);
return v___x_2391_;
}
else
{
lean_object* v_a_2392_; 
v_a_2392_ = lean_ctor_get(v___x_2389_, 0);
lean_inc_ref(v_a_2392_);
lean_dec_ref_known(v___x_2389_, 1);
return v_a_2392_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toBaseIO___boxed(lean_object* v_00_u03b5_2393_, lean_object* v_00_u03b1_2394_, lean_object* v_x_2395_, lean_object* v_a_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l_Std_Async_EAsync_toBaseIO(v_00_u03b5_2393_, v_00_u03b1_2394_, v_x_2395_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofTask___redArg(lean_object* v_x_2398_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2400_, 0, v_x_2398_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofTask___redArg___boxed(lean_object* v_x_2401_, lean_object* v_a_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l_Std_Async_EAsync_ofTask___redArg(v_x_2401_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofTask(lean_object* v_00_u03b5_2404_, lean_object* v_00_u03b1_2405_, lean_object* v_x_2406_){
_start:
{
lean_object* v___x_2408_; 
v___x_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2408_, 0, v_x_2406_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofTask___boxed(lean_object* v_00_u03b5_2409_, lean_object* v_00_u03b1_2410_, lean_object* v_x_2411_, lean_object* v_a_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Std_Async_EAsync_ofTask(v_00_u03b5_2409_, v_00_u03b1_2410_, v_x_2411_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toEIO___redArg(lean_object* v_x_2414_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = lean_apply_1(v_x_2414_, lean_box(0));
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2425_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2419_ = v___x_2416_;
v_isShared_2420_ = v_isSharedCheck_2425_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2416_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2425_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2421_; lean_object* v___x_2423_; 
v___x_2421_ = lean_task_pure(v_a_2417_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 0, v___x_2421_);
v___x_2423_ = v___x_2419_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2421_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
v_a_2426_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2416_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2416_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
lean_ctor_set_tag(v___x_2428_, 0);
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toEIO___redArg___boxed(lean_object* v_x_2434_, lean_object* v_a_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Std_Async_EAsync_toEIO___redArg(v_x_2434_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toEIO(lean_object* v_00_u03b5_2437_, lean_object* v_00_u03b1_2438_, lean_object* v_x_2439_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = lean_apply_1(v_x_2439_, lean_box(0));
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2450_; 
v_a_2442_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2444_ = v___x_2441_;
v_isShared_2445_ = v_isSharedCheck_2450_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2441_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2450_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2446_ = lean_task_pure(v_a_2442_);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 0, v___x_2446_);
v___x_2448_ = v___x_2444_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2446_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
v_a_2451_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2441_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2441_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
lean_ctor_set_tag(v___x_2453_, 0);
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_toEIO___boxed(lean_object* v_00_u03b5_2459_, lean_object* v_00_u03b1_2460_, lean_object* v_x_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Std_Async_EAsync_toEIO(v_00_u03b5_2459_, v_00_u03b1_2460_, v_x_2461_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofETask___redArg(lean_object* v_x_2464_){
_start:
{
lean_object* v___x_2466_; 
v___x_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2466_, 0, v_x_2464_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofETask___redArg___boxed(lean_object* v_x_2467_, lean_object* v_a_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l_Std_Async_EAsync_ofETask___redArg(v_x_2467_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofETask(lean_object* v_00_u03b5_2470_, lean_object* v_00_u03b1_2471_, lean_object* v_x_2472_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2474_, 0, v_x_2472_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofETask___boxed(lean_object* v_00_u03b5_2475_, lean_object* v_00_u03b1_2476_, lean_object* v_x_2477_, lean_object* v_a_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Std_Async_EAsync_ofETask(v_00_u03b5_2475_, v_00_u03b1_2476_, v_x_2477_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_pure___redArg(lean_object* v_a_2480_){
_start:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2482_, 0, v_a_2480_);
v___x_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_pure___redArg___boxed(lean_object* v_a_2484_, lean_object* v_a_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Std_Async_EAsync_pure___redArg(v_a_2484_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_pure(lean_object* v_00_u03b1_2487_, lean_object* v_00_u03b5_2488_, lean_object* v_a_2489_){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2491_, 0, v_a_2489_);
v___x_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2491_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_pure___boxed(lean_object* v_00_u03b1_2493_, lean_object* v_00_u03b5_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l_Std_Async_EAsync_pure(v_00_u03b1_2493_, v_00_u03b5_2494_, v_a_2495_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_map___redArg(lean_object* v_f_2498_, lean_object* v_self_2499_){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; lean_object* v___x_2504_; lean_object* v___y_2506_; 
lean_inc(v_f_2498_);
v___x_2501_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_2501_, 0, lean_box(0));
lean_closure_set(v___x_2501_, 1, lean_box(0));
lean_closure_set(v___x_2501_, 2, lean_box(0));
lean_closure_set(v___x_2501_, 3, v_f_2498_);
v___x_2502_ = lean_unsigned_to_nat(0u);
v___x_2503_ = 0;
v___x_2504_ = lean_apply_1(v_self_2499_, lean_box(0));
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2508_; 
lean_dec_ref(v___x_2501_);
v_a_2508_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2508_);
lean_dec_ref_known(v___x_2504_, 1);
if (lean_obj_tag(v_a_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
lean_dec(v_f_2498_);
v_a_2509_ = lean_ctor_get(v_a_2508_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v_a_2508_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v_a_2508_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v_a_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
v___y_2506_ = v___x_2514_;
goto v___jp_2505_;
}
}
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2525_; 
v_a_2517_ = lean_ctor_get(v_a_2508_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v_a_2508_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2519_ = v_a_2508_;
v_isShared_2520_ = v_isSharedCheck_2525_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v_a_2508_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2525_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2521_; lean_object* v___x_2523_; 
v___x_2521_ = lean_apply_1(v_f_2498_, v_a_2517_);
if (v_isShared_2520_ == 0)
{
lean_ctor_set(v___x_2519_, 0, v___x_2521_);
v___x_2523_ = v___x_2519_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
v___y_2506_ = v___x_2523_;
goto v___jp_2505_;
}
}
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2534_; 
lean_dec(v_f_2498_);
v_a_2526_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2528_ = v___x_2504_;
v_isShared_2529_ = v_isSharedCheck_2534_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2504_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2534_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2530_; lean_object* v___x_2532_; 
v___x_2530_ = lean_task_map(v___x_2501_, v_a_2526_, v___x_2502_, v___x_2503_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 0, v___x_2530_);
v___x_2532_ = v___x_2528_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2530_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
v___jp_2505_:
{
lean_object* v___x_2507_; 
v___x_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2507_, 0, v___y_2506_);
return v___x_2507_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_map___redArg___boxed(lean_object* v_f_2535_, lean_object* v_self_2536_, lean_object* v_a_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Std_Async_EAsync_map___redArg(v_f_2535_, v_self_2536_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_map(lean_object* v_00_u03b1_2539_, lean_object* v_00_u03b2_2540_, lean_object* v_00_u03b5_2541_, lean_object* v_f_2542_, lean_object* v_self_2543_){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; lean_object* v___x_2548_; lean_object* v___y_2550_; 
lean_inc(v_f_2542_);
v___x_2545_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_2545_, 0, lean_box(0));
lean_closure_set(v___x_2545_, 1, lean_box(0));
lean_closure_set(v___x_2545_, 2, lean_box(0));
lean_closure_set(v___x_2545_, 3, v_f_2542_);
v___x_2546_ = lean_unsigned_to_nat(0u);
v___x_2547_ = 0;
v___x_2548_ = lean_apply_1(v_self_2543_, lean_box(0));
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2552_; 
lean_dec_ref(v___x_2545_);
v_a_2552_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2552_);
lean_dec_ref_known(v___x_2548_, 1);
if (lean_obj_tag(v_a_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec(v_f_2542_);
v_a_2553_ = lean_ctor_get(v_a_2552_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v_a_2552_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v_a_2552_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v_a_2552_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
v___y_2550_ = v___x_2558_;
goto v___jp_2549_;
}
}
}
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2569_; 
v_a_2561_ = lean_ctor_get(v_a_2552_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v_a_2552_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2563_ = v_a_2552_;
v_isShared_2564_ = v_isSharedCheck_2569_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v_a_2552_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2569_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2565_; lean_object* v___x_2567_; 
v___x_2565_ = lean_apply_1(v_f_2542_, v_a_2561_);
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 0, v___x_2565_);
v___x_2567_ = v___x_2563_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2565_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
v___y_2550_ = v___x_2567_;
goto v___jp_2549_;
}
}
}
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2578_; 
lean_dec(v_f_2542_);
v_a_2570_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2572_ = v___x_2548_;
v_isShared_2573_ = v_isSharedCheck_2578_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2548_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2578_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2574_; lean_object* v___x_2576_; 
v___x_2574_ = lean_task_map(v___x_2545_, v_a_2570_, v___x_2546_, v___x_2547_);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 0, v___x_2574_);
v___x_2576_ = v___x_2572_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2574_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
v___jp_2549_:
{
lean_object* v___x_2551_; 
v___x_2551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2551_, 0, v___y_2550_);
return v___x_2551_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_map___boxed(lean_object* v_00_u03b1_2579_, lean_object* v_00_u03b2_2580_, lean_object* v_00_u03b5_2581_, lean_object* v_f_2582_, lean_object* v_self_2583_, lean_object* v_a_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Std_Async_EAsync_map(v_00_u03b1_2579_, v_00_u03b2_2580_, v_00_u03b5_2581_, v_f_2582_, v_self_2583_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind___redArg___lam__0(lean_object* v_f_2586_, lean_object* v_x_2587_){
_start:
{
if (lean_obj_tag(v_x_2587_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2597_; 
lean_dec_ref(v_f_2586_);
v_a_2589_ = lean_ctor_get(v_x_2587_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v_x_2587_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2591_ = v_x_2587_;
v_isShared_2592_ = v_isSharedCheck_2597_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v_x_2587_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2597_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
lean_object* v___x_2595_; 
v___x_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
return v___x_2595_;
}
}
}
else
{
lean_object* v_a_2598_; lean_object* v___x_2599_; 
v_a_2598_ = lean_ctor_get(v_x_2587_, 0);
lean_inc(v_a_2598_);
lean_dec_ref_known(v_x_2587_, 1);
v___x_2599_ = lean_apply_2(v_f_2586_, v_a_2598_, lean_box(0));
return v___x_2599_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind___redArg___lam__0___boxed(lean_object* v_f_2600_, lean_object* v_x_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l_Std_Async_EAsync_bind___redArg___lam__0(v_f_2600_, v_x_2601_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind___redArg(lean_object* v_self_2604_, lean_object* v_f_2605_){
_start:
{
lean_object* v___f_2607_; lean_object* v___x_2608_; uint8_t v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___f_2607_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_bind___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2607_, 0, v_f_2605_);
v___x_2608_ = lean_unsigned_to_nat(0u);
v___x_2609_ = 0;
v___x_2610_ = lean_apply_1(v_self_2604_, lean_box(0));
v___x_2611_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2608_, v___x_2609_, v___x_2610_, v___f_2607_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind___redArg___boxed(lean_object* v_self_2612_, lean_object* v_f_2613_, lean_object* v_a_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Std_Async_EAsync_bind___redArg(v_self_2612_, v_f_2613_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind(lean_object* v_00_u03b5_2616_, lean_object* v_00_u03b1_2617_, lean_object* v_00_u03b2_2618_, lean_object* v_self_2619_, lean_object* v_f_2620_){
_start:
{
lean_object* v___f_2622_; lean_object* v___x_2623_; uint8_t v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___f_2622_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_bind___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2622_, 0, v_f_2620_);
v___x_2623_ = lean_unsigned_to_nat(0u);
v___x_2624_ = 0;
v___x_2625_ = lean_apply_1(v_self_2619_, lean_box(0));
v___x_2626_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2623_, v___x_2624_, v___x_2625_, v___f_2622_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_bind___boxed(lean_object* v_00_u03b5_2627_, lean_object* v_00_u03b1_2628_, lean_object* v_00_u03b2_2629_, lean_object* v_self_2630_, lean_object* v_f_2631_, lean_object* v_a_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Std_Async_EAsync_bind(v_00_u03b5_2627_, v_00_u03b1_2628_, v_00_u03b2_2629_, v_self_2630_, v_f_2631_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_lift___redArg(lean_object* v_x_2634_){
_start:
{
lean_object* v_val_2637_; lean_object* v___x_2639_; 
v___x_2639_ = lean_apply_1(v_x_2634_, lean_box(0));
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2642_ = v___x_2639_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2639_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
lean_ctor_set_tag(v___x_2642_, 1);
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
v_val_2637_ = v___x_2645_;
goto v___jp_2636_;
}
}
}
else
{
lean_object* v_a_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2655_; 
v_a_2648_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2650_ = v___x_2639_;
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_a_2648_);
lean_dec(v___x_2639_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2653_; 
if (v_isShared_2651_ == 0)
{
lean_ctor_set_tag(v___x_2650_, 0);
v___x_2653_ = v___x_2650_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_a_2648_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
v_val_2637_ = v___x_2653_;
goto v___jp_2636_;
}
}
}
v___jp_2636_:
{
lean_object* v___x_2638_; 
v___x_2638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2638_, 0, v_val_2637_);
return v___x_2638_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_lift___redArg___boxed(lean_object* v_x_2656_, lean_object* v_a_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l_Std_Async_EAsync_lift___redArg(v_x_2656_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_lift(lean_object* v_00_u03b5_2659_, lean_object* v_00_u03b1_2660_, lean_object* v_x_2661_){
_start:
{
lean_object* v_val_2664_; lean_object* v___x_2666_; 
v___x_2666_ = lean_apply_1(v_x_2661_, lean_box(0));
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2666_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2666_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
lean_ctor_set_tag(v___x_2669_, 1);
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
v_val_2664_ = v___x_2672_;
goto v___jp_2663_;
}
}
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
v_a_2675_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2666_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2666_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
lean_ctor_set_tag(v___x_2677_, 0);
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
v_val_2664_ = v___x_2680_;
goto v___jp_2663_;
}
}
}
v___jp_2663_:
{
lean_object* v___x_2665_; 
v___x_2665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2665_, 0, v_val_2664_);
return v___x_2665_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_lift___boxed(lean_object* v_00_u03b5_2683_, lean_object* v_00_u03b1_2684_, lean_object* v_x_2685_, lean_object* v_a_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Std_Async_EAsync_lift(v_00_u03b5_2683_, v_00_u03b1_2684_, v_x_2685_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_wait___redArg(lean_object* v_self_2688_){
_start:
{
lean_object* v_val_2691_; lean_object* v___x_2709_; 
v___x_2709_ = lean_apply_1(v_self_2688_, lean_box(0));
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2711_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_a_2710_);
lean_dec_ref_known(v___x_2709_, 1);
v___x_2711_ = lean_task_pure(v_a_2710_);
v_val_2691_ = v___x_2711_;
goto v___jp_2690_;
}
else
{
lean_object* v_a_2712_; 
v_a_2712_ = lean_ctor_get(v___x_2709_, 0);
lean_inc_ref(v_a_2712_);
lean_dec_ref_known(v___x_2709_, 1);
v_val_2691_ = v_a_2712_;
goto v___jp_2690_;
}
v___jp_2690_:
{
lean_object* v___x_2692_; 
v___x_2692_ = lean_task_get_own(v_val_2691_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v___x_2692_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2692_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
lean_ctor_set_tag(v___x_2695_, 1);
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2693_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
else
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2708_; 
v_a_2701_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2703_ = v___x_2692_;
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2692_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2706_; 
if (v_isShared_2704_ == 0)
{
lean_ctor_set_tag(v___x_2703_, 0);
v___x_2706_ = v___x_2703_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_a_2701_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_wait___redArg___boxed(lean_object* v_self_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_Std_Async_EAsync_wait___redArg(v_self_2713_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_wait(lean_object* v_00_u03b5_2716_, lean_object* v_00_u03b1_2717_, lean_object* v_self_2718_){
_start:
{
lean_object* v_val_2721_; lean_object* v___x_2739_; 
v___x_2739_ = lean_apply_1(v_self_2718_, lean_box(0));
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v_a_2740_; lean_object* v___x_2741_; 
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
lean_inc(v_a_2740_);
lean_dec_ref_known(v___x_2739_, 1);
v___x_2741_ = lean_task_pure(v_a_2740_);
v_val_2721_ = v___x_2741_;
goto v___jp_2720_;
}
else
{
lean_object* v_a_2742_; 
v_a_2742_ = lean_ctor_get(v___x_2739_, 0);
lean_inc_ref(v_a_2742_);
lean_dec_ref_known(v___x_2739_, 1);
v_val_2721_ = v_a_2742_;
goto v___jp_2720_;
}
v___jp_2720_:
{
lean_object* v___x_2722_; 
v___x_2722_ = lean_task_get_own(v_val_2721_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2722_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2722_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
lean_ctor_set_tag(v___x_2725_, 1);
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2738_; 
v_a_2731_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2733_ = v___x_2722_;
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2722_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2736_; 
if (v_isShared_2734_ == 0)
{
lean_ctor_set_tag(v___x_2733_, 0);
v___x_2736_ = v___x_2733_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_a_2731_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_wait___boxed(lean_object* v_00_u03b5_2743_, lean_object* v_00_u03b1_2744_, lean_object* v_self_2745_, lean_object* v_a_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Std_Async_EAsync_wait(v_00_u03b5_2743_, v_00_u03b1_2744_, v_self_2745_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_asTask___redArg___lam__0(lean_object* v_x_2748_){
_start:
{
if (lean_obj_tag(v_x_2748_) == 0)
{
lean_object* v_a_2749_; lean_object* v___x_2750_; 
v_a_2749_ = lean_ctor_get(v_x_2748_, 0);
lean_inc(v_a_2749_);
lean_dec_ref_known(v_x_2748_, 1);
v___x_2750_ = lean_task_pure(v_a_2749_);
return v___x_2750_;
}
else
{
lean_object* v_a_2751_; 
v_a_2751_ = lean_ctor_get(v_x_2748_, 0);
lean_inc_ref(v_a_2751_);
lean_dec_ref_known(v_x_2748_, 1);
return v_a_2751_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_asTask___redArg(lean_object* v_x_2753_, lean_object* v_prio_2754_){
_start:
{
lean_object* v___f_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; uint8_t v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___f_2756_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___x_2757_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2757_, 0, lean_box(0));
lean_closure_set(v___x_2757_, 1, v_x_2753_);
v___x_2758_ = lean_io_as_task(v___x_2757_, v_prio_2754_);
v___x_2759_ = lean_unsigned_to_nat(0u);
v___x_2760_ = 1;
v___x_2761_ = lean_task_bind(v___x_2758_, v___f_2756_, v___x_2759_, v___x_2760_);
v___x_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2761_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_asTask___redArg___boxed(lean_object* v_x_2763_, lean_object* v_prio_2764_, lean_object* v_a_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l_Std_Async_EAsync_asTask___redArg(v_x_2763_, v_prio_2764_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_asTask(lean_object* v_00_u03b5_2767_, lean_object* v_00_u03b1_2768_, lean_object* v_x_2769_, lean_object* v_prio_2770_){
_start:
{
lean_object* v___f_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; uint8_t v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___f_2772_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___x_2773_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2773_, 0, lean_box(0));
lean_closure_set(v___x_2773_, 1, v_x_2769_);
v___x_2774_ = lean_io_as_task(v___x_2773_, v_prio_2770_);
v___x_2775_ = lean_unsigned_to_nat(0u);
v___x_2776_ = 1;
v___x_2777_ = lean_task_bind(v___x_2774_, v___f_2772_, v___x_2775_, v___x_2776_);
v___x_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2777_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_asTask___boxed(lean_object* v_00_u03b5_2779_, lean_object* v_00_u03b1_2780_, lean_object* v_x_2781_, lean_object* v_prio_2782_, lean_object* v_a_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l_Std_Async_EAsync_asTask(v_00_u03b5_2779_, v_00_u03b1_2780_, v_x_2781_, v_prio_2782_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_block___redArg(lean_object* v_x_2785_, lean_object* v_prio_2786_){
_start:
{
lean_object* v___f_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; uint8_t v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___f_2788_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___x_2789_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2789_, 0, lean_box(0));
lean_closure_set(v___x_2789_, 1, v_x_2785_);
v___x_2790_ = lean_io_as_task(v___x_2789_, v_prio_2786_);
v___x_2791_ = lean_unsigned_to_nat(0u);
v___x_2792_ = 1;
v___x_2793_ = lean_task_bind(v___x_2790_, v___f_2788_, v___x_2791_, v___x_2792_);
v___x_2794_ = lean_task_get_own(v___x_2793_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2794_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2794_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
lean_ctor_set_tag(v___x_2797_, 1);
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
v_a_2803_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2805_ = v___x_2794_;
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2794_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
lean_ctor_set_tag(v___x_2805_, 0);
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2803_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_block___redArg___boxed(lean_object* v_x_2811_, lean_object* v_prio_2812_, lean_object* v_a_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Std_Async_EAsync_block___redArg(v_x_2811_, v_prio_2812_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_block(lean_object* v_00_u03b5_2815_, lean_object* v_00_u03b1_2816_, lean_object* v_x_2817_, lean_object* v_prio_2818_){
_start:
{
lean_object* v___f_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; uint8_t v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___f_2820_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___x_2821_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2821_, 0, lean_box(0));
lean_closure_set(v___x_2821_, 1, v_x_2817_);
v___x_2822_ = lean_io_as_task(v___x_2821_, v_prio_2818_);
v___x_2823_ = lean_unsigned_to_nat(0u);
v___x_2824_ = 1;
v___x_2825_ = lean_task_bind(v___x_2822_, v___f_2820_, v___x_2823_, v___x_2824_);
v___x_2826_ = lean_task_get_own(v___x_2825_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2826_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2826_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
lean_ctor_set_tag(v___x_2829_, 1);
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
v_a_2835_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2826_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2826_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
lean_ctor_set_tag(v___x_2837_, 0);
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_block___boxed(lean_object* v_00_u03b5_2843_, lean_object* v_00_u03b1_2844_, lean_object* v_x_2845_, lean_object* v_prio_2846_, lean_object* v_a_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Std_Async_EAsync_block(v_00_u03b5_2843_, v_00_u03b1_2844_, v_x_2845_, v_prio_2846_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_throw___redArg(lean_object* v_e_2849_){
_start:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2851_, 0, v_e_2849_);
v___x_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2851_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_throw___redArg___boxed(lean_object* v_e_2853_, lean_object* v_a_2854_){
_start:
{
lean_object* v_res_2855_; 
v_res_2855_ = l_Std_Async_EAsync_throw___redArg(v_e_2853_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_throw(lean_object* v_00_u03b5_2856_, lean_object* v_00_u03b1_2857_, lean_object* v_e_2858_){
_start:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2860_, 0, v_e_2858_);
v___x_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2860_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_throw___boxed(lean_object* v_00_u03b5_2862_, lean_object* v_00_u03b1_2863_, lean_object* v_e_2864_, lean_object* v_a_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l_Std_Async_EAsync_throw(v_00_u03b5_2862_, v_00_u03b1_2863_, v_e_2864_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch___redArg___lam__0(lean_object* v_f_2867_, lean_object* v_x_2868_){
_start:
{
if (lean_obj_tag(v_x_2868_) == 0)
{
lean_object* v_a_2870_; lean_object* v___x_2871_; 
v_a_2870_ = lean_ctor_get(v_x_2868_, 0);
lean_inc(v_a_2870_);
lean_dec_ref_known(v_x_2868_, 1);
v___x_2871_ = lean_apply_2(v_f_2867_, v_a_2870_, lean_box(0));
return v___x_2871_;
}
else
{
lean_object* v___x_2872_; 
lean_dec_ref(v_f_2867_);
v___x_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2872_, 0, v_x_2868_);
return v___x_2872_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch___redArg___lam__0___boxed(lean_object* v_f_2873_, lean_object* v_x_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v_res_2876_; 
v_res_2876_ = l_Std_Async_EAsync_tryCatch___redArg___lam__0(v_f_2873_, v_x_2874_);
return v_res_2876_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch___redArg(lean_object* v_x_2877_, lean_object* v_f_2878_, lean_object* v_prio_2879_, uint8_t v_sync_2880_){
_start:
{
lean_object* v___f_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___f_2882_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_tryCatch___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2882_, 0, v_f_2878_);
v___x_2883_ = lean_apply_1(v_x_2877_, lean_box(0));
v___x_2884_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_2879_, v_sync_2880_, v___x_2883_, v___f_2882_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch___redArg___boxed(lean_object* v_x_2885_, lean_object* v_f_2886_, lean_object* v_prio_2887_, lean_object* v_sync_2888_, lean_object* v_a_2889_){
_start:
{
uint8_t v_sync_boxed_2890_; lean_object* v_res_2891_; 
v_sync_boxed_2890_ = lean_unbox(v_sync_2888_);
v_res_2891_ = l_Std_Async_EAsync_tryCatch___redArg(v_x_2885_, v_f_2886_, v_prio_2887_, v_sync_boxed_2890_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch(lean_object* v_00_u03b5_2892_, lean_object* v_00_u03b1_2893_, lean_object* v_x_2894_, lean_object* v_f_2895_, lean_object* v_prio_2896_, uint8_t v_sync_2897_){
_start:
{
lean_object* v___f_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___f_2899_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_tryCatch___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2899_, 0, v_f_2895_);
v___x_2900_ = lean_apply_1(v_x_2894_, lean_box(0));
v___x_2901_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_2896_, v_sync_2897_, v___x_2900_, v___f_2899_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryCatch___boxed(lean_object* v_00_u03b5_2902_, lean_object* v_00_u03b1_2903_, lean_object* v_x_2904_, lean_object* v_f_2905_, lean_object* v_prio_2906_, lean_object* v_sync_2907_, lean_object* v_a_2908_){
_start:
{
uint8_t v_sync_boxed_2909_; lean_object* v_res_2910_; 
v_sync_boxed_2909_ = lean_unbox(v_sync_2907_);
v_res_2910_ = l_Std_Async_EAsync_tryCatch(v_00_u03b5_2902_, v_00_u03b1_2903_, v_x_2904_, v_f_2905_, v_prio_2906_, v_sync_boxed_2909_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__0(lean_object* v_a_2911_, lean_object* v_____do__lift_2912_){
_start:
{
if (lean_obj_tag(v_____do__lift_2912_) == 0)
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2922_; 
lean_dec(v_a_2911_);
v_a_2914_ = lean_ctor_get(v_____do__lift_2912_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v_____do__lift_2912_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2916_ = v_____do__lift_2912_;
v_isShared_2917_ = v_isSharedCheck_2922_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v_____do__lift_2912_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2922_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2914_);
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
else
{
lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2930_; 
v_isSharedCheck_2930_ = !lean_is_exclusive(v_____do__lift_2912_);
if (v_isSharedCheck_2930_ == 0)
{
lean_object* v_unused_2931_; 
v_unused_2931_ = lean_ctor_get(v_____do__lift_2912_, 0);
lean_dec(v_unused_2931_);
v___x_2924_ = v_____do__lift_2912_;
v_isShared_2925_ = v_isSharedCheck_2930_;
goto v_resetjp_2923_;
}
else
{
lean_dec(v_____do__lift_2912_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2930_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
lean_ctor_set_tag(v___x_2924_, 0);
lean_ctor_set(v___x_2924_, 0, v_a_2911_);
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2911_);
v___x_2927_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
lean_object* v___x_2928_; 
v___x_2928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2927_);
return v___x_2928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__0___boxed(lean_object* v_a_2932_, lean_object* v_____do__lift_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l_Std_Async_EAsync_tryFinally_x27___redArg___lam__0(v_a_2932_, v_____do__lift_2933_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__1(lean_object* v_a_2936_, lean_object* v_____do__lift_2937_){
_start:
{
if (lean_obj_tag(v_____do__lift_2937_) == 0)
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2947_; 
lean_dec(v_a_2936_);
v_a_2939_ = lean_ctor_get(v_____do__lift_2937_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v_____do__lift_2937_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2941_ = v_____do__lift_2937_;
v_isShared_2942_ = v_isSharedCheck_2947_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v_____do__lift_2937_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2947_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2939_);
v___x_2944_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
lean_object* v___x_2945_; 
v___x_2945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2944_);
return v___x_2945_;
}
}
}
else
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2957_; 
v_a_2948_ = lean_ctor_get(v_____do__lift_2937_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v_____do__lift_2937_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2950_ = v_____do__lift_2937_;
v_isShared_2951_ = v_isSharedCheck_2957_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v_____do__lift_2937_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2957_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2952_; lean_object* v___x_2954_; 
v___x_2952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2952_, 0, v_a_2936_);
lean_ctor_set(v___x_2952_, 1, v_a_2948_);
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 0, v___x_2952_);
v___x_2954_ = v___x_2950_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v___x_2952_);
v___x_2954_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_object* v___x_2955_; 
v___x_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
return v___x_2955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__1___boxed(lean_object* v_a_2958_, lean_object* v_____do__lift_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_Std_Async_EAsync_tryFinally_x27___redArg___lam__1(v_a_2958_, v_____do__lift_2959_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__2(lean_object* v_f_2962_, lean_object* v_x_2963_){
_start:
{
if (lean_obj_tag(v_x_2963_) == 0)
{
lean_object* v_a_2965_; lean_object* v___f_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; uint8_t v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v_a_2965_ = lean_ctor_get(v_x_2963_, 0);
lean_inc(v_a_2965_);
lean_dec_ref_known(v_x_2963_, 1);
v___f_2966_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_tryFinally_x27___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2966_, 0, v_a_2965_);
v___x_2967_ = lean_box(0);
v___x_2968_ = lean_unsigned_to_nat(0u);
v___x_2969_ = 0;
v___x_2970_ = lean_apply_2(v_f_2962_, v___x_2967_, lean_box(0));
v___x_2971_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2968_, v___x_2969_, v___x_2970_, v___f_2966_);
return v___x_2971_;
}
else
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2984_; 
v_a_2972_ = lean_ctor_get(v_x_2963_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v_x_2963_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2974_ = v_x_2963_;
v_isShared_2975_ = v_isSharedCheck_2984_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v_x_2963_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2984_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___f_2976_; lean_object* v___x_2978_; 
lean_inc(v_a_2972_);
v___f_2976_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_tryFinally_x27___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2976_, 0, v_a_2972_);
if (v_isShared_2975_ == 0)
{
v___x_2978_ = v___x_2974_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_a_2972_);
v___x_2978_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
lean_object* v___x_2979_; uint8_t v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2979_ = lean_unsigned_to_nat(0u);
v___x_2980_ = 0;
v___x_2981_ = lean_apply_2(v_f_2962_, v___x_2978_, lean_box(0));
v___x_2982_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_2979_, v___x_2980_, v___x_2981_, v___f_2976_);
return v___x_2982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___lam__2___boxed(lean_object* v_f_2985_, lean_object* v_x_2986_, lean_object* v___y_2987_){
_start:
{
lean_object* v_res_2988_; 
v_res_2988_ = l_Std_Async_EAsync_tryFinally_x27___redArg___lam__2(v_f_2985_, v_x_2986_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg(lean_object* v_x_2989_, lean_object* v_f_2990_, lean_object* v_prio_2991_, uint8_t v_sync_2992_){
_start:
{
lean_object* v___f_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___f_2994_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_tryFinally_x27___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2994_, 0, v_f_2990_);
v___x_2995_ = lean_apply_1(v_x_2989_, lean_box(0));
v___x_2996_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v_prio_2991_, v_sync_2992_, v___x_2995_, v___f_2994_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg___boxed(lean_object* v_x_2997_, lean_object* v_f_2998_, lean_object* v_prio_2999_, lean_object* v_sync_3000_, lean_object* v_a_3001_){
_start:
{
uint8_t v_sync_boxed_3002_; lean_object* v_res_3003_; 
v_sync_boxed_3002_ = lean_unbox(v_sync_3000_);
v_res_3003_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v_x_2997_, v_f_2998_, v_prio_2999_, v_sync_boxed_3002_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27(lean_object* v_00_u03b5_3004_, lean_object* v_00_u03b1_3005_, lean_object* v_00_u03b2_3006_, lean_object* v_x_3007_, lean_object* v_f_3008_, lean_object* v_prio_3009_, uint8_t v_sync_3010_){
_start:
{
lean_object* v___x_3012_; 
v___x_3012_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v_x_3007_, v_f_3008_, v_prio_3009_, v_sync_3010_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_tryFinally_x27___boxed(lean_object* v_00_u03b5_3013_, lean_object* v_00_u03b1_3014_, lean_object* v_00_u03b2_3015_, lean_object* v_x_3016_, lean_object* v_f_3017_, lean_object* v_prio_3018_, lean_object* v_sync_3019_, lean_object* v_a_3020_){
_start:
{
uint8_t v_sync_boxed_3021_; lean_object* v_res_3022_; 
v_sync_boxed_3021_ = lean_unbox(v_sync_3019_);
v_res_3022_ = l_Std_Async_EAsync_tryFinally_x27(v_00_u03b5_3013_, v_00_u03b1_3014_, v_00_u03b2_3015_, v_x_3016_, v_f_3017_, v_prio_3018_, v_sync_boxed_3021_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_await___redArg(lean_object* v_x_3023_){
_start:
{
lean_object* v___x_3025_; 
v___x_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3025_, 0, v_x_3023_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_await___redArg___boxed(lean_object* v_x_3026_, lean_object* v_a_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Std_Async_EAsync_await___redArg(v_x_3026_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_await(lean_object* v_00_u03b5_3029_, lean_object* v_00_u03b1_3030_, lean_object* v_x_3031_){
_start:
{
lean_object* v___x_3033_; 
v___x_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3033_, 0, v_x_3031_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_await___boxed(lean_object* v_00_u03b5_3034_, lean_object* v_00_u03b1_3035_, lean_object* v_x_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Std_Async_EAsync_await(v_00_u03b5_3034_, v_00_u03b1_3035_, v_x_3036_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_async___redArg(lean_object* v_self_3039_, lean_object* v_prio_3040_){
_start:
{
lean_object* v___f_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; uint8_t v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___f_3042_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___x_3043_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_3043_, 0, lean_box(0));
lean_closure_set(v___x_3043_, 1, v_self_3039_);
v___x_3044_ = lean_io_as_task(v___x_3043_, v_prio_3040_);
v___x_3045_ = lean_unsigned_to_nat(0u);
v___x_3046_ = 1;
v___x_3047_ = lean_task_bind(v___x_3044_, v___f_3042_, v___x_3045_, v___x_3046_);
v___x_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3047_);
v___x_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_async___redArg___boxed(lean_object* v_self_3050_, lean_object* v_prio_3051_, lean_object* v_a_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l_Std_Async_EAsync_async___redArg(v_self_3050_, v_prio_3051_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_async(lean_object* v_00_u03b5_3054_, lean_object* v_00_u03b1_3055_, lean_object* v_self_3056_, lean_object* v_prio_3057_){
_start:
{
lean_object* v___f_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; uint8_t v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___f_3059_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___x_3060_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_3060_, 0, lean_box(0));
lean_closure_set(v___x_3060_, 1, v_self_3056_);
v___x_3061_ = lean_io_as_task(v___x_3060_, v_prio_3057_);
v___x_3062_ = lean_unsigned_to_nat(0u);
v___x_3063_ = 1;
v___x_3064_ = lean_task_bind(v___x_3061_, v___f_3059_, v___x_3062_, v___x_3063_);
v___x_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3064_);
v___x_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_async___boxed(lean_object* v_00_u03b5_3067_, lean_object* v_00_u03b1_3068_, lean_object* v_self_3069_, lean_object* v_prio_3070_, lean_object* v_a_3071_){
_start:
{
lean_object* v_res_3072_; 
v_res_3072_ = l_Std_Async_EAsync_async(v_00_u03b5_3067_, v_00_u03b1_3068_, v_self_3069_, v_prio_3070_);
return v_res_3072_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___redArg___lam__0(lean_object* v_00_u03b1_3073_, lean_object* v_00_u03b2_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; uint8_t v___x_3080_; lean_object* v___x_3081_; lean_object* v___y_3083_; 
lean_inc(v___y_3075_);
v___x_3078_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_3078_, 0, lean_box(0));
lean_closure_set(v___x_3078_, 1, lean_box(0));
lean_closure_set(v___x_3078_, 2, lean_box(0));
lean_closure_set(v___x_3078_, 3, v___y_3075_);
v___x_3079_ = lean_unsigned_to_nat(0u);
v___x_3080_ = 0;
v___x_3081_ = lean_apply_1(v___y_3076_, lean_box(0));
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v_a_3085_; 
lean_dec_ref(v___x_3078_);
v_a_3085_ = lean_ctor_get(v___x_3081_, 0);
lean_inc(v_a_3085_);
lean_dec_ref_known(v___x_3081_, 1);
if (lean_obj_tag(v_a_3085_) == 0)
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
lean_dec(v___y_3075_);
v_a_3086_ = lean_ctor_get(v_a_3085_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v_a_3085_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v_a_3085_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v_a_3085_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3089_ == 0)
{
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
v___y_3083_ = v___x_3091_;
goto v___jp_3082_;
}
}
}
else
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3102_; 
v_a_3094_ = lean_ctor_get(v_a_3085_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v_a_3085_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3096_ = v_a_3085_;
v_isShared_3097_ = v_isSharedCheck_3102_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v_a_3085_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3102_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3098_; lean_object* v___x_3100_; 
v___x_3098_ = lean_apply_1(v___y_3075_, v_a_3094_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 0, v___x_3098_);
v___x_3100_ = v___x_3096_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3098_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
v___y_3083_ = v___x_3100_;
goto v___jp_3082_;
}
}
}
}
else
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3111_; 
lean_dec(v___y_3075_);
v_a_3103_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3105_ = v___x_3081_;
v_isShared_3106_ = v_isSharedCheck_3111_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3081_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3111_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3107_; lean_object* v___x_3109_; 
v___x_3107_ = lean_task_map(v___x_3078_, v_a_3103_, v___x_3079_, v___x_3080_);
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 0, v___x_3107_);
v___x_3109_ = v___x_3105_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3107_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
v___jp_3082_:
{
lean_object* v___x_3084_; 
v___x_3084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3084_, 0, v___y_3083_);
return v___x_3084_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___redArg___lam__0___boxed(lean_object* v_00_u03b1_3112_, lean_object* v_00_u03b2_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l_Std_Async_EAsync_instFunctor___redArg___lam__0(v_00_u03b1_3112_, v_00_u03b2_3113_, v___y_3114_, v___y_3115_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___redArg___lam__1(lean_object* v___f_3118_, lean_object* v_00_u03b1_3119_, lean_object* v_00_u03b2_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3124_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_3124_, 0, lean_box(0));
lean_closure_set(v___x_3124_, 1, lean_box(0));
lean_closure_set(v___x_3124_, 2, v___y_3121_);
v___x_3125_ = lean_apply_5(v___f_3118_, lean_box(0), lean_box(0), v___x_3124_, v___y_3122_, lean_box(0));
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___redArg___lam__1___boxed(lean_object* v___f_3126_, lean_object* v_00_u03b1_3127_, lean_object* v_00_u03b2_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
lean_object* v_res_3132_; 
v_res_3132_ = l_Std_Async_EAsync_instFunctor___redArg___lam__1(v___f_3126_, v_00_u03b1_3127_, v_00_u03b2_3128_, v___y_3129_, v___y_3130_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___redArg(){
_start:
{
lean_object* v___x_3140_; 
v___x_3140_ = ((lean_object*)(l_Std_Async_EAsync_instFunctor___redArg___closed__2));
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor___redArg___boxed(lean_object* v___dummy_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l_Std_Async_EAsync_instFunctor___redArg();
return v_res_3142_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instFunctor___closed__0(void){
_start:
{
lean_object* v___x_3143_; 
v___x_3143_ = l_Std_Async_EAsync_instFunctor___redArg();
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instFunctor(lean_object* v_00_u03b5_3144_){
_start:
{
lean_object* v___x_3145_; 
v___x_3145_ = lean_obj_once(&l_Std_Async_EAsync_instFunctor___closed__0, &l_Std_Async_EAsync_instFunctor___closed__0_once, _init_l_Std_Async_EAsync_instFunctor___closed__0);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__0(lean_object* v_00_u03b1_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3149_, 0, v___y_3147_);
v___x_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__0___boxed(lean_object* v_00_u03b1_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l_Std_Async_EAsync_instMonad___redArg___lam__0(v_00_u03b1_3151_, v___y_3152_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__1(lean_object* v_x_3155_, lean_object* v_x_3156_){
_start:
{
if (lean_obj_tag(v_x_3156_) == 0)
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3166_; 
lean_dec_ref(v_x_3155_);
v_a_3158_ = lean_ctor_get(v_x_3156_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v_x_3156_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3160_ = v_x_3156_;
v_isShared_3161_ = v_isSharedCheck_3166_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v_x_3156_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3166_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3163_; 
if (v_isShared_3161_ == 0)
{
v___x_3163_ = v___x_3160_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_a_3158_);
v___x_3163_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
lean_object* v___x_3164_; 
v___x_3164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3163_);
return v___x_3164_;
}
}
}
else
{
lean_object* v_a_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; uint8_t v___x_3171_; lean_object* v___x_3172_; lean_object* v___y_3174_; 
v_a_3167_ = lean_ctor_get(v_x_3156_, 0);
lean_inc_n(v_a_3167_, 2);
lean_dec_ref_known(v_x_3156_, 1);
v___x_3168_ = lean_box(0);
v___x_3169_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_3169_, 0, lean_box(0));
lean_closure_set(v___x_3169_, 1, lean_box(0));
lean_closure_set(v___x_3169_, 2, lean_box(0));
lean_closure_set(v___x_3169_, 3, v_a_3167_);
v___x_3170_ = lean_unsigned_to_nat(0u);
v___x_3171_ = 0;
v___x_3172_ = lean_apply_2(v_x_3155_, v___x_3168_, lean_box(0));
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v_a_3176_; 
lean_dec_ref(v___x_3169_);
v_a_3176_ = lean_ctor_get(v___x_3172_, 0);
lean_inc(v_a_3176_);
lean_dec_ref_known(v___x_3172_, 1);
if (lean_obj_tag(v_a_3176_) == 0)
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
lean_dec(v_a_3167_);
v_a_3177_ = lean_ctor_get(v_a_3176_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v_a_3176_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v_a_3176_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v_a_3176_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
v___y_3174_ = v___x_3182_;
goto v___jp_3173_;
}
}
}
else
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3193_; 
v_a_3185_ = lean_ctor_get(v_a_3176_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v_a_3176_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3187_ = v_a_3176_;
v_isShared_3188_ = v_isSharedCheck_3193_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v_a_3176_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3193_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___x_3189_; lean_object* v___x_3191_; 
v___x_3189_ = lean_apply_1(v_a_3167_, v_a_3185_);
if (v_isShared_3188_ == 0)
{
lean_ctor_set(v___x_3187_, 0, v___x_3189_);
v___x_3191_ = v___x_3187_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3189_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
v___y_3174_ = v___x_3191_;
goto v___jp_3173_;
}
}
}
}
else
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3202_; 
lean_dec(v_a_3167_);
v_a_3194_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3196_ = v___x_3172_;
v_isShared_3197_ = v_isSharedCheck_3202_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3172_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3202_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3198_; lean_object* v___x_3200_; 
v___x_3198_ = lean_task_map(v___x_3169_, v_a_3194_, v___x_3170_, v___x_3171_);
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 0, v___x_3198_);
v___x_3200_ = v___x_3196_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_3198_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
v___jp_3173_:
{
lean_object* v___x_3175_; 
v___x_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3175_, 0, v___y_3174_);
return v___x_3175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__1___boxed(lean_object* v_x_3203_, lean_object* v_x_3204_, lean_object* v___y_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l_Std_Async_EAsync_instMonad___redArg___lam__1(v_x_3203_, v_x_3204_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__2(lean_object* v_00_u03b1_3207_, lean_object* v_00_u03b2_3208_, lean_object* v_f_3209_, lean_object* v_x_3210_){
_start:
{
lean_object* v___f_3212_; lean_object* v___x_3213_; uint8_t v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___f_3212_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_instMonad___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3212_, 0, v_x_3210_);
v___x_3213_ = lean_unsigned_to_nat(0u);
v___x_3214_ = 0;
v___x_3215_ = lean_apply_1(v_f_3209_, lean_box(0));
v___x_3216_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3213_, v___x_3214_, v___x_3215_, v___f_3212_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__2___boxed(lean_object* v_00_u03b1_3217_, lean_object* v_00_u03b2_3218_, lean_object* v_f_3219_, lean_object* v_x_3220_, lean_object* v___y_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l_Std_Async_EAsync_instMonad___redArg___lam__2(v_00_u03b1_3217_, v_00_u03b2_3218_, v_f_3219_, v_x_3220_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__3(lean_object* v___f_3223_, lean_object* v_a_3224_, lean_object* v_x_3225_){
_start:
{
if (lean_obj_tag(v_x_3225_) == 0)
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3235_; 
lean_dec(v_a_3224_);
lean_dec_ref(v___f_3223_);
v_a_3227_ = lean_ctor_get(v_x_3225_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v_x_3225_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3229_ = v_x_3225_;
v_isShared_3230_ = v_isSharedCheck_3235_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v_x_3225_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3235_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_a_3227_);
v___x_3232_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
lean_object* v___x_3233_; 
v___x_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3232_);
return v___x_3233_;
}
}
}
else
{
lean_object* v___x_3236_; 
lean_dec_ref_known(v_x_3225_, 1);
v___x_3236_ = lean_apply_3(v___f_3223_, lean_box(0), v_a_3224_, lean_box(0));
return v___x_3236_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__3___boxed(lean_object* v___f_3237_, lean_object* v_a_3238_, lean_object* v_x_3239_, lean_object* v___y_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l_Std_Async_EAsync_instMonad___redArg___lam__3(v___f_3237_, v_a_3238_, v_x_3239_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__4(lean_object* v___f_3242_, lean_object* v_y_3243_, lean_object* v_x_3244_){
_start:
{
if (lean_obj_tag(v_x_3244_) == 0)
{
lean_object* v___x_3246_; 
lean_dec_ref(v_y_3243_);
lean_dec_ref(v___f_3242_);
v___x_3246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3246_, 0, v_x_3244_);
return v___x_3246_;
}
else
{
lean_object* v_a_3247_; lean_object* v___f_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; uint8_t v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v_a_3247_ = lean_ctor_get(v_x_3244_, 0);
lean_inc(v_a_3247_);
lean_dec_ref_known(v_x_3244_, 1);
v___f_3248_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_instMonad___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_3248_, 0, v___f_3242_);
lean_closure_set(v___f_3248_, 1, v_a_3247_);
v___x_3249_ = lean_box(0);
v___x_3250_ = lean_unsigned_to_nat(0u);
v___x_3251_ = 0;
v___x_3252_ = lean_apply_2(v_y_3243_, v___x_3249_, lean_box(0));
v___x_3253_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3250_, v___x_3251_, v___x_3252_, v___f_3248_);
return v___x_3253_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__4___boxed(lean_object* v___f_3254_, lean_object* v_y_3255_, lean_object* v_x_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l_Std_Async_EAsync_instMonad___redArg___lam__4(v___f_3254_, v_y_3255_, v_x_3256_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__5(lean_object* v___f_3259_, lean_object* v_00_u03b1_3260_, lean_object* v_00_u03b2_3261_, lean_object* v_x_3262_, lean_object* v_y_3263_){
_start:
{
lean_object* v___f_3265_; lean_object* v___x_3266_; uint8_t v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___f_3265_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_instMonad___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_3265_, 0, v___f_3259_);
lean_closure_set(v___f_3265_, 1, v_y_3263_);
v___x_3266_ = lean_unsigned_to_nat(0u);
v___x_3267_ = 0;
v___x_3268_ = lean_apply_1(v_x_3262_, lean_box(0));
v___x_3269_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3266_, v___x_3267_, v___x_3268_, v___f_3265_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__5___boxed(lean_object* v___f_3270_, lean_object* v_00_u03b1_3271_, lean_object* v_00_u03b2_3272_, lean_object* v_x_3273_, lean_object* v_y_3274_, lean_object* v___y_3275_){
_start:
{
lean_object* v_res_3276_; 
v_res_3276_ = l_Std_Async_EAsync_instMonad___redArg___lam__5(v___f_3270_, v_00_u03b1_3271_, v_00_u03b2_3272_, v_x_3273_, v_y_3274_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__6(lean_object* v_y_3277_, lean_object* v_x_3278_){
_start:
{
if (lean_obj_tag(v_x_3278_) == 0)
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3288_; 
lean_dec_ref(v_y_3277_);
v_a_3280_ = lean_ctor_get(v_x_3278_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v_x_3278_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3282_ = v_x_3278_;
v_isShared_3283_ = v_isSharedCheck_3288_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v_x_3278_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3288_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3280_);
v___x_3285_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
lean_object* v___x_3286_; 
v___x_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3285_);
return v___x_3286_;
}
}
}
else
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
lean_dec_ref_known(v_x_3278_, 1);
v___x_3289_ = lean_box(0);
v___x_3290_ = lean_apply_2(v_y_3277_, v___x_3289_, lean_box(0));
return v___x_3290_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__6___boxed(lean_object* v_y_3291_, lean_object* v_x_3292_, lean_object* v___y_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l_Std_Async_EAsync_instMonad___redArg___lam__6(v_y_3291_, v_x_3292_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__7(lean_object* v_00_u03b1_3295_, lean_object* v_00_u03b2_3296_, lean_object* v_x_3297_, lean_object* v_y_3298_){
_start:
{
lean_object* v___f_3300_; lean_object* v___x_3301_; uint8_t v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___f_3300_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_instMonad___redArg___lam__6___boxed), 3, 1);
lean_closure_set(v___f_3300_, 0, v_y_3298_);
v___x_3301_ = lean_unsigned_to_nat(0u);
v___x_3302_ = 0;
v___x_3303_ = lean_apply_1(v_x_3297_, lean_box(0));
v___x_3304_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3301_, v___x_3302_, v___x_3303_, v___f_3300_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___lam__7___boxed(lean_object* v_00_u03b1_3305_, lean_object* v_00_u03b2_3306_, lean_object* v_x_3307_, lean_object* v_y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Std_Async_EAsync_instMonad___redArg___lam__7(v_00_u03b1_3305_, v_00_u03b2_3306_, v_x_3307_, v_y_3308_);
return v_res_3310_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonad___redArg___closed__4(void){
_start:
{
lean_object* v___f_3316_; lean_object* v___f_3317_; lean_object* v___f_3318_; lean_object* v___f_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___f_3316_ = ((lean_object*)(l_Std_Async_EAsync_instMonad___redArg___closed__3));
v___f_3317_ = ((lean_object*)(l_Std_Async_EAsync_instMonad___redArg___closed__2));
v___f_3318_ = ((lean_object*)(l_Std_Async_EAsync_instMonad___redArg___closed__1));
v___f_3319_ = ((lean_object*)(l_Std_Async_EAsync_instMonad___redArg___closed__0));
v___x_3320_ = lean_obj_once(&l_Std_Async_EAsync_instFunctor___closed__0, &l_Std_Async_EAsync_instFunctor___closed__0_once, _init_l_Std_Async_EAsync_instFunctor___closed__0);
v___x_3321_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3320_);
lean_ctor_set(v___x_3321_, 1, v___f_3319_);
lean_ctor_set(v___x_3321_, 2, v___f_3318_);
lean_ctor_set(v___x_3321_, 3, v___f_3317_);
lean_ctor_set(v___x_3321_, 4, v___f_3316_);
return v___x_3321_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonad___redArg___closed__6(void){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3323_ = ((lean_object*)(l_Std_Async_EAsync_instMonad___redArg___closed__5));
v___x_3324_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___redArg___closed__4, &l_Std_Async_EAsync_instMonad___redArg___closed__4_once, _init_l_Std_Async_EAsync_instMonad___redArg___closed__4);
v___x_3325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3324_);
lean_ctor_set(v___x_3325_, 1, v___x_3323_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg(){
_start:
{
lean_object* v___x_3327_; 
v___x_3327_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___redArg___closed__6, &l_Std_Async_EAsync_instMonad___redArg___closed__6_once, _init_l_Std_Async_EAsync_instMonad___redArg___closed__6);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad___redArg___boxed(lean_object* v___dummy_3328_){
_start:
{
lean_object* v_res_3329_; 
v_res_3329_ = l_Std_Async_EAsync_instMonad___redArg();
return v_res_3329_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonad___closed__0(void){
_start:
{
lean_object* v___x_3330_; 
v___x_3330_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonad(lean_object* v_00_u03b5_3331_){
_start:
{
lean_object* v___x_3332_; 
v___x_3332_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___closed__0, &l_Std_Async_EAsync_instMonad___closed__0_once, _init_l_Std_Async_EAsync_instMonad___closed__0);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO___redArg(){
_start:
{
lean_object* v___x_3335_; 
v___x_3335_ = ((lean_object*)(l_Std_Async_EAsync_instMonadLiftEIO___redArg___closed__0));
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO___redArg___boxed(lean_object* v___dummy_3336_){
_start:
{
lean_object* v_res_3337_; 
v_res_3337_ = l_Std_Async_EAsync_instMonadLiftEIO___redArg();
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO(lean_object* v_00_u03b5_3338_){
_start:
{
lean_object* v___x_3339_; 
v___x_3339_ = ((lean_object*)(l_Std_Async_EAsync_instMonadLiftEIO___redArg___closed__0));
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExcept___redArg___lam__1(lean_object* v_00_u03b1_3340_, lean_object* v_x_3341_, lean_object* v_f_3342_){
_start:
{
lean_object* v___f_3344_; lean_object* v___x_3345_; uint8_t v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___f_3344_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_tryCatch___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3344_, 0, v_f_3342_);
v___x_3345_ = lean_unsigned_to_nat(0u);
v___x_3346_ = 0;
v___x_3347_ = lean_apply_1(v_x_3341_, lean_box(0));
v___x_3348_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3345_, v___x_3346_, v___x_3347_, v___f_3344_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExcept___redArg___lam__1___boxed(lean_object* v_00_u03b1_3349_, lean_object* v_x_3350_, lean_object* v_f_3351_, lean_object* v___y_3352_){
_start:
{
lean_object* v_res_3353_; 
v_res_3353_ = l_Std_Async_EAsync_instMonadExcept___redArg___lam__1(v_00_u03b1_3349_, v_x_3350_, v_f_3351_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExcept___redArg(){
_start:
{
lean_object* v___x_3360_; 
v___x_3360_ = ((lean_object*)(l_Std_Async_EAsync_instMonadExcept___redArg___closed__2));
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExcept___redArg___boxed(lean_object* v___dummy_3361_){
_start:
{
lean_object* v_res_3362_; 
v_res_3362_ = l_Std_Async_EAsync_instMonadExcept___redArg();
return v_res_3362_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonadExcept___closed__0(void){
_start:
{
lean_object* v___x_3363_; 
v___x_3363_ = l_Std_Async_EAsync_instMonadExcept___redArg();
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExcept(lean_object* v_00_u03b5_3364_){
_start:
{
lean_object* v___x_3365_; 
v___x_3365_ = lean_obj_once(&l_Std_Async_EAsync_instMonadExcept___closed__0, &l_Std_Async_EAsync_instMonadExcept___closed__0_once, _init_l_Std_Async_EAsync_instMonadExcept___closed__0);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExceptOf___redArg(){
_start:
{
lean_object* v___x_3370_; 
v___x_3370_ = ((lean_object*)(l_Std_Async_EAsync_instMonadExceptOf___redArg___closed__0));
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExceptOf___redArg___boxed(lean_object* v___dummy_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l_Std_Async_EAsync_instMonadExceptOf___redArg();
return v_res_3372_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonadExceptOf___closed__0(void){
_start:
{
lean_object* v___x_3373_; 
v___x_3373_ = l_Std_Async_EAsync_instMonadExceptOf___redArg();
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadExceptOf(lean_object* v_00_u03b5_3374_){
_start:
{
lean_object* v___x_3375_; 
v___x_3375_ = lean_obj_once(&l_Std_Async_EAsync_instMonadExceptOf___closed__0, &l_Std_Async_EAsync_instMonadExceptOf___closed__0_once, _init_l_Std_Async_EAsync_instMonadExceptOf___closed__0);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadFinally___redArg___lam__0(lean_object* v_00_u03b1_3376_, lean_object* v_00_u03b2_3377_, lean_object* v_x_3378_, lean_object* v_f_3379_){
_start:
{
lean_object* v___x_3381_; uint8_t v___x_3382_; lean_object* v___x_3383_; 
v___x_3381_ = lean_unsigned_to_nat(0u);
v___x_3382_ = 0;
v___x_3383_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v_x_3378_, v_f_3379_, v___x_3381_, v___x_3382_);
return v___x_3383_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadFinally___redArg___lam__0___boxed(lean_object* v_00_u03b1_3384_, lean_object* v_00_u03b2_3385_, lean_object* v_x_3386_, lean_object* v_f_3387_, lean_object* v___y_3388_){
_start:
{
lean_object* v_res_3389_; 
v_res_3389_ = l_Std_Async_EAsync_instMonadFinally___redArg___lam__0(v_00_u03b1_3384_, v_00_u03b2_3385_, v_x_3386_, v_f_3387_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadFinally___redArg(){
_start:
{
lean_object* v___f_3392_; 
v___f_3392_ = ((lean_object*)(l_Std_Async_EAsync_instMonadFinally___redArg___closed__0));
return v___f_3392_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadFinally___redArg___boxed(lean_object* v___dummy_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l_Std_Async_EAsync_instMonadFinally___redArg();
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadFinally(lean_object* v_00_u03b5_3395_){
_start:
{
lean_object* v___f_3396_; 
v___f_3396_ = ((lean_object*)(l_Std_Async_EAsync_instMonadFinally___redArg___closed__0));
return v___f_3396_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instOrElse___redArg___closed__0(void){
_start:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3397_ = lean_obj_once(&l_Std_Async_EAsync_instMonadExcept___closed__0, &l_Std_Async_EAsync_instMonadExcept___closed__0_once, _init_l_Std_Async_EAsync_instMonadExcept___closed__0);
v___x_3398_ = lean_alloc_closure((void*)(l_MonadExcept_orElse), 6, 4);
lean_closure_set(v___x_3398_, 0, lean_box(0));
lean_closure_set(v___x_3398_, 1, lean_box(0));
lean_closure_set(v___x_3398_, 2, v___x_3397_);
lean_closure_set(v___x_3398_, 3, lean_box(0));
return v___x_3398_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instOrElse___redArg(){
_start:
{
lean_object* v___x_3400_; 
v___x_3400_ = lean_obj_once(&l_Std_Async_EAsync_instOrElse___redArg___closed__0, &l_Std_Async_EAsync_instOrElse___redArg___closed__0_once, _init_l_Std_Async_EAsync_instOrElse___redArg___closed__0);
return v___x_3400_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instOrElse___redArg___boxed(lean_object* v___dummy_3401_){
_start:
{
lean_object* v_res_3402_; 
v_res_3402_ = l_Std_Async_EAsync_instOrElse___redArg();
return v_res_3402_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instOrElse___closed__0(void){
_start:
{
lean_object* v___x_3403_; 
v___x_3403_ = l_Std_Async_EAsync_instOrElse___redArg();
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instOrElse(lean_object* v_00_u03b5_3404_, lean_object* v_00_u03b1_3405_){
_start:
{
lean_object* v___x_3406_; 
v___x_3406_ = lean_obj_once(&l_Std_Async_EAsync_instOrElse___closed__0, &l_Std_Async_EAsync_instOrElse___closed__0_once, _init_l_Std_Async_EAsync_instOrElse___closed__0);
return v___x_3406_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instInhabited___redArg(lean_object* v_inst_3407_){
_start:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3408_, 0, v_inst_3407_);
v___x_3409_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_pure___boxed), 3, 2);
lean_closure_set(v___x_3409_, 0, lean_box(0));
lean_closure_set(v___x_3409_, 1, v___x_3408_);
v___x_3410_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_mk___boxed), 3, 2);
lean_closure_set(v___x_3410_, 0, lean_box(0));
lean_closure_set(v___x_3410_, 1, v___x_3409_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instInhabited(lean_object* v_00_u03b5_3411_, lean_object* v_00_u03b1_3412_, lean_object* v_inst_3413_){
_start:
{
lean_object* v___x_3414_; 
v___x_3414_ = l_Std_Async_EAsync_instInhabited___redArg(v_inst_3413_);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitETask___redArg___lam__0(lean_object* v_00_u03b1_3415_, lean_object* v_t_3416_){
_start:
{
lean_object* v___x_3418_; 
v___x_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3418_, 0, v_t_3416_);
return v___x_3418_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitETask___redArg___lam__0___boxed(lean_object* v_00_u03b1_3419_, lean_object* v_t_3420_, lean_object* v___y_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l_Std_Async_EAsync_instMonadAwaitETask___redArg___lam__0(v_00_u03b1_3419_, v_t_3420_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitETask___redArg(){
_start:
{
lean_object* v___f_3425_; 
v___f_3425_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAwaitETask___redArg___closed__0));
return v___f_3425_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitETask___redArg___boxed(lean_object* v___dummy_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l_Std_Async_EAsync_instMonadAwaitETask___redArg();
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitETask(lean_object* v_00_u03b5_3428_){
_start:
{
lean_object* v___f_3429_; 
v___f_3429_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAwaitETask___redArg___closed__0));
return v___f_3429_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitTask___redArg___lam__1(lean_object* v___f_3430_, lean_object* v_00_u03b1_3431_, lean_object* v_t_3432_){
_start:
{
lean_object* v___x_3434_; uint8_t v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3434_ = lean_unsigned_to_nat(0u);
v___x_3435_ = 0;
v___x_3436_ = lean_task_map(v___f_3430_, v_t_3432_, v___x_3434_, v___x_3435_);
v___x_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3436_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitTask___redArg___lam__1___boxed(lean_object* v___f_3438_, lean_object* v_00_u03b1_3439_, lean_object* v_t_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l_Std_Async_EAsync_instMonadAwaitTask___redArg___lam__1(v___f_3438_, v_00_u03b1_3439_, v_t_3440_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitTask___redArg(){
_start:
{
lean_object* v___f_3446_; 
v___f_3446_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAwaitTask___redArg___closed__0));
return v___f_3446_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitTask___redArg___boxed(lean_object* v___dummy_3447_){
_start:
{
lean_object* v_res_3448_; 
v_res_3448_ = l_Std_Async_EAsync_instMonadAwaitTask___redArg();
return v_res_3448_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonadAwaitTask___closed__0(void){
_start:
{
lean_object* v___x_3449_; 
v___x_3449_ = l_Std_Async_EAsync_instMonadAwaitTask___redArg();
return v___x_3449_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitTask(lean_object* v_00_u03b5_3450_){
_start:
{
lean_object* v___x_3451_; 
v___x_3451_ = lean_obj_once(&l_Std_Async_EAsync_instMonadAwaitTask___closed__0, &l_Std_Async_EAsync_instMonadAwaitTask___closed__0_once, _init_l_Std_Async_EAsync_instMonadAwaitTask___closed__0);
return v___x_3451_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___lam__0(lean_object* v_00_u03b1_3452_, lean_object* v_t_3453_){
_start:
{
lean_object* v___x_3455_; 
v___x_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3455_, 0, v_t_3453_);
return v___x_3455_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___lam__0___boxed(lean_object* v_00_u03b1_3456_, lean_object* v_t_3457_, lean_object* v___y_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___lam__0(v_00_u03b1_3456_, v_t_3457_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitPromise___redArg___lam__1(lean_object* v___f_3462_, lean_object* v_00_u03b1_3463_, lean_object* v_t_3464_){
_start:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; uint8_t v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3466_ = l_IO_Promise_result_x21___redArg(v_t_3464_);
v___x_3467_ = lean_unsigned_to_nat(0u);
v___x_3468_ = 0;
v___x_3469_ = lean_task_map(v___f_3462_, v___x_3466_, v___x_3467_, v___x_3468_);
v___x_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3469_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitPromise___redArg___lam__1___boxed(lean_object* v___f_3471_, lean_object* v_00_u03b1_3472_, lean_object* v_t_3473_, lean_object* v___y_3474_){
_start:
{
lean_object* v_res_3475_; 
v_res_3475_ = l_Std_Async_EAsync_instMonadAwaitPromise___redArg___lam__1(v___f_3471_, v_00_u03b1_3472_, v_t_3473_);
lean_dec(v_t_3473_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitPromise___redArg(){
_start:
{
lean_object* v___f_3479_; 
v___f_3479_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAwaitPromise___redArg___closed__0));
return v___f_3479_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitPromise___redArg___boxed(lean_object* v___dummy_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Std_Async_EAsync_instMonadAwaitPromise___redArg();
return v_res_3481_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonadAwaitPromise___closed__0(void){
_start:
{
lean_object* v___x_3482_; 
v___x_3482_ = l_Std_Async_EAsync_instMonadAwaitPromise___redArg();
return v___x_3482_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAwaitPromise(lean_object* v_00_u03b5_3483_){
_start:
{
lean_object* v___x_3484_; 
v___x_3484_ = lean_obj_once(&l_Std_Async_EAsync_instMonadAwaitPromise___closed__0, &l_Std_Async_EAsync_instMonadAwaitPromise___closed__0_once, _init_l_Std_Async_EAsync_instMonadAwaitPromise___closed__0);
return v___x_3484_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncETask___redArg___lam__1(lean_object* v___f_3485_, lean_object* v_00_u03b1_3486_, lean_object* v_t_3487_, lean_object* v_prio_3488_){
_start:
{
lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; uint8_t v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3490_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_3490_, 0, lean_box(0));
lean_closure_set(v___x_3490_, 1, v_t_3487_);
v___x_3491_ = lean_io_as_task(v___x_3490_, v_prio_3488_);
v___x_3492_ = lean_unsigned_to_nat(0u);
v___x_3493_ = 1;
v___x_3494_ = lean_task_bind(v___x_3491_, v___f_3485_, v___x_3492_, v___x_3493_);
v___x_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3494_);
v___x_3496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3495_);
return v___x_3496_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncETask___redArg___lam__1___boxed(lean_object* v___f_3497_, lean_object* v_00_u03b1_3498_, lean_object* v_t_3499_, lean_object* v_prio_3500_, lean_object* v___y_3501_){
_start:
{
lean_object* v_res_3502_; 
v_res_3502_ = l_Std_Async_EAsync_instMonadAsyncETask___redArg___lam__1(v___f_3497_, v_00_u03b1_3498_, v_t_3499_, v_prio_3500_);
return v_res_3502_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncETask___redArg(){
_start:
{
lean_object* v___f_3506_; 
v___f_3506_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncETask___redArg___closed__0));
return v___f_3506_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncETask___redArg___boxed(lean_object* v___dummy_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l_Std_Async_EAsync_instMonadAsyncETask___redArg();
return v_res_3508_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonadAsyncETask___closed__0(void){
_start:
{
lean_object* v___x_3509_; 
v___x_3509_ = l_Std_Async_EAsync_instMonadAsyncETask___redArg();
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncETask(lean_object* v_00_u03b5_3510_){
_start:
{
lean_object* v___x_3511_; 
v___x_3511_ = lean_obj_once(&l_Std_Async_EAsync_instMonadAsyncETask___closed__0, &l_Std_Async_EAsync_instMonadAsyncETask___closed__0_once, _init_l_Std_Async_EAsync_instMonadAsyncETask___closed__0);
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__0(lean_object* v_x_3512_){
_start:
{
if (lean_obj_tag(v_x_3512_) == 0)
{
lean_object* v_a_3513_; lean_object* v___x_3514_; 
v_a_3513_ = lean_ctor_get(v_x_3512_, 0);
lean_inc(v_a_3513_);
lean_dec_ref_known(v_x_3512_, 1);
v___x_3514_ = lean_task_pure(v_a_3513_);
return v___x_3514_;
}
else
{
lean_object* v_a_3515_; 
v_a_3515_ = lean_ctor_get(v_x_3512_, 0);
lean_inc_ref(v_a_3515_);
lean_dec_ref_known(v_x_3512_, 1);
return v_a_3515_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__1(lean_object* v___f_3516_, lean_object* v_00_u03b1_3517_, lean_object* v_t_3518_, lean_object* v_prio_3519_){
_start:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; uint8_t v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3521_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_3521_, 0, lean_box(0));
lean_closure_set(v___x_3521_, 1, v_t_3518_);
v___x_3522_ = lean_io_as_task(v___x_3521_, v_prio_3519_);
v___x_3523_ = lean_unsigned_to_nat(0u);
v___x_3524_ = 1;
v___x_3525_ = lean_task_bind(v___x_3522_, v___f_3516_, v___x_3523_, v___x_3524_);
v___x_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3525_);
v___x_3527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3526_);
return v___x_3527_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__1___boxed(lean_object* v___f_3528_, lean_object* v_00_u03b1_3529_, lean_object* v_t_3530_, lean_object* v_prio_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__1(v___f_3528_, v_00_u03b1_3529_, v_t_3530_, v_prio_3531_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___lam__0(lean_object* v_00_u03b1_3538_, lean_object* v_x_3539_){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3541_ = lean_apply_1(v_x_3539_, lean_box(0));
v___x_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3541_);
v___x_3543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3542_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___lam__0___boxed(lean_object* v_00_u03b1_3544_, lean_object* v_x_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___lam__0(v_00_u03b1_3544_, v_x_3545_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO___redArg(){
_start:
{
lean_object* v___f_3550_; 
v___f_3550_ = ((lean_object*)(l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___closed__0));
return v___f_3550_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___boxed(lean_object* v___dummy_3551_){
_start:
{
lean_object* v_res_3552_; 
v_res_3552_ = l_Std_Async_EAsync_instMonadLiftBaseIO___redArg();
return v_res_3552_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseIO(lean_object* v_00_u03b5_3553_){
_start:
{
lean_object* v___f_3554_; 
v___f_3554_ = ((lean_object*)(l_Std_Async_EAsync_instMonadLiftBaseIO___redArg___closed__0));
return v___f_3554_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___lam__0(lean_object* v_00_u03b1_3555_, lean_object* v_x_3556_){
_start:
{
lean_object* v_val_3559_; lean_object* v___x_3561_; 
v___x_3561_ = lean_apply_1(v_x_3556_, lean_box(0));
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
v_a_3562_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___x_3561_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3561_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
lean_ctor_set_tag(v___x_3564_, 1);
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
v_val_3559_ = v___x_3567_;
goto v___jp_3558_;
}
}
}
else
{
lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3577_; 
v_a_3570_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3572_ = v___x_3561_;
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v___x_3561_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
lean_ctor_set_tag(v___x_3572_, 0);
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3570_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
v_val_3559_ = v___x_3575_;
goto v___jp_3558_;
}
}
}
v___jp_3558_:
{
lean_object* v___x_3560_; 
v___x_3560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3560_, 0, v_val_3559_);
return v___x_3560_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___lam__0___boxed(lean_object* v_00_u03b1_3578_, lean_object* v_x_3579_, lean_object* v___y_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___lam__0(v_00_u03b1_3578_, v_x_3579_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1___redArg(){
_start:
{
lean_object* v___f_3584_; 
v___f_3584_ = ((lean_object*)(l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___closed__0));
return v___f_3584_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___boxed(lean_object* v___dummy_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l_Std_Async_EAsync_instMonadLiftEIO__1___redArg();
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftEIO__1(lean_object* v_00_u03b5_3587_){
_start:
{
lean_object* v___f_3588_; 
v___f_3588_ = ((lean_object*)(l_Std_Async_EAsync_instMonadLiftEIO__1___redArg___closed__0));
return v___f_3588_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg___lam__1(lean_object* v___f_3589_, lean_object* v_00_u03b1_3590_, lean_object* v_x_3591_){
_start:
{
lean_object* v___x_3593_; uint8_t v___x_3594_; lean_object* v___x_3595_; 
v___x_3593_ = lean_unsigned_to_nat(0u);
v___x_3594_ = 0;
v___x_3595_ = lean_apply_1(v_x_3591_, lean_box(0));
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v_a_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3604_; 
lean_dec_ref(v___f_3589_);
v_a_3596_ = lean_ctor_get(v___x_3595_, 0);
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3598_ = v___x_3595_;
v_isShared_3599_ = v_isSharedCheck_3604_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_a_3596_);
lean_dec(v___x_3595_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3604_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3600_; lean_object* v___x_3602_; 
v___x_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3600_, 0, v_a_3596_);
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 0, v___x_3600_);
v___x_3602_ = v___x_3598_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v___x_3600_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
}
else
{
lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3613_; 
v_a_3605_ = lean_ctor_get(v___x_3595_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3607_ = v___x_3595_;
v_isShared_3608_ = v_isSharedCheck_3613_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_dec(v___x_3595_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3613_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3609_; lean_object* v___x_3611_; 
v___x_3609_ = lean_task_map(v___f_3589_, v_a_3605_, v___x_3593_, v___x_3594_);
if (v_isShared_3608_ == 0)
{
lean_ctor_set(v___x_3607_, 0, v___x_3609_);
v___x_3611_ = v___x_3607_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v___x_3609_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg___lam__1___boxed(lean_object* v___f_3614_, lean_object* v_00_u03b1_3615_, lean_object* v_x_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg___lam__1(v___f_3614_, v_00_u03b1_3615_, v_x_3616_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg(){
_start:
{
lean_object* v___f_3622_; 
v___f_3622_ = ((lean_object*)(l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg___closed__0));
return v___f_3622_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg___boxed(lean_object* v___dummy_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
return v_res_3624_;
}
}
static lean_object* _init_l_Std_Async_EAsync_instMonadLiftBaseAsync___closed__0(void){
_start:
{
lean_object* v___x_3625_; 
v___x_3625_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync(lean_object* v_00_u03b5_3626_){
_start:
{
lean_object* v___x_3627_; 
v___x_3627_ = lean_obj_once(&l_Std_Async_EAsync_instMonadLiftBaseAsync___closed__0, &l_Std_Async_EAsync_instMonadLiftBaseAsync___closed__0_once, _init_l_Std_Async_EAsync_instMonadLiftBaseAsync___closed__0);
return v___x_3627_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___lam__0___boxed(lean_object* v_promise_3628_, lean_object* v_f_3629_, lean_object* v_prio_3630_, lean_object* v_x_3631_, lean_object* v___y_3632_){
_start:
{
lean_object* v_res_3633_; 
v_res_3633_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___lam__0(v_promise_3628_, v_f_3629_, v_prio_3630_, v_x_3631_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(lean_object* v_f_3634_, lean_object* v_prio_3635_, lean_object* v_promise_3636_, lean_object* v_b_3637_){
_start:
{
lean_object* v___f_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; 
lean_inc(v_prio_3635_);
lean_inc_ref_n(v_f_3634_, 2);
lean_inc(v_promise_3636_);
v___f_3639_ = lean_alloc_closure((void*)(l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3639_, 0, v_promise_3636_);
lean_closure_set(v___f_3639_, 1, v_f_3634_);
lean_closure_set(v___f_3639_, 2, v_prio_3635_);
v___x_3640_ = lean_box(0);
v___x_3641_ = lean_apply_3(v_f_3634_, v___x_3640_, v_b_3637_, lean_box(0));
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_a_3642_; 
lean_dec_ref(v___f_3639_);
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
lean_inc(v_a_3642_);
lean_dec_ref_known(v___x_3641_, 1);
if (lean_obj_tag(v_a_3642_) == 0)
{
lean_object* v_a_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3651_; 
lean_dec(v_prio_3635_);
lean_dec_ref(v_f_3634_);
v_a_3643_ = lean_ctor_get(v_a_3642_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v_a_3642_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3645_ = v_a_3642_;
v_isShared_3646_ = v_isSharedCheck_3651_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_a_3643_);
lean_dec(v_a_3642_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3651_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3648_; 
if (v_isShared_3646_ == 0)
{
v___x_3648_ = v___x_3645_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3643_);
v___x_3648_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
lean_object* v___x_3649_; 
v___x_3649_ = lean_io_promise_resolve(v___x_3648_, v_promise_3636_);
lean_dec(v_promise_3636_);
return v___x_3649_;
}
}
}
else
{
lean_object* v_a_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3663_; 
v_a_3652_ = lean_ctor_get(v_a_3642_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v_a_3642_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3654_ = v_a_3642_;
v_isShared_3655_ = v_isSharedCheck_3663_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_a_3652_);
lean_dec(v_a_3642_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3663_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
if (lean_obj_tag(v_a_3652_) == 0)
{
lean_object* v_a_3656_; lean_object* v___x_3658_; 
lean_dec(v_prio_3635_);
lean_dec_ref(v_f_3634_);
v_a_3656_ = lean_ctor_get(v_a_3652_, 0);
lean_inc(v_a_3656_);
lean_dec_ref_known(v_a_3652_, 1);
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 0, v_a_3656_);
v___x_3658_ = v___x_3654_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3656_);
v___x_3658_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
lean_object* v___x_3659_; 
v___x_3659_ = lean_io_promise_resolve(v___x_3658_, v_promise_3636_);
lean_dec(v_promise_3636_);
return v___x_3659_;
}
}
else
{
lean_object* v_a_3661_; 
lean_del_object(v___x_3654_);
v_a_3661_ = lean_ctor_get(v_a_3652_, 0);
lean_inc(v_a_3661_);
lean_dec_ref_known(v_a_3652_, 1);
v_b_3637_ = v_a_3661_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3664_; uint8_t v___x_3665_; lean_object* v___x_3666_; 
lean_dec(v_promise_3636_);
lean_dec_ref(v_f_3634_);
v_a_3664_ = lean_ctor_get(v___x_3641_, 0);
lean_inc_ref(v_a_3664_);
lean_dec_ref_known(v___x_3641_, 1);
v___x_3665_ = 0;
v___x_3666_ = l_BaseIO_chainTask___redArg(v_a_3664_, v___f_3639_, v_prio_3635_, v___x_3665_);
return v___x_3666_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___lam__0(lean_object* v_promise_3667_, lean_object* v_f_3668_, lean_object* v_prio_3669_, lean_object* v_x_3670_){
_start:
{
if (lean_obj_tag(v_x_3670_) == 0)
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3680_; 
lean_dec(v_prio_3669_);
lean_dec_ref(v_f_3668_);
v_a_3672_ = lean_ctor_get(v_x_3670_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v_x_3670_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3674_ = v_x_3670_;
v_isShared_3675_ = v_isSharedCheck_3680_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v_x_3670_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3680_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3677_; 
if (v_isShared_3675_ == 0)
{
v___x_3677_ = v___x_3674_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_a_3672_);
v___x_3677_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
lean_object* v___x_3678_; 
v___x_3678_ = lean_io_promise_resolve(v___x_3677_, v_promise_3667_);
lean_dec(v_promise_3667_);
return v___x_3678_;
}
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3692_; 
v_a_3681_ = lean_ctor_get(v_x_3670_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v_x_3670_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3683_ = v_x_3670_;
v_isShared_3684_ = v_isSharedCheck_3692_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v_x_3670_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3692_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
if (lean_obj_tag(v_a_3681_) == 0)
{
lean_object* v_a_3685_; lean_object* v___x_3687_; 
lean_dec(v_prio_3669_);
lean_dec_ref(v_f_3668_);
v_a_3685_ = lean_ctor_get(v_a_3681_, 0);
lean_inc(v_a_3685_);
lean_dec_ref_known(v_a_3681_, 1);
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 0, v_a_3685_);
v___x_3687_ = v___x_3683_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3685_);
v___x_3687_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
lean_object* v___x_3688_; 
v___x_3688_ = lean_io_promise_resolve(v___x_3687_, v_promise_3667_);
lean_dec(v_promise_3667_);
return v___x_3688_;
}
}
else
{
lean_object* v_a_3690_; lean_object* v___x_3691_; 
lean_del_object(v___x_3683_);
v_a_3690_ = lean_ctor_get(v_a_3681_, 0);
lean_inc(v_a_3690_);
lean_dec_ref_known(v_a_3681_, 1);
v___x_3691_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(v_f_3668_, v_prio_3669_, v_promise_3667_, v_a_3690_);
return v___x_3691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___boxed(lean_object* v_f_3693_, lean_object* v_prio_3694_, lean_object* v_promise_3695_, lean_object* v_b_3696_, lean_object* v_a_3697_){
_start:
{
lean_object* v_res_3698_; 
v_res_3698_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(v_f_3693_, v_prio_3694_, v_promise_3695_, v_b_3696_);
return v_res_3698_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_object* v_00_u03b5_3699_, lean_object* v_00_u03b2_3700_, lean_object* v_f_3701_, lean_object* v_prio_3702_, lean_object* v_promise_3703_, lean_object* v_b_3704_){
_start:
{
lean_object* v___x_3706_; 
v___x_3706_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(v_f_3701_, v_prio_3702_, v_promise_3703_, v_b_3704_);
return v___x_3706_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___boxed(lean_object* v_00_u03b5_3707_, lean_object* v_00_u03b2_3708_, lean_object* v_f_3709_, lean_object* v_prio_3710_, lean_object* v_promise_3711_, lean_object* v_b_3712_, lean_object* v_a_3713_){
_start:
{
lean_object* v_res_3714_; 
v_res_3714_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(v_00_u03b5_3707_, v_00_u03b2_3708_, v_f_3709_, v_prio_3710_, v_promise_3711_, v_b_3712_);
return v_res_3714_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg___lam__0(lean_object* v_a_3715_, lean_object* v_x_3716_){
_start:
{
if (lean_obj_tag(v_x_3716_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3726_; 
v_a_3718_ = lean_ctor_get(v_x_3716_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v_x_3716_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3720_ = v_x_3716_;
v_isShared_3721_ = v_isSharedCheck_3726_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v_x_3716_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3726_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___x_3723_; 
if (v_isShared_3721_ == 0)
{
v___x_3723_ = v___x_3720_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_a_3718_);
v___x_3723_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
lean_object* v___x_3724_; 
v___x_3724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3723_);
return v___x_3724_;
}
}
}
else
{
lean_object* v___x_3727_; lean_object* v___x_3728_; 
lean_dec_ref_known(v_x_3716_, 1);
v___x_3727_ = l_IO_Promise_result_x21___redArg(v_a_3715_);
v___x_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3727_);
return v___x_3728_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg___lam__0___boxed(lean_object* v_a_3729_, lean_object* v_x_3730_, lean_object* v___y_3731_){
_start:
{
lean_object* v_res_3732_; 
v_res_3732_ = l_Std_Async_EAsync_forIn___redArg___lam__0(v_a_3729_, v_x_3730_);
lean_dec(v_a_3729_);
return v_res_3732_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg___lam__1(lean_object* v_f_3733_, lean_object* v_prio_3734_, lean_object* v_init_3735_, lean_object* v_x_3736_){
_start:
{
if (lean_obj_tag(v_x_3736_) == 0)
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3746_; 
lean_dec(v_init_3735_);
lean_dec(v_prio_3734_);
lean_dec_ref(v_f_3733_);
v_a_3738_ = lean_ctor_get(v_x_3736_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v_x_3736_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3740_ = v_x_3736_;
v_isShared_3741_ = v_isSharedCheck_3746_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v_x_3736_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3746_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3743_; 
if (v_isShared_3741_ == 0)
{
v___x_3743_ = v___x_3740_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3738_);
v___x_3743_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
lean_object* v___x_3744_; 
v___x_3744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3743_);
return v___x_3744_;
}
}
}
else
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3760_; 
v_a_3747_ = lean_ctor_get(v_x_3736_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v_x_3736_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3749_ = v_x_3736_;
v_isShared_3750_ = v_isSharedCheck_3760_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v_x_3736_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3760_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___f_3751_; lean_object* v___x_3752_; uint8_t v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3756_; 
lean_inc(v_a_3747_);
v___f_3751_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_forIn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3751_, 0, v_a_3747_);
v___x_3752_ = lean_unsigned_to_nat(0u);
v___x_3753_ = 0;
v___x_3754_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(v_f_3733_, v_prio_3734_, v_a_3747_, v_init_3735_);
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 0, v___x_3754_);
v___x_3756_ = v___x_3749_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v___x_3754_);
v___x_3756_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3756_);
v___x_3758_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3752_, v___x_3753_, v___x_3757_, v___f_3751_);
return v___x_3758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg___lam__1___boxed(lean_object* v_f_3761_, lean_object* v_prio_3762_, lean_object* v_init_3763_, lean_object* v_x_3764_, lean_object* v___y_3765_){
_start:
{
lean_object* v_res_3766_; 
v_res_3766_ = l_Std_Async_EAsync_forIn___redArg___lam__1(v_f_3761_, v_prio_3762_, v_init_3763_, v_x_3764_);
return v_res_3766_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg(lean_object* v_init_3767_, lean_object* v_f_3768_, lean_object* v_prio_3769_){
_start:
{
lean_object* v___f_3771_; lean_object* v___x_3772_; uint8_t v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
v___f_3771_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_forIn___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_3771_, 0, v_f_3768_);
lean_closure_set(v___f_3771_, 1, v_prio_3769_);
lean_closure_set(v___f_3771_, 2, v_init_3767_);
v___x_3772_ = lean_unsigned_to_nat(0u);
v___x_3773_ = 0;
v___x_3774_ = lean_io_promise_new();
v___x_3775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3775_, 0, v___x_3774_);
v___x_3776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3775_);
v___x_3777_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3772_, v___x_3773_, v___x_3776_, v___f_3771_);
return v___x_3777_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___redArg___boxed(lean_object* v_init_3778_, lean_object* v_f_3779_, lean_object* v_prio_3780_, lean_object* v_a_3781_){
_start:
{
lean_object* v_res_3782_; 
v_res_3782_ = l_Std_Async_EAsync_forIn___redArg(v_init_3778_, v_f_3779_, v_prio_3780_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn(lean_object* v_00_u03b5_3783_, lean_object* v_00_u03b2_3784_, lean_object* v_init_3785_, lean_object* v_f_3786_, lean_object* v_prio_3787_){
_start:
{
lean_object* v___f_3789_; lean_object* v___x_3790_; uint8_t v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; 
v___f_3789_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_forIn___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_3789_, 0, v_f_3786_);
lean_closure_set(v___f_3789_, 1, v_prio_3787_);
lean_closure_set(v___f_3789_, 2, v_init_3785_);
v___x_3790_ = lean_unsigned_to_nat(0u);
v___x_3791_ = 0;
v___x_3792_ = lean_io_promise_new();
v___x_3793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3792_);
v___x_3794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3793_);
v___x_3795_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3790_, v___x_3791_, v___x_3794_, v___f_3789_);
return v___x_3795_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_forIn___boxed(lean_object* v_00_u03b5_3796_, lean_object* v_00_u03b2_3797_, lean_object* v_init_3798_, lean_object* v_f_3799_, lean_object* v_prio_3800_, lean_object* v_a_3801_){
_start:
{
lean_object* v_res_3802_; 
v_res_3802_ = l_Std_Async_EAsync_forIn(v_00_u03b5_3796_, v_00_u03b2_3797_, v_init_3798_, v_f_3799_, v_prio_3800_);
return v_res_3802_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__1(lean_object* v_f_3803_, lean_object* v___x_3804_, lean_object* v_init_3805_, lean_object* v_x_3806_){
_start:
{
if (lean_obj_tag(v_x_3806_) == 0)
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3816_; 
lean_dec(v_init_3805_);
lean_dec(v___x_3804_);
lean_dec_ref(v_f_3803_);
v_a_3808_ = lean_ctor_get(v_x_3806_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v_x_3806_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3810_ = v_x_3806_;
v_isShared_3811_ = v_isSharedCheck_3816_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v_x_3806_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3816_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
lean_object* v___x_3814_; 
v___x_3814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3813_);
return v___x_3814_;
}
}
}
else
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3829_; 
v_a_3817_ = lean_ctor_get(v_x_3806_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v_x_3806_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3819_ = v_x_3806_;
v_isShared_3820_ = v_isSharedCheck_3829_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v_x_3806_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3829_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___f_3821_; uint8_t v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3825_; 
lean_inc(v_a_3817_);
v___f_3821_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_forIn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3821_, 0, v_a_3817_);
v___x_3822_ = 0;
lean_inc(v___x_3804_);
v___x_3823_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(v_f_3803_, v___x_3804_, v_a_3817_, v_init_3805_);
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 0, v___x_3823_);
v___x_3825_ = v___x_3819_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v___x_3823_);
v___x_3825_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
lean_object* v___x_3826_; lean_object* v___x_3827_; 
v___x_3826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3825_);
v___x_3827_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3804_, v___x_3822_, v___x_3826_, v___f_3821_);
return v___x_3827_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__1___boxed(lean_object* v_f_3830_, lean_object* v___x_3831_, lean_object* v_init_3832_, lean_object* v_x_3833_, lean_object* v___y_3834_){
_start:
{
lean_object* v_res_3835_; 
v_res_3835_ = l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__1(v_f_3830_, v___x_3831_, v_init_3832_, v_x_3833_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__0(lean_object* v_00_u03b2_3836_, lean_object* v_x_3837_, lean_object* v_init_3838_, lean_object* v_f_3839_){
_start:
{
lean_object* v___x_3841_; lean_object* v___f_3842_; uint8_t v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; 
v___x_3841_ = lean_unsigned_to_nat(0u);
v___f_3842_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_3842_, 0, v_f_3839_);
lean_closure_set(v___f_3842_, 1, v___x_3841_);
lean_closure_set(v___f_3842_, 2, v_init_3838_);
v___x_3843_ = 0;
v___x_3844_ = lean_io_promise_new();
v___x_3845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3844_);
v___x_3846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3846_, 0, v___x_3845_);
v___x_3847_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3841_, v___x_3843_, v___x_3846_, v___f_3842_);
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__0___boxed(lean_object* v_00_u03b2_3848_, lean_object* v_x_3849_, lean_object* v_init_3850_, lean_object* v_f_3851_, lean_object* v___y_3852_){
_start:
{
lean_object* v_res_3853_; 
v_res_3853_ = l_Std_Async_EAsync_instForInLoopUnit___redArg___lam__0(v_00_u03b2_3848_, v_x_3849_, v_init_3850_, v_f_3851_);
return v_res_3853_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___redArg(){
_start:
{
lean_object* v___f_3856_; 
v___f_3856_ = ((lean_object*)(l_Std_Async_EAsync_instForInLoopUnit___redArg___closed__0));
return v___f_3856_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit___redArg___boxed(lean_object* v___dummy_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l_Std_Async_EAsync_instForInLoopUnit___redArg();
return v_res_3858_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_instForInLoopUnit(lean_object* v_00_u03b5_3859_){
_start:
{
lean_object* v___f_3860_; 
v___f_3860_ = ((lean_object*)(l_Std_Async_EAsync_instForInLoopUnit___redArg___closed__0));
return v___f_3860_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofExcept___redArg(lean_object* v_except_3861_){
_start:
{
lean_object* v___x_3863_; 
v___x_3863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3863_, 0, v_except_3861_);
return v___x_3863_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofExcept___redArg___boxed(lean_object* v_except_3864_, lean_object* v_a_3865_){
_start:
{
lean_object* v_res_3866_; 
v_res_3866_ = l_Std_Async_EAsync_ofExcept___redArg(v_except_3864_);
return v_res_3866_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofExcept(lean_object* v_00_u03b5_3867_, lean_object* v_00_u03b1_3868_, lean_object* v_except_3869_){
_start:
{
lean_object* v___x_3871_; 
v___x_3871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3871_, 0, v_except_3869_);
return v___x_3871_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_ofExcept___boxed(lean_object* v_00_u03b5_3872_, lean_object* v_00_u03b1_3873_, lean_object* v_except_3874_, lean_object* v_a_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l_Std_Async_EAsync_ofExcept(v_00_u03b5_3872_, v_00_u03b1_3873_, v_except_3874_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__1(lean_object* v_a_3877_, lean_object* v_x_3878_){
_start:
{
if (lean_obj_tag(v_x_3878_) == 0)
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3888_; 
lean_dec(v_a_3877_);
v_a_3880_ = lean_ctor_get(v_x_3878_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v_x_3878_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3882_ = v_x_3878_;
v_isShared_3883_ = v_isSharedCheck_3888_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v_x_3878_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3888_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_a_3880_);
v___x_3885_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
lean_object* v___x_3886_; 
v___x_3886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3885_);
return v___x_3886_;
}
}
}
else
{
lean_object* v_a_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3898_; 
v_a_3889_ = lean_ctor_get(v_x_3878_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v_x_3878_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3891_ = v_x_3878_;
v_isShared_3892_ = v_isSharedCheck_3898_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_a_3889_);
lean_dec(v_x_3878_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3898_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3893_; lean_object* v___x_3895_; 
v___x_3893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3893_, 0, v_a_3877_);
lean_ctor_set(v___x_3893_, 1, v_a_3889_);
if (v_isShared_3892_ == 0)
{
lean_ctor_set(v___x_3891_, 0, v___x_3893_);
v___x_3895_ = v___x_3891_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___x_3893_);
v___x_3895_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
lean_object* v___x_3896_; 
v___x_3896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3895_);
return v___x_3896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__1___boxed(lean_object* v_a_3899_, lean_object* v_x_3900_, lean_object* v___y_3901_){
_start:
{
lean_object* v_res_3902_; 
v_res_3902_ = l_Std_Async_EAsync_concurrently___redArg___lam__1(v_a_3899_, v_x_3900_);
return v_res_3902_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__0(lean_object* v_a_3903_, lean_object* v_x_3904_){
_start:
{
if (lean_obj_tag(v_x_3904_) == 0)
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3914_; 
lean_dec_ref(v_a_3903_);
v_a_3906_ = lean_ctor_get(v_x_3904_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v_x_3904_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3908_ = v_x_3904_;
v_isShared_3909_ = v_isSharedCheck_3914_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v_x_3904_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3914_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3911_; 
if (v_isShared_3909_ == 0)
{
v___x_3911_ = v___x_3908_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_a_3906_);
v___x_3911_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
lean_object* v___x_3912_; 
v___x_3912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3911_);
return v___x_3912_;
}
}
}
else
{
lean_object* v_a_3915_; lean_object* v___f_3916_; lean_object* v___x_3917_; uint8_t v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; 
v_a_3915_ = lean_ctor_get(v_x_3904_, 0);
lean_inc(v_a_3915_);
lean_dec_ref_known(v_x_3904_, 1);
v___f_3916_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrently___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3916_, 0, v_a_3915_);
v___x_3917_ = lean_unsigned_to_nat(0u);
v___x_3918_ = 0;
v___x_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3919_, 0, v_a_3903_);
v___x_3920_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3917_, v___x_3918_, v___x_3919_, v___f_3916_);
return v___x_3920_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__0___boxed(lean_object* v_a_3921_, lean_object* v_x_3922_, lean_object* v___y_3923_){
_start:
{
lean_object* v_res_3924_; 
v_res_3924_ = l_Std_Async_EAsync_concurrently___redArg___lam__0(v_a_3921_, v_x_3922_);
return v_res_3924_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__2(lean_object* v_a_3925_, lean_object* v_x_3926_){
_start:
{
if (lean_obj_tag(v_x_3926_) == 0)
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3936_; 
lean_dec_ref(v_a_3925_);
v_a_3928_ = lean_ctor_get(v_x_3926_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v_x_3926_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3930_ = v_x_3926_;
v_isShared_3931_ = v_isSharedCheck_3936_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v_x_3926_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3936_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_a_3928_);
v___x_3933_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
lean_object* v___x_3934_; 
v___x_3934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3933_);
return v___x_3934_;
}
}
}
else
{
lean_object* v_a_3937_; lean_object* v___f_3938_; lean_object* v___x_3939_; uint8_t v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
v_a_3937_ = lean_ctor_get(v_x_3926_, 0);
lean_inc(v_a_3937_);
lean_dec_ref_known(v_x_3926_, 1);
v___f_3938_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrently___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3938_, 0, v_a_3937_);
v___x_3939_ = lean_unsigned_to_nat(0u);
v___x_3940_ = 0;
v___x_3941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3941_, 0, v_a_3925_);
v___x_3942_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3939_, v___x_3940_, v___x_3941_, v___f_3938_);
return v___x_3942_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__2___boxed(lean_object* v_a_3943_, lean_object* v_x_3944_, lean_object* v___y_3945_){
_start:
{
lean_object* v_res_3946_; 
v_res_3946_ = l_Std_Async_EAsync_concurrently___redArg___lam__2(v_a_3943_, v_x_3944_);
return v_res_3946_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__3(lean_object* v_y_3947_, lean_object* v_prio_3948_, lean_object* v___f_3949_, lean_object* v_x_3950_){
_start:
{
if (lean_obj_tag(v_x_3950_) == 0)
{
lean_object* v_a_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3960_; 
lean_dec_ref(v___f_3949_);
lean_dec(v_prio_3948_);
lean_dec_ref(v_y_3947_);
v_a_3952_ = lean_ctor_get(v_x_3950_, 0);
v_isSharedCheck_3960_ = !lean_is_exclusive(v_x_3950_);
if (v_isSharedCheck_3960_ == 0)
{
v___x_3954_ = v_x_3950_;
v_isShared_3955_ = v_isSharedCheck_3960_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_a_3952_);
lean_dec(v_x_3950_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3960_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3957_; 
if (v_isShared_3955_ == 0)
{
v___x_3957_ = v___x_3954_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_a_3952_);
v___x_3957_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
lean_object* v___x_3958_; 
v___x_3958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3957_);
return v___x_3958_;
}
}
}
else
{
lean_object* v_a_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3977_; 
v_a_3961_ = lean_ctor_get(v_x_3950_, 0);
v_isSharedCheck_3977_ = !lean_is_exclusive(v_x_3950_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3963_ = v_x_3950_;
v_isShared_3964_ = v_isSharedCheck_3977_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_a_3961_);
lean_dec(v_x_3950_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3977_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v___f_3965_; lean_object* v___x_3966_; uint8_t v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; uint8_t v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3973_; 
v___f_3965_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrently___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3965_, 0, v_a_3961_);
v___x_3966_ = lean_unsigned_to_nat(0u);
v___x_3967_ = 0;
v___x_3968_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_3968_, 0, lean_box(0));
lean_closure_set(v___x_3968_, 1, v_y_3947_);
v___x_3969_ = lean_io_as_task(v___x_3968_, v_prio_3948_);
v___x_3970_ = 1;
v___x_3971_ = lean_task_bind(v___x_3969_, v___f_3949_, v___x_3966_, v___x_3970_);
if (v_isShared_3964_ == 0)
{
lean_ctor_set(v___x_3963_, 0, v___x_3971_);
v___x_3973_ = v___x_3963_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v___x_3971_);
v___x_3973_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3973_);
v___x_3975_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3966_, v___x_3967_, v___x_3974_, v___f_3965_);
return v___x_3975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___lam__3___boxed(lean_object* v_y_3978_, lean_object* v_prio_3979_, lean_object* v___f_3980_, lean_object* v_x_3981_, lean_object* v___y_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l_Std_Async_EAsync_concurrently___redArg___lam__3(v_y_3978_, v_prio_3979_, v___f_3980_, v_x_3981_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg(lean_object* v_x_3984_, lean_object* v_y_3985_, lean_object* v_prio_3986_){
_start:
{
lean_object* v___f_3988_; lean_object* v___f_3989_; lean_object* v___x_3990_; uint8_t v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; uint8_t v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___f_3988_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
lean_inc(v_prio_3986_);
v___f_3989_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrently___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3989_, 0, v_y_3985_);
lean_closure_set(v___f_3989_, 1, v_prio_3986_);
lean_closure_set(v___f_3989_, 2, v___f_3988_);
v___x_3990_ = lean_unsigned_to_nat(0u);
v___x_3991_ = 0;
v___x_3992_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_3992_, 0, lean_box(0));
lean_closure_set(v___x_3992_, 1, v_x_3984_);
v___x_3993_ = lean_io_as_task(v___x_3992_, v_prio_3986_);
v___x_3994_ = 1;
v___x_3995_ = lean_task_bind(v___x_3993_, v___f_3988_, v___x_3990_, v___x_3994_);
v___x_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3995_);
v___x_3997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3997_, 0, v___x_3996_);
v___x_3998_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_3990_, v___x_3991_, v___x_3997_, v___f_3989_);
return v___x_3998_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___redArg___boxed(lean_object* v_x_3999_, lean_object* v_y_4000_, lean_object* v_prio_4001_, lean_object* v_a_4002_){
_start:
{
lean_object* v_res_4003_; 
v_res_4003_ = l_Std_Async_EAsync_concurrently___redArg(v_x_3999_, v_y_4000_, v_prio_4001_);
return v_res_4003_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently(lean_object* v_00_u03b5_4004_, lean_object* v_00_u03b1_4005_, lean_object* v_00_u03b2_4006_, lean_object* v_x_4007_, lean_object* v_y_4008_, lean_object* v_prio_4009_){
_start:
{
lean_object* v___f_4011_; lean_object* v___f_4012_; lean_object* v___x_4013_; uint8_t v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; uint8_t v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
v___f_4011_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
lean_inc(v_prio_4009_);
v___f_4012_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrently___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_4012_, 0, v_y_4008_);
lean_closure_set(v___f_4012_, 1, v_prio_4009_);
lean_closure_set(v___f_4012_, 2, v___f_4011_);
v___x_4013_ = lean_unsigned_to_nat(0u);
v___x_4014_ = 0;
v___x_4015_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4015_, 0, lean_box(0));
lean_closure_set(v___x_4015_, 1, v_x_4007_);
v___x_4016_ = lean_io_as_task(v___x_4015_, v_prio_4009_);
v___x_4017_ = 1;
v___x_4018_ = lean_task_bind(v___x_4016_, v___f_4011_, v___x_4013_, v___x_4017_);
v___x_4019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4019_, 0, v___x_4018_);
v___x_4020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4020_, 0, v___x_4019_);
v___x_4021_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4013_, v___x_4014_, v___x_4020_, v___f_4012_);
return v___x_4021_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrently___boxed(lean_object* v_00_u03b5_4022_, lean_object* v_00_u03b1_4023_, lean_object* v_00_u03b2_4024_, lean_object* v_x_4025_, lean_object* v_y_4026_, lean_object* v_prio_4027_, lean_object* v_a_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l_Std_Async_EAsync_concurrently(v_00_u03b5_4022_, v_00_u03b1_4023_, v_00_u03b2_4024_, v_x_4025_, v_y_4026_, v_prio_4027_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__1(lean_object* v_x_4030_){
_start:
{
if (lean_obj_tag(v_x_4030_) == 0)
{
lean_object* v_a_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4040_; 
v_a_4032_ = lean_ctor_get(v_x_4030_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v_x_4030_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4034_ = v_x_4030_;
v_isShared_4035_ = v_isSharedCheck_4040_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_a_4032_);
lean_dec(v_x_4030_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4040_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v___x_4037_; 
if (v_isShared_4035_ == 0)
{
v___x_4037_ = v___x_4034_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_a_4032_);
v___x_4037_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
lean_object* v___x_4038_; 
v___x_4038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4037_);
return v___x_4038_;
}
}
}
else
{
lean_object* v_a_4041_; lean_object* v___x_4042_; 
v_a_4041_ = lean_ctor_get(v_x_4030_, 0);
lean_inc(v_a_4041_);
lean_dec_ref_known(v_x_4030_, 1);
v___x_4042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4042_, 0, v_a_4041_);
return v___x_4042_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__1___boxed(lean_object* v_x_4043_, lean_object* v___y_4044_){
_start:
{
lean_object* v_res_4045_; 
v_res_4045_ = l_Std_Async_EAsync_race___redArg___lam__1(v_x_4043_);
return v_res_4045_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__0(lean_object* v_a_4046_){
_start:
{
lean_object* v___x_4047_; 
v___x_4047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4047_, 0, v_a_4046_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__3(lean_object* v_a_4048_, lean_object* v_value_4049_){
_start:
{
lean_object* v___x_4051_; 
v___x_4051_ = lean_io_promise_resolve(v_value_4049_, v_a_4048_);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__3___boxed(lean_object* v_a_4052_, lean_object* v_value_4053_, lean_object* v___y_4054_){
_start:
{
lean_object* v_res_4055_; 
v_res_4055_ = l_Std_Async_EAsync_race___redArg___lam__3(v_a_4052_, v_value_4053_);
lean_dec(v_a_4052_);
return v_res_4055_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__2(lean_object* v_a_4056_, lean_object* v___f_4057_, lean_object* v___f_4058_, lean_object* v_x_4059_){
_start:
{
if (lean_obj_tag(v_x_4059_) == 0)
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4069_; 
lean_dec_ref(v___f_4058_);
lean_dec_ref(v___f_4057_);
v_a_4061_ = lean_ctor_get(v_x_4059_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v_x_4059_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4063_ = v_x_4059_;
v_isShared_4064_ = v_isSharedCheck_4069_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v_x_4059_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4069_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4066_; 
if (v_isShared_4064_ == 0)
{
v___x_4066_ = v___x_4063_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_a_4061_);
v___x_4066_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
lean_object* v___x_4067_; 
v___x_4067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4066_);
return v___x_4067_;
}
}
}
else
{
lean_object* v___x_4070_; lean_object* v___x_4071_; uint8_t v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; 
lean_dec_ref_known(v_x_4059_, 1);
v___x_4070_ = l_IO_Promise_result_x21___redArg(v_a_4056_);
v___x_4071_ = lean_unsigned_to_nat(0u);
v___x_4072_ = 0;
v___x_4073_ = lean_task_map(v___f_4057_, v___x_4070_, v___x_4071_, v___x_4072_);
v___x_4074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4073_);
v___x_4075_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4071_, v___x_4072_, v___x_4074_, v___f_4058_);
return v___x_4075_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__2___boxed(lean_object* v_a_4076_, lean_object* v___f_4077_, lean_object* v___f_4078_, lean_object* v_x_4079_, lean_object* v___y_4080_){
_start:
{
lean_object* v_res_4081_; 
v_res_4081_ = l_Std_Async_EAsync_race___redArg___lam__2(v_a_4076_, v___f_4077_, v___f_4078_, v_x_4079_);
lean_dec(v_a_4076_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__4(lean_object* v_a_4082_, lean_object* v___x_4083_, lean_object* v___x_4084_, uint8_t v___x_4085_, lean_object* v___f_4086_, lean_object* v_x_4087_){
_start:
{
if (lean_obj_tag(v_x_4087_) == 0)
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4097_; 
lean_dec_ref(v___f_4086_);
lean_dec(v___x_4084_);
lean_dec_ref(v___x_4083_);
lean_dec_ref(v_a_4082_);
v_a_4089_ = lean_ctor_get(v_x_4087_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v_x_4087_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4091_ = v_x_4087_;
v_isShared_4092_ = v_isSharedCheck_4097_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_a_4089_);
lean_dec(v_x_4087_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4097_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4094_; 
if (v_isShared_4092_ == 0)
{
v___x_4094_ = v___x_4091_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4089_);
v___x_4094_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
lean_object* v___x_4095_; 
v___x_4095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4095_, 0, v___x_4094_);
return v___x_4095_;
}
}
}
else
{
lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4107_; 
v_isSharedCheck_4107_ = !lean_is_exclusive(v_x_4087_);
if (v_isSharedCheck_4107_ == 0)
{
lean_object* v_unused_4108_; 
v_unused_4108_ = lean_ctor_get(v_x_4087_, 0);
lean_dec(v_unused_4108_);
v___x_4099_ = v_x_4087_;
v_isShared_4100_ = v_isSharedCheck_4107_;
goto v_resetjp_4098_;
}
else
{
lean_dec(v_x_4087_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4107_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4101_; lean_object* v___x_4103_; 
lean_inc(v___x_4084_);
v___x_4101_ = l_BaseIO_chainTask___redArg(v_a_4082_, v___x_4083_, v___x_4084_, v___x_4085_);
if (v_isShared_4100_ == 0)
{
lean_ctor_set(v___x_4099_, 0, v___x_4101_);
v___x_4103_ = v___x_4099_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v___x_4101_);
v___x_4103_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4103_);
v___x_4105_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4084_, v___x_4085_, v___x_4104_, v___f_4086_);
return v___x_4105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__4___boxed(lean_object* v_a_4109_, lean_object* v___x_4110_, lean_object* v___x_4111_, lean_object* v___x_4112_, lean_object* v___f_4113_, lean_object* v_x_4114_, lean_object* v___y_4115_){
_start:
{
uint8_t v___x_1434__boxed_4116_; lean_object* v_res_4117_; 
v___x_1434__boxed_4116_ = lean_unbox(v___x_4112_);
v_res_4117_ = l_Std_Async_EAsync_race___redArg___lam__4(v_a_4109_, v___x_4110_, v___x_4111_, v___x_1434__boxed_4116_, v___f_4113_, v_x_4114_);
return v_res_4117_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__5(lean_object* v___f_4118_, lean_object* v___f_4119_, lean_object* v___f_4120_, lean_object* v_a_4121_, lean_object* v_x_4122_){
_start:
{
if (lean_obj_tag(v_x_4122_) == 0)
{
lean_object* v_a_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4132_; 
lean_dec_ref(v_a_4121_);
lean_dec_ref(v___f_4120_);
lean_dec_ref(v___f_4119_);
lean_dec(v___f_4118_);
v_a_4124_ = lean_ctor_get(v_x_4122_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v_x_4122_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4126_ = v_x_4122_;
v_isShared_4127_ = v_isSharedCheck_4132_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_a_4124_);
lean_dec(v_x_4122_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4132_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4127_ == 0)
{
v___x_4129_ = v___x_4126_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_a_4124_);
v___x_4129_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
lean_object* v___x_4130_; 
v___x_4130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4130_, 0, v___x_4129_);
return v___x_4130_;
}
}
}
else
{
lean_object* v_a_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4149_; 
v_a_4133_ = lean_ctor_get(v_x_4122_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v_x_4122_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4135_ = v_x_4122_;
v_isShared_4136_ = v_isSharedCheck_4149_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_a_4133_);
lean_dec(v_x_4122_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4149_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; uint8_t v___x_4140_; lean_object* v___x_4141_; lean_object* v___f_4142_; lean_object* v___x_4143_; lean_object* v___x_4145_; 
v___x_4137_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_4137_, 0, lean_box(0));
lean_closure_set(v___x_4137_, 1, lean_box(0));
lean_closure_set(v___x_4137_, 2, v___f_4118_);
lean_closure_set(v___x_4137_, 3, lean_box(0));
v___x_4138_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4138_, 0, lean_box(0));
lean_closure_set(v___x_4138_, 1, lean_box(0));
lean_closure_set(v___x_4138_, 2, lean_box(0));
lean_closure_set(v___x_4138_, 3, v___x_4137_);
lean_closure_set(v___x_4138_, 4, v___f_4119_);
v___x_4139_ = lean_unsigned_to_nat(0u);
v___x_4140_ = 0;
v___x_4141_ = lean_box(v___x_4140_);
lean_inc_ref(v___x_4138_);
v___f_4142_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__4___boxed), 7, 5);
lean_closure_set(v___f_4142_, 0, v_a_4133_);
lean_closure_set(v___f_4142_, 1, v___x_4138_);
lean_closure_set(v___f_4142_, 2, v___x_4139_);
lean_closure_set(v___f_4142_, 3, v___x_4141_);
lean_closure_set(v___f_4142_, 4, v___f_4120_);
v___x_4143_ = l_BaseIO_chainTask___redArg(v_a_4121_, v___x_4138_, v___x_4139_, v___x_4140_);
if (v_isShared_4136_ == 0)
{
lean_ctor_set(v___x_4135_, 0, v___x_4143_);
v___x_4145_ = v___x_4135_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v___x_4143_);
v___x_4145_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4145_);
v___x_4147_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4139_, v___x_4140_, v___x_4146_, v___f_4142_);
return v___x_4147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__5___boxed(lean_object* v___f_4150_, lean_object* v___f_4151_, lean_object* v___f_4152_, lean_object* v_a_4153_, lean_object* v_x_4154_, lean_object* v___y_4155_){
_start:
{
lean_object* v_res_4156_; 
v_res_4156_ = l_Std_Async_EAsync_race___redArg___lam__5(v___f_4150_, v___f_4151_, v___f_4152_, v_a_4153_, v_x_4154_);
return v_res_4156_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__6(lean_object* v___f_4157_, lean_object* v___f_4158_, lean_object* v___f_4159_, lean_object* v_y_4160_, lean_object* v_prio_4161_, lean_object* v___f_4162_, lean_object* v_x_4163_){
_start:
{
if (lean_obj_tag(v_x_4163_) == 0)
{
lean_object* v_a_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4173_; 
lean_dec_ref(v___f_4162_);
lean_dec(v_prio_4161_);
lean_dec_ref(v_y_4160_);
lean_dec_ref(v___f_4159_);
lean_dec_ref(v___f_4158_);
lean_dec(v___f_4157_);
v_a_4165_ = lean_ctor_get(v_x_4163_, 0);
v_isSharedCheck_4173_ = !lean_is_exclusive(v_x_4163_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4167_ = v_x_4163_;
v_isShared_4168_ = v_isSharedCheck_4173_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_a_4165_);
lean_dec(v_x_4163_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4173_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4170_; 
if (v_isShared_4168_ == 0)
{
v___x_4170_ = v___x_4167_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4165_);
v___x_4170_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
lean_object* v___x_4171_; 
v___x_4171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4170_);
return v___x_4171_;
}
}
}
else
{
lean_object* v_a_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4190_; 
v_a_4174_ = lean_ctor_get(v_x_4163_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v_x_4163_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4176_ = v_x_4163_;
v_isShared_4177_ = v_isSharedCheck_4190_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_a_4174_);
lean_dec(v_x_4163_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4190_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v___f_4178_; lean_object* v___x_4179_; uint8_t v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; uint8_t v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4186_; 
v___f_4178_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__5___boxed), 6, 4);
lean_closure_set(v___f_4178_, 0, v___f_4157_);
lean_closure_set(v___f_4178_, 1, v___f_4158_);
lean_closure_set(v___f_4178_, 2, v___f_4159_);
lean_closure_set(v___f_4178_, 3, v_a_4174_);
v___x_4179_ = lean_unsigned_to_nat(0u);
v___x_4180_ = 0;
v___x_4181_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4181_, 0, lean_box(0));
lean_closure_set(v___x_4181_, 1, v_y_4160_);
v___x_4182_ = lean_io_as_task(v___x_4181_, v_prio_4161_);
v___x_4183_ = 1;
v___x_4184_ = lean_task_bind(v___x_4182_, v___f_4162_, v___x_4179_, v___x_4183_);
if (v_isShared_4177_ == 0)
{
lean_ctor_set(v___x_4176_, 0, v___x_4184_);
v___x_4186_ = v___x_4176_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v___x_4184_);
v___x_4186_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4186_);
v___x_4188_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4179_, v___x_4180_, v___x_4187_, v___f_4178_);
return v___x_4188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__6___boxed(lean_object* v___f_4191_, lean_object* v___f_4192_, lean_object* v___f_4193_, lean_object* v_y_4194_, lean_object* v_prio_4195_, lean_object* v___f_4196_, lean_object* v_x_4197_, lean_object* v___y_4198_){
_start:
{
lean_object* v_res_4199_; 
v_res_4199_ = l_Std_Async_EAsync_race___redArg___lam__6(v___f_4191_, v___f_4192_, v___f_4193_, v_y_4194_, v_prio_4195_, v___f_4196_, v_x_4197_);
return v_res_4199_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__7(lean_object* v___f_4200_, lean_object* v___f_4201_, lean_object* v___f_4202_, lean_object* v_y_4203_, lean_object* v_prio_4204_, lean_object* v___f_4205_, lean_object* v_x_4206_, lean_object* v___f_4207_, lean_object* v_x_4208_){
_start:
{
if (lean_obj_tag(v_x_4208_) == 0)
{
lean_object* v_a_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4218_; 
lean_dec_ref(v___f_4207_);
lean_dec_ref(v_x_4206_);
lean_dec_ref(v___f_4205_);
lean_dec(v_prio_4204_);
lean_dec_ref(v_y_4203_);
lean_dec(v___f_4202_);
lean_dec_ref(v___f_4201_);
lean_dec_ref(v___f_4200_);
v_a_4210_ = lean_ctor_get(v_x_4208_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v_x_4208_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4212_ = v_x_4208_;
v_isShared_4213_ = v_isSharedCheck_4218_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_a_4210_);
lean_dec(v_x_4208_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4218_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
lean_object* v___x_4215_; 
if (v_isShared_4213_ == 0)
{
v___x_4215_ = v___x_4212_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_a_4210_);
v___x_4215_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
lean_object* v___x_4216_; 
v___x_4216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4216_, 0, v___x_4215_);
return v___x_4216_;
}
}
}
else
{
lean_object* v_a_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4237_; 
v_a_4219_ = lean_ctor_get(v_x_4208_, 0);
v_isSharedCheck_4237_ = !lean_is_exclusive(v_x_4208_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4221_ = v_x_4208_;
v_isShared_4222_ = v_isSharedCheck_4237_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v_x_4208_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4237_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___f_4223_; lean_object* v___f_4224_; lean_object* v___f_4225_; lean_object* v___x_4226_; uint8_t v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; uint8_t v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4233_; 
lean_inc(v_a_4219_);
v___f_4223_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4223_, 0, v_a_4219_);
v___f_4224_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_4224_, 0, v_a_4219_);
lean_closure_set(v___f_4224_, 1, v___f_4200_);
lean_closure_set(v___f_4224_, 2, v___f_4201_);
lean_inc(v_prio_4204_);
v___f_4225_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__6___boxed), 8, 6);
lean_closure_set(v___f_4225_, 0, v___f_4202_);
lean_closure_set(v___f_4225_, 1, v___f_4223_);
lean_closure_set(v___f_4225_, 2, v___f_4224_);
lean_closure_set(v___f_4225_, 3, v_y_4203_);
lean_closure_set(v___f_4225_, 4, v_prio_4204_);
lean_closure_set(v___f_4225_, 5, v___f_4205_);
v___x_4226_ = lean_unsigned_to_nat(0u);
v___x_4227_ = 0;
v___x_4228_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4228_, 0, lean_box(0));
lean_closure_set(v___x_4228_, 1, v_x_4206_);
v___x_4229_ = lean_io_as_task(v___x_4228_, v_prio_4204_);
v___x_4230_ = 1;
v___x_4231_ = lean_task_bind(v___x_4229_, v___f_4207_, v___x_4226_, v___x_4230_);
if (v_isShared_4222_ == 0)
{
lean_ctor_set(v___x_4221_, 0, v___x_4231_);
v___x_4233_ = v___x_4221_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v___x_4231_);
v___x_4233_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
lean_object* v___x_4234_; lean_object* v___x_4235_; 
v___x_4234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4234_, 0, v___x_4233_);
v___x_4235_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4226_, v___x_4227_, v___x_4234_, v___f_4225_);
return v___x_4235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___lam__7___boxed(lean_object* v___f_4238_, lean_object* v___f_4239_, lean_object* v___f_4240_, lean_object* v_y_4241_, lean_object* v_prio_4242_, lean_object* v___f_4243_, lean_object* v_x_4244_, lean_object* v___f_4245_, lean_object* v_x_4246_, lean_object* v___y_4247_){
_start:
{
lean_object* v_res_4248_; 
v_res_4248_ = l_Std_Async_EAsync_race___redArg___lam__7(v___f_4238_, v___f_4239_, v___f_4240_, v_y_4241_, v_prio_4242_, v___f_4243_, v_x_4244_, v___f_4245_, v_x_4246_);
return v_res_4248_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg(lean_object* v_x_4251_, lean_object* v_y_4252_, lean_object* v_prio_4253_){
_start:
{
lean_object* v___f_4255_; lean_object* v___f_4256_; lean_object* v___f_4257_; lean_object* v___f_4258_; lean_object* v___f_4259_; lean_object* v___x_4260_; uint8_t v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
v___f_4255_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___f_4256_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__0));
v___f_4257_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__1));
v___f_4258_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_4259_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_4259_, 0, v___f_4257_);
lean_closure_set(v___f_4259_, 1, v___f_4256_);
lean_closure_set(v___f_4259_, 2, v___f_4258_);
lean_closure_set(v___f_4259_, 3, v_y_4252_);
lean_closure_set(v___f_4259_, 4, v_prio_4253_);
lean_closure_set(v___f_4259_, 5, v___f_4255_);
lean_closure_set(v___f_4259_, 6, v_x_4251_);
lean_closure_set(v___f_4259_, 7, v___f_4255_);
v___x_4260_ = lean_unsigned_to_nat(0u);
v___x_4261_ = 0;
v___x_4262_ = lean_io_promise_new();
v___x_4263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4263_, 0, v___x_4262_);
v___x_4264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4264_, 0, v___x_4263_);
v___x_4265_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4260_, v___x_4261_, v___x_4264_, v___f_4259_);
return v___x_4265_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___redArg___boxed(lean_object* v_x_4266_, lean_object* v_y_4267_, lean_object* v_prio_4268_, lean_object* v_a_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l_Std_Async_EAsync_race___redArg(v_x_4266_, v_y_4267_, v_prio_4268_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race(lean_object* v_00_u03b1_4271_, lean_object* v_00_u03b5_4272_, lean_object* v_inst_4273_, lean_object* v_x_4274_, lean_object* v_y_4275_, lean_object* v_prio_4276_){
_start:
{
lean_object* v___f_4278_; lean_object* v___f_4279_; lean_object* v___f_4280_; lean_object* v___f_4281_; lean_object* v___f_4282_; lean_object* v___x_4283_; uint8_t v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; 
v___f_4278_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___f_4279_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__0));
v___f_4280_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__1));
v___f_4281_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_4282_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_4282_, 0, v___f_4280_);
lean_closure_set(v___f_4282_, 1, v___f_4279_);
lean_closure_set(v___f_4282_, 2, v___f_4281_);
lean_closure_set(v___f_4282_, 3, v_y_4275_);
lean_closure_set(v___f_4282_, 4, v_prio_4276_);
lean_closure_set(v___f_4282_, 5, v___f_4278_);
lean_closure_set(v___f_4282_, 6, v_x_4274_);
lean_closure_set(v___f_4282_, 7, v___f_4278_);
v___x_4283_ = lean_unsigned_to_nat(0u);
v___x_4284_ = 0;
v___x_4285_ = lean_io_promise_new();
v___x_4286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4286_, 0, v___x_4285_);
v___x_4287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4286_);
v___x_4288_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4283_, v___x_4284_, v___x_4287_, v___f_4282_);
return v___x_4288_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_race___boxed(lean_object* v_00_u03b1_4289_, lean_object* v_00_u03b5_4290_, lean_object* v_inst_4291_, lean_object* v_x_4292_, lean_object* v_y_4293_, lean_object* v_prio_4294_, lean_object* v_a_4295_){
_start:
{
lean_object* v_res_4296_; 
v_res_4296_ = l_Std_Async_EAsync_race(v_00_u03b1_4289_, v_00_u03b5_4290_, v_inst_4291_, v_x_4292_, v_y_4293_, v_prio_4294_);
lean_dec(v_inst_4291_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1(lean_object* v_prio_4297_, lean_object* v___f_4298_, lean_object* v_x_4299_){
_start:
{
lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; uint8_t v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; 
v___x_4301_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4301_, 0, lean_box(0));
lean_closure_set(v___x_4301_, 1, v_x_4299_);
v___x_4302_ = lean_io_as_task(v___x_4301_, v_prio_4297_);
v___x_4303_ = lean_unsigned_to_nat(0u);
v___x_4304_ = 1;
v___x_4305_ = lean_task_bind(v___x_4302_, v___f_4298_, v___x_4303_, v___x_4304_);
v___x_4306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4305_);
v___x_4307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4306_);
return v___x_4307_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1___boxed(lean_object* v_prio_4308_, lean_object* v___f_4309_, lean_object* v_x_4310_, lean_object* v___y_4311_){
_start:
{
lean_object* v_res_4312_; 
v_res_4312_ = l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1(v_prio_4308_, v___f_4309_, v_x_4310_);
return v_res_4312_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__0(lean_object* v___y_4313_){
_start:
{
lean_object* v___x_4315_; 
v___x_4315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4315_, 0, v___y_4313_);
return v___x_4315_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__0___boxed(lean_object* v___y_4316_, lean_object* v___y_4317_){
_start:
{
lean_object* v_res_4318_; 
v_res_4318_ = l_Std_Async_EAsync_concurrentlyAll___redArg___lam__0(v___y_4316_);
return v_res_4318_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__2(lean_object* v___x_4319_, lean_object* v___f_4320_, lean_object* v_x_4321_){
_start:
{
if (lean_obj_tag(v_x_4321_) == 0)
{
lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4331_; 
lean_dec_ref(v___f_4320_);
lean_dec_ref(v___x_4319_);
v_a_4323_ = lean_ctor_get(v_x_4321_, 0);
v_isSharedCheck_4331_ = !lean_is_exclusive(v_x_4321_);
if (v_isSharedCheck_4331_ == 0)
{
v___x_4325_ = v_x_4321_;
v_isShared_4326_ = v_isSharedCheck_4331_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_dec(v_x_4321_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4331_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4328_; 
if (v_isShared_4326_ == 0)
{
v___x_4328_ = v___x_4325_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v_a_4323_);
v___x_4328_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
lean_object* v___x_4329_; 
v___x_4329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4329_, 0, v___x_4328_);
return v___x_4329_;
}
}
}
else
{
lean_object* v_a_4332_; size_t v_sz_4333_; size_t v___x_4334_; lean_object* v___x_292__overap_4335_; lean_object* v___x_4336_; 
v_a_4332_ = lean_ctor_get(v_x_4321_, 0);
lean_inc(v_a_4332_);
lean_dec_ref_known(v_x_4321_, 1);
v_sz_4333_ = lean_array_size(v_a_4332_);
v___x_4334_ = ((size_t)0ULL);
v___x_292__overap_4335_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_4319_, v___f_4320_, v_sz_4333_, v___x_4334_, v_a_4332_);
v___x_4336_ = lean_apply_1(v___x_292__overap_4335_, lean_box(0));
return v___x_4336_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___lam__2___boxed(lean_object* v___x_4337_, lean_object* v___f_4338_, lean_object* v_x_4339_, lean_object* v___y_4340_){
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = l_Std_Async_EAsync_concurrentlyAll___redArg___lam__2(v___x_4337_, v___f_4338_, v_x_4339_);
return v_res_4341_;
}
}
static lean_object* _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1(void){
_start:
{
lean_object* v___f_4343_; lean_object* v___x_4344_; lean_object* v___f_4345_; 
v___f_4343_ = ((lean_object*)(l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0));
v___x_4344_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___closed__0, &l_Std_Async_EAsync_instMonad___closed__0_once, _init_l_Std_Async_EAsync_instMonad___closed__0);
v___f_4345_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrentlyAll___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4345_, 0, v___x_4344_);
lean_closure_set(v___f_4345_, 1, v___f_4343_);
return v___f_4345_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg(lean_object* v_xs_4346_, lean_object* v_prio_4347_){
_start:
{
lean_object* v___f_4349_; lean_object* v___f_4350_; lean_object* v___x_4351_; lean_object* v___f_4352_; lean_object* v___x_4353_; uint8_t v___x_4354_; size_t v_sz_4355_; size_t v___x_4356_; lean_object* v___x_217__overap_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; 
v___f_4349_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___f_4350_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4350_, 0, v_prio_4347_);
lean_closure_set(v___f_4350_, 1, v___f_4349_);
v___x_4351_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___closed__0, &l_Std_Async_EAsync_instMonad___closed__0_once, _init_l_Std_Async_EAsync_instMonad___closed__0);
v___f_4352_ = lean_obj_once(&l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1, &l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1_once, _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1);
v___x_4353_ = lean_unsigned_to_nat(0u);
v___x_4354_ = 0;
v_sz_4355_ = lean_array_size(v_xs_4346_);
v___x_4356_ = ((size_t)0ULL);
v___x_217__overap_4357_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_4351_, v___f_4350_, v_sz_4355_, v___x_4356_, v_xs_4346_);
v___x_4358_ = lean_apply_1(v___x_217__overap_4357_, lean_box(0));
v___x_4359_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4353_, v___x_4354_, v___x_4358_, v___f_4352_);
return v___x_4359_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___redArg___boxed(lean_object* v_xs_4360_, lean_object* v_prio_4361_, lean_object* v_a_4362_){
_start:
{
lean_object* v_res_4363_; 
v_res_4363_ = l_Std_Async_EAsync_concurrentlyAll___redArg(v_xs_4360_, v_prio_4361_);
return v_res_4363_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll(lean_object* v_00_u03b5_4364_, lean_object* v_00_u03b1_4365_, lean_object* v_xs_4366_, lean_object* v_prio_4367_){
_start:
{
lean_object* v___f_4369_; lean_object* v___f_4370_; lean_object* v___x_4371_; lean_object* v___f_4372_; lean_object* v___x_4373_; uint8_t v___x_4374_; size_t v_sz_4375_; size_t v___x_4376_; lean_object* v___x_258__overap_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; 
v___f_4369_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___f_4370_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_4370_, 0, v_prio_4367_);
lean_closure_set(v___f_4370_, 1, v___f_4369_);
v___x_4371_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___closed__0, &l_Std_Async_EAsync_instMonad___closed__0_once, _init_l_Std_Async_EAsync_instMonad___closed__0);
v___f_4372_ = lean_obj_once(&l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1, &l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1_once, _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1);
v___x_4373_ = lean_unsigned_to_nat(0u);
v___x_4374_ = 0;
v_sz_4375_ = lean_array_size(v_xs_4366_);
v___x_4376_ = ((size_t)0ULL);
v___x_258__overap_4377_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_4371_, v___f_4370_, v_sz_4375_, v___x_4376_, v_xs_4366_);
v___x_4378_ = lean_apply_1(v___x_258__overap_4377_, lean_box(0));
v___x_4379_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4373_, v___x_4374_, v___x_4378_, v___f_4372_);
return v___x_4379_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_concurrentlyAll___boxed(lean_object* v_00_u03b5_4380_, lean_object* v_00_u03b1_4381_, lean_object* v_xs_4382_, lean_object* v_prio_4383_, lean_object* v_a_4384_){
_start:
{
lean_object* v_res_4385_; 
v_res_4385_ = l_Std_Async_EAsync_concurrentlyAll(v_00_u03b5_4380_, v_00_u03b1_4381_, v_xs_4382_, v_prio_4383_);
return v_res_4385_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__4(lean_object* v___f_4386_, lean_object* v___f_4387_, lean_object* v_x_4388_){
_start:
{
if (lean_obj_tag(v_x_4388_) == 0)
{
lean_object* v_a_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4398_; 
lean_dec_ref(v___f_4387_);
lean_dec(v___f_4386_);
v_a_4390_ = lean_ctor_get(v_x_4388_, 0);
v_isSharedCheck_4398_ = !lean_is_exclusive(v_x_4388_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4392_ = v_x_4388_;
v_isShared_4393_ = v_isSharedCheck_4398_;
goto v_resetjp_4391_;
}
else
{
lean_inc(v_a_4390_);
lean_dec(v_x_4388_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4398_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
lean_object* v___x_4395_; 
if (v_isShared_4393_ == 0)
{
v___x_4395_ = v___x_4392_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_a_4390_);
v___x_4395_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
lean_object* v___x_4396_; 
v___x_4396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4396_, 0, v___x_4395_);
return v___x_4396_;
}
}
}
else
{
lean_object* v_a_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4412_; 
v_a_4399_ = lean_ctor_get(v_x_4388_, 0);
v_isSharedCheck_4412_ = !lean_is_exclusive(v_x_4388_);
if (v_isSharedCheck_4412_ == 0)
{
v___x_4401_ = v_x_4388_;
v_isShared_4402_ = v_isSharedCheck_4412_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_a_4399_);
lean_dec(v_x_4388_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4412_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; uint8_t v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4409_; 
v___x_4403_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_4403_, 0, lean_box(0));
lean_closure_set(v___x_4403_, 1, lean_box(0));
lean_closure_set(v___x_4403_, 2, v___f_4386_);
lean_closure_set(v___x_4403_, 3, lean_box(0));
v___x_4404_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4404_, 0, lean_box(0));
lean_closure_set(v___x_4404_, 1, lean_box(0));
lean_closure_set(v___x_4404_, 2, lean_box(0));
lean_closure_set(v___x_4404_, 3, v___x_4403_);
lean_closure_set(v___x_4404_, 4, v___f_4387_);
v___x_4405_ = lean_unsigned_to_nat(0u);
v___x_4406_ = 0;
v___x_4407_ = l_BaseIO_chainTask___redArg(v_a_4399_, v___x_4404_, v___x_4405_, v___x_4406_);
if (v_isShared_4402_ == 0)
{
lean_ctor_set(v___x_4401_, 0, v___x_4407_);
v___x_4409_ = v___x_4401_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v___x_4407_);
v___x_4409_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
lean_object* v___x_4410_; 
v___x_4410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4410_, 0, v___x_4409_);
return v___x_4410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__4___boxed(lean_object* v___f_4413_, lean_object* v___f_4414_, lean_object* v_x_4415_, lean_object* v___y_4416_){
_start:
{
lean_object* v_res_4417_; 
v_res_4417_ = l_Std_Async_EAsync_raceAll___redArg___lam__4(v___f_4413_, v___f_4414_, v_x_4415_);
return v_res_4417_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__0(lean_object* v_prio_4418_, lean_object* v___f_4419_, lean_object* v___f_4420_, lean_object* v_x_4421_){
_start:
{
lean_object* v___x_4423_; uint8_t v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; uint8_t v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; 
v___x_4423_ = lean_unsigned_to_nat(0u);
v___x_4424_ = 0;
v___x_4425_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4425_, 0, lean_box(0));
lean_closure_set(v___x_4425_, 1, v_x_4421_);
v___x_4426_ = lean_io_as_task(v___x_4425_, v_prio_4418_);
v___x_4427_ = 1;
v___x_4428_ = lean_task_bind(v___x_4426_, v___f_4419_, v___x_4423_, v___x_4427_);
v___x_4429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4429_, 0, v___x_4428_);
v___x_4430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4430_, 0, v___x_4429_);
v___x_4431_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4423_, v___x_4424_, v___x_4430_, v___f_4420_);
return v___x_4431_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__0___boxed(lean_object* v_prio_4432_, lean_object* v___f_4433_, lean_object* v___f_4434_, lean_object* v_x_4435_, lean_object* v___y_4436_){
_start:
{
lean_object* v_res_4437_; 
v_res_4437_ = l_Std_Async_EAsync_raceAll___redArg___lam__0(v_prio_4432_, v___f_4433_, v___f_4434_, v_x_4435_);
return v_res_4437_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__2(lean_object* v___f_4438_, lean_object* v_prio_4439_, lean_object* v___f_4440_, lean_object* v___f_4441_, lean_object* v___f_4442_, lean_object* v_inst_4443_, lean_object* v_xs_4444_, lean_object* v_x_4445_){
_start:
{
if (lean_obj_tag(v_x_4445_) == 0)
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4455_; 
lean_dec(v_xs_4444_);
lean_dec_ref(v_inst_4443_);
lean_dec_ref(v___f_4442_);
lean_dec_ref(v___f_4441_);
lean_dec_ref(v___f_4440_);
lean_dec(v_prio_4439_);
lean_dec(v___f_4438_);
v_a_4447_ = lean_ctor_get(v_x_4445_, 0);
v_isSharedCheck_4455_ = !lean_is_exclusive(v_x_4445_);
if (v_isSharedCheck_4455_ == 0)
{
v___x_4449_ = v_x_4445_;
v_isShared_4450_ = v_isSharedCheck_4455_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v_x_4445_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4455_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4452_; 
if (v_isShared_4450_ == 0)
{
v___x_4452_ = v___x_4449_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4454_; 
v_reuseFailAlloc_4454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4454_, 0, v_a_4447_);
v___x_4452_ = v_reuseFailAlloc_4454_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
lean_object* v___x_4453_; 
v___x_4453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4453_, 0, v___x_4452_);
return v___x_4453_;
}
}
}
else
{
lean_object* v_a_4456_; lean_object* v___f_4457_; lean_object* v___f_4458_; lean_object* v___f_4459_; lean_object* v___f_4460_; lean_object* v___x_4461_; uint8_t v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; 
v_a_4456_ = lean_ctor_get(v_x_4445_, 0);
lean_inc_n(v_a_4456_, 2);
lean_dec_ref_known(v_x_4445_, 1);
v___f_4457_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4457_, 0, v_a_4456_);
v___f_4458_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_raceAll___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_4458_, 0, v___f_4438_);
lean_closure_set(v___f_4458_, 1, v___f_4457_);
v___f_4459_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_raceAll___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4459_, 0, v_prio_4439_);
lean_closure_set(v___f_4459_, 1, v___f_4440_);
lean_closure_set(v___f_4459_, 2, v___f_4458_);
v___f_4460_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_race___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_4460_, 0, v_a_4456_);
lean_closure_set(v___f_4460_, 1, v___f_4441_);
lean_closure_set(v___f_4460_, 2, v___f_4442_);
v___x_4461_ = lean_unsigned_to_nat(0u);
v___x_4462_ = 0;
v___x_4463_ = lean_apply_3(v_inst_4443_, v_xs_4444_, v___f_4459_, lean_box(0));
v___x_4464_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4461_, v___x_4462_, v___x_4463_, v___f_4460_);
return v___x_4464_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___lam__2___boxed(lean_object* v___f_4465_, lean_object* v_prio_4466_, lean_object* v___f_4467_, lean_object* v___f_4468_, lean_object* v___f_4469_, lean_object* v_inst_4470_, lean_object* v_xs_4471_, lean_object* v_x_4472_, lean_object* v___y_4473_){
_start:
{
lean_object* v_res_4474_; 
v_res_4474_ = l_Std_Async_EAsync_raceAll___redArg___lam__2(v___f_4465_, v_prio_4466_, v___f_4467_, v___f_4468_, v___f_4469_, v_inst_4470_, v_xs_4471_, v_x_4472_);
return v_res_4474_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg(lean_object* v_inst_4475_, lean_object* v_xs_4476_, lean_object* v_prio_4477_){
_start:
{
lean_object* v___f_4479_; lean_object* v___f_4480_; lean_object* v___f_4481_; lean_object* v___f_4482_; lean_object* v___f_4483_; lean_object* v___x_4484_; uint8_t v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; 
v___f_4479_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__1));
v___f_4480_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__0));
v___f_4481_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___f_4482_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_4483_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_raceAll___redArg___lam__2___boxed), 9, 7);
lean_closure_set(v___f_4483_, 0, v___f_4482_);
lean_closure_set(v___f_4483_, 1, v_prio_4477_);
lean_closure_set(v___f_4483_, 2, v___f_4481_);
lean_closure_set(v___f_4483_, 3, v___f_4479_);
lean_closure_set(v___f_4483_, 4, v___f_4480_);
lean_closure_set(v___f_4483_, 5, v_inst_4475_);
lean_closure_set(v___f_4483_, 6, v_xs_4476_);
v___x_4484_ = lean_unsigned_to_nat(0u);
v___x_4485_ = 0;
v___x_4486_ = lean_io_promise_new();
v___x_4487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4487_, 0, v___x_4486_);
v___x_4488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4488_, 0, v___x_4487_);
v___x_4489_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4484_, v___x_4485_, v___x_4488_, v___f_4483_);
return v___x_4489_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___redArg___boxed(lean_object* v_inst_4490_, lean_object* v_xs_4491_, lean_object* v_prio_4492_, lean_object* v_a_4493_){
_start:
{
lean_object* v_res_4494_; 
v_res_4494_ = l_Std_Async_EAsync_raceAll___redArg(v_inst_4490_, v_xs_4491_, v_prio_4492_);
return v_res_4494_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll(lean_object* v_00_u03b1_4495_, lean_object* v_00_u03b5_4496_, lean_object* v_c_4497_, lean_object* v_inst_4498_, lean_object* v_inst_4499_, lean_object* v_xs_4500_, lean_object* v_prio_4501_){
_start:
{
lean_object* v___f_4503_; lean_object* v___f_4504_; lean_object* v___f_4505_; lean_object* v___f_4506_; lean_object* v___f_4507_; lean_object* v___x_4508_; uint8_t v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; 
v___f_4503_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__1));
v___f_4504_ = ((lean_object*)(l_Std_Async_EAsync_race___redArg___closed__0));
v___f_4505_ = ((lean_object*)(l_Std_Async_EAsync_asTask___redArg___closed__0));
v___f_4506_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_4507_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_raceAll___redArg___lam__2___boxed), 9, 7);
lean_closure_set(v___f_4507_, 0, v___f_4506_);
lean_closure_set(v___f_4507_, 1, v_prio_4501_);
lean_closure_set(v___f_4507_, 2, v___f_4505_);
lean_closure_set(v___f_4507_, 3, v___f_4503_);
lean_closure_set(v___f_4507_, 4, v___f_4504_);
lean_closure_set(v___f_4507_, 5, v_inst_4499_);
lean_closure_set(v___f_4507_, 6, v_xs_4500_);
v___x_4508_ = lean_unsigned_to_nat(0u);
v___x_4509_ = 0;
v___x_4510_ = lean_io_promise_new();
v___x_4511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4511_, 0, v___x_4510_);
v___x_4512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4512_, 0, v___x_4511_);
v___x_4513_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4508_, v___x_4509_, v___x_4512_, v___f_4507_);
return v___x_4513_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_EAsync_raceAll___boxed(lean_object* v_00_u03b1_4514_, lean_object* v_00_u03b5_4515_, lean_object* v_c_4516_, lean_object* v_inst_4517_, lean_object* v_inst_4518_, lean_object* v_xs_4519_, lean_object* v_prio_4520_, lean_object* v_a_4521_){
_start:
{
lean_object* v_res_4522_; 
v_res_4522_ = l_Std_Async_EAsync_raceAll(v_00_u03b1_4514_, v_00_u03b5_4515_, v_c_4516_, v_inst_4517_, v_inst_4518_, v_xs_4519_, v_prio_4520_);
lean_dec(v_inst_4517_);
return v_res_4522_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_toIO___redArg(lean_object* v_x_4523_){
_start:
{
lean_object* v___x_4525_; 
v___x_4525_ = lean_apply_1(v_x_4523_, lean_box(0));
if (lean_obj_tag(v___x_4525_) == 0)
{
lean_object* v_a_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4534_; 
v_a_4526_ = lean_ctor_get(v___x_4525_, 0);
v_isSharedCheck_4534_ = !lean_is_exclusive(v___x_4525_);
if (v_isSharedCheck_4534_ == 0)
{
v___x_4528_ = v___x_4525_;
v_isShared_4529_ = v_isSharedCheck_4534_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_a_4526_);
lean_dec(v___x_4525_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4534_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v___x_4530_; lean_object* v___x_4532_; 
v___x_4530_ = lean_task_pure(v_a_4526_);
if (v_isShared_4529_ == 0)
{
lean_ctor_set(v___x_4528_, 0, v___x_4530_);
v___x_4532_ = v___x_4528_;
goto v_reusejp_4531_;
}
else
{
lean_object* v_reuseFailAlloc_4533_; 
v_reuseFailAlloc_4533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4533_, 0, v___x_4530_);
v___x_4532_ = v_reuseFailAlloc_4533_;
goto v_reusejp_4531_;
}
v_reusejp_4531_:
{
return v___x_4532_;
}
}
}
else
{
lean_object* v_a_4535_; lean_object* v___x_4537_; uint8_t v_isShared_4538_; uint8_t v_isSharedCheck_4542_; 
v_a_4535_ = lean_ctor_get(v___x_4525_, 0);
v_isSharedCheck_4542_ = !lean_is_exclusive(v___x_4525_);
if (v_isSharedCheck_4542_ == 0)
{
v___x_4537_ = v___x_4525_;
v_isShared_4538_ = v_isSharedCheck_4542_;
goto v_resetjp_4536_;
}
else
{
lean_inc(v_a_4535_);
lean_dec(v___x_4525_);
v___x_4537_ = lean_box(0);
v_isShared_4538_ = v_isSharedCheck_4542_;
goto v_resetjp_4536_;
}
v_resetjp_4536_:
{
lean_object* v___x_4540_; 
if (v_isShared_4538_ == 0)
{
lean_ctor_set_tag(v___x_4537_, 0);
v___x_4540_ = v___x_4537_;
goto v_reusejp_4539_;
}
else
{
lean_object* v_reuseFailAlloc_4541_; 
v_reuseFailAlloc_4541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4541_, 0, v_a_4535_);
v___x_4540_ = v_reuseFailAlloc_4541_;
goto v_reusejp_4539_;
}
v_reusejp_4539_:
{
return v___x_4540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_toIO___redArg___boxed(lean_object* v_x_4543_, lean_object* v_a_4544_){
_start:
{
lean_object* v_res_4545_; 
v_res_4545_ = l_Std_Async_Async_toIO___redArg(v_x_4543_);
return v_res_4545_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_toIO(lean_object* v_00_u03b1_4546_, lean_object* v_x_4547_){
_start:
{
lean_object* v___x_4549_; 
v___x_4549_ = lean_apply_1(v_x_4547_, lean_box(0));
if (lean_obj_tag(v___x_4549_) == 0)
{
lean_object* v_a_4550_; lean_object* v___x_4552_; uint8_t v_isShared_4553_; uint8_t v_isSharedCheck_4558_; 
v_a_4550_ = lean_ctor_get(v___x_4549_, 0);
v_isSharedCheck_4558_ = !lean_is_exclusive(v___x_4549_);
if (v_isSharedCheck_4558_ == 0)
{
v___x_4552_ = v___x_4549_;
v_isShared_4553_ = v_isSharedCheck_4558_;
goto v_resetjp_4551_;
}
else
{
lean_inc(v_a_4550_);
lean_dec(v___x_4549_);
v___x_4552_ = lean_box(0);
v_isShared_4553_ = v_isSharedCheck_4558_;
goto v_resetjp_4551_;
}
v_resetjp_4551_:
{
lean_object* v___x_4554_; lean_object* v___x_4556_; 
v___x_4554_ = lean_task_pure(v_a_4550_);
if (v_isShared_4553_ == 0)
{
lean_ctor_set(v___x_4552_, 0, v___x_4554_);
v___x_4556_ = v___x_4552_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v___x_4554_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
}
}
}
else
{
lean_object* v_a_4559_; lean_object* v___x_4561_; uint8_t v_isShared_4562_; uint8_t v_isSharedCheck_4566_; 
v_a_4559_ = lean_ctor_get(v___x_4549_, 0);
v_isSharedCheck_4566_ = !lean_is_exclusive(v___x_4549_);
if (v_isSharedCheck_4566_ == 0)
{
v___x_4561_ = v___x_4549_;
v_isShared_4562_ = v_isSharedCheck_4566_;
goto v_resetjp_4560_;
}
else
{
lean_inc(v_a_4559_);
lean_dec(v___x_4549_);
v___x_4561_ = lean_box(0);
v_isShared_4562_ = v_isSharedCheck_4566_;
goto v_resetjp_4560_;
}
v_resetjp_4560_:
{
lean_object* v___x_4564_; 
if (v_isShared_4562_ == 0)
{
lean_ctor_set_tag(v___x_4561_, 0);
v___x_4564_ = v___x_4561_;
goto v_reusejp_4563_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v_a_4559_);
v___x_4564_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4563_;
}
v_reusejp_4563_:
{
return v___x_4564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_toIO___boxed(lean_object* v_00_u03b1_4567_, lean_object* v_x_4568_, lean_object* v_a_4569_){
_start:
{
lean_object* v_res_4570_; 
v_res_4570_ = l_Std_Async_Async_toIO(v_00_u03b1_4567_, v_x_4568_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_block___redArg(lean_object* v_x_4571_, lean_object* v_prio_4572_){
_start:
{
lean_object* v___f_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; uint8_t v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; 
v___f_4574_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___x_4575_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4575_, 0, lean_box(0));
lean_closure_set(v___x_4575_, 1, v_x_4571_);
v___x_4576_ = lean_io_as_task(v___x_4575_, v_prio_4572_);
v___x_4577_ = lean_unsigned_to_nat(0u);
v___x_4578_ = 1;
v___x_4579_ = lean_task_bind(v___x_4576_, v___f_4574_, v___x_4577_, v___x_4578_);
v___x_4580_ = lean_task_get_own(v___x_4579_);
if (lean_obj_tag(v___x_4580_) == 0)
{
lean_object* v_a_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4588_; 
v_a_4581_ = lean_ctor_get(v___x_4580_, 0);
v_isSharedCheck_4588_ = !lean_is_exclusive(v___x_4580_);
if (v_isSharedCheck_4588_ == 0)
{
v___x_4583_ = v___x_4580_;
v_isShared_4584_ = v_isSharedCheck_4588_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_a_4581_);
lean_dec(v___x_4580_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4588_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
lean_object* v___x_4586_; 
if (v_isShared_4584_ == 0)
{
lean_ctor_set_tag(v___x_4583_, 1);
v___x_4586_ = v___x_4583_;
goto v_reusejp_4585_;
}
else
{
lean_object* v_reuseFailAlloc_4587_; 
v_reuseFailAlloc_4587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4587_, 0, v_a_4581_);
v___x_4586_ = v_reuseFailAlloc_4587_;
goto v_reusejp_4585_;
}
v_reusejp_4585_:
{
return v___x_4586_;
}
}
}
else
{
lean_object* v_a_4589_; lean_object* v___x_4591_; uint8_t v_isShared_4592_; uint8_t v_isSharedCheck_4596_; 
v_a_4589_ = lean_ctor_get(v___x_4580_, 0);
v_isSharedCheck_4596_ = !lean_is_exclusive(v___x_4580_);
if (v_isSharedCheck_4596_ == 0)
{
v___x_4591_ = v___x_4580_;
v_isShared_4592_ = v_isSharedCheck_4596_;
goto v_resetjp_4590_;
}
else
{
lean_inc(v_a_4589_);
lean_dec(v___x_4580_);
v___x_4591_ = lean_box(0);
v_isShared_4592_ = v_isSharedCheck_4596_;
goto v_resetjp_4590_;
}
v_resetjp_4590_:
{
lean_object* v___x_4594_; 
if (v_isShared_4592_ == 0)
{
lean_ctor_set_tag(v___x_4591_, 0);
v___x_4594_ = v___x_4591_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4595_; 
v_reuseFailAlloc_4595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4595_, 0, v_a_4589_);
v___x_4594_ = v_reuseFailAlloc_4595_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
return v___x_4594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_block___redArg___boxed(lean_object* v_x_4597_, lean_object* v_prio_4598_, lean_object* v_a_4599_){
_start:
{
lean_object* v_res_4600_; 
v_res_4600_ = l_Std_Async_Async_block___redArg(v_x_4597_, v_prio_4598_);
return v_res_4600_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_block(lean_object* v_00_u03b1_4601_, lean_object* v_x_4602_, lean_object* v_prio_4603_){
_start:
{
lean_object* v___f_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; uint8_t v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; 
v___f_4605_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___x_4606_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_4606_, 0, lean_box(0));
lean_closure_set(v___x_4606_, 1, v_x_4602_);
v___x_4607_ = lean_io_as_task(v___x_4606_, v_prio_4603_);
v___x_4608_ = lean_unsigned_to_nat(0u);
v___x_4609_ = 1;
v___x_4610_ = lean_task_bind(v___x_4607_, v___f_4605_, v___x_4608_, v___x_4609_);
v___x_4611_ = lean_task_get_own(v___x_4610_);
if (lean_obj_tag(v___x_4611_) == 0)
{
lean_object* v_a_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4619_; 
v_a_4612_ = lean_ctor_get(v___x_4611_, 0);
v_isSharedCheck_4619_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4619_ == 0)
{
v___x_4614_ = v___x_4611_;
v_isShared_4615_ = v_isSharedCheck_4619_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_a_4612_);
lean_dec(v___x_4611_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4619_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
lean_object* v___x_4617_; 
if (v_isShared_4615_ == 0)
{
lean_ctor_set_tag(v___x_4614_, 1);
v___x_4617_ = v___x_4614_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v_a_4612_);
v___x_4617_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
return v___x_4617_;
}
}
}
else
{
lean_object* v_a_4620_; lean_object* v___x_4622_; uint8_t v_isShared_4623_; uint8_t v_isSharedCheck_4627_; 
v_a_4620_ = lean_ctor_get(v___x_4611_, 0);
v_isSharedCheck_4627_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4627_ == 0)
{
v___x_4622_ = v___x_4611_;
v_isShared_4623_ = v_isSharedCheck_4627_;
goto v_resetjp_4621_;
}
else
{
lean_inc(v_a_4620_);
lean_dec(v___x_4611_);
v___x_4622_ = lean_box(0);
v_isShared_4623_ = v_isSharedCheck_4627_;
goto v_resetjp_4621_;
}
v_resetjp_4621_:
{
lean_object* v___x_4625_; 
if (v_isShared_4623_ == 0)
{
lean_ctor_set_tag(v___x_4622_, 0);
v___x_4625_ = v___x_4622_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v_a_4620_);
v___x_4625_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
return v___x_4625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_block___boxed(lean_object* v_00_u03b1_4628_, lean_object* v_x_4629_, lean_object* v_prio_4630_, lean_object* v_a_4631_){
_start:
{
lean_object* v_res_4632_; 
v_res_4632_ = l_Std_Async_Async_block(v_00_u03b1_4628_, v_x_4629_, v_prio_4630_);
return v_res_4632_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise___redArg___lam__1(lean_object* v___f_4633_, lean_object* v_x_4634_){
_start:
{
if (lean_obj_tag(v_x_4634_) == 0)
{
lean_object* v_a_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4644_; 
lean_dec_ref(v___f_4633_);
v_a_4636_ = lean_ctor_get(v_x_4634_, 0);
v_isSharedCheck_4644_ = !lean_is_exclusive(v_x_4634_);
if (v_isSharedCheck_4644_ == 0)
{
v___x_4638_ = v_x_4634_;
v_isShared_4639_ = v_isSharedCheck_4644_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_a_4636_);
lean_dec(v_x_4634_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4644_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
lean_object* v___x_4641_; 
if (v_isShared_4639_ == 0)
{
v___x_4641_ = v___x_4638_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4643_; 
v_reuseFailAlloc_4643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4643_, 0, v_a_4636_);
v___x_4641_ = v_reuseFailAlloc_4643_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
lean_object* v___x_4642_; 
v___x_4642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4642_, 0, v___x_4641_);
return v___x_4642_;
}
}
}
else
{
lean_object* v_a_4645_; 
v_a_4645_ = lean_ctor_get(v_x_4634_, 0);
lean_inc(v_a_4645_);
lean_dec_ref_known(v_x_4634_, 1);
if (lean_obj_tag(v_a_4645_) == 0)
{
lean_object* v_a_4646_; lean_object* v___x_4648_; uint8_t v_isShared_4649_; uint8_t v_isSharedCheck_4654_; 
lean_dec_ref(v___f_4633_);
v_a_4646_ = lean_ctor_get(v_a_4645_, 0);
v_isSharedCheck_4654_ = !lean_is_exclusive(v_a_4645_);
if (v_isSharedCheck_4654_ == 0)
{
v___x_4648_ = v_a_4645_;
v_isShared_4649_ = v_isSharedCheck_4654_;
goto v_resetjp_4647_;
}
else
{
lean_inc(v_a_4646_);
lean_dec(v_a_4645_);
v___x_4648_ = lean_box(0);
v_isShared_4649_ = v_isSharedCheck_4654_;
goto v_resetjp_4647_;
}
v_resetjp_4647_:
{
lean_object* v___x_4651_; 
if (v_isShared_4649_ == 0)
{
v___x_4651_ = v___x_4648_;
goto v_reusejp_4650_;
}
else
{
lean_object* v_reuseFailAlloc_4653_; 
v_reuseFailAlloc_4653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4653_, 0, v_a_4646_);
v___x_4651_ = v_reuseFailAlloc_4653_;
goto v_reusejp_4650_;
}
v_reusejp_4650_:
{
lean_object* v___x_4652_; 
v___x_4652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4652_, 0, v___x_4651_);
return v___x_4652_;
}
}
}
else
{
lean_object* v_a_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; uint8_t v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; 
v_a_4655_ = lean_ctor_get(v_a_4645_, 0);
lean_inc(v_a_4655_);
lean_dec_ref_known(v_a_4645_, 1);
v___x_4656_ = lean_io_promise_result_opt(v_a_4655_);
lean_dec(v_a_4655_);
v___x_4657_ = lean_unsigned_to_nat(0u);
v___x_4658_ = 0;
v___x_4659_ = lean_task_map(v___f_4633_, v___x_4656_, v___x_4657_, v___x_4658_);
v___x_4660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4660_, 0, v___x_4659_);
return v___x_4660_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise___redArg___lam__1___boxed(lean_object* v___f_4661_, lean_object* v_x_4662_, lean_object* v___y_4663_){
_start:
{
lean_object* v_res_4664_; 
v_res_4664_ = l_Std_Async_Async_ofPromise___redArg___lam__1(v___f_4661_, v_x_4662_);
return v_res_4664_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise___redArg(lean_object* v_task_4665_, lean_object* v_error_4666_){
_start:
{
lean_object* v___f_4668_; lean_object* v___f_4669_; lean_object* v___x_4670_; uint8_t v___x_4671_; lean_object* v_val_4673_; lean_object* v___x_4677_; 
v___f_4668_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPromise___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4668_, 0, v_error_4666_);
v___f_4669_ = lean_alloc_closure((void*)(l_Std_Async_Async_ofPromise___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4669_, 0, v___f_4668_);
v___x_4670_ = lean_unsigned_to_nat(0u);
v___x_4671_ = 0;
v___x_4677_ = lean_apply_1(v_task_4665_, lean_box(0));
if (lean_obj_tag(v___x_4677_) == 0)
{
lean_object* v_a_4678_; lean_object* v___x_4680_; uint8_t v_isShared_4681_; uint8_t v_isSharedCheck_4685_; 
v_a_4678_ = lean_ctor_get(v___x_4677_, 0);
v_isSharedCheck_4685_ = !lean_is_exclusive(v___x_4677_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4680_ = v___x_4677_;
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
else
{
lean_inc(v_a_4678_);
lean_dec(v___x_4677_);
v___x_4680_ = lean_box(0);
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
v_resetjp_4679_:
{
lean_object* v___x_4683_; 
if (v_isShared_4681_ == 0)
{
lean_ctor_set_tag(v___x_4680_, 1);
v___x_4683_ = v___x_4680_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v_a_4678_);
v___x_4683_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
v_val_4673_ = v___x_4683_;
goto v___jp_4672_;
}
}
}
else
{
lean_object* v_a_4686_; lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4693_; 
v_a_4686_ = lean_ctor_get(v___x_4677_, 0);
v_isSharedCheck_4693_ = !lean_is_exclusive(v___x_4677_);
if (v_isSharedCheck_4693_ == 0)
{
v___x_4688_ = v___x_4677_;
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
else
{
lean_inc(v_a_4686_);
lean_dec(v___x_4677_);
v___x_4688_ = lean_box(0);
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
v_resetjp_4687_:
{
lean_object* v___x_4691_; 
if (v_isShared_4689_ == 0)
{
lean_ctor_set_tag(v___x_4688_, 0);
v___x_4691_ = v___x_4688_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v_a_4686_);
v___x_4691_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
v_val_4673_ = v___x_4691_;
goto v___jp_4672_;
}
}
}
v___jp_4672_:
{
lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; 
v___x_4674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4674_, 0, v_val_4673_);
v___x_4675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4675_, 0, v___x_4674_);
v___x_4676_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4670_, v___x_4671_, v___x_4675_, v___f_4669_);
return v___x_4676_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise___redArg___boxed(lean_object* v_task_4694_, lean_object* v_error_4695_, lean_object* v_a_4696_){
_start:
{
lean_object* v_res_4697_; 
v_res_4697_ = l_Std_Async_Async_ofPromise___redArg(v_task_4694_, v_error_4695_);
return v_res_4697_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise(lean_object* v_00_u03b1_4698_, lean_object* v_task_4699_, lean_object* v_error_4700_){
_start:
{
lean_object* v___f_4702_; lean_object* v___f_4703_; lean_object* v___x_4704_; uint8_t v___x_4705_; lean_object* v_val_4707_; lean_object* v___x_4711_; 
v___f_4702_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPromise___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4702_, 0, v_error_4700_);
v___f_4703_ = lean_alloc_closure((void*)(l_Std_Async_Async_ofPromise___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4703_, 0, v___f_4702_);
v___x_4704_ = lean_unsigned_to_nat(0u);
v___x_4705_ = 0;
v___x_4711_ = lean_apply_1(v_task_4699_, lean_box(0));
if (lean_obj_tag(v___x_4711_) == 0)
{
lean_object* v_a_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4719_; 
v_a_4712_ = lean_ctor_get(v___x_4711_, 0);
v_isSharedCheck_4719_ = !lean_is_exclusive(v___x_4711_);
if (v_isSharedCheck_4719_ == 0)
{
v___x_4714_ = v___x_4711_;
v_isShared_4715_ = v_isSharedCheck_4719_;
goto v_resetjp_4713_;
}
else
{
lean_inc(v_a_4712_);
lean_dec(v___x_4711_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4719_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v___x_4717_; 
if (v_isShared_4715_ == 0)
{
lean_ctor_set_tag(v___x_4714_, 1);
v___x_4717_ = v___x_4714_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4718_; 
v_reuseFailAlloc_4718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4718_, 0, v_a_4712_);
v___x_4717_ = v_reuseFailAlloc_4718_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
v_val_4707_ = v___x_4717_;
goto v___jp_4706_;
}
}
}
else
{
lean_object* v_a_4720_; lean_object* v___x_4722_; uint8_t v_isShared_4723_; uint8_t v_isSharedCheck_4727_; 
v_a_4720_ = lean_ctor_get(v___x_4711_, 0);
v_isSharedCheck_4727_ = !lean_is_exclusive(v___x_4711_);
if (v_isSharedCheck_4727_ == 0)
{
v___x_4722_ = v___x_4711_;
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
else
{
lean_inc(v_a_4720_);
lean_dec(v___x_4711_);
v___x_4722_ = lean_box(0);
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
v_resetjp_4721_:
{
lean_object* v___x_4725_; 
if (v_isShared_4723_ == 0)
{
lean_ctor_set_tag(v___x_4722_, 0);
v___x_4725_ = v___x_4722_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v_a_4720_);
v___x_4725_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
v_val_4707_ = v___x_4725_;
goto v___jp_4706_;
}
}
}
v___jp_4706_:
{
lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; 
v___x_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4708_, 0, v_val_4707_);
v___x_4709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4708_);
v___x_4710_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4704_, v___x_4705_, v___x_4709_, v___f_4703_);
return v___x_4710_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPromise___boxed(lean_object* v_00_u03b1_4728_, lean_object* v_task_4729_, lean_object* v_error_4730_, lean_object* v_a_4731_){
_start:
{
lean_object* v_res_4732_; 
v_res_4732_ = l_Std_Async_Async_ofPromise(v_00_u03b1_4728_, v_task_4729_, v_error_4730_);
return v_res_4732_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofAsyncTask___redArg(lean_object* v_task_4733_){
_start:
{
lean_object* v___x_4735_; 
v___x_4735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4735_, 0, v_task_4733_);
return v___x_4735_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofAsyncTask___redArg___boxed(lean_object* v_task_4736_, lean_object* v_a_4737_){
_start:
{
lean_object* v_res_4738_; 
v_res_4738_ = l_Std_Async_Async_ofAsyncTask___redArg(v_task_4736_);
return v_res_4738_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofAsyncTask(lean_object* v_00_u03b1_4739_, lean_object* v_task_4740_){
_start:
{
lean_object* v___x_4742_; 
v___x_4742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4742_, 0, v_task_4740_);
return v___x_4742_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofAsyncTask___boxed(lean_object* v_00_u03b1_4743_, lean_object* v_task_4744_, lean_object* v_a_4745_){
_start:
{
lean_object* v_res_4746_; 
v_res_4746_ = l_Std_Async_Async_ofAsyncTask(v_00_u03b1_4743_, v_task_4744_);
return v_res_4746_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___redArg___lam__0(lean_object* v_a_4747_){
_start:
{
lean_object* v___x_4748_; 
v___x_4748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4748_, 0, v_a_4747_);
return v___x_4748_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___redArg___lam__1(lean_object* v___f_4749_, lean_object* v_x_4750_){
_start:
{
if (lean_obj_tag(v_x_4750_) == 0)
{
lean_object* v_a_4752_; lean_object* v___x_4754_; uint8_t v_isShared_4755_; uint8_t v_isSharedCheck_4760_; 
lean_dec_ref(v___f_4749_);
v_a_4752_ = lean_ctor_get(v_x_4750_, 0);
v_isSharedCheck_4760_ = !lean_is_exclusive(v_x_4750_);
if (v_isSharedCheck_4760_ == 0)
{
v___x_4754_ = v_x_4750_;
v_isShared_4755_ = v_isSharedCheck_4760_;
goto v_resetjp_4753_;
}
else
{
lean_inc(v_a_4752_);
lean_dec(v_x_4750_);
v___x_4754_ = lean_box(0);
v_isShared_4755_ = v_isSharedCheck_4760_;
goto v_resetjp_4753_;
}
v_resetjp_4753_:
{
lean_object* v___x_4757_; 
if (v_isShared_4755_ == 0)
{
v___x_4757_ = v___x_4754_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4759_; 
v_reuseFailAlloc_4759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4759_, 0, v_a_4752_);
v___x_4757_ = v_reuseFailAlloc_4759_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
lean_object* v___x_4758_; 
v___x_4758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4758_, 0, v___x_4757_);
return v___x_4758_;
}
}
}
else
{
lean_object* v_a_4761_; 
v_a_4761_ = lean_ctor_get(v_x_4750_, 0);
lean_inc(v_a_4761_);
lean_dec_ref_known(v_x_4750_, 1);
if (lean_obj_tag(v_a_4761_) == 0)
{
lean_object* v_a_4762_; lean_object* v___x_4764_; uint8_t v_isShared_4765_; uint8_t v_isSharedCheck_4770_; 
lean_dec_ref(v___f_4749_);
v_a_4762_ = lean_ctor_get(v_a_4761_, 0);
v_isSharedCheck_4770_ = !lean_is_exclusive(v_a_4761_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4764_ = v_a_4761_;
v_isShared_4765_ = v_isSharedCheck_4770_;
goto v_resetjp_4763_;
}
else
{
lean_inc(v_a_4762_);
lean_dec(v_a_4761_);
v___x_4764_ = lean_box(0);
v_isShared_4765_ = v_isSharedCheck_4770_;
goto v_resetjp_4763_;
}
v_resetjp_4763_:
{
lean_object* v___x_4767_; 
if (v_isShared_4765_ == 0)
{
v___x_4767_ = v___x_4764_;
goto v_reusejp_4766_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_a_4762_);
v___x_4767_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4766_;
}
v_reusejp_4766_:
{
lean_object* v___x_4768_; 
v___x_4768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4768_, 0, v___x_4767_);
return v___x_4768_;
}
}
}
else
{
lean_object* v_a_4771_; lean_object* v___x_4772_; uint8_t v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; 
v_a_4771_ = lean_ctor_get(v_a_4761_, 0);
lean_inc(v_a_4771_);
lean_dec_ref_known(v_a_4761_, 1);
v___x_4772_ = lean_unsigned_to_nat(0u);
v___x_4773_ = 0;
v___x_4774_ = lean_task_map(v___f_4749_, v_a_4771_, v___x_4772_, v___x_4773_);
v___x_4775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4775_, 0, v___x_4774_);
return v___x_4775_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___redArg___lam__1___boxed(lean_object* v___f_4776_, lean_object* v_x_4777_, lean_object* v___y_4778_){
_start:
{
lean_object* v_res_4779_; 
v_res_4779_ = l_Std_Async_Async_ofIOTask___redArg___lam__1(v___f_4776_, v_x_4777_);
return v_res_4779_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___redArg(lean_object* v_task_4783_){
_start:
{
lean_object* v___f_4785_; lean_object* v___x_4786_; uint8_t v___x_4787_; lean_object* v_val_4789_; lean_object* v___x_4793_; 
v___f_4785_ = ((lean_object*)(l_Std_Async_Async_ofIOTask___redArg___closed__1));
v___x_4786_ = lean_unsigned_to_nat(0u);
v___x_4787_ = 0;
v___x_4793_ = lean_apply_1(v_task_4783_, lean_box(0));
if (lean_obj_tag(v___x_4793_) == 0)
{
lean_object* v_a_4794_; lean_object* v___x_4796_; uint8_t v_isShared_4797_; uint8_t v_isSharedCheck_4801_; 
v_a_4794_ = lean_ctor_get(v___x_4793_, 0);
v_isSharedCheck_4801_ = !lean_is_exclusive(v___x_4793_);
if (v_isSharedCheck_4801_ == 0)
{
v___x_4796_ = v___x_4793_;
v_isShared_4797_ = v_isSharedCheck_4801_;
goto v_resetjp_4795_;
}
else
{
lean_inc(v_a_4794_);
lean_dec(v___x_4793_);
v___x_4796_ = lean_box(0);
v_isShared_4797_ = v_isSharedCheck_4801_;
goto v_resetjp_4795_;
}
v_resetjp_4795_:
{
lean_object* v___x_4799_; 
if (v_isShared_4797_ == 0)
{
lean_ctor_set_tag(v___x_4796_, 1);
v___x_4799_ = v___x_4796_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4800_; 
v_reuseFailAlloc_4800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4800_, 0, v_a_4794_);
v___x_4799_ = v_reuseFailAlloc_4800_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
v_val_4789_ = v___x_4799_;
goto v___jp_4788_;
}
}
}
else
{
lean_object* v_a_4802_; lean_object* v___x_4804_; uint8_t v_isShared_4805_; uint8_t v_isSharedCheck_4809_; 
v_a_4802_ = lean_ctor_get(v___x_4793_, 0);
v_isSharedCheck_4809_ = !lean_is_exclusive(v___x_4793_);
if (v_isSharedCheck_4809_ == 0)
{
v___x_4804_ = v___x_4793_;
v_isShared_4805_ = v_isSharedCheck_4809_;
goto v_resetjp_4803_;
}
else
{
lean_inc(v_a_4802_);
lean_dec(v___x_4793_);
v___x_4804_ = lean_box(0);
v_isShared_4805_ = v_isSharedCheck_4809_;
goto v_resetjp_4803_;
}
v_resetjp_4803_:
{
lean_object* v___x_4807_; 
if (v_isShared_4805_ == 0)
{
lean_ctor_set_tag(v___x_4804_, 0);
v___x_4807_ = v___x_4804_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v_a_4802_);
v___x_4807_ = v_reuseFailAlloc_4808_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
v_val_4789_ = v___x_4807_;
goto v___jp_4788_;
}
}
}
v___jp_4788_:
{
lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; 
v___x_4790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4790_, 0, v_val_4789_);
v___x_4791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4791_, 0, v___x_4790_);
v___x_4792_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4786_, v___x_4787_, v___x_4791_, v___f_4785_);
return v___x_4792_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___redArg___boxed(lean_object* v_task_4810_, lean_object* v_a_4811_){
_start:
{
lean_object* v_res_4812_; 
v_res_4812_ = l_Std_Async_Async_ofIOTask___redArg(v_task_4810_);
return v_res_4812_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask(lean_object* v_00_u03b1_4813_, lean_object* v_task_4814_){
_start:
{
lean_object* v___f_4816_; lean_object* v___x_4817_; uint8_t v___x_4818_; lean_object* v_val_4820_; lean_object* v___x_4824_; 
v___f_4816_ = ((lean_object*)(l_Std_Async_Async_ofIOTask___redArg___closed__1));
v___x_4817_ = lean_unsigned_to_nat(0u);
v___x_4818_ = 0;
v___x_4824_ = lean_apply_1(v_task_4814_, lean_box(0));
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
v_val_4820_ = v___x_4830_;
goto v___jp_4819_;
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
v_val_4820_ = v___x_4838_;
goto v___jp_4819_;
}
}
}
v___jp_4819_:
{
lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; 
v___x_4821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4821_, 0, v_val_4820_);
v___x_4822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4822_, 0, v___x_4821_);
v___x_4823_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_4817_, v___x_4818_, v___x_4822_, v___f_4816_);
return v___x_4823_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofIOTask___boxed(lean_object* v_00_u03b1_4841_, lean_object* v_task_4842_, lean_object* v_a_4843_){
_start:
{
lean_object* v_res_4844_; 
v_res_4844_ = l_Std_Async_Async_ofIOTask(v_00_u03b1_4841_, v_task_4842_);
return v_res_4844_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofExcept___redArg(lean_object* v_except_4845_){
_start:
{
lean_object* v___x_4847_; 
v___x_4847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4847_, 0, v_except_4845_);
return v___x_4847_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofExcept___redArg___boxed(lean_object* v_except_4848_, lean_object* v_a_4849_){
_start:
{
lean_object* v_res_4850_; 
v_res_4850_ = l_Std_Async_Async_ofExcept___redArg(v_except_4848_);
return v_res_4850_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofExcept(lean_object* v_00_u03b1_4851_, lean_object* v_except_4852_){
_start:
{
lean_object* v___x_4854_; 
v___x_4854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4854_, 0, v_except_4852_);
return v___x_4854_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofExcept___boxed(lean_object* v_00_u03b1_4855_, lean_object* v_except_4856_, lean_object* v_a_4857_){
_start:
{
lean_object* v_res_4858_; 
v_res_4858_ = l_Std_Async_Async_ofExcept(v_00_u03b1_4855_, v_except_4856_);
return v_res_4858_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofTask___redArg(lean_object* v_task_4859_){
_start:
{
lean_object* v___f_4861_; lean_object* v___x_4862_; uint8_t v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; 
v___f_4861_ = ((lean_object*)(l_Std_Async_Async_ofIOTask___redArg___closed__0));
v___x_4862_ = lean_unsigned_to_nat(0u);
v___x_4863_ = 0;
v___x_4864_ = lean_task_map(v___f_4861_, v_task_4859_, v___x_4862_, v___x_4863_);
v___x_4865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4865_, 0, v___x_4864_);
return v___x_4865_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofTask___redArg___boxed(lean_object* v_task_4866_, lean_object* v_a_4867_){
_start:
{
lean_object* v_res_4868_; 
v_res_4868_ = l_Std_Async_Async_ofTask___redArg(v_task_4866_);
return v_res_4868_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofTask(lean_object* v_00_u03b1_4869_, lean_object* v_task_4870_){
_start:
{
lean_object* v___f_4872_; lean_object* v___x_4873_; uint8_t v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; 
v___f_4872_ = ((lean_object*)(l_Std_Async_Async_ofIOTask___redArg___closed__0));
v___x_4873_ = lean_unsigned_to_nat(0u);
v___x_4874_ = 0;
v___x_4875_ = lean_task_map(v___f_4872_, v_task_4870_, v___x_4873_, v___x_4874_);
v___x_4876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4876_, 0, v___x_4875_);
return v___x_4876_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofTask___boxed(lean_object* v_00_u03b1_4877_, lean_object* v_task_4878_, lean_object* v_a_4879_){
_start:
{
lean_object* v_res_4880_; 
v_res_4880_ = l_Std_Async_Async_ofTask(v_00_u03b1_4877_, v_task_4878_);
return v_res_4880_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPurePromise___redArg(lean_object* v_task_4881_, lean_object* v_error_4882_){
_start:
{
lean_object* v___f_4884_; lean_object* v___x_4885_; 
v___f_4884_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPurePromise___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4884_, 0, v_error_4882_);
v___x_4885_ = lean_apply_1(v_task_4881_, lean_box(0));
if (lean_obj_tag(v___x_4885_) == 0)
{
lean_object* v_a_4886_; lean_object* v___x_4888_; uint8_t v_isShared_4889_; uint8_t v_isSharedCheck_4897_; 
v_a_4886_ = lean_ctor_get(v___x_4885_, 0);
v_isSharedCheck_4897_ = !lean_is_exclusive(v___x_4885_);
if (v_isSharedCheck_4897_ == 0)
{
v___x_4888_ = v___x_4885_;
v_isShared_4889_ = v_isSharedCheck_4897_;
goto v_resetjp_4887_;
}
else
{
lean_inc(v_a_4886_);
lean_dec(v___x_4885_);
v___x_4888_ = lean_box(0);
v_isShared_4889_ = v_isSharedCheck_4897_;
goto v_resetjp_4887_;
}
v_resetjp_4887_:
{
lean_object* v___x_4890_; lean_object* v___x_4891_; uint8_t v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4895_; 
v___x_4890_ = lean_io_promise_result_opt(v_a_4886_);
lean_dec(v_a_4886_);
v___x_4891_ = lean_unsigned_to_nat(0u);
v___x_4892_ = 0;
v___x_4893_ = lean_task_map(v___f_4884_, v___x_4890_, v___x_4891_, v___x_4892_);
if (v_isShared_4889_ == 0)
{
lean_ctor_set_tag(v___x_4888_, 1);
lean_ctor_set(v___x_4888_, 0, v___x_4893_);
v___x_4895_ = v___x_4888_;
goto v_reusejp_4894_;
}
else
{
lean_object* v_reuseFailAlloc_4896_; 
v_reuseFailAlloc_4896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4896_, 0, v___x_4893_);
v___x_4895_ = v_reuseFailAlloc_4896_;
goto v_reusejp_4894_;
}
v_reusejp_4894_:
{
return v___x_4895_;
}
}
}
else
{
lean_object* v_a_4898_; lean_object* v___x_4900_; uint8_t v_isShared_4901_; uint8_t v_isSharedCheck_4906_; 
lean_dec_ref(v___f_4884_);
v_a_4898_ = lean_ctor_get(v___x_4885_, 0);
v_isSharedCheck_4906_ = !lean_is_exclusive(v___x_4885_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4900_ = v___x_4885_;
v_isShared_4901_ = v_isSharedCheck_4906_;
goto v_resetjp_4899_;
}
else
{
lean_inc(v_a_4898_);
lean_dec(v___x_4885_);
v___x_4900_ = lean_box(0);
v_isShared_4901_ = v_isSharedCheck_4906_;
goto v_resetjp_4899_;
}
v_resetjp_4899_:
{
lean_object* v___x_4903_; 
if (v_isShared_4901_ == 0)
{
lean_ctor_set_tag(v___x_4900_, 0);
v___x_4903_ = v___x_4900_;
goto v_reusejp_4902_;
}
else
{
lean_object* v_reuseFailAlloc_4905_; 
v_reuseFailAlloc_4905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4905_, 0, v_a_4898_);
v___x_4903_ = v_reuseFailAlloc_4905_;
goto v_reusejp_4902_;
}
v_reusejp_4902_:
{
lean_object* v___x_4904_; 
v___x_4904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4904_, 0, v___x_4903_);
return v___x_4904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPurePromise___redArg___boxed(lean_object* v_task_4907_, lean_object* v_error_4908_, lean_object* v_a_4909_){
_start:
{
lean_object* v_res_4910_; 
v_res_4910_ = l_Std_Async_Async_ofPurePromise___redArg(v_task_4907_, v_error_4908_);
return v_res_4910_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPurePromise(lean_object* v_00_u03b1_4911_, lean_object* v_task_4912_, lean_object* v_error_4913_){
_start:
{
lean_object* v___f_4915_; lean_object* v___x_4916_; 
v___f_4915_ = lean_alloc_closure((void*)(l_Std_Async_AsyncTask_ofPurePromise___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4915_, 0, v_error_4913_);
v___x_4916_ = lean_apply_1(v_task_4912_, lean_box(0));
if (lean_obj_tag(v___x_4916_) == 0)
{
lean_object* v_a_4917_; lean_object* v___x_4919_; uint8_t v_isShared_4920_; uint8_t v_isSharedCheck_4928_; 
v_a_4917_ = lean_ctor_get(v___x_4916_, 0);
v_isSharedCheck_4928_ = !lean_is_exclusive(v___x_4916_);
if (v_isSharedCheck_4928_ == 0)
{
v___x_4919_ = v___x_4916_;
v_isShared_4920_ = v_isSharedCheck_4928_;
goto v_resetjp_4918_;
}
else
{
lean_inc(v_a_4917_);
lean_dec(v___x_4916_);
v___x_4919_ = lean_box(0);
v_isShared_4920_ = v_isSharedCheck_4928_;
goto v_resetjp_4918_;
}
v_resetjp_4918_:
{
lean_object* v___x_4921_; lean_object* v___x_4922_; uint8_t v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4926_; 
v___x_4921_ = lean_io_promise_result_opt(v_a_4917_);
lean_dec(v_a_4917_);
v___x_4922_ = lean_unsigned_to_nat(0u);
v___x_4923_ = 0;
v___x_4924_ = lean_task_map(v___f_4915_, v___x_4921_, v___x_4922_, v___x_4923_);
if (v_isShared_4920_ == 0)
{
lean_ctor_set_tag(v___x_4919_, 1);
lean_ctor_set(v___x_4919_, 0, v___x_4924_);
v___x_4926_ = v___x_4919_;
goto v_reusejp_4925_;
}
else
{
lean_object* v_reuseFailAlloc_4927_; 
v_reuseFailAlloc_4927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4927_, 0, v___x_4924_);
v___x_4926_ = v_reuseFailAlloc_4927_;
goto v_reusejp_4925_;
}
v_reusejp_4925_:
{
return v___x_4926_;
}
}
}
else
{
lean_object* v_a_4929_; lean_object* v___x_4931_; uint8_t v_isShared_4932_; uint8_t v_isSharedCheck_4937_; 
lean_dec_ref(v___f_4915_);
v_a_4929_ = lean_ctor_get(v___x_4916_, 0);
v_isSharedCheck_4937_ = !lean_is_exclusive(v___x_4916_);
if (v_isSharedCheck_4937_ == 0)
{
v___x_4931_ = v___x_4916_;
v_isShared_4932_ = v_isSharedCheck_4937_;
goto v_resetjp_4930_;
}
else
{
lean_inc(v_a_4929_);
lean_dec(v___x_4916_);
v___x_4931_ = lean_box(0);
v_isShared_4932_ = v_isSharedCheck_4937_;
goto v_resetjp_4930_;
}
v_resetjp_4930_:
{
lean_object* v___x_4934_; 
if (v_isShared_4932_ == 0)
{
lean_ctor_set_tag(v___x_4931_, 0);
v___x_4934_ = v___x_4931_;
goto v_reusejp_4933_;
}
else
{
lean_object* v_reuseFailAlloc_4936_; 
v_reuseFailAlloc_4936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4936_, 0, v_a_4929_);
v___x_4934_ = v_reuseFailAlloc_4936_;
goto v_reusejp_4933_;
}
v_reusejp_4933_:
{
lean_object* v___x_4935_; 
v___x_4935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4935_, 0, v___x_4934_);
return v___x_4935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_ofPurePromise___boxed(lean_object* v_00_u03b1_4938_, lean_object* v_task_4939_, lean_object* v_error_4940_, lean_object* v_a_4941_){
_start:
{
lean_object* v_res_4942_; 
v_res_4942_ = l_Std_Async_Async_ofPurePromise(v_00_u03b1_4938_, v_task_4939_, v_error_4940_);
return v_res_4942_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___redArg(lean_object* v_t_4944_){
_start:
{
lean_object* v___x_4946_; 
v___x_4946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4946_, 0, v_t_4944_);
return v___x_4946_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___redArg___boxed(lean_object* v_t_4947_, lean_object* v_a_4948_){
_start:
{
lean_object* v_res_4949_; 
v_res_4949_ = l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___redArg(v_t_4947_);
return v_res_4949_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1(lean_object* v_00_u03b1_4950_, lean_object* v_t_4951_){
_start:
{
lean_object* v___x_4953_; 
v___x_4953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4953_, 0, v_t_4951_);
return v___x_4953_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___boxed(lean_object* v_00_u03b1_4954_, lean_object* v_t_4955_, lean_object* v_a_4956_){
_start:
{
lean_object* v_res_4957_; 
v_res_4957_ = l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1(v_00_u03b1_4954_, v_t_4955_);
return v_res_4957_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitPromise___aux__1___redArg(lean_object* v_t_4960_){
_start:
{
lean_object* v___f_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; uint8_t v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; 
v___f_4962_ = ((lean_object*)(l_Std_Async_Async_ofIOTask___redArg___closed__0));
v___x_4963_ = l_IO_Promise_result_x21___redArg(v_t_4960_);
v___x_4964_ = lean_unsigned_to_nat(0u);
v___x_4965_ = 0;
v___x_4966_ = lean_task_map(v___f_4962_, v___x_4963_, v___x_4964_, v___x_4965_);
v___x_4967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4967_, 0, v___x_4966_);
return v___x_4967_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitPromise___aux__1___redArg___boxed(lean_object* v_t_4968_, lean_object* v_a_4969_){
_start:
{
lean_object* v_res_4970_; 
v_res_4970_ = l_Std_Async_Async_instMonadAwaitPromise___aux__1___redArg(v_t_4968_);
lean_dec(v_t_4968_);
return v_res_4970_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitPromise___aux__1(lean_object* v_00_u03b1_4971_, lean_object* v_t_4972_){
_start:
{
lean_object* v___f_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; uint8_t v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; 
v___f_4974_ = ((lean_object*)(l_Std_Async_Async_ofIOTask___redArg___closed__0));
v___x_4975_ = l_IO_Promise_result_x21___redArg(v_t_4972_);
v___x_4976_ = lean_unsigned_to_nat(0u);
v___x_4977_ = 0;
v___x_4978_ = lean_task_map(v___f_4974_, v___x_4975_, v___x_4976_, v___x_4977_);
v___x_4979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4979_, 0, v___x_4978_);
return v___x_4979_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_instMonadAwaitPromise___aux__1___boxed(lean_object* v_00_u03b1_4980_, lean_object* v_t_4981_, lean_object* v_a_4982_){
_start:
{
lean_object* v_res_4983_; 
v_res_4983_ = l_Std_Async_Async_instMonadAwaitPromise___aux__1(v_00_u03b1_4980_, v_t_4981_);
lean_dec(v_t_4981_);
return v_res_4983_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__1(lean_object* v_a_4986_, lean_object* v_x_4987_){
_start:
{
if (lean_obj_tag(v_x_4987_) == 0)
{
lean_object* v_a_4989_; lean_object* v___x_4991_; uint8_t v_isShared_4992_; uint8_t v_isSharedCheck_4997_; 
lean_dec(v_a_4986_);
v_a_4989_ = lean_ctor_get(v_x_4987_, 0);
v_isSharedCheck_4997_ = !lean_is_exclusive(v_x_4987_);
if (v_isSharedCheck_4997_ == 0)
{
v___x_4991_ = v_x_4987_;
v_isShared_4992_ = v_isSharedCheck_4997_;
goto v_resetjp_4990_;
}
else
{
lean_inc(v_a_4989_);
lean_dec(v_x_4987_);
v___x_4991_ = lean_box(0);
v_isShared_4992_ = v_isSharedCheck_4997_;
goto v_resetjp_4990_;
}
v_resetjp_4990_:
{
lean_object* v___x_4994_; 
if (v_isShared_4992_ == 0)
{
v___x_4994_ = v___x_4991_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4996_; 
v_reuseFailAlloc_4996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4996_, 0, v_a_4989_);
v___x_4994_ = v_reuseFailAlloc_4996_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
lean_object* v___x_4995_; 
v___x_4995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4995_, 0, v___x_4994_);
return v___x_4995_;
}
}
}
else
{
lean_object* v_a_4998_; lean_object* v___x_5000_; uint8_t v_isShared_5001_; uint8_t v_isSharedCheck_5007_; 
v_a_4998_ = lean_ctor_get(v_x_4987_, 0);
v_isSharedCheck_5007_ = !lean_is_exclusive(v_x_4987_);
if (v_isSharedCheck_5007_ == 0)
{
v___x_5000_ = v_x_4987_;
v_isShared_5001_ = v_isSharedCheck_5007_;
goto v_resetjp_4999_;
}
else
{
lean_inc(v_a_4998_);
lean_dec(v_x_4987_);
v___x_5000_ = lean_box(0);
v_isShared_5001_ = v_isSharedCheck_5007_;
goto v_resetjp_4999_;
}
v_resetjp_4999_:
{
lean_object* v___x_5002_; lean_object* v___x_5004_; 
v___x_5002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5002_, 0, v_a_4986_);
lean_ctor_set(v___x_5002_, 1, v_a_4998_);
if (v_isShared_5001_ == 0)
{
lean_ctor_set(v___x_5000_, 0, v___x_5002_);
v___x_5004_ = v___x_5000_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5006_; 
v_reuseFailAlloc_5006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5006_, 0, v___x_5002_);
v___x_5004_ = v_reuseFailAlloc_5006_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
lean_object* v___x_5005_; 
v___x_5005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5005_, 0, v___x_5004_);
return v___x_5005_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__1___boxed(lean_object* v_a_5008_, lean_object* v_x_5009_, lean_object* v___y_5010_){
_start:
{
lean_object* v_res_5011_; 
v_res_5011_ = l_Std_Async_Async_concurrently___redArg___lam__1(v_a_5008_, v_x_5009_);
return v_res_5011_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__0(lean_object* v_a_5012_, lean_object* v_x_5013_){
_start:
{
if (lean_obj_tag(v_x_5013_) == 0)
{
lean_object* v_a_5015_; lean_object* v___x_5017_; uint8_t v_isShared_5018_; uint8_t v_isSharedCheck_5023_; 
lean_dec_ref(v_a_5012_);
v_a_5015_ = lean_ctor_get(v_x_5013_, 0);
v_isSharedCheck_5023_ = !lean_is_exclusive(v_x_5013_);
if (v_isSharedCheck_5023_ == 0)
{
v___x_5017_ = v_x_5013_;
v_isShared_5018_ = v_isSharedCheck_5023_;
goto v_resetjp_5016_;
}
else
{
lean_inc(v_a_5015_);
lean_dec(v_x_5013_);
v___x_5017_ = lean_box(0);
v_isShared_5018_ = v_isSharedCheck_5023_;
goto v_resetjp_5016_;
}
v_resetjp_5016_:
{
lean_object* v___x_5020_; 
if (v_isShared_5018_ == 0)
{
v___x_5020_ = v___x_5017_;
goto v_reusejp_5019_;
}
else
{
lean_object* v_reuseFailAlloc_5022_; 
v_reuseFailAlloc_5022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5022_, 0, v_a_5015_);
v___x_5020_ = v_reuseFailAlloc_5022_;
goto v_reusejp_5019_;
}
v_reusejp_5019_:
{
lean_object* v___x_5021_; 
v___x_5021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5021_, 0, v___x_5020_);
return v___x_5021_;
}
}
}
else
{
lean_object* v_a_5024_; lean_object* v___f_5025_; lean_object* v___x_5026_; uint8_t v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; 
v_a_5024_ = lean_ctor_get(v_x_5013_, 0);
lean_inc(v_a_5024_);
lean_dec_ref_known(v_x_5013_, 1);
v___f_5025_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrently___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_5025_, 0, v_a_5024_);
v___x_5026_ = lean_unsigned_to_nat(0u);
v___x_5027_ = 0;
v___x_5028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5028_, 0, v_a_5012_);
v___x_5029_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5026_, v___x_5027_, v___x_5028_, v___f_5025_);
return v___x_5029_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__0___boxed(lean_object* v_a_5030_, lean_object* v_x_5031_, lean_object* v___y_5032_){
_start:
{
lean_object* v_res_5033_; 
v_res_5033_ = l_Std_Async_Async_concurrently___redArg___lam__0(v_a_5030_, v_x_5031_);
return v_res_5033_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__2(lean_object* v_a_5034_, lean_object* v_x_5035_){
_start:
{
if (lean_obj_tag(v_x_5035_) == 0)
{
lean_object* v_a_5037_; lean_object* v___x_5039_; uint8_t v_isShared_5040_; uint8_t v_isSharedCheck_5045_; 
lean_dec_ref(v_a_5034_);
v_a_5037_ = lean_ctor_get(v_x_5035_, 0);
v_isSharedCheck_5045_ = !lean_is_exclusive(v_x_5035_);
if (v_isSharedCheck_5045_ == 0)
{
v___x_5039_ = v_x_5035_;
v_isShared_5040_ = v_isSharedCheck_5045_;
goto v_resetjp_5038_;
}
else
{
lean_inc(v_a_5037_);
lean_dec(v_x_5035_);
v___x_5039_ = lean_box(0);
v_isShared_5040_ = v_isSharedCheck_5045_;
goto v_resetjp_5038_;
}
v_resetjp_5038_:
{
lean_object* v___x_5042_; 
if (v_isShared_5040_ == 0)
{
v___x_5042_ = v___x_5039_;
goto v_reusejp_5041_;
}
else
{
lean_object* v_reuseFailAlloc_5044_; 
v_reuseFailAlloc_5044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5044_, 0, v_a_5037_);
v___x_5042_ = v_reuseFailAlloc_5044_;
goto v_reusejp_5041_;
}
v_reusejp_5041_:
{
lean_object* v___x_5043_; 
v___x_5043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5043_, 0, v___x_5042_);
return v___x_5043_;
}
}
}
else
{
lean_object* v_a_5046_; lean_object* v___f_5047_; lean_object* v___x_5048_; uint8_t v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; 
v_a_5046_ = lean_ctor_get(v_x_5035_, 0);
lean_inc(v_a_5046_);
lean_dec_ref_known(v_x_5035_, 1);
v___f_5047_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrently___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5047_, 0, v_a_5046_);
v___x_5048_ = lean_unsigned_to_nat(0u);
v___x_5049_ = 0;
v___x_5050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5050_, 0, v_a_5034_);
v___x_5051_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5048_, v___x_5049_, v___x_5050_, v___f_5047_);
return v___x_5051_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__2___boxed(lean_object* v_a_5052_, lean_object* v_x_5053_, lean_object* v___y_5054_){
_start:
{
lean_object* v_res_5055_; 
v_res_5055_ = l_Std_Async_Async_concurrently___redArg___lam__2(v_a_5052_, v_x_5053_);
return v_res_5055_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__3(lean_object* v_y_5056_, lean_object* v_prio_5057_, lean_object* v___f_5058_, lean_object* v_x_5059_){
_start:
{
if (lean_obj_tag(v_x_5059_) == 0)
{
lean_object* v_a_5061_; lean_object* v___x_5063_; uint8_t v_isShared_5064_; uint8_t v_isSharedCheck_5069_; 
lean_dec_ref(v___f_5058_);
lean_dec(v_prio_5057_);
lean_dec_ref(v_y_5056_);
v_a_5061_ = lean_ctor_get(v_x_5059_, 0);
v_isSharedCheck_5069_ = !lean_is_exclusive(v_x_5059_);
if (v_isSharedCheck_5069_ == 0)
{
v___x_5063_ = v_x_5059_;
v_isShared_5064_ = v_isSharedCheck_5069_;
goto v_resetjp_5062_;
}
else
{
lean_inc(v_a_5061_);
lean_dec(v_x_5059_);
v___x_5063_ = lean_box(0);
v_isShared_5064_ = v_isSharedCheck_5069_;
goto v_resetjp_5062_;
}
v_resetjp_5062_:
{
lean_object* v___x_5066_; 
if (v_isShared_5064_ == 0)
{
v___x_5066_ = v___x_5063_;
goto v_reusejp_5065_;
}
else
{
lean_object* v_reuseFailAlloc_5068_; 
v_reuseFailAlloc_5068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5068_, 0, v_a_5061_);
v___x_5066_ = v_reuseFailAlloc_5068_;
goto v_reusejp_5065_;
}
v_reusejp_5065_:
{
lean_object* v___x_5067_; 
v___x_5067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5067_, 0, v___x_5066_);
return v___x_5067_;
}
}
}
else
{
lean_object* v_a_5070_; lean_object* v___x_5072_; uint8_t v_isShared_5073_; uint8_t v_isSharedCheck_5086_; 
v_a_5070_ = lean_ctor_get(v_x_5059_, 0);
v_isSharedCheck_5086_ = !lean_is_exclusive(v_x_5059_);
if (v_isSharedCheck_5086_ == 0)
{
v___x_5072_ = v_x_5059_;
v_isShared_5073_ = v_isSharedCheck_5086_;
goto v_resetjp_5071_;
}
else
{
lean_inc(v_a_5070_);
lean_dec(v_x_5059_);
v___x_5072_ = lean_box(0);
v_isShared_5073_ = v_isSharedCheck_5086_;
goto v_resetjp_5071_;
}
v_resetjp_5071_:
{
lean_object* v___f_5074_; lean_object* v___x_5075_; uint8_t v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; uint8_t v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5082_; 
v___f_5074_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrently___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_5074_, 0, v_a_5070_);
v___x_5075_ = lean_unsigned_to_nat(0u);
v___x_5076_ = 0;
v___x_5077_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5077_, 0, lean_box(0));
lean_closure_set(v___x_5077_, 1, v_y_5056_);
v___x_5078_ = lean_io_as_task(v___x_5077_, v_prio_5057_);
v___x_5079_ = 1;
v___x_5080_ = lean_task_bind(v___x_5078_, v___f_5058_, v___x_5075_, v___x_5079_);
if (v_isShared_5073_ == 0)
{
lean_ctor_set(v___x_5072_, 0, v___x_5080_);
v___x_5082_ = v___x_5072_;
goto v_reusejp_5081_;
}
else
{
lean_object* v_reuseFailAlloc_5085_; 
v_reuseFailAlloc_5085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5085_, 0, v___x_5080_);
v___x_5082_ = v_reuseFailAlloc_5085_;
goto v_reusejp_5081_;
}
v_reusejp_5081_:
{
lean_object* v___x_5083_; lean_object* v___x_5084_; 
v___x_5083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5083_, 0, v___x_5082_);
v___x_5084_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5075_, v___x_5076_, v___x_5083_, v___f_5074_);
return v___x_5084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___lam__3___boxed(lean_object* v_y_5087_, lean_object* v_prio_5088_, lean_object* v___f_5089_, lean_object* v_x_5090_, lean_object* v___y_5091_){
_start:
{
lean_object* v_res_5092_; 
v_res_5092_ = l_Std_Async_Async_concurrently___redArg___lam__3(v_y_5087_, v_prio_5088_, v___f_5089_, v_x_5090_);
return v_res_5092_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg(lean_object* v_x_5093_, lean_object* v_y_5094_, lean_object* v_prio_5095_){
_start:
{
lean_object* v___f_5097_; lean_object* v___f_5098_; lean_object* v___x_5099_; uint8_t v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; uint8_t v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; 
v___f_5097_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
lean_inc(v_prio_5095_);
v___f_5098_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrently___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_5098_, 0, v_y_5094_);
lean_closure_set(v___f_5098_, 1, v_prio_5095_);
lean_closure_set(v___f_5098_, 2, v___f_5097_);
v___x_5099_ = lean_unsigned_to_nat(0u);
v___x_5100_ = 0;
v___x_5101_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5101_, 0, lean_box(0));
lean_closure_set(v___x_5101_, 1, v_x_5093_);
v___x_5102_ = lean_io_as_task(v___x_5101_, v_prio_5095_);
v___x_5103_ = 1;
v___x_5104_ = lean_task_bind(v___x_5102_, v___f_5097_, v___x_5099_, v___x_5103_);
v___x_5105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5105_, 0, v___x_5104_);
v___x_5106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5106_, 0, v___x_5105_);
v___x_5107_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5099_, v___x_5100_, v___x_5106_, v___f_5098_);
return v___x_5107_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___redArg___boxed(lean_object* v_x_5108_, lean_object* v_y_5109_, lean_object* v_prio_5110_, lean_object* v_a_5111_){
_start:
{
lean_object* v_res_5112_; 
v_res_5112_ = l_Std_Async_Async_concurrently___redArg(v_x_5108_, v_y_5109_, v_prio_5110_);
return v_res_5112_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently(lean_object* v_00_u03b1_5113_, lean_object* v_00_u03b2_5114_, lean_object* v_x_5115_, lean_object* v_y_5116_, lean_object* v_prio_5117_){
_start:
{
lean_object* v___f_5119_; lean_object* v___f_5120_; lean_object* v___x_5121_; uint8_t v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; uint8_t v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; 
v___f_5119_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
lean_inc(v_prio_5117_);
v___f_5120_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrently___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_5120_, 0, v_y_5116_);
lean_closure_set(v___f_5120_, 1, v_prio_5117_);
lean_closure_set(v___f_5120_, 2, v___f_5119_);
v___x_5121_ = lean_unsigned_to_nat(0u);
v___x_5122_ = 0;
v___x_5123_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5123_, 0, lean_box(0));
lean_closure_set(v___x_5123_, 1, v_x_5115_);
v___x_5124_ = lean_io_as_task(v___x_5123_, v_prio_5117_);
v___x_5125_ = 1;
v___x_5126_ = lean_task_bind(v___x_5124_, v___f_5119_, v___x_5121_, v___x_5125_);
v___x_5127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5127_, 0, v___x_5126_);
v___x_5128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5128_, 0, v___x_5127_);
v___x_5129_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5121_, v___x_5122_, v___x_5128_, v___f_5120_);
return v___x_5129_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrently___boxed(lean_object* v_00_u03b1_5130_, lean_object* v_00_u03b2_5131_, lean_object* v_x_5132_, lean_object* v_y_5133_, lean_object* v_prio_5134_, lean_object* v_a_5135_){
_start:
{
lean_object* v_res_5136_; 
v_res_5136_ = l_Std_Async_Async_concurrently(v_00_u03b1_5130_, v_00_u03b2_5131_, v_x_5132_, v_y_5133_, v_prio_5134_);
return v_res_5136_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__1(lean_object* v_x_5137_){
_start:
{
if (lean_obj_tag(v_x_5137_) == 0)
{
lean_object* v_a_5139_; lean_object* v___x_5141_; uint8_t v_isShared_5142_; uint8_t v_isSharedCheck_5147_; 
v_a_5139_ = lean_ctor_get(v_x_5137_, 0);
v_isSharedCheck_5147_ = !lean_is_exclusive(v_x_5137_);
if (v_isSharedCheck_5147_ == 0)
{
v___x_5141_ = v_x_5137_;
v_isShared_5142_ = v_isSharedCheck_5147_;
goto v_resetjp_5140_;
}
else
{
lean_inc(v_a_5139_);
lean_dec(v_x_5137_);
v___x_5141_ = lean_box(0);
v_isShared_5142_ = v_isSharedCheck_5147_;
goto v_resetjp_5140_;
}
v_resetjp_5140_:
{
lean_object* v___x_5144_; 
if (v_isShared_5142_ == 0)
{
v___x_5144_ = v___x_5141_;
goto v_reusejp_5143_;
}
else
{
lean_object* v_reuseFailAlloc_5146_; 
v_reuseFailAlloc_5146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5146_, 0, v_a_5139_);
v___x_5144_ = v_reuseFailAlloc_5146_;
goto v_reusejp_5143_;
}
v_reusejp_5143_:
{
lean_object* v___x_5145_; 
v___x_5145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5145_, 0, v___x_5144_);
return v___x_5145_;
}
}
}
else
{
lean_object* v_a_5148_; lean_object* v___x_5149_; 
v_a_5148_ = lean_ctor_get(v_x_5137_, 0);
lean_inc(v_a_5148_);
lean_dec_ref_known(v_x_5137_, 1);
v___x_5149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5149_, 0, v_a_5148_);
return v___x_5149_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__1___boxed(lean_object* v_x_5150_, lean_object* v___y_5151_){
_start:
{
lean_object* v_res_5152_; 
v_res_5152_ = l_Std_Async_Async_race___redArg___lam__1(v_x_5150_);
return v_res_5152_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__0(lean_object* v_a_5153_){
_start:
{
lean_object* v___x_5154_; 
v___x_5154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5154_, 0, v_a_5153_);
return v___x_5154_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__3(lean_object* v_a_5155_, lean_object* v_value_5156_){
_start:
{
lean_object* v___x_5158_; 
v___x_5158_ = lean_io_promise_resolve(v_value_5156_, v_a_5155_);
return v___x_5158_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__3___boxed(lean_object* v_a_5159_, lean_object* v_value_5160_, lean_object* v___y_5161_){
_start:
{
lean_object* v_res_5162_; 
v_res_5162_ = l_Std_Async_Async_race___redArg___lam__3(v_a_5159_, v_value_5160_);
lean_dec(v_a_5159_);
return v_res_5162_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__2(lean_object* v_a_5163_, lean_object* v___f_5164_, lean_object* v___f_5165_, lean_object* v_x_5166_){
_start:
{
if (lean_obj_tag(v_x_5166_) == 0)
{
lean_object* v_a_5168_; lean_object* v___x_5170_; uint8_t v_isShared_5171_; uint8_t v_isSharedCheck_5176_; 
lean_dec_ref(v___f_5165_);
lean_dec_ref(v___f_5164_);
v_a_5168_ = lean_ctor_get(v_x_5166_, 0);
v_isSharedCheck_5176_ = !lean_is_exclusive(v_x_5166_);
if (v_isSharedCheck_5176_ == 0)
{
v___x_5170_ = v_x_5166_;
v_isShared_5171_ = v_isSharedCheck_5176_;
goto v_resetjp_5169_;
}
else
{
lean_inc(v_a_5168_);
lean_dec(v_x_5166_);
v___x_5170_ = lean_box(0);
v_isShared_5171_ = v_isSharedCheck_5176_;
goto v_resetjp_5169_;
}
v_resetjp_5169_:
{
lean_object* v___x_5173_; 
if (v_isShared_5171_ == 0)
{
v___x_5173_ = v___x_5170_;
goto v_reusejp_5172_;
}
else
{
lean_object* v_reuseFailAlloc_5175_; 
v_reuseFailAlloc_5175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5175_, 0, v_a_5168_);
v___x_5173_ = v_reuseFailAlloc_5175_;
goto v_reusejp_5172_;
}
v_reusejp_5172_:
{
lean_object* v___x_5174_; 
v___x_5174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5174_, 0, v___x_5173_);
return v___x_5174_;
}
}
}
else
{
lean_object* v___x_5177_; uint8_t v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; 
lean_dec_ref_known(v_x_5166_, 1);
v___x_5177_ = lean_unsigned_to_nat(0u);
v___x_5178_ = 0;
v___x_5179_ = l_IO_Promise_result_x21___redArg(v_a_5163_);
v___x_5180_ = lean_task_map(v___f_5164_, v___x_5179_, v___x_5177_, v___x_5178_);
v___x_5181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5181_, 0, v___x_5180_);
v___x_5182_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5177_, v___x_5178_, v___x_5181_, v___f_5165_);
return v___x_5182_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__2___boxed(lean_object* v_a_5183_, lean_object* v___f_5184_, lean_object* v___f_5185_, lean_object* v_x_5186_, lean_object* v___y_5187_){
_start:
{
lean_object* v_res_5188_; 
v_res_5188_ = l_Std_Async_Async_race___redArg___lam__2(v_a_5183_, v___f_5184_, v___f_5185_, v_x_5186_);
lean_dec(v_a_5183_);
return v_res_5188_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__4(lean_object* v_a_5189_, lean_object* v___x_5190_, lean_object* v___x_5191_, uint8_t v___x_5192_, lean_object* v___f_5193_, lean_object* v_x_5194_){
_start:
{
if (lean_obj_tag(v_x_5194_) == 0)
{
lean_object* v_a_5196_; lean_object* v___x_5198_; uint8_t v_isShared_5199_; uint8_t v_isSharedCheck_5204_; 
lean_dec_ref(v___f_5193_);
lean_dec(v___x_5191_);
lean_dec_ref(v___x_5190_);
lean_dec_ref(v_a_5189_);
v_a_5196_ = lean_ctor_get(v_x_5194_, 0);
v_isSharedCheck_5204_ = !lean_is_exclusive(v_x_5194_);
if (v_isSharedCheck_5204_ == 0)
{
v___x_5198_ = v_x_5194_;
v_isShared_5199_ = v_isSharedCheck_5204_;
goto v_resetjp_5197_;
}
else
{
lean_inc(v_a_5196_);
lean_dec(v_x_5194_);
v___x_5198_ = lean_box(0);
v_isShared_5199_ = v_isSharedCheck_5204_;
goto v_resetjp_5197_;
}
v_resetjp_5197_:
{
lean_object* v___x_5201_; 
if (v_isShared_5199_ == 0)
{
v___x_5201_ = v___x_5198_;
goto v_reusejp_5200_;
}
else
{
lean_object* v_reuseFailAlloc_5203_; 
v_reuseFailAlloc_5203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5203_, 0, v_a_5196_);
v___x_5201_ = v_reuseFailAlloc_5203_;
goto v_reusejp_5200_;
}
v_reusejp_5200_:
{
lean_object* v___x_5202_; 
v___x_5202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5202_, 0, v___x_5201_);
return v___x_5202_;
}
}
}
else
{
lean_object* v___x_5206_; uint8_t v_isShared_5207_; uint8_t v_isSharedCheck_5214_; 
v_isSharedCheck_5214_ = !lean_is_exclusive(v_x_5194_);
if (v_isSharedCheck_5214_ == 0)
{
lean_object* v_unused_5215_; 
v_unused_5215_ = lean_ctor_get(v_x_5194_, 0);
lean_dec(v_unused_5215_);
v___x_5206_ = v_x_5194_;
v_isShared_5207_ = v_isSharedCheck_5214_;
goto v_resetjp_5205_;
}
else
{
lean_dec(v_x_5194_);
v___x_5206_ = lean_box(0);
v_isShared_5207_ = v_isSharedCheck_5214_;
goto v_resetjp_5205_;
}
v_resetjp_5205_:
{
lean_object* v___x_5208_; lean_object* v___x_5210_; 
lean_inc(v___x_5191_);
v___x_5208_ = l_BaseIO_chainTask___redArg(v_a_5189_, v___x_5190_, v___x_5191_, v___x_5192_);
if (v_isShared_5207_ == 0)
{
lean_ctor_set(v___x_5206_, 0, v___x_5208_);
v___x_5210_ = v___x_5206_;
goto v_reusejp_5209_;
}
else
{
lean_object* v_reuseFailAlloc_5213_; 
v_reuseFailAlloc_5213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5213_, 0, v___x_5208_);
v___x_5210_ = v_reuseFailAlloc_5213_;
goto v_reusejp_5209_;
}
v_reusejp_5209_:
{
lean_object* v___x_5211_; lean_object* v___x_5212_; 
v___x_5211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5211_, 0, v___x_5210_);
v___x_5212_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5191_, v___x_5192_, v___x_5211_, v___f_5193_);
return v___x_5212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__4___boxed(lean_object* v_a_5216_, lean_object* v___x_5217_, lean_object* v___x_5218_, lean_object* v___x_5219_, lean_object* v___f_5220_, lean_object* v_x_5221_, lean_object* v___y_5222_){
_start:
{
uint8_t v___x_1414__boxed_5223_; lean_object* v_res_5224_; 
v___x_1414__boxed_5223_ = lean_unbox(v___x_5219_);
v_res_5224_ = l_Std_Async_Async_race___redArg___lam__4(v_a_5216_, v___x_5217_, v___x_5218_, v___x_1414__boxed_5223_, v___f_5220_, v_x_5221_);
return v_res_5224_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__5(lean_object* v___f_5225_, lean_object* v___f_5226_, lean_object* v___f_5227_, lean_object* v_a_5228_, lean_object* v_x_5229_){
_start:
{
if (lean_obj_tag(v_x_5229_) == 0)
{
lean_object* v_a_5231_; lean_object* v___x_5233_; uint8_t v_isShared_5234_; uint8_t v_isSharedCheck_5239_; 
lean_dec_ref(v_a_5228_);
lean_dec_ref(v___f_5227_);
lean_dec_ref(v___f_5226_);
lean_dec(v___f_5225_);
v_a_5231_ = lean_ctor_get(v_x_5229_, 0);
v_isSharedCheck_5239_ = !lean_is_exclusive(v_x_5229_);
if (v_isSharedCheck_5239_ == 0)
{
v___x_5233_ = v_x_5229_;
v_isShared_5234_ = v_isSharedCheck_5239_;
goto v_resetjp_5232_;
}
else
{
lean_inc(v_a_5231_);
lean_dec(v_x_5229_);
v___x_5233_ = lean_box(0);
v_isShared_5234_ = v_isSharedCheck_5239_;
goto v_resetjp_5232_;
}
v_resetjp_5232_:
{
lean_object* v___x_5236_; 
if (v_isShared_5234_ == 0)
{
v___x_5236_ = v___x_5233_;
goto v_reusejp_5235_;
}
else
{
lean_object* v_reuseFailAlloc_5238_; 
v_reuseFailAlloc_5238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5238_, 0, v_a_5231_);
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
else
{
lean_object* v_a_5240_; lean_object* v___x_5242_; uint8_t v_isShared_5243_; uint8_t v_isSharedCheck_5256_; 
v_a_5240_ = lean_ctor_get(v_x_5229_, 0);
v_isSharedCheck_5256_ = !lean_is_exclusive(v_x_5229_);
if (v_isSharedCheck_5256_ == 0)
{
v___x_5242_ = v_x_5229_;
v_isShared_5243_ = v_isSharedCheck_5256_;
goto v_resetjp_5241_;
}
else
{
lean_inc(v_a_5240_);
lean_dec(v_x_5229_);
v___x_5242_ = lean_box(0);
v_isShared_5243_ = v_isSharedCheck_5256_;
goto v_resetjp_5241_;
}
v_resetjp_5241_:
{
lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; uint8_t v___x_5247_; lean_object* v___x_5248_; lean_object* v___f_5249_; lean_object* v___x_5250_; lean_object* v___x_5252_; 
v___x_5244_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_5244_, 0, lean_box(0));
lean_closure_set(v___x_5244_, 1, lean_box(0));
lean_closure_set(v___x_5244_, 2, v___f_5225_);
lean_closure_set(v___x_5244_, 3, lean_box(0));
v___x_5245_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_5245_, 0, lean_box(0));
lean_closure_set(v___x_5245_, 1, lean_box(0));
lean_closure_set(v___x_5245_, 2, lean_box(0));
lean_closure_set(v___x_5245_, 3, v___x_5244_);
lean_closure_set(v___x_5245_, 4, v___f_5226_);
v___x_5246_ = lean_unsigned_to_nat(0u);
v___x_5247_ = 0;
v___x_5248_ = lean_box(v___x_5247_);
lean_inc_ref(v___x_5245_);
v___f_5249_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__4___boxed), 7, 5);
lean_closure_set(v___f_5249_, 0, v_a_5240_);
lean_closure_set(v___f_5249_, 1, v___x_5245_);
lean_closure_set(v___f_5249_, 2, v___x_5246_);
lean_closure_set(v___f_5249_, 3, v___x_5248_);
lean_closure_set(v___f_5249_, 4, v___f_5227_);
v___x_5250_ = l_BaseIO_chainTask___redArg(v_a_5228_, v___x_5245_, v___x_5246_, v___x_5247_);
if (v_isShared_5243_ == 0)
{
lean_ctor_set(v___x_5242_, 0, v___x_5250_);
v___x_5252_ = v___x_5242_;
goto v_reusejp_5251_;
}
else
{
lean_object* v_reuseFailAlloc_5255_; 
v_reuseFailAlloc_5255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5255_, 0, v___x_5250_);
v___x_5252_ = v_reuseFailAlloc_5255_;
goto v_reusejp_5251_;
}
v_reusejp_5251_:
{
lean_object* v___x_5253_; lean_object* v___x_5254_; 
v___x_5253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5253_, 0, v___x_5252_);
v___x_5254_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5246_, v___x_5247_, v___x_5253_, v___f_5249_);
return v___x_5254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__5___boxed(lean_object* v___f_5257_, lean_object* v___f_5258_, lean_object* v___f_5259_, lean_object* v_a_5260_, lean_object* v_x_5261_, lean_object* v___y_5262_){
_start:
{
lean_object* v_res_5263_; 
v_res_5263_ = l_Std_Async_Async_race___redArg___lam__5(v___f_5257_, v___f_5258_, v___f_5259_, v_a_5260_, v_x_5261_);
return v_res_5263_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__6(lean_object* v___f_5264_, lean_object* v___f_5265_, lean_object* v___f_5266_, lean_object* v_y_5267_, lean_object* v_prio_5268_, lean_object* v___f_5269_, lean_object* v_x_5270_){
_start:
{
if (lean_obj_tag(v_x_5270_) == 0)
{
lean_object* v_a_5272_; lean_object* v___x_5274_; uint8_t v_isShared_5275_; uint8_t v_isSharedCheck_5280_; 
lean_dec_ref(v___f_5269_);
lean_dec(v_prio_5268_);
lean_dec_ref(v_y_5267_);
lean_dec_ref(v___f_5266_);
lean_dec_ref(v___f_5265_);
lean_dec(v___f_5264_);
v_a_5272_ = lean_ctor_get(v_x_5270_, 0);
v_isSharedCheck_5280_ = !lean_is_exclusive(v_x_5270_);
if (v_isSharedCheck_5280_ == 0)
{
v___x_5274_ = v_x_5270_;
v_isShared_5275_ = v_isSharedCheck_5280_;
goto v_resetjp_5273_;
}
else
{
lean_inc(v_a_5272_);
lean_dec(v_x_5270_);
v___x_5274_ = lean_box(0);
v_isShared_5275_ = v_isSharedCheck_5280_;
goto v_resetjp_5273_;
}
v_resetjp_5273_:
{
lean_object* v___x_5277_; 
if (v_isShared_5275_ == 0)
{
v___x_5277_ = v___x_5274_;
goto v_reusejp_5276_;
}
else
{
lean_object* v_reuseFailAlloc_5279_; 
v_reuseFailAlloc_5279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5279_, 0, v_a_5272_);
v___x_5277_ = v_reuseFailAlloc_5279_;
goto v_reusejp_5276_;
}
v_reusejp_5276_:
{
lean_object* v___x_5278_; 
v___x_5278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5278_, 0, v___x_5277_);
return v___x_5278_;
}
}
}
else
{
lean_object* v_a_5281_; lean_object* v___x_5283_; uint8_t v_isShared_5284_; uint8_t v_isSharedCheck_5297_; 
v_a_5281_ = lean_ctor_get(v_x_5270_, 0);
v_isSharedCheck_5297_ = !lean_is_exclusive(v_x_5270_);
if (v_isSharedCheck_5297_ == 0)
{
v___x_5283_ = v_x_5270_;
v_isShared_5284_ = v_isSharedCheck_5297_;
goto v_resetjp_5282_;
}
else
{
lean_inc(v_a_5281_);
lean_dec(v_x_5270_);
v___x_5283_ = lean_box(0);
v_isShared_5284_ = v_isSharedCheck_5297_;
goto v_resetjp_5282_;
}
v_resetjp_5282_:
{
lean_object* v___f_5285_; lean_object* v___x_5286_; uint8_t v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; uint8_t v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5293_; 
v___f_5285_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__5___boxed), 6, 4);
lean_closure_set(v___f_5285_, 0, v___f_5264_);
lean_closure_set(v___f_5285_, 1, v___f_5265_);
lean_closure_set(v___f_5285_, 2, v___f_5266_);
lean_closure_set(v___f_5285_, 3, v_a_5281_);
v___x_5286_ = lean_unsigned_to_nat(0u);
v___x_5287_ = 0;
v___x_5288_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5288_, 0, lean_box(0));
lean_closure_set(v___x_5288_, 1, v_y_5267_);
v___x_5289_ = lean_io_as_task(v___x_5288_, v_prio_5268_);
v___x_5290_ = 1;
v___x_5291_ = lean_task_bind(v___x_5289_, v___f_5269_, v___x_5286_, v___x_5290_);
if (v_isShared_5284_ == 0)
{
lean_ctor_set(v___x_5283_, 0, v___x_5291_);
v___x_5293_ = v___x_5283_;
goto v_reusejp_5292_;
}
else
{
lean_object* v_reuseFailAlloc_5296_; 
v_reuseFailAlloc_5296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5296_, 0, v___x_5291_);
v___x_5293_ = v_reuseFailAlloc_5296_;
goto v_reusejp_5292_;
}
v_reusejp_5292_:
{
lean_object* v___x_5294_; lean_object* v___x_5295_; 
v___x_5294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5294_, 0, v___x_5293_);
v___x_5295_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5286_, v___x_5287_, v___x_5294_, v___f_5285_);
return v___x_5295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__6___boxed(lean_object* v___f_5298_, lean_object* v___f_5299_, lean_object* v___f_5300_, lean_object* v_y_5301_, lean_object* v_prio_5302_, lean_object* v___f_5303_, lean_object* v_x_5304_, lean_object* v___y_5305_){
_start:
{
lean_object* v_res_5306_; 
v_res_5306_ = l_Std_Async_Async_race___redArg___lam__6(v___f_5298_, v___f_5299_, v___f_5300_, v_y_5301_, v_prio_5302_, v___f_5303_, v_x_5304_);
return v_res_5306_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__7(lean_object* v___f_5307_, lean_object* v___f_5308_, lean_object* v___f_5309_, lean_object* v_y_5310_, lean_object* v_prio_5311_, lean_object* v___f_5312_, lean_object* v_x_5313_, lean_object* v___f_5314_, lean_object* v_x_5315_){
_start:
{
if (lean_obj_tag(v_x_5315_) == 0)
{
lean_object* v_a_5317_; lean_object* v___x_5319_; uint8_t v_isShared_5320_; uint8_t v_isSharedCheck_5325_; 
lean_dec_ref(v___f_5314_);
lean_dec_ref(v_x_5313_);
lean_dec_ref(v___f_5312_);
lean_dec(v_prio_5311_);
lean_dec_ref(v_y_5310_);
lean_dec(v___f_5309_);
lean_dec_ref(v___f_5308_);
lean_dec_ref(v___f_5307_);
v_a_5317_ = lean_ctor_get(v_x_5315_, 0);
v_isSharedCheck_5325_ = !lean_is_exclusive(v_x_5315_);
if (v_isSharedCheck_5325_ == 0)
{
v___x_5319_ = v_x_5315_;
v_isShared_5320_ = v_isSharedCheck_5325_;
goto v_resetjp_5318_;
}
else
{
lean_inc(v_a_5317_);
lean_dec(v_x_5315_);
v___x_5319_ = lean_box(0);
v_isShared_5320_ = v_isSharedCheck_5325_;
goto v_resetjp_5318_;
}
v_resetjp_5318_:
{
lean_object* v___x_5322_; 
if (v_isShared_5320_ == 0)
{
v___x_5322_ = v___x_5319_;
goto v_reusejp_5321_;
}
else
{
lean_object* v_reuseFailAlloc_5324_; 
v_reuseFailAlloc_5324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5324_, 0, v_a_5317_);
v___x_5322_ = v_reuseFailAlloc_5324_;
goto v_reusejp_5321_;
}
v_reusejp_5321_:
{
lean_object* v___x_5323_; 
v___x_5323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5323_, 0, v___x_5322_);
return v___x_5323_;
}
}
}
else
{
lean_object* v_a_5326_; lean_object* v___x_5328_; uint8_t v_isShared_5329_; uint8_t v_isSharedCheck_5344_; 
v_a_5326_ = lean_ctor_get(v_x_5315_, 0);
v_isSharedCheck_5344_ = !lean_is_exclusive(v_x_5315_);
if (v_isSharedCheck_5344_ == 0)
{
v___x_5328_ = v_x_5315_;
v_isShared_5329_ = v_isSharedCheck_5344_;
goto v_resetjp_5327_;
}
else
{
lean_inc(v_a_5326_);
lean_dec(v_x_5315_);
v___x_5328_ = lean_box(0);
v_isShared_5329_ = v_isSharedCheck_5344_;
goto v_resetjp_5327_;
}
v_resetjp_5327_:
{
lean_object* v___f_5330_; lean_object* v___f_5331_; lean_object* v___f_5332_; lean_object* v___x_5333_; uint8_t v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; uint8_t v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5340_; 
lean_inc(v_a_5326_);
v___f_5330_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_5330_, 0, v_a_5326_);
v___f_5331_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_5331_, 0, v_a_5326_);
lean_closure_set(v___f_5331_, 1, v___f_5307_);
lean_closure_set(v___f_5331_, 2, v___f_5308_);
lean_inc(v_prio_5311_);
v___f_5332_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__6___boxed), 8, 6);
lean_closure_set(v___f_5332_, 0, v___f_5309_);
lean_closure_set(v___f_5332_, 1, v___f_5330_);
lean_closure_set(v___f_5332_, 2, v___f_5331_);
lean_closure_set(v___f_5332_, 3, v_y_5310_);
lean_closure_set(v___f_5332_, 4, v_prio_5311_);
lean_closure_set(v___f_5332_, 5, v___f_5312_);
v___x_5333_ = lean_unsigned_to_nat(0u);
v___x_5334_ = 0;
v___x_5335_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5335_, 0, lean_box(0));
lean_closure_set(v___x_5335_, 1, v_x_5313_);
v___x_5336_ = lean_io_as_task(v___x_5335_, v_prio_5311_);
v___x_5337_ = 1;
v___x_5338_ = lean_task_bind(v___x_5336_, v___f_5314_, v___x_5333_, v___x_5337_);
if (v_isShared_5329_ == 0)
{
lean_ctor_set(v___x_5328_, 0, v___x_5338_);
v___x_5340_ = v___x_5328_;
goto v_reusejp_5339_;
}
else
{
lean_object* v_reuseFailAlloc_5343_; 
v_reuseFailAlloc_5343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5343_, 0, v___x_5338_);
v___x_5340_ = v_reuseFailAlloc_5343_;
goto v_reusejp_5339_;
}
v_reusejp_5339_:
{
lean_object* v___x_5341_; lean_object* v___x_5342_; 
v___x_5341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5341_, 0, v___x_5340_);
v___x_5342_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5333_, v___x_5334_, v___x_5341_, v___f_5332_);
return v___x_5342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___lam__7___boxed(lean_object* v___f_5345_, lean_object* v___f_5346_, lean_object* v___f_5347_, lean_object* v_y_5348_, lean_object* v_prio_5349_, lean_object* v___f_5350_, lean_object* v_x_5351_, lean_object* v___f_5352_, lean_object* v_x_5353_, lean_object* v___y_5354_){
_start:
{
lean_object* v_res_5355_; 
v_res_5355_ = l_Std_Async_Async_race___redArg___lam__7(v___f_5345_, v___f_5346_, v___f_5347_, v_y_5348_, v_prio_5349_, v___f_5350_, v_x_5351_, v___f_5352_, v_x_5353_);
return v_res_5355_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg(lean_object* v_x_5358_, lean_object* v_y_5359_, lean_object* v_prio_5360_){
_start:
{
lean_object* v___f_5362_; lean_object* v___f_5363_; lean_object* v___f_5364_; lean_object* v___f_5365_; lean_object* v___f_5366_; lean_object* v___x_5367_; uint8_t v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; 
v___f_5362_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___f_5363_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__0));
v___f_5364_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__1));
v___f_5365_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_5366_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_5366_, 0, v___f_5364_);
lean_closure_set(v___f_5366_, 1, v___f_5363_);
lean_closure_set(v___f_5366_, 2, v___f_5365_);
lean_closure_set(v___f_5366_, 3, v_y_5359_);
lean_closure_set(v___f_5366_, 4, v_prio_5360_);
lean_closure_set(v___f_5366_, 5, v___f_5362_);
lean_closure_set(v___f_5366_, 6, v_x_5358_);
lean_closure_set(v___f_5366_, 7, v___f_5362_);
v___x_5367_ = lean_unsigned_to_nat(0u);
v___x_5368_ = 0;
v___x_5369_ = lean_io_promise_new();
v___x_5370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5370_, 0, v___x_5369_);
v___x_5371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5371_, 0, v___x_5370_);
v___x_5372_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5367_, v___x_5368_, v___x_5371_, v___f_5366_);
return v___x_5372_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___redArg___boxed(lean_object* v_x_5373_, lean_object* v_y_5374_, lean_object* v_prio_5375_, lean_object* v_a_5376_){
_start:
{
lean_object* v_res_5377_; 
v_res_5377_ = l_Std_Async_Async_race___redArg(v_x_5373_, v_y_5374_, v_prio_5375_);
return v_res_5377_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race(lean_object* v_00_u03b1_5378_, lean_object* v_inst_5379_, lean_object* v_x_5380_, lean_object* v_y_5381_, lean_object* v_prio_5382_){
_start:
{
lean_object* v___f_5384_; lean_object* v___f_5385_; lean_object* v___f_5386_; lean_object* v___f_5387_; lean_object* v___f_5388_; lean_object* v___x_5389_; uint8_t v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; 
v___f_5384_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___f_5385_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__0));
v___f_5386_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__1));
v___f_5387_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_5388_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_5388_, 0, v___f_5386_);
lean_closure_set(v___f_5388_, 1, v___f_5385_);
lean_closure_set(v___f_5388_, 2, v___f_5387_);
lean_closure_set(v___f_5388_, 3, v_y_5381_);
lean_closure_set(v___f_5388_, 4, v_prio_5382_);
lean_closure_set(v___f_5388_, 5, v___f_5384_);
lean_closure_set(v___f_5388_, 6, v_x_5380_);
lean_closure_set(v___f_5388_, 7, v___f_5384_);
v___x_5389_ = lean_unsigned_to_nat(0u);
v___x_5390_ = 0;
v___x_5391_ = lean_io_promise_new();
v___x_5392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5392_, 0, v___x_5391_);
v___x_5393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5393_, 0, v___x_5392_);
v___x_5394_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5389_, v___x_5390_, v___x_5393_, v___f_5388_);
return v___x_5394_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_race___boxed(lean_object* v_00_u03b1_5395_, lean_object* v_inst_5396_, lean_object* v_x_5397_, lean_object* v_y_5398_, lean_object* v_prio_5399_, lean_object* v_a_5400_){
_start:
{
lean_object* v_res_5401_; 
v_res_5401_ = l_Std_Async_Async_race(v_00_u03b1_5395_, v_inst_5396_, v_x_5397_, v_y_5398_, v_prio_5399_);
lean_dec(v_inst_5396_);
return v_res_5401_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg___lam__1(lean_object* v_prio_5402_, lean_object* v___f_5403_, lean_object* v_x_5404_){
_start:
{
lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; uint8_t v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; 
v___x_5406_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5406_, 0, lean_box(0));
lean_closure_set(v___x_5406_, 1, v_x_5404_);
v___x_5407_ = lean_io_as_task(v___x_5406_, v_prio_5402_);
v___x_5408_ = lean_unsigned_to_nat(0u);
v___x_5409_ = 1;
v___x_5410_ = lean_task_bind(v___x_5407_, v___f_5403_, v___x_5408_, v___x_5409_);
v___x_5411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5411_, 0, v___x_5410_);
v___x_5412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5412_, 0, v___x_5411_);
return v___x_5412_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg___lam__1___boxed(lean_object* v_prio_5413_, lean_object* v___f_5414_, lean_object* v_x_5415_, lean_object* v___y_5416_){
_start:
{
lean_object* v_res_5417_; 
v_res_5417_ = l_Std_Async_Async_concurrentlyAll___redArg___lam__1(v_prio_5413_, v___f_5414_, v_x_5415_);
return v_res_5417_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg___lam__0(lean_object* v___x_5419_, lean_object* v_x_5420_){
_start:
{
if (lean_obj_tag(v_x_5420_) == 0)
{
lean_object* v_a_5422_; lean_object* v___x_5424_; uint8_t v_isShared_5425_; uint8_t v_isSharedCheck_5430_; 
lean_dec_ref(v___x_5419_);
v_a_5422_ = lean_ctor_get(v_x_5420_, 0);
v_isSharedCheck_5430_ = !lean_is_exclusive(v_x_5420_);
if (v_isSharedCheck_5430_ == 0)
{
v___x_5424_ = v_x_5420_;
v_isShared_5425_ = v_isSharedCheck_5430_;
goto v_resetjp_5423_;
}
else
{
lean_inc(v_a_5422_);
lean_dec(v_x_5420_);
v___x_5424_ = lean_box(0);
v_isShared_5425_ = v_isSharedCheck_5430_;
goto v_resetjp_5423_;
}
v_resetjp_5423_:
{
lean_object* v___x_5427_; 
if (v_isShared_5425_ == 0)
{
v___x_5427_ = v___x_5424_;
goto v_reusejp_5426_;
}
else
{
lean_object* v_reuseFailAlloc_5429_; 
v_reuseFailAlloc_5429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5429_, 0, v_a_5422_);
v___x_5427_ = v_reuseFailAlloc_5429_;
goto v_reusejp_5426_;
}
v_reusejp_5426_:
{
lean_object* v___x_5428_; 
v___x_5428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5428_, 0, v___x_5427_);
return v___x_5428_;
}
}
}
else
{
lean_object* v_a_5431_; lean_object* v___x_5432_; size_t v_sz_5433_; size_t v___x_5434_; lean_object* v___x_271__overap_5435_; lean_object* v___x_5436_; 
v_a_5431_ = lean_ctor_get(v_x_5420_, 0);
lean_inc(v_a_5431_);
lean_dec_ref_known(v_x_5420_, 1);
v___x_5432_ = ((lean_object*)(l_Std_Async_Async_concurrentlyAll___redArg___lam__0___closed__0));
v_sz_5433_ = lean_array_size(v_a_5431_);
v___x_5434_ = ((size_t)0ULL);
v___x_271__overap_5435_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_5419_, v___x_5432_, v_sz_5433_, v___x_5434_, v_a_5431_);
v___x_5436_ = lean_apply_1(v___x_271__overap_5435_, lean_box(0));
return v___x_5436_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg___lam__0___boxed(lean_object* v___x_5437_, lean_object* v_x_5438_, lean_object* v___y_5439_){
_start:
{
lean_object* v_res_5440_; 
v_res_5440_ = l_Std_Async_Async_concurrentlyAll___redArg___lam__0(v___x_5437_, v_x_5438_);
return v_res_5440_;
}
}
static lean_object* _init_l_Std_Async_Async_concurrentlyAll___redArg___closed__0(void){
_start:
{
lean_object* v___x_5441_; lean_object* v___f_5442_; 
v___x_5441_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___closed__0, &l_Std_Async_EAsync_instMonad___closed__0_once, _init_l_Std_Async_EAsync_instMonad___closed__0);
v___f_5442_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrentlyAll___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5442_, 0, v___x_5441_);
return v___f_5442_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg(lean_object* v_xs_5443_, lean_object* v_prio_5444_){
_start:
{
lean_object* v___f_5446_; lean_object* v___f_5447_; lean_object* v___x_5448_; lean_object* v___f_5449_; lean_object* v___x_5450_; uint8_t v___x_5451_; size_t v_sz_5452_; size_t v___x_5453_; lean_object* v___x_204__overap_5454_; lean_object* v___x_5455_; lean_object* v___x_5456_; 
v___f_5446_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___f_5447_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrentlyAll___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_5447_, 0, v_prio_5444_);
lean_closure_set(v___f_5447_, 1, v___f_5446_);
v___x_5448_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___closed__0, &l_Std_Async_EAsync_instMonad___closed__0_once, _init_l_Std_Async_EAsync_instMonad___closed__0);
v___f_5449_ = lean_obj_once(&l_Std_Async_Async_concurrentlyAll___redArg___closed__0, &l_Std_Async_Async_concurrentlyAll___redArg___closed__0_once, _init_l_Std_Async_Async_concurrentlyAll___redArg___closed__0);
v___x_5450_ = lean_unsigned_to_nat(0u);
v___x_5451_ = 0;
v_sz_5452_ = lean_array_size(v_xs_5443_);
v___x_5453_ = ((size_t)0ULL);
v___x_204__overap_5454_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_5448_, v___f_5447_, v_sz_5452_, v___x_5453_, v_xs_5443_);
v___x_5455_ = lean_apply_1(v___x_204__overap_5454_, lean_box(0));
v___x_5456_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5450_, v___x_5451_, v___x_5455_, v___f_5449_);
return v___x_5456_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___redArg___boxed(lean_object* v_xs_5457_, lean_object* v_prio_5458_, lean_object* v_a_5459_){
_start:
{
lean_object* v_res_5460_; 
v_res_5460_ = l_Std_Async_Async_concurrentlyAll___redArg(v_xs_5457_, v_prio_5458_);
return v_res_5460_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll(lean_object* v_00_u03b1_5461_, lean_object* v_xs_5462_, lean_object* v_prio_5463_){
_start:
{
lean_object* v___f_5465_; lean_object* v___f_5466_; lean_object* v___x_5467_; lean_object* v___f_5468_; lean_object* v___x_5469_; uint8_t v___x_5470_; size_t v_sz_5471_; size_t v___x_5472_; lean_object* v___x_241__overap_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; 
v___f_5465_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___f_5466_ = lean_alloc_closure((void*)(l_Std_Async_Async_concurrentlyAll___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_5466_, 0, v_prio_5463_);
lean_closure_set(v___f_5466_, 1, v___f_5465_);
v___x_5467_ = lean_obj_once(&l_Std_Async_EAsync_instMonad___closed__0, &l_Std_Async_EAsync_instMonad___closed__0_once, _init_l_Std_Async_EAsync_instMonad___closed__0);
v___f_5468_ = lean_obj_once(&l_Std_Async_Async_concurrentlyAll___redArg___closed__0, &l_Std_Async_Async_concurrentlyAll___redArg___closed__0_once, _init_l_Std_Async_Async_concurrentlyAll___redArg___closed__0);
v___x_5469_ = lean_unsigned_to_nat(0u);
v___x_5470_ = 0;
v_sz_5471_ = lean_array_size(v_xs_5462_);
v___x_5472_ = ((size_t)0ULL);
v___x_241__overap_5473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_5467_, v___f_5466_, v_sz_5471_, v___x_5472_, v_xs_5462_);
v___x_5474_ = lean_apply_1(v___x_241__overap_5473_, lean_box(0));
v___x_5475_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5469_, v___x_5470_, v___x_5474_, v___f_5468_);
return v___x_5475_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_concurrentlyAll___boxed(lean_object* v_00_u03b1_5476_, lean_object* v_xs_5477_, lean_object* v_prio_5478_, lean_object* v_a_5479_){
_start:
{
lean_object* v_res_5480_; 
v_res_5480_ = l_Std_Async_Async_concurrentlyAll(v_00_u03b1_5476_, v_xs_5477_, v_prio_5478_);
return v_res_5480_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__4(lean_object* v___f_5481_, lean_object* v___f_5482_, lean_object* v_x_5483_){
_start:
{
if (lean_obj_tag(v_x_5483_) == 0)
{
lean_object* v_a_5485_; lean_object* v___x_5487_; uint8_t v_isShared_5488_; uint8_t v_isSharedCheck_5493_; 
lean_dec_ref(v___f_5482_);
lean_dec(v___f_5481_);
v_a_5485_ = lean_ctor_get(v_x_5483_, 0);
v_isSharedCheck_5493_ = !lean_is_exclusive(v_x_5483_);
if (v_isSharedCheck_5493_ == 0)
{
v___x_5487_ = v_x_5483_;
v_isShared_5488_ = v_isSharedCheck_5493_;
goto v_resetjp_5486_;
}
else
{
lean_inc(v_a_5485_);
lean_dec(v_x_5483_);
v___x_5487_ = lean_box(0);
v_isShared_5488_ = v_isSharedCheck_5493_;
goto v_resetjp_5486_;
}
v_resetjp_5486_:
{
lean_object* v___x_5490_; 
if (v_isShared_5488_ == 0)
{
v___x_5490_ = v___x_5487_;
goto v_reusejp_5489_;
}
else
{
lean_object* v_reuseFailAlloc_5492_; 
v_reuseFailAlloc_5492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5492_, 0, v_a_5485_);
v___x_5490_ = v_reuseFailAlloc_5492_;
goto v_reusejp_5489_;
}
v_reusejp_5489_:
{
lean_object* v___x_5491_; 
v___x_5491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5491_, 0, v___x_5490_);
return v___x_5491_;
}
}
}
else
{
lean_object* v_a_5494_; lean_object* v___x_5496_; uint8_t v_isShared_5497_; uint8_t v_isSharedCheck_5507_; 
v_a_5494_ = lean_ctor_get(v_x_5483_, 0);
v_isSharedCheck_5507_ = !lean_is_exclusive(v_x_5483_);
if (v_isSharedCheck_5507_ == 0)
{
v___x_5496_ = v_x_5483_;
v_isShared_5497_ = v_isSharedCheck_5507_;
goto v_resetjp_5495_;
}
else
{
lean_inc(v_a_5494_);
lean_dec(v_x_5483_);
v___x_5496_ = lean_box(0);
v_isShared_5497_ = v_isSharedCheck_5507_;
goto v_resetjp_5495_;
}
v_resetjp_5495_:
{
lean_object* v___x_5498_; lean_object* v___x_5499_; lean_object* v___x_5500_; uint8_t v___x_5501_; lean_object* v___x_5502_; lean_object* v___x_5504_; 
v___x_5498_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_5498_, 0, lean_box(0));
lean_closure_set(v___x_5498_, 1, lean_box(0));
lean_closure_set(v___x_5498_, 2, v___f_5481_);
lean_closure_set(v___x_5498_, 3, lean_box(0));
v___x_5499_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_5499_, 0, lean_box(0));
lean_closure_set(v___x_5499_, 1, lean_box(0));
lean_closure_set(v___x_5499_, 2, lean_box(0));
lean_closure_set(v___x_5499_, 3, v___x_5498_);
lean_closure_set(v___x_5499_, 4, v___f_5482_);
v___x_5500_ = lean_unsigned_to_nat(0u);
v___x_5501_ = 0;
v___x_5502_ = l_BaseIO_chainTask___redArg(v_a_5494_, v___x_5499_, v___x_5500_, v___x_5501_);
if (v_isShared_5497_ == 0)
{
lean_ctor_set(v___x_5496_, 0, v___x_5502_);
v___x_5504_ = v___x_5496_;
goto v_reusejp_5503_;
}
else
{
lean_object* v_reuseFailAlloc_5506_; 
v_reuseFailAlloc_5506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5506_, 0, v___x_5502_);
v___x_5504_ = v_reuseFailAlloc_5506_;
goto v_reusejp_5503_;
}
v_reusejp_5503_:
{
lean_object* v___x_5505_; 
v___x_5505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5505_, 0, v___x_5504_);
return v___x_5505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__4___boxed(lean_object* v___f_5508_, lean_object* v___f_5509_, lean_object* v_x_5510_, lean_object* v___y_5511_){
_start:
{
lean_object* v_res_5512_; 
v_res_5512_ = l_Std_Async_Async_raceAll___redArg___lam__4(v___f_5508_, v___f_5509_, v_x_5510_);
return v_res_5512_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__0(lean_object* v_prio_5513_, lean_object* v___f_5514_, lean_object* v___f_5515_, lean_object* v_x_5516_){
_start:
{
lean_object* v___x_5518_; uint8_t v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; uint8_t v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; 
v___x_5518_ = lean_unsigned_to_nat(0u);
v___x_5519_ = 0;
v___x_5520_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_5520_, 0, lean_box(0));
lean_closure_set(v___x_5520_, 1, v_x_5516_);
v___x_5521_ = lean_io_as_task(v___x_5520_, v_prio_5513_);
v___x_5522_ = 1;
v___x_5523_ = lean_task_bind(v___x_5521_, v___f_5514_, v___x_5518_, v___x_5522_);
v___x_5524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5524_, 0, v___x_5523_);
v___x_5525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5525_, 0, v___x_5524_);
v___x_5526_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5518_, v___x_5519_, v___x_5525_, v___f_5515_);
return v___x_5526_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__0___boxed(lean_object* v_prio_5527_, lean_object* v___f_5528_, lean_object* v___f_5529_, lean_object* v_x_5530_, lean_object* v___y_5531_){
_start:
{
lean_object* v_res_5532_; 
v_res_5532_ = l_Std_Async_Async_raceAll___redArg___lam__0(v_prio_5527_, v___f_5528_, v___f_5529_, v_x_5530_);
return v_res_5532_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__2(lean_object* v___f_5533_, lean_object* v_prio_5534_, lean_object* v___f_5535_, lean_object* v___f_5536_, lean_object* v___f_5537_, lean_object* v_inst_5538_, lean_object* v_xs_5539_, lean_object* v_x_5540_){
_start:
{
if (lean_obj_tag(v_x_5540_) == 0)
{
lean_object* v_a_5542_; lean_object* v___x_5544_; uint8_t v_isShared_5545_; uint8_t v_isSharedCheck_5550_; 
lean_dec(v_xs_5539_);
lean_dec_ref(v_inst_5538_);
lean_dec_ref(v___f_5537_);
lean_dec_ref(v___f_5536_);
lean_dec_ref(v___f_5535_);
lean_dec(v_prio_5534_);
lean_dec(v___f_5533_);
v_a_5542_ = lean_ctor_get(v_x_5540_, 0);
v_isSharedCheck_5550_ = !lean_is_exclusive(v_x_5540_);
if (v_isSharedCheck_5550_ == 0)
{
v___x_5544_ = v_x_5540_;
v_isShared_5545_ = v_isSharedCheck_5550_;
goto v_resetjp_5543_;
}
else
{
lean_inc(v_a_5542_);
lean_dec(v_x_5540_);
v___x_5544_ = lean_box(0);
v_isShared_5545_ = v_isSharedCheck_5550_;
goto v_resetjp_5543_;
}
v_resetjp_5543_:
{
lean_object* v___x_5547_; 
if (v_isShared_5545_ == 0)
{
v___x_5547_ = v___x_5544_;
goto v_reusejp_5546_;
}
else
{
lean_object* v_reuseFailAlloc_5549_; 
v_reuseFailAlloc_5549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5549_, 0, v_a_5542_);
v___x_5547_ = v_reuseFailAlloc_5549_;
goto v_reusejp_5546_;
}
v_reusejp_5546_:
{
lean_object* v___x_5548_; 
v___x_5548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5548_, 0, v___x_5547_);
return v___x_5548_;
}
}
}
else
{
lean_object* v_a_5551_; lean_object* v___f_5552_; lean_object* v___f_5553_; lean_object* v___f_5554_; lean_object* v___f_5555_; lean_object* v___x_5556_; uint8_t v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; 
v_a_5551_ = lean_ctor_get(v_x_5540_, 0);
lean_inc_n(v_a_5551_, 2);
lean_dec_ref_known(v_x_5540_, 1);
v___f_5552_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_5552_, 0, v_a_5551_);
v___f_5553_ = lean_alloc_closure((void*)(l_Std_Async_Async_raceAll___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_5553_, 0, v___f_5533_);
lean_closure_set(v___f_5553_, 1, v___f_5552_);
v___f_5554_ = lean_alloc_closure((void*)(l_Std_Async_Async_raceAll___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_5554_, 0, v_prio_5534_);
lean_closure_set(v___f_5554_, 1, v___f_5535_);
lean_closure_set(v___f_5554_, 2, v___f_5553_);
v___f_5555_ = lean_alloc_closure((void*)(l_Std_Async_Async_race___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_5555_, 0, v_a_5551_);
lean_closure_set(v___f_5555_, 1, v___f_5536_);
lean_closure_set(v___f_5555_, 2, v___f_5537_);
v___x_5556_ = lean_unsigned_to_nat(0u);
v___x_5557_ = 0;
v___x_5558_ = lean_apply_3(v_inst_5538_, v_xs_5539_, v___f_5554_, lean_box(0));
v___x_5559_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5556_, v___x_5557_, v___x_5558_, v___f_5555_);
return v___x_5559_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___lam__2___boxed(lean_object* v___f_5560_, lean_object* v_prio_5561_, lean_object* v___f_5562_, lean_object* v___f_5563_, lean_object* v___f_5564_, lean_object* v_inst_5565_, lean_object* v_xs_5566_, lean_object* v_x_5567_, lean_object* v___y_5568_){
_start:
{
lean_object* v_res_5569_; 
v_res_5569_ = l_Std_Async_Async_raceAll___redArg___lam__2(v___f_5560_, v_prio_5561_, v___f_5562_, v___f_5563_, v___f_5564_, v_inst_5565_, v_xs_5566_, v_x_5567_);
return v_res_5569_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg(lean_object* v_inst_5570_, lean_object* v_xs_5571_, lean_object* v_prio_5572_){
_start:
{
lean_object* v___f_5574_; lean_object* v___f_5575_; lean_object* v___f_5576_; lean_object* v___f_5577_; lean_object* v___f_5578_; lean_object* v___x_5579_; uint8_t v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; 
v___f_5574_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__1));
v___f_5575_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__0));
v___f_5576_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___f_5577_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_5578_ = lean_alloc_closure((void*)(l_Std_Async_Async_raceAll___redArg___lam__2___boxed), 9, 7);
lean_closure_set(v___f_5578_, 0, v___f_5577_);
lean_closure_set(v___f_5578_, 1, v_prio_5572_);
lean_closure_set(v___f_5578_, 2, v___f_5576_);
lean_closure_set(v___f_5578_, 3, v___f_5574_);
lean_closure_set(v___f_5578_, 4, v___f_5575_);
lean_closure_set(v___f_5578_, 5, v_inst_5570_);
lean_closure_set(v___f_5578_, 6, v_xs_5571_);
v___x_5579_ = lean_unsigned_to_nat(0u);
v___x_5580_ = 0;
v___x_5581_ = lean_io_promise_new();
v___x_5582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5582_, 0, v___x_5581_);
v___x_5583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5583_, 0, v___x_5582_);
v___x_5584_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5579_, v___x_5580_, v___x_5583_, v___f_5578_);
return v___x_5584_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___redArg___boxed(lean_object* v_inst_5585_, lean_object* v_xs_5586_, lean_object* v_prio_5587_, lean_object* v_a_5588_){
_start:
{
lean_object* v_res_5589_; 
v_res_5589_ = l_Std_Async_Async_raceAll___redArg(v_inst_5585_, v_xs_5586_, v_prio_5587_);
return v_res_5589_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll(lean_object* v_c_5590_, lean_object* v_00_u03b1_5591_, lean_object* v_inst_5592_, lean_object* v_xs_5593_, lean_object* v_prio_5594_){
_start:
{
lean_object* v___f_5596_; lean_object* v___f_5597_; lean_object* v___f_5598_; lean_object* v___f_5599_; lean_object* v___f_5600_; lean_object* v___x_5601_; uint8_t v___x_5602_; lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; 
v___f_5596_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__1));
v___f_5597_ = ((lean_object*)(l_Std_Async_Async_race___redArg___closed__0));
v___f_5598_ = ((lean_object*)(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0));
v___f_5599_ = ((lean_object*)(l_Std_Async_BaseAsync_race___redArg___closed__0));
v___f_5600_ = lean_alloc_closure((void*)(l_Std_Async_Async_raceAll___redArg___lam__2___boxed), 9, 7);
lean_closure_set(v___f_5600_, 0, v___f_5599_);
lean_closure_set(v___f_5600_, 1, v_prio_5594_);
lean_closure_set(v___f_5600_, 2, v___f_5598_);
lean_closure_set(v___f_5600_, 3, v___f_5596_);
lean_closure_set(v___f_5600_, 4, v___f_5597_);
lean_closure_set(v___f_5600_, 5, v_inst_5592_);
lean_closure_set(v___f_5600_, 6, v_xs_5593_);
v___x_5601_ = lean_unsigned_to_nat(0u);
v___x_5602_ = 0;
v___x_5603_ = lean_io_promise_new();
v___x_5604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5604_, 0, v___x_5603_);
v___x_5605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5605_, 0, v___x_5604_);
v___x_5606_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_5601_, v___x_5602_, v___x_5605_, v___f_5600_);
return v___x_5606_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Async_raceAll___boxed(lean_object* v_c_5607_, lean_object* v_00_u03b1_5608_, lean_object* v_inst_5609_, lean_object* v_xs_5610_, lean_object* v_prio_5611_, lean_object* v_a_5612_){
_start:
{
lean_object* v_res_5613_; 
v_res_5613_ = l_Std_Async_Async_raceAll(v_c_5607_, v_00_u03b1_5608_, v_inst_5609_, v_xs_5610_, v_prio_5611_);
return v_res_5613_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_background___redArg(lean_object* v_inst_5614_, lean_object* v_inst_5615_, lean_object* v_action_5616_, lean_object* v_prio_5617_){
_start:
{
lean_object* v_toApplicative_5618_; lean_object* v_toFunctor_5619_; lean_object* v_mapConst_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; 
v_toApplicative_5618_ = lean_ctor_get(v_inst_5614_, 0);
lean_inc_ref(v_toApplicative_5618_);
lean_dec_ref(v_inst_5614_);
v_toFunctor_5619_ = lean_ctor_get(v_toApplicative_5618_, 0);
lean_inc_ref(v_toFunctor_5619_);
lean_dec_ref(v_toApplicative_5618_);
v_mapConst_5620_ = lean_ctor_get(v_toFunctor_5619_, 1);
lean_inc(v_mapConst_5620_);
lean_dec_ref(v_toFunctor_5619_);
v___x_5621_ = lean_apply_3(v_inst_5615_, lean_box(0), v_action_5616_, v_prio_5617_);
v___x_5622_ = lean_box(0);
v___x_5623_ = lean_apply_4(v_mapConst_5620_, lean_box(0), lean_box(0), v___x_5622_, v___x_5621_);
return v___x_5623_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_background(lean_object* v_m_5624_, lean_object* v_t_5625_, lean_object* v_00_u03b1_5626_, lean_object* v_inst_5627_, lean_object* v_inst_5628_, lean_object* v_action_5629_, lean_object* v_prio_5630_){
_start:
{
lean_object* v_toApplicative_5631_; lean_object* v_toFunctor_5632_; lean_object* v_mapConst_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; 
v_toApplicative_5631_ = lean_ctor_get(v_inst_5627_, 0);
lean_inc_ref(v_toApplicative_5631_);
lean_dec_ref(v_inst_5627_);
v_toFunctor_5632_ = lean_ctor_get(v_toApplicative_5631_, 0);
lean_inc_ref(v_toFunctor_5632_);
lean_dec_ref(v_toApplicative_5631_);
v_mapConst_5633_ = lean_ctor_get(v_toFunctor_5632_, 1);
lean_inc(v_mapConst_5633_);
lean_dec_ref(v_toFunctor_5632_);
v___x_5634_ = lean_apply_3(v_inst_5628_, lean_box(0), v_action_5629_, v_prio_5630_);
v___x_5635_ = lean_box(0);
v___x_5636_ = lean_apply_4(v_mapConst_5633_, lean_box(0), lean_box(0), v___x_5635_, v___x_5634_);
return v___x_5636_;
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
