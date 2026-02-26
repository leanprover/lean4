// Lean compiler output
// Module: Std.Internal.Async.Select
// Imports: public import Init.Data.Random public import Std.Internal.Async.Basic import Init.Data.ByteArray.Extra import Init.Data.Array.Lemmas import Init.Omega
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_withPromise___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_withPromise(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___redArg___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_IO_Async_Waiter_race___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_Waiter_race___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_IO_Async_Waiter_race___redArg___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Waiter_race___redArg___closed__0_value;
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_checkFinished___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_checkFinished(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_checkFinished___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_stdNext(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_stdRange;
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "the promise linked to the Async was dropped"};
static const lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___closed__0_value;
static const lean_closure_object l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_Selectable_one___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___closed__0_value)} };
static const lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___closed__1 = (const lean_object*)&l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___closed__1_value;
lean_object* l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__1(size_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__7(size_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_new();
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__4(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__1_value;
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__1_value)} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__3(size_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_ByteArray_toUInt64LE_x21(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_mkStdGen(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_random_bytes(size_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Internal_IO_Async_Selectable_one___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Selectable_one___redArg___closed__0_value;
static const lean_ctor_object l_Std_Internal_IO_Async_Selectable_one___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Selectable_one___redArg___closed__0_value)}};
static const lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___closed__1 = (const lean_object*)&l_Std_Internal_IO_Async_Selectable_one___redArg___closed__1_value;
static const lean_string_object l_Std_Internal_IO_Async_Selectable_one___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Selectable.one requires at least one Selectable"};
static const lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___closed__2 = (const lean_object*)&l_Std_Internal_IO_Async_Selectable_one___redArg___closed__2_value;
static const lean_ctor_object l_Std_Internal_IO_Async_Selectable_one___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Selectable_one___redArg___closed__2_value)}};
static const lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___closed__3 = (const lean_object*)&l_Std_Internal_IO_Async_Selectable_one___redArg___closed__3_value;
static const lean_ctor_object l_Std_Internal_IO_Async_Selectable_one___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Selectable_one___redArg___closed__3_value)}};
static const lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___closed__4 = (const lean_object*)&l_Std_Internal_IO_Async_Selectable_one___redArg___closed__4_value;
static const lean_ctor_object l_Std_Internal_IO_Async_Selectable_one___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Selectable_one___redArg___closed__4_value)}};
static const lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___closed__5 = (const lean_object*)&l_Std_Internal_IO_Async_Selectable_one___redArg___closed__5_value;
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0___closed__1 = (const lean_object*)&l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__1_value;
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__1_value)} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__3(size_t, uint8_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__3(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_IO_Async_Selectable_tryOne___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Selectable_tryOne___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg___lam__1(size_t, uint8_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__5(size_t, lean_object*, uint8_t, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__4(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__2(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_IO_Async_Selectable_combine___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Selectable_combine___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___boxed__const__1;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_withPromise___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_withPromise(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 1);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_4);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___redArg___lam__0(uint8_t x_1) {
_start:
{
uint8_t x_2; 
if (x_1 == 0)
{
uint8_t x_8; 
x_8 = 1;
x_2 = x_8;
goto block_7;
}
else
{
uint8_t x_9; 
x_9 = 0;
x_2 = x_9;
goto block_7;
}
block_7:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = 1;
x_4 = lean_box(x_2);
x_5 = lean_box(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Internal_IO_Async_Waiter_race___redArg___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
if (x_4 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_5; 
x_5 = lean_apply_1(x_2, x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
x_6 = l_Std_Internal_IO_Async_Waiter_race___redArg___lam__1(x_1, x_2, x_3, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = ((lean_object*)(l_Std_Internal_IO_Async_Waiter_race___redArg___closed__0));
x_10 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Waiter_race___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_8);
x_11 = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, lean_box(0));
lean_closure_set(x_11, 2, lean_box(0));
lean_closure_set(x_11, 3, x_7);
lean_closure_set(x_11, 4, x_9);
x_12 = lean_apply_2(x_2, lean_box(0), x_11);
x_13 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_12, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Internal_IO_Async_Waiter_race___redArg(x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_checkFinished___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec_ref(x_2);
x_4 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, lean_box(0));
lean_closure_set(x_4, 2, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_checkFinished(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, x_6);
x_8 = lean_apply_2(x_4, lean_box(0), x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_checkFinished___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_IO_Async_Waiter_checkFinished(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 1)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = l_stdNext(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_nat_mul(x_7, x_2);
lean_dec(x_7);
x_13 = lean_nat_sub(x_11, x_1);
lean_dec(x_11);
x_14 = lean_nat_add(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
x_15 = lean_nat_div(x_3, x_2);
lean_dec(x_3);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_15, x_16);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
x_3 = x_17;
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_21 = lean_nat_mul(x_7, x_2);
lean_dec(x_7);
x_22 = lean_nat_sub(x_19, x_1);
lean_dec(x_19);
x_23 = lean_nat_add(x_21, x_22);
lean_dec(x_22);
lean_dec(x_21);
x_24 = lean_nat_div(x_3, x_2);
lean_dec(x_3);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_24, x_25);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_20);
x_3 = x_26;
x_4 = x_27;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_47; lean_object* x_48; 
x_47 = lean_nat_dec_lt(x_3, x_2);
if (x_47 == 0)
{
x_48 = x_2;
goto block_49;
}
else
{
x_48 = x_3;
goto block_49;
}
block_46:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_stdRange;
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_nat_sub(x_9, x_8);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_10, x_11);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(1000u);
x_14 = lean_nat_sub(x_5, x_4);
x_15 = lean_nat_add(x_14, x_11);
lean_dec(x_14);
x_16 = lean_nat_mul(x_15, x_13);
x_17 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 0, x_17);
x_18 = l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0_spec__0(x_8, x_12, x_16, x_6);
lean_dec(x_12);
lean_dec(x_8);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_nat_mod(x_20, x_15);
lean_dec(x_15);
lean_dec(x_20);
x_22 = lean_nat_add(x_4, x_21);
lean_dec(x_21);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_nat_mod(x_23, x_15);
lean_dec(x_15);
lean_dec(x_23);
x_26 = lean_nat_add(x_4, x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_28 = lean_ctor_get(x_6, 0);
x_29 = lean_ctor_get(x_6, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_6);
x_30 = lean_nat_sub(x_29, x_28);
lean_dec(x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_30, x_31);
lean_dec(x_30);
x_33 = lean_unsigned_to_nat(1000u);
x_34 = lean_nat_sub(x_5, x_4);
x_35 = lean_nat_add(x_34, x_31);
lean_dec(x_34);
x_36 = lean_nat_mul(x_35, x_33);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_1);
x_39 = l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0_spec__0(x_28, x_32, x_36, x_38);
lean_dec(x_32);
lean_dec(x_28);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = lean_nat_mod(x_40, x_35);
lean_dec(x_35);
lean_dec(x_40);
x_44 = lean_nat_add(x_4, x_43);
lean_dec(x_43);
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
}
block_49:
{
if (x_47 == 0)
{
x_4 = x_48;
x_5 = x_3;
goto block_46;
}
else
{
x_4 = x_48;
x_5 = x_2;
goto block_46;
}
}
}
}
LEAN_EXPORT lean_object* l_randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_4, x_5);
x_7 = lean_nat_dec_lt(x_3, x_6);
if (x_7 == 0)
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0(x_2, x_3, x_6);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_array_swap(x_1, x_3, x_9);
lean_dec(x_9);
x_12 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_1 = x_11;
x_2 = x_10;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_match__1_splitter___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_io_error_to_string(x_4);
x_6 = lean_mk_io_user_error(x_5);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_io_error_to_string(x_7);
x_9 = lean_mk_io_user_error(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_ctor_set_tag(x_1, 0);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_io_user_error(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
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
lean_object* x_10; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec_ref(x_3);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec_ref(x_1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec_ref(x_10);
x_17 = lean_io_promise_result_opt(x_16);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_task_map(x_1, x_17, x_18, x_2);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__1(x_1, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
lean_dec_ref(x_2);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_3, 0);
lean_dec(x_11);
x_12 = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___closed__1));
x_13 = lean_box(x_1);
x_14 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__1___boxed), 4, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
lean_ctor_set(x_3, 0, x_2);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_3);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_16, x_1, x_15, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_3);
x_18 = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___closed__1));
x_19 = lean_box(x_1);
x_20 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__1___boxed), 4, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_2);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_23, x_1, x_22, x_20);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2(x_5, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
x_18 = lean_task_pure(x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
lean_dec_ref(x_5);
x_20 = l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg(x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_ctor_set_tag(x_20, 1);
x_7 = x_20;
x_8 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_7 = x_23;
x_8 = lean_box(0);
goto block_16;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
lean_ctor_set_tag(x_20, 0);
x_7 = x_20;
x_8 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_7 = x_26;
x_8 = lean_box(0);
goto block_16;
}
}
}
block_16:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_10, x_2, x_9, x_3);
x_12 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_10, x_2, x_11, x_4);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_task_pure(x_13);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_15);
lean_dec_ref(x_12);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__4(x_1, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_io_promise_resolve(x_2, x_1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_io_promise_resolve(x_9, x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__0(x_1, x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_dec(x_10);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_2, 0, x_11);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; 
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_5);
x_8 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_2(x_8, x_2, lean_box(0));
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_10, x_3, x_9, x_4);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__3(x_1, x_2, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__1(x_6, x_2, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_uget_borrowed(x_1, x_3);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_10, 2);
lean_inc_ref(x_11);
x_12 = lean_apply_1(x_11, lean_box(0));
x_13 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___closed__0));
x_14 = lean_unsigned_to_nat(0u);
x_15 = 0;
x_16 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_14, x_15, x_12, x_13);
x_17 = lean_box_usize(x_3);
x_18 = lean_box_usize(x_2);
x_19 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__1___boxed), 5, 3);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_18);
x_20 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_14, x_15, x_16, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__1(size_t x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_6; 
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
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec_ref(x_2);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_4, 0, x_14);
lean_ctor_set(x_12, 0, x_4);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_4, 0, x_15);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_4);
return x_16;
}
}
else
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
lean_free_object(x_4);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec_ref(x_12);
x_18 = 1;
x_19 = lean_usize_add(x_1, x_18);
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg(x_2, x_3, x_19, x_17);
return x_20;
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
lean_dec(x_4);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_2);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_23 = x_21;
} else {
 lean_dec_ref(x_21);
 x_23 = lean_box(0);
}
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_22);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 1, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec_ref(x_21);
x_27 = 1;
x_28 = lean_usize_add(x_1, x_27);
x_29 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg(x_2, x_3, x_28, x_26);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg(x_1, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_8; 
lean_dec_ref(x_5);
lean_dec_ref(x_3);
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
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec_ref(x_6);
x_14 = lean_array_size(x_1);
x_15 = 0;
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg(x_1, x_14, x_15, x_2);
x_17 = lean_box(x_4);
x_18 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__3___boxed), 6, 4);
lean_closure_set(x_18, 0, x_3);
lean_closure_set(x_18, 1, x_13);
lean_closure_set(x_18, 2, x_17);
lean_closure_set(x_18, 3, x_5);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_19, x_4, x_16, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__2(x_1, x_2, x_3, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__1(x_1, x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__5(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_8; 
lean_dec_ref(x_5);
lean_dec_ref(x_2);
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_6, 0);
lean_dec(x_14);
x_15 = lean_io_promise_result_opt(x_1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_io_bind_task(x_15, x_2, x_16, x_3);
lean_dec_ref(x_17);
lean_ctor_set(x_6, 0, x_4);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_6);
x_19 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_16, x_3, x_18, x_5);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_6);
x_20 = lean_io_promise_result_opt(x_1);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_io_bind_task(x_20, x_2, x_21, x_3);
lean_dec_ref(x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_4);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_21, x_3, x_24, x_5);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__5(x_1, x_2, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_9; 
lean_dec_ref(x_6);
lean_dec_ref(x_3);
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
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
lean_dec_ref(x_7);
x_18 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_18);
lean_dec_ref(x_15);
lean_inc(x_17);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_2);
x_19 = lean_apply_2(x_18, x_1, lean_box(0));
x_20 = lean_box(x_4);
x_21 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__5___boxed), 7, 5);
lean_closure_set(x_21, 0, x_17);
lean_closure_set(x_21, 1, x_3);
lean_closure_set(x_21, 2, x_20);
lean_closure_set(x_21, 3, x_5);
lean_closure_set(x_21, 4, x_6);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_22, x_4, x_19, x_21);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
lean_dec_ref(x_7);
x_26 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_26);
lean_dec_ref(x_24);
lean_inc(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_apply_2(x_26, x_27, lean_box(0));
x_29 = lean_box(x_4);
x_30 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__5___boxed), 7, 5);
lean_closure_set(x_30, 0, x_25);
lean_closure_set(x_30, 1, x_3);
lean_closure_set(x_30, 2, x_29);
lean_closure_set(x_30, 3, x_5);
lean_closure_set(x_30, 4, x_6);
x_31 = lean_unsigned_to_nat(0u);
x_32 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_31, x_4, x_28, x_30);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__6(x_1, x_2, x_3, x_9, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__7(x_9, x_2, x_3, x_4, x_5, x_10, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_6, x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_12 = lean_io_promise_new();
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_13, 0, x_1);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__1___boxed), 3, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = lean_box(0);
x_16 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___closed__0));
x_17 = 0;
x_18 = lean_array_uget_borrowed(x_4, x_6);
x_19 = lean_box(x_17);
lean_inc(x_18);
lean_inc_ref(x_2);
x_20 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__2___boxed), 7, 5);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_15);
lean_closure_set(x_20, 2, x_18);
lean_closure_set(x_20, 3, x_19);
lean_closure_set(x_20, 4, x_14);
x_21 = lean_box(x_17);
x_22 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__4___boxed), 6, 4);
lean_closure_set(x_22, 0, x_15);
lean_closure_set(x_22, 1, x_21);
lean_closure_set(x_22, 2, x_20);
lean_closure_set(x_22, 3, x_13);
x_23 = lean_box(x_17);
lean_inc(x_3);
lean_inc(x_18);
x_24 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__6___boxed), 8, 6);
lean_closure_set(x_24, 0, x_18);
lean_closure_set(x_24, 1, x_3);
lean_closure_set(x_24, 2, x_22);
lean_closure_set(x_24, 3, x_23);
lean_closure_set(x_24, 4, x_15);
lean_closure_set(x_24, 5, x_16);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_12);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_27, x_17, x_26, x_24);
x_29 = lean_box_usize(x_6);
x_30 = lean_box_usize(x_5);
x_31 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__7___boxed), 8, 6);
lean_closure_set(x_31, 0, x_29);
lean_closure_set(x_31, 1, x_1);
lean_closure_set(x_31, 2, x_2);
lean_closure_set(x_31, 3, x_3);
lean_closure_set(x_31, 4, x_4);
lean_closure_set(x_31, 5, x_30);
x_32 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_27, x_17, x_28, x_31);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__7(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_9; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
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
lean_object* x_15; 
x_15 = lean_ctor_get(x_7, 0);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_7, 0, x_17);
lean_ctor_set(x_15, 0, x_7);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_7, 0, x_18);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_7);
return x_19;
}
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
lean_free_object(x_7);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec_ref(x_15);
x_21 = 1;
x_22 = lean_usize_add(x_1, x_21);
x_23 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_22, x_20);
return x_23;
}
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_7, 0);
lean_inc(x_24);
lean_dec(x_7);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_26 = x_24;
} else {
 lean_dec_ref(x_24);
 x_26 = lean_box(0);
}
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_25);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 1, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
else
{
lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
lean_dec_ref(x_24);
x_30 = 1;
x_31 = lean_usize_add(x_1, x_30);
x_32 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_31, x_29);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg(x_1, x_2, x_3, x_4, x_9, x_10, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_7; 
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
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_array_size(x_1);
x_14 = 0;
lean_inc_ref(x_1);
lean_inc(x_12);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg(x_12, x_1, x_2, x_1, x_13, x_14, x_3);
x_16 = lean_box(x_4);
x_17 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___boxed), 4, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_5);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_18, x_4, x_15, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
x_8 = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__3(x_1, x_2, x_3, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_6; 
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_io_promise_new();
x_14 = lean_box(x_3);
x_15 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__3___boxed), 6, 4);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_12);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_14);
lean_ctor_set(x_4, 0, x_13);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_4);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_17, x_3, x_16, x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_io_promise_new();
x_21 = lean_box(x_3);
x_22 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__3___boxed), 6, 4);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_19);
lean_closure_set(x_22, 2, x_2);
lean_closure_set(x_22, 3, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_25, x_3, x_24, x_22);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__4(x_1, x_2, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
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
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_3, 0);
lean_dec(x_11);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_st_mk_ref(x_13);
x_15 = lean_box(x_12);
x_16 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__4___boxed), 5, 3);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_15);
lean_ctor_set(x_3, 0, x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_18, x_12, x_17, x_16);
return x_19;
}
else
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_3);
x_20 = 0;
x_21 = lean_box(x_20);
x_22 = lean_st_mk_ref(x_21);
x_23 = lean_box(x_20);
x_24 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__4___boxed), 5, 3);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_27, x_20, x_26, x_24);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__5(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
lean_dec_ref(x_2);
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
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
lean_ctor_set(x_3, 0, x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_3);
x_14 = lean_unsigned_to_nat(0u);
x_15 = 0;
x_16 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_14, x_15, x_13, x_2);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec_ref(x_2);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_3, 0, x_18);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
lean_ctor_set(x_3, 0, x_19);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
lean_dec(x_3);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_1);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = 0;
x_27 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_25, x_26, x_24, x_2);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_2);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_29 = x_22;
} else {
 lean_dec_ref(x_22);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_28);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 1, 0);
} else {
 x_31 = x_29;
 lean_ctor_set_tag(x_31, 0);
}
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__6(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_2, 0, x_13);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_1);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_dec(x_10);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_2, 0, x_11);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_7; 
lean_dec_ref(x_4);
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
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
lean_free_object(x_5);
lean_dec_ref(x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_15);
lean_dec_ref(x_1);
x_16 = lean_apply_2(x_15, x_14, lean_box(0));
x_17 = lean_unsigned_to_nat(0u);
x_18 = 0;
x_19 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_17, x_18, x_16, x_2);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
lean_dec(x_13);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
lean_ctor_set(x_5, 0, x_3);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_5);
x_21 = lean_unsigned_to_nat(0u);
x_22 = 0;
x_23 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_21, x_22, x_20, x_4);
return x_23;
}
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
lean_dec(x_5);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
lean_dec_ref(x_4);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_26);
lean_dec_ref(x_1);
x_27 = lean_apply_2(x_26, x_25, lean_box(0));
x_28 = lean_unsigned_to_nat(0u);
x_29 = 0;
x_30 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_28, x_29, x_27, x_2);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
lean_dec(x_24);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_3);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_unsigned_to_nat(0u);
x_34 = 0;
x_35 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_33, x_34, x_32, x_4);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__2(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__3(x_6, x_2, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_4);
x_9 = lean_array_uget_borrowed(x_1, x_3);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
x_12 = lean_apply_1(x_11, lean_box(0));
x_13 = lean_box(0);
x_14 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__0));
x_15 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__2));
lean_inc(x_9);
x_16 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__2___boxed), 6, 4);
lean_closure_set(x_16, 0, x_9);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_13);
lean_closure_set(x_16, 3, x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = 0;
x_19 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_17, x_18, x_12, x_16);
x_20 = lean_box_usize(x_3);
x_21 = lean_box_usize(x_2);
x_22 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__3___boxed), 5, 3);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_1);
lean_closure_set(x_22, 2, x_21);
x_23 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_17, x_18, x_19, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__3(size_t x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_6; 
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
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec_ref(x_2);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_4, 0, x_14);
lean_ctor_set(x_12, 0, x_4);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_4, 0, x_15);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_4);
return x_16;
}
}
else
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
lean_free_object(x_4);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec_ref(x_12);
x_18 = 1;
x_19 = lean_usize_add(x_1, x_18);
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg(x_2, x_3, x_19, x_17);
return x_20;
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
lean_dec(x_4);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_2);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_23 = x_21;
} else {
 lean_dec_ref(x_21);
 x_23 = lean_box(0);
}
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_22);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 1, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec_ref(x_21);
x_27 = 1;
x_28 = lean_usize_add(x_1, x_27);
x_29 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg(x_2, x_3, x_28, x_26);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg(x_1, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = l_ByteArray_toUInt64LE_x21(x_9);
lean_dec(x_9);
x_11 = lean_uint64_to_nat(x_10);
x_12 = l_mkStdGen(x_11);
lean_dec(x_11);
x_13 = l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt___redArg(x_1, x_12);
x_14 = lean_box(0);
x_15 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__1));
x_16 = lean_array_size(x_13);
x_17 = 0;
lean_inc_ref(x_13);
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg(x_13, x_16, x_17, x_15);
x_19 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__5___boxed), 4, 2);
lean_closure_set(x_19, 0, x_13);
lean_closure_set(x_19, 1, x_14);
x_20 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__6___boxed), 4, 2);
lean_closure_set(x_20, 0, x_14);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = 0;
x_23 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_21, x_22, x_18, x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__7(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; size_t x_11; lean_object* x_12; 
x_11 = 8;
x_12 = lean_io_get_random_bytes(x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 1);
x_4 = x_12;
x_5 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_4 = x_15;
x_5 = lean_box(0);
goto block_10;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_ctor_set_tag(x_12, 0);
x_4 = x_12;
x_5 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_4 = x_18;
x_5 = lean_box(0);
goto block_10;
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__8(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__9(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = lean_apply_2(x_1, x_9, lean_box(0));
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__9(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
lean_inc_ref(x_1);
x_3 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__7___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__8___boxed), 3, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = l_Array_isEmpty___redArg(x_1);
lean_dec_ref(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__9___boxed), 3, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_one___redArg___closed__1));
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_8, x_5, x_7, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__9___boxed), 3, 1);
lean_closure_set(x_10, 0, x_4);
x_11 = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_one___redArg___closed__5));
x_12 = lean_unsigned_to_nat(0u);
x_13 = 0;
x_14 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_12, x_13, x_11, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Selectable_one___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_Selectable_one___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_Selectable_one(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0(x_1, x_2, x_7, x_8, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_11 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2(x_1, x_2, x_3, x_4, x_5, x_10, x_11, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3(x_1, x_2, x_7, x_8, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0(lean_object* x_1) {
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
lean_object* x_8; 
lean_dec_ref(x_1);
x_8 = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0___closed__1));
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_6; 
lean_dec_ref(x_3);
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
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_ctor_set(x_4, 0, x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_4);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_15, x_2, x_14, x_3);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec_ref(x_3);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_13, 0);
lean_ctor_set(x_4, 0, x_18);
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
lean_ctor_set(x_4, 0, x_19);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_4);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
lean_dec(x_4);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_1);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_25, x_2, x_24, x_3);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_3);
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_28 = x_22;
} else {
 lean_dec_ref(x_22);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_27);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 1, 0);
} else {
 x_30 = x_28;
 lean_ctor_set_tag(x_30, 0);
}
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__1(x_1, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_8; 
lean_dec_ref(x_5);
lean_dec_ref(x_3);
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
lean_object* x_14; 
x_14 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_free_object(x_6);
lean_dec_ref(x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_1);
x_17 = lean_apply_2(x_16, x_15, lean_box(0));
x_18 = lean_unsigned_to_nat(0u);
x_19 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_18, x_2, x_17, x_3);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_14);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
lean_ctor_set(x_6, 0, x_4);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_6);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_21, x_2, x_20, x_5);
return x_22;
}
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_6, 0);
lean_inc(x_23);
lean_dec(x_6);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_5);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_25);
lean_dec_ref(x_1);
x_26 = lean_apply_2(x_25, x_24, lean_box(0));
x_27 = lean_unsigned_to_nat(0u);
x_28 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_27, x_2, x_26, x_3);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_23);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_4);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_unsigned_to_nat(0u);
x_32 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_31, x_2, x_30, x_5);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__2(x_1, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_dec(x_10);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_2, 0, x_11);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_2, 0, x_14);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_1);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; uint8_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox(x_2);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__3(x_7, x_8, x_3, x_9, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
lean_dec_ref(x_5);
x_10 = lean_array_uget_borrowed(x_2, x_4);
x_11 = lean_ctor_get(x_10, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
x_13 = lean_apply_1(x_12, lean_box(0));
x_14 = lean_box(0);
x_15 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__0));
x_16 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__2));
x_17 = lean_box(x_1);
lean_inc(x_10);
x_18 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__2___boxed), 7, 5);
lean_closure_set(x_18, 0, x_10);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_15);
lean_closure_set(x_18, 3, x_14);
lean_closure_set(x_18, 4, x_16);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_19, x_1, x_13, x_18);
x_21 = lean_box_usize(x_4);
x_22 = lean_box(x_1);
x_23 = lean_box_usize(x_3);
x_24 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__3___boxed), 6, 4);
lean_closure_set(x_24, 0, x_21);
lean_closure_set(x_24, 1, x_22);
lean_closure_set(x_24, 2, x_2);
lean_closure_set(x_24, 3, x_23);
x_25 = 0;
x_26 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_19, x_25, x_20, x_24);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__3(size_t x_1, uint8_t x_2, lean_object* x_3, size_t x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_7; 
lean_dec_ref(x_3);
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
lean_object* x_13; 
x_13 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec_ref(x_3);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_ctor_set(x_5, 0, x_15);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_5, 0, x_16);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_5);
return x_17;
}
}
else
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
lean_free_object(x_5);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec_ref(x_13);
x_19 = 1;
x_20 = lean_usize_add(x_1, x_19);
x_21 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(x_2, x_3, x_4, x_20, x_18);
return x_21;
}
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_5, 0);
lean_inc(x_22);
lean_dec(x_5);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_3);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_24 = x_22;
} else {
 lean_dec_ref(x_22);
 x_24 = lean_box(0);
}
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 1, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
lean_dec_ref(x_22);
x_28 = 1;
x_29 = lean_usize_add(x_1, x_28);
x_30 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(x_2, x_3, x_4, x_29, x_27);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(x_7, x_2, x_8, x_9, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_6; 
lean_dec_ref(x_3);
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
lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = l_ByteArray_toUInt64LE_x21(x_11);
lean_dec(x_11);
x_13 = lean_uint64_to_nat(x_12);
x_14 = l_mkStdGen(x_13);
lean_dec(x_13);
x_15 = l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt___redArg(x_1, x_14);
x_16 = lean_box(0);
x_17 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__1));
x_18 = lean_array_size(x_15);
x_19 = 0;
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(x_2, x_15, x_18, x_19, x_17);
x_21 = lean_box(x_2);
x_22 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__1___boxed), 5, 3);
lean_closure_set(x_22, 0, x_16);
lean_closure_set(x_22, 1, x_21);
lean_closure_set(x_22, 2, x_3);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_23, x_2, x_20, x_22);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__2(x_1, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__3(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_11; 
lean_dec_ref(x_2);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
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
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
lean_object* x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_3, 0);
lean_dec(x_17);
x_18 = 8;
x_19 = lean_io_get_random_bytes(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
lean_ctor_set(x_3, 0, x_20);
x_5 = x_3;
x_6 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec_ref(x_19);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_21);
x_5 = x_3;
x_6 = lean_box(0);
goto block_10;
}
}
else
{
size_t x_22; lean_object* x_23; 
lean_dec(x_3);
x_22 = 8;
x_23 = lean_io_get_random_bytes(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_5 = x_25;
x_6 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec_ref(x_23);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_5 = x_27;
x_6 = lean_box(0);
goto block_10;
}
}
}
block_10:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_8, x_1, x_7, x_2);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__3(x_5, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg(lean_object* x_1) {
_start:
{
uint8_t x_3; 
x_3 = l_Array_isEmpty___redArg(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_tryOne___redArg___closed__0));
x_5 = lean_box(x_3);
x_6 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__2___boxed), 5, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_4);
x_7 = lean_box(x_3);
x_8 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__3___boxed), 4, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_6);
x_9 = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_one___redArg___closed__1));
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_10, x_3, x_9, x_8);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec_ref(x_1);
x_12 = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0___closed__1));
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Selectable_tryOne___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_Selectable_tryOne___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_Selectable_tryOne(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_2);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0(x_1, x_8, x_3, x_9, x_10, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
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
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
lean_ctor_set(x_2, 0, x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_9; 
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
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
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_14);
lean_dec_ref(x_2);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec_ref(x_7);
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_1, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_18);
lean_dec_ref(x_14);
lean_inc(x_15);
lean_ctor_set(x_1, 1, x_15);
x_19 = lean_apply_2(x_18, x_1, lean_box(0));
x_20 = lean_box(x_4);
x_21 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__5___boxed), 7, 5);
lean_closure_set(x_21, 0, x_15);
lean_closure_set(x_21, 1, x_3);
lean_closure_set(x_21, 2, x_20);
lean_closure_set(x_21, 3, x_5);
lean_closure_set(x_21, 4, x_6);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_22, x_4, x_19, x_21);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_25);
lean_dec_ref(x_14);
lean_inc(x_15);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_15);
x_27 = lean_apply_2(x_25, x_26, lean_box(0));
x_28 = lean_box(x_4);
x_29 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__5___boxed), 7, 5);
lean_closure_set(x_29, 0, x_15);
lean_closure_set(x_29, 1, x_3);
lean_closure_set(x_29, 2, x_28);
lean_closure_set(x_29, 3, x_5);
lean_closure_set(x_29, 4, x_6);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_30, x_4, x_27, x_29);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__6(x_1, x_2, x_3, x_9, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; uint8_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox(x_2);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg___lam__1(x_7, x_8, x_3, x_9, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_10 = lean_array_uget_borrowed(x_2, x_4);
x_11 = lean_ctor_get(x_10, 0);
x_12 = lean_ctor_get(x_11, 2);
lean_inc_ref(x_12);
x_13 = lean_apply_1(x_12, lean_box(0));
x_14 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___closed__0));
x_15 = lean_unsigned_to_nat(0u);
x_16 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_15, x_1, x_13, x_14);
x_17 = lean_box_usize(x_4);
x_18 = lean_box(x_1);
x_19 = lean_box_usize(x_3);
x_20 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg___lam__1___boxed), 6, 4);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_18);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_19);
x_21 = 0;
x_22 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_15, x_21, x_16, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg___lam__1(size_t x_1, uint8_t x_2, lean_object* x_3, size_t x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_7; 
lean_dec_ref(x_3);
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
lean_object* x_13; 
x_13 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec_ref(x_3);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_ctor_set(x_5, 0, x_15);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_5, 0, x_16);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_5);
return x_17;
}
}
else
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
lean_free_object(x_5);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec_ref(x_13);
x_19 = 1;
x_20 = lean_usize_add(x_1, x_19);
x_21 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(x_2, x_3, x_4, x_20, x_18);
return x_21;
}
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_5, 0);
lean_inc(x_22);
lean_dec(x_5);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_3);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_24 = x_22;
} else {
 lean_dec_ref(x_22);
 x_24 = lean_box(0);
}
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 1, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
lean_dec_ref(x_22);
x_28 = 1;
x_29 = lean_usize_add(x_1, x_28);
x_30 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(x_2, x_3, x_4, x_29, x_27);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(x_7, x_2, x_8, x_9, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_14; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_5);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
x_17 = l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg(x_4);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
lean_ctor_set(x_5, 0, x_18);
x_7 = x_5;
x_8 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec_ref(x_17);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_19);
x_7 = x_5;
x_8 = lean_box(0);
goto block_13;
}
}
else
{
lean_object* x_20; 
lean_dec(x_5);
x_20 = l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg(x_4);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_7 = x_22;
x_8 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec_ref(x_20);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_7 = x_24;
x_8 = lean_box(0);
goto block_13;
}
}
}
block_13:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_10, x_1, x_9, x_2);
x_12 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_10, x_1, x_11, x_3);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__3(x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_6; 
lean_dec_ref(x_3);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_apply_2(x_12, x_11, lean_box(0));
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_14, x_2, x_13, x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__2(x_1, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__0(x_1, x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_io_promise_resolve(x_2, x_1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_io_promise_resolve(x_9, x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__1(x_1, x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_task_pure(x_8);
return x_9;
}
else
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec_ref(x_6);
x_11 = lean_array_size(x_2);
x_12 = 0;
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(x_3, x_2, x_11, x_12, x_1);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec_ref(x_4);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__1___boxed), 3, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_16, 0, x_14);
x_17 = lean_box(x_3);
x_18 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__2___boxed), 5, 3);
lean_closure_set(x_18, 0, x_5);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_16);
x_19 = lean_box(x_3);
x_20 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__3___boxed), 6, 4);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_18);
lean_closure_set(x_20, 2, x_15);
lean_closure_set(x_20, 3, x_10);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_21, x_3, x_13, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_task_pure(x_23);
return x_24;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_25);
lean_dec_ref(x_22);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__4(x_1, x_2, x_8, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; uint8_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox(x_3);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__5(x_9, x_2, x_10, x_4, x_5, x_11, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_6, x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_12 = lean_io_promise_new();
x_13 = lean_box(0);
x_14 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___closed__0));
x_15 = lean_array_uget_borrowed(x_4, x_6);
x_16 = lean_box(x_2);
lean_inc(x_15);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_17 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__4___boxed), 7, 5);
lean_closure_set(x_17, 0, x_13);
lean_closure_set(x_17, 1, x_1);
lean_closure_set(x_17, 2, x_16);
lean_closure_set(x_17, 3, x_3);
lean_closure_set(x_17, 4, x_15);
x_18 = lean_box(x_2);
lean_inc(x_15);
lean_inc_ref(x_3);
x_19 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__6___boxed), 8, 6);
lean_closure_set(x_19, 0, x_3);
lean_closure_set(x_19, 1, x_15);
lean_closure_set(x_19, 2, x_17);
lean_closure_set(x_19, 3, x_18);
lean_closure_set(x_19, 4, x_13);
lean_closure_set(x_19, 5, x_14);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_12);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_22, x_2, x_21, x_19);
x_24 = lean_box_usize(x_6);
x_25 = lean_box(x_2);
x_26 = lean_box_usize(x_5);
x_27 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__5___boxed), 8, 6);
lean_closure_set(x_27, 0, x_24);
lean_closure_set(x_27, 1, x_1);
lean_closure_set(x_27, 2, x_25);
lean_closure_set(x_27, 3, x_3);
lean_closure_set(x_27, 4, x_4);
lean_closure_set(x_27, 5, x_26);
x_28 = 0;
x_29 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_22, x_28, x_23, x_27);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__5(size_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, size_t x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_9; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
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
lean_object* x_15; 
x_15 = lean_ctor_get(x_7, 0);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_7, 0, x_17);
lean_ctor_set(x_15, 0, x_7);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_7, 0, x_18);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_7);
return x_19;
}
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
lean_free_object(x_7);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec_ref(x_15);
x_21 = 1;
x_22 = lean_usize_add(x_1, x_21);
x_23 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_22, x_20);
return x_23;
}
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_7, 0);
lean_inc(x_24);
lean_dec(x_7);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_26 = x_24;
} else {
 lean_dec_ref(x_24);
 x_26 = lean_box(0);
}
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_25);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 1, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
else
{
lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
lean_dec_ref(x_24);
x_30 = 1;
x_31 = lean_usize_add(x_1, x_30);
x_32 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_31, x_29);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg(x_1, x_9, x_3, x_4, x_10, x_11, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_array_size(x_1);
x_8 = 0;
lean_inc_ref(x_1);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg(x_1, x_2, x_5, x_1, x_7, x_8, x_3);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_10, x_2, x_9, x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
x_8 = l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__0(x_1, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__4(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_9, x_1, x_8, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_1);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__4(x_8, x_2, x_9, x_10, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__2(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_9, x_1, x_8, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_1);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__2(x_8, x_2, x_9, x_10, x_5, x_6);
return x_11;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Selectable_combine___redArg___boxed__const__1(void) {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg(lean_object* x_1) {
_start:
{
uint8_t x_3; 
x_3 = l_Array_isEmpty___redArg(x_1);
if (x_3 == 0)
{
size_t x_4; lean_object* x_5; 
x_4 = 8;
x_5 = lean_io_get_random_bytes(x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_tryOne___redArg___closed__0));
x_9 = l_ByteArray_toUInt64LE_x21(x_7);
lean_dec(x_7);
x_10 = lean_uint64_to_nat(x_9);
x_11 = l_mkStdGen(x_10);
lean_dec(x_10);
x_12 = l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt___redArg(x_1, x_11);
x_13 = lean_box(0);
x_14 = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_combine___redArg___closed__0));
x_15 = lean_box(x_3);
lean_inc_ref(x_12);
x_16 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__0___boxed), 6, 4);
lean_closure_set(x_16, 0, x_12);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_13);
lean_closure_set(x_16, 3, x_14);
x_17 = lean_box(x_3);
x_18 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__1___boxed), 5, 3);
lean_closure_set(x_18, 0, x_13);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_8);
x_19 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__1));
x_20 = lean_array_size(x_12);
x_21 = lean_box(x_3);
x_22 = lean_box_usize(x_20);
x_23 = l_Std_Internal_IO_Async_Selectable_combine___redArg___boxed__const__1;
lean_inc_ref(x_12);
x_24 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__4___boxed), 7, 6);
lean_closure_set(x_24, 0, x_21);
lean_closure_set(x_24, 1, x_12);
lean_closure_set(x_24, 2, x_22);
lean_closure_set(x_24, 3, x_23);
lean_closure_set(x_24, 4, x_13);
lean_closure_set(x_24, 5, x_14);
x_25 = lean_box(x_3);
x_26 = lean_box_usize(x_20);
x_27 = l_Std_Internal_IO_Async_Selectable_combine___redArg___boxed__const__1;
x_28 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__2___boxed), 7, 6);
lean_closure_set(x_28, 0, x_25);
lean_closure_set(x_28, 1, x_12);
lean_closure_set(x_28, 2, x_26);
lean_closure_set(x_28, 3, x_27);
lean_closure_set(x_28, 4, x_19);
lean_closure_set(x_28, 5, x_18);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_16);
lean_ctor_set(x_29, 2, x_24);
lean_ctor_set(x_5, 0, x_29);
return x_5;
}
else
{
lean_object* x_30; lean_object* x_31; uint64_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_30 = lean_ctor_get(x_5, 0);
lean_inc(x_30);
lean_dec(x_5);
x_31 = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_tryOne___redArg___closed__0));
x_32 = l_ByteArray_toUInt64LE_x21(x_30);
lean_dec(x_30);
x_33 = lean_uint64_to_nat(x_32);
x_34 = l_mkStdGen(x_33);
lean_dec(x_33);
x_35 = l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt___redArg(x_1, x_34);
x_36 = lean_box(0);
x_37 = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_combine___redArg___closed__0));
x_38 = lean_box(x_3);
lean_inc_ref(x_35);
x_39 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__0___boxed), 6, 4);
lean_closure_set(x_39, 0, x_35);
lean_closure_set(x_39, 1, x_38);
lean_closure_set(x_39, 2, x_36);
lean_closure_set(x_39, 3, x_37);
x_40 = lean_box(x_3);
x_41 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__1___boxed), 5, 3);
lean_closure_set(x_41, 0, x_36);
lean_closure_set(x_41, 1, x_40);
lean_closure_set(x_41, 2, x_31);
x_42 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__1));
x_43 = lean_array_size(x_35);
x_44 = lean_box(x_3);
x_45 = lean_box_usize(x_43);
x_46 = l_Std_Internal_IO_Async_Selectable_combine___redArg___boxed__const__1;
lean_inc_ref(x_35);
x_47 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__4___boxed), 7, 6);
lean_closure_set(x_47, 0, x_44);
lean_closure_set(x_47, 1, x_35);
lean_closure_set(x_47, 2, x_45);
lean_closure_set(x_47, 3, x_46);
lean_closure_set(x_47, 4, x_36);
lean_closure_set(x_47, 5, x_37);
x_48 = lean_box(x_3);
x_49 = lean_box_usize(x_43);
x_50 = l_Std_Internal_IO_Async_Selectable_combine___redArg___boxed__const__1;
x_51 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__2___boxed), 7, 6);
lean_closure_set(x_51, 0, x_48);
lean_closure_set(x_51, 1, x_35);
lean_closure_set(x_51, 2, x_49);
lean_closure_set(x_51, 3, x_50);
lean_closure_set(x_51, 4, x_42);
lean_closure_set(x_51, 5, x_41);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_39);
lean_ctor_set(x_52, 2, x_47);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec_ref(x_1);
x_54 = !lean_is_exclusive(x_5);
if (x_54 == 0)
{
return x_5;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_5, 0);
lean_inc(x_55);
lean_dec(x_5);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec_ref(x_1);
x_57 = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_one___redArg___closed__3));
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Selectable_combine___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_Selectable_combine___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_Selectable_combine(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_2);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0(x_1, x_8, x_3, x_9, x_10, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1(x_1, x_2, x_10, x_4, x_5, x_11, x_12, x_8);
return x_13;
}
}
lean_object* initialize_Init_Data_Random(uint8_t builtin);
lean_object* initialize_Std_Internal_Async_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_ByteArray_Extra(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Async_Select(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Random(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Async_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Internal_IO_Async_Selectable_combine___redArg___boxed__const__1 = _init_l_Std_Internal_IO_Async_Selectable_combine___redArg___boxed__const__1();
lean_mark_persistent(l_Std_Internal_IO_Async_Selectable_combine___redArg___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
