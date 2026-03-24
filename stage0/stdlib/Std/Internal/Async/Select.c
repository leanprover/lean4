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
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_stdRange;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_stdNext(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_io_promise_new();
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
uint64_t l_ByteArray_toUInt64LE_x21(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_mkStdGen(lean_object*);
lean_object* lean_io_get_random_bytes(size_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_withPromise___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_withPromise(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___redArg___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_IO_Async_Waiter_race___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_Waiter_race___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_IO_Async_Waiter_race___redArg___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Waiter_race___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_checkFinished___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_checkFinished(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_checkFinished___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "the promise linked to the Async was dropped"};
static const lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___closed__0_value;
static const lean_closure_object l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_Selectable_one___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___closed__0_value)} };
static const lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___closed__1 = (const lean_object*)&l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__1(size_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__7(size_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__4(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__2(size_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_IO_Async_Selectable_one___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Selectable.one requires at least one Selectable"};
static const lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Selectable_one___redArg___closed__0_value;
static const lean_ctor_object l_Std_Internal_IO_Async_Selectable_one___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Selectable_one___redArg___closed__0_value)}};
static const lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___closed__1 = (const lean_object*)&l_Std_Internal_IO_Async_Selectable_one___redArg___closed__1_value;
static const lean_ctor_object l_Std_Internal_IO_Async_Selectable_one___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Selectable_one___redArg___closed__1_value)}};
static const lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___closed__2 = (const lean_object*)&l_Std_Internal_IO_Async_Selectable_one___redArg___closed__2_value;
static const lean_ctor_object l_Std_Internal_IO_Async_Selectable_one___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Selectable_one___redArg___closed__2_value)}};
static const lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___closed__3 = (const lean_object*)&l_Std_Internal_IO_Async_Selectable_one___redArg___closed__3_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__2(size_t, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_IO_Async_Selectable_tryOne___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Selectable_tryOne___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg___lam__1(size_t, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__7(size_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_IO_Async_Selectable_combine___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Selectable_combine___redArg___closed__0_value;
static const lean_ctor_object l_Std_Internal_IO_Async_Selectable_combine___redArg___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___boxed__const__1 = (const lean_object*)&l_Std_Internal_IO_Async_Selectable_combine___redArg___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_withPromise___redArg(lean_object* v_w_1_, lean_object* v_p_2_){
_start:
{
lean_object* v_finished_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_10_; 
v_finished_3_ = lean_ctor_get(v_w_1_, 0);
v_isSharedCheck_10_ = !lean_is_exclusive(v_w_1_);
if (v_isSharedCheck_10_ == 0)
{
lean_object* v_unused_11_; 
v_unused_11_ = lean_ctor_get(v_w_1_, 1);
lean_dec(v_unused_11_);
v___x_5_ = v_w_1_;
v_isShared_6_ = v_isSharedCheck_10_;
goto v_resetjp_4_;
}
else
{
lean_inc(v_finished_3_);
lean_dec(v_w_1_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_10_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
lean_object* v___x_8_; 
if (v_isShared_6_ == 0)
{
lean_ctor_set(v___x_5_, 1, v_p_2_);
v___x_8_ = v___x_5_;
goto v_reusejp_7_;
}
else
{
lean_object* v_reuseFailAlloc_9_; 
v_reuseFailAlloc_9_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_9_, 0, v_finished_3_);
lean_ctor_set(v_reuseFailAlloc_9_, 1, v_p_2_);
v___x_8_ = v_reuseFailAlloc_9_;
goto v_reusejp_7_;
}
v_reusejp_7_:
{
return v___x_8_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_withPromise(lean_object* v_00_u03b1_12_, lean_object* v_00_u03b2_13_, lean_object* v_w_14_, lean_object* v_p_15_){
_start:
{
lean_object* v_finished_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_23_; 
v_finished_16_ = lean_ctor_get(v_w_14_, 0);
v_isSharedCheck_23_ = !lean_is_exclusive(v_w_14_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; 
v_unused_24_ = lean_ctor_get(v_w_14_, 1);
lean_dec(v_unused_24_);
v___x_18_ = v_w_14_;
v_isShared_19_ = v_isSharedCheck_23_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_finished_16_);
lean_dec(v_w_14_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_23_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v___x_21_; 
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 1, v_p_15_);
v___x_21_ = v___x_18_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_finished_16_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_p_15_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
return v___x_21_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___redArg___lam__0(uint8_t v_s_25_){
_start:
{
uint8_t v___y_27_; 
if (v_s_25_ == 0)
{
uint8_t v___x_32_; 
v___x_32_ = 1;
v___y_27_ = v___x_32_;
goto v___jp_26_;
}
else
{
uint8_t v___x_33_; 
v___x_33_ = 0;
v___y_27_ = v___x_33_;
goto v___jp_26_;
}
v___jp_26_:
{
uint8_t v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_28_ = 1;
v___x_29_ = lean_box(v___y_27_);
v___x_30_ = lean_box(v___x_28_);
v___x_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_31_, 0, v___x_29_);
lean_ctor_set(v___x_31_, 1, v___x_30_);
return v___x_31_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___redArg___lam__0___boxed(lean_object* v_s_34_){
_start:
{
uint8_t v_s_boxed_35_; lean_object* v_res_36_; 
v_s_boxed_35_ = lean_unbox(v_s_34_);
v_res_36_ = l_Std_Internal_IO_Async_Waiter_race___redArg___lam__0(v_s_boxed_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___redArg___lam__1(lean_object* v_lose_37_, lean_object* v_win_38_, lean_object* v_promise_39_, uint8_t v_first_40_){
_start:
{
if (v_first_40_ == 0)
{
lean_dec(v_promise_39_);
lean_dec(v_win_38_);
lean_inc(v_lose_37_);
return v_lose_37_;
}
else
{
lean_object* v___x_41_; 
v___x_41_ = lean_apply_1(v_win_38_, v_promise_39_);
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___redArg___lam__1___boxed(lean_object* v_lose_42_, lean_object* v_win_43_, lean_object* v_promise_44_, lean_object* v_first_45_){
_start:
{
uint8_t v_first_boxed_46_; lean_object* v_res_47_; 
v_first_boxed_46_ = lean_unbox(v_first_45_);
v_res_47_ = l_Std_Internal_IO_Async_Waiter_race___redArg___lam__1(v_lose_42_, v_win_43_, v_promise_44_, v_first_boxed_46_);
lean_dec(v_lose_42_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___redArg(lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_w_51_, lean_object* v_lose_52_, lean_object* v_win_53_){
_start:
{
lean_object* v_toBind_54_; lean_object* v_finished_55_; lean_object* v_promise_56_; lean_object* v___f_57_; lean_object* v___f_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v_toBind_54_ = lean_ctor_get(v_inst_49_, 1);
lean_inc(v_toBind_54_);
lean_dec_ref(v_inst_49_);
v_finished_55_ = lean_ctor_get(v_w_51_, 0);
lean_inc(v_finished_55_);
v_promise_56_ = lean_ctor_get(v_w_51_, 1);
lean_inc(v_promise_56_);
lean_dec_ref(v_w_51_);
v___f_57_ = ((lean_object*)(l_Std_Internal_IO_Async_Waiter_race___redArg___closed__0));
v___f_58_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Waiter_race___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_58_, 0, v_lose_52_);
lean_closure_set(v___f_58_, 1, v_win_53_);
lean_closure_set(v___f_58_, 2, v_promise_56_);
v___x_59_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_59_, 0, lean_box(0));
lean_closure_set(v___x_59_, 1, lean_box(0));
lean_closure_set(v___x_59_, 2, lean_box(0));
lean_closure_set(v___x_59_, 3, v_finished_55_);
lean_closure_set(v___x_59_, 4, v___f_57_);
v___x_60_ = lean_apply_2(v_inst_50_, lean_box(0), v___x_59_);
v___x_61_ = lean_apply_4(v_toBind_54_, lean_box(0), lean_box(0), v___x_60_, v___f_58_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race(lean_object* v_m_62_, lean_object* v_00_u03b1_63_, lean_object* v_00_u03b2_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_w_67_, lean_object* v_lose_68_, lean_object* v_win_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Std_Internal_IO_Async_Waiter_race___redArg(v_inst_65_, v_inst_66_, v_w_67_, v_lose_68_, v_win_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_checkFinished___redArg(lean_object* v_inst_71_, lean_object* v_w_72_){
_start:
{
lean_object* v_finished_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v_finished_73_ = lean_ctor_get(v_w_72_, 0);
lean_inc(v_finished_73_);
lean_dec_ref(v_w_72_);
v___x_74_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_74_, 0, lean_box(0));
lean_closure_set(v___x_74_, 1, lean_box(0));
lean_closure_set(v___x_74_, 2, v_finished_73_);
v___x_75_ = lean_apply_2(v_inst_71_, lean_box(0), v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_checkFinished(lean_object* v_m_76_, lean_object* v_00_u03b1_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_w_80_){
_start:
{
lean_object* v_finished_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v_finished_81_ = lean_ctor_get(v_w_80_, 0);
lean_inc(v_finished_81_);
lean_dec_ref(v_w_80_);
v___x_82_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_82_, 0, lean_box(0));
lean_closure_set(v___x_82_, 1, lean_box(0));
lean_closure_set(v___x_82_, 2, v_finished_81_);
v___x_83_ = lean_apply_2(v_inst_79_, lean_box(0), v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_checkFinished___boxed(lean_object* v_m_84_, lean_object* v_00_u03b1_85_, lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_w_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Std_Internal_IO_Async_Waiter_checkFinished(v_m_84_, v_00_u03b1_85_, v_inst_86_, v_inst_87_, v_w_88_);
lean_dec_ref(v_inst_86_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0_spec__0(lean_object* v_genLo_90_, lean_object* v_genMag_91_, lean_object* v_x_92_, lean_object* v_x_93_){
_start:
{
lean_object* v_zero_94_; uint8_t v_isZero_95_; 
v_zero_94_ = lean_unsigned_to_nat(0u);
v_isZero_95_ = lean_nat_dec_eq(v_x_92_, v_zero_94_);
if (v_isZero_95_ == 1)
{
lean_dec(v_x_92_);
return v_x_93_;
}
else
{
lean_object* v_fst_96_; lean_object* v_snd_97_; lean_object* v___x_98_; lean_object* v_fst_99_; lean_object* v_snd_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_114_; 
v_fst_96_ = lean_ctor_get(v_x_93_, 0);
lean_inc(v_fst_96_);
v_snd_97_ = lean_ctor_get(v_x_93_, 1);
lean_inc(v_snd_97_);
lean_dec_ref(v_x_93_);
v___x_98_ = l_stdNext(v_snd_97_);
v_fst_99_ = lean_ctor_get(v___x_98_, 0);
v_snd_100_ = lean_ctor_get(v___x_98_, 1);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_114_ == 0)
{
v___x_102_ = v___x_98_;
v_isShared_103_ = v_isSharedCheck_114_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_snd_100_);
lean_inc(v_fst_99_);
lean_dec(v___x_98_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_114_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v_v_x27_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_111_; 
v___x_104_ = lean_nat_mul(v_fst_96_, v_genMag_91_);
lean_dec(v_fst_96_);
v___x_105_ = lean_nat_sub(v_fst_99_, v_genLo_90_);
lean_dec(v_fst_99_);
v_v_x27_106_ = lean_nat_add(v___x_104_, v___x_105_);
lean_dec(v___x_105_);
lean_dec(v___x_104_);
v___x_107_ = lean_nat_div(v_x_92_, v_genMag_91_);
lean_dec(v_x_92_);
v___x_108_ = lean_unsigned_to_nat(1u);
v___x_109_ = lean_nat_sub(v___x_107_, v___x_108_);
lean_dec(v___x_107_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 0, v_v_x27_106_);
v___x_111_ = v___x_102_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_v_x27_106_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_snd_100_);
v___x_111_ = v_reuseFailAlloc_113_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
v_x_92_ = v___x_109_;
v_x_93_ = v___x_111_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0_spec__0___boxed(lean_object* v_genLo_115_, lean_object* v_genMag_116_, lean_object* v_x_117_, lean_object* v_x_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0_spec__0(v_genLo_115_, v_genMag_116_, v_x_117_, v_x_118_);
lean_dec(v_genMag_116_);
lean_dec(v_genLo_115_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0(lean_object* v_g_120_, lean_object* v_lo_121_, lean_object* v_hi_122_){
_start:
{
lean_object* v___y_124_; lean_object* v___y_125_; uint8_t v___x_156_; lean_object* v___y_158_; 
v___x_156_ = lean_nat_dec_lt(v_hi_122_, v_lo_121_);
if (v___x_156_ == 0)
{
v___y_158_ = v_lo_121_;
goto v___jp_157_;
}
else
{
v___y_158_ = v_hi_122_;
goto v___jp_157_;
}
v___jp_123_:
{
lean_object* v___x_126_; lean_object* v_fst_127_; lean_object* v_snd_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_155_; 
v___x_126_ = l_stdRange;
v_fst_127_ = lean_ctor_get(v___x_126_, 0);
v_snd_128_ = lean_ctor_get(v___x_126_, 1);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_155_ == 0)
{
v___x_130_ = v___x_126_;
v_isShared_131_ = v_isSharedCheck_155_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_snd_128_);
lean_inc(v_fst_127_);
lean_dec(v___x_126_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_155_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v_genMag_134_; lean_object* v_q_135_; lean_object* v___x_136_; lean_object* v_k_137_; lean_object* v_tgtMag_138_; lean_object* v___x_139_; lean_object* v___x_141_; 
v___x_132_ = lean_nat_sub(v_snd_128_, v_fst_127_);
lean_dec(v_snd_128_);
v___x_133_ = lean_unsigned_to_nat(1u);
v_genMag_134_ = lean_nat_add(v___x_132_, v___x_133_);
lean_dec(v___x_132_);
v_q_135_ = lean_unsigned_to_nat(1000u);
v___x_136_ = lean_nat_sub(v___y_125_, v___y_124_);
v_k_137_ = lean_nat_add(v___x_136_, v___x_133_);
lean_dec(v___x_136_);
v_tgtMag_138_ = lean_nat_mul(v_k_137_, v_q_135_);
v___x_139_ = lean_unsigned_to_nat(0u);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v_g_120_);
lean_ctor_set(v___x_130_, 0, v___x_139_);
v___x_141_ = v___x_130_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_139_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_g_120_);
v___x_141_ = v_reuseFailAlloc_154_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_142_; lean_object* v_fst_143_; lean_object* v_snd_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_153_; 
v___x_142_ = l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0_spec__0(v_fst_127_, v_genMag_134_, v_tgtMag_138_, v___x_141_);
lean_dec(v_genMag_134_);
lean_dec(v_fst_127_);
v_fst_143_ = lean_ctor_get(v___x_142_, 0);
v_snd_144_ = lean_ctor_get(v___x_142_, 1);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_153_ == 0)
{
v___x_146_ = v___x_142_;
v_isShared_147_ = v_isSharedCheck_153_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_snd_144_);
lean_inc(v_fst_143_);
lean_dec(v___x_142_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_153_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v_v_x27_149_; lean_object* v___x_151_; 
v___x_148_ = lean_nat_mod(v_fst_143_, v_k_137_);
lean_dec(v_k_137_);
lean_dec(v_fst_143_);
v_v_x27_149_ = lean_nat_add(v___y_124_, v___x_148_);
lean_dec(v___x_148_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 0, v_v_x27_149_);
v___x_151_ = v___x_146_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_v_x27_149_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_snd_144_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
}
v___jp_157_:
{
if (v___x_156_ == 0)
{
v___y_124_ = v___y_158_;
v___y_125_ = v_hi_122_;
goto v___jp_123_;
}
else
{
v___y_124_ = v___y_158_;
v___y_125_ = v_lo_121_;
goto v___jp_123_;
}
}
}
}
LEAN_EXPORT lean_object* l_randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0___boxed(lean_object* v_g_159_, lean_object* v_lo_160_, lean_object* v_hi_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0(v_g_159_, v_lo_160_, v_hi_161_);
lean_dec(v_hi_161_);
lean_dec(v_lo_160_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go___redArg(lean_object* v_xs_163_, lean_object* v_gen_164_, lean_object* v_i_165_){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_166_ = lean_array_get_size(v_xs_163_);
v___x_167_ = lean_unsigned_to_nat(1u);
v___x_168_ = lean_nat_sub(v___x_166_, v___x_167_);
v___x_169_ = lean_nat_dec_lt(v_i_165_, v___x_168_);
if (v___x_169_ == 0)
{
lean_dec(v___x_168_);
lean_dec(v_i_165_);
lean_dec_ref(v_gen_164_);
return v_xs_163_;
}
else
{
lean_object* v___x_170_; lean_object* v_fst_171_; lean_object* v_snd_172_; lean_object* v_xs_173_; lean_object* v___x_174_; 
v___x_170_ = l_randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0(v_gen_164_, v_i_165_, v___x_168_);
lean_dec(v___x_168_);
v_fst_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_fst_171_);
v_snd_172_ = lean_ctor_get(v___x_170_, 1);
lean_inc(v_snd_172_);
lean_dec_ref(v___x_170_);
v_xs_173_ = lean_array_swap(v_xs_163_, v_i_165_, v_fst_171_);
lean_dec(v_fst_171_);
v___x_174_ = lean_nat_add(v_i_165_, v___x_167_);
lean_dec(v_i_165_);
v_xs_163_ = v_xs_173_;
v_gen_164_ = v_snd_172_;
v_i_165_ = v___x_174_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go(lean_object* v_00_u03b1_176_, lean_object* v_xs_177_, lean_object* v_gen_178_, lean_object* v_i_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go___redArg(v_xs_177_, v_gen_178_, v_i_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_match__1_splitter___redArg(lean_object* v_x_181_, lean_object* v_h__1_182_){
_start:
{
lean_object* v_fst_183_; lean_object* v_snd_184_; lean_object* v___x_185_; 
v_fst_183_ = lean_ctor_get(v_x_181_, 0);
lean_inc(v_fst_183_);
v_snd_184_ = lean_ctor_get(v_x_181_, 1);
lean_inc(v_snd_184_);
lean_dec_ref(v_x_181_);
v___x_185_ = lean_apply_2(v_h__1_182_, v_fst_183_, v_snd_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_match__1_splitter(lean_object* v_motive_186_, lean_object* v_x_187_, lean_object* v_h__1_188_){
_start:
{
lean_object* v_fst_189_; lean_object* v_snd_190_; lean_object* v___x_191_; 
v_fst_189_ = lean_ctor_get(v_x_187_, 0);
lean_inc(v_fst_189_);
v_snd_190_ = lean_ctor_get(v_x_187_, 1);
lean_inc(v_snd_190_);
lean_dec_ref(v_x_187_);
v___x_191_ = lean_apply_2(v_h__1_188_, v_fst_189_, v_snd_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt___redArg(lean_object* v_xs_192_, lean_object* v_gen_193_){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go___redArg(v_xs_192_, v_gen_193_, v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt(lean_object* v_00_u03b1_196_, lean_object* v_xs_197_, lean_object* v_gen_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt___redArg(v_xs_197_, v_gen_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg(lean_object* v_e_200_){
_start:
{
if (lean_obj_tag(v_e_200_) == 0)
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_211_; 
v_a_202_ = lean_ctor_get(v_e_200_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v_e_200_);
if (v_isSharedCheck_211_ == 0)
{
v___x_204_ = v_e_200_;
v_isShared_205_ = v_isSharedCheck_211_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v_e_200_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_211_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_206_ = lean_io_error_to_string(v_a_202_);
v___x_207_ = lean_mk_io_user_error(v___x_206_);
if (v_isShared_205_ == 0)
{
lean_ctor_set_tag(v___x_204_, 1);
lean_ctor_set(v___x_204_, 0, v___x_207_);
v___x_209_ = v___x_204_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
else
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_219_; 
v_a_212_ = lean_ctor_get(v_e_200_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v_e_200_);
if (v_isSharedCheck_219_ == 0)
{
v___x_214_ = v_e_200_;
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v_e_200_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
lean_ctor_set_tag(v___x_214_, 0);
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_a_212_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg___boxed(lean_object* v_e_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg(v_e_220_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1(lean_object* v_00_u03b1_223_, lean_object* v_e_224_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg(v_e_224_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___boxed(lean_object* v_00_u03b1_227_, lean_object* v_e_228_, lean_object* v_a_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1(v_00_u03b1_227_, v_e_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__0(lean_object* v___x_231_, lean_object* v_x_232_){
_start:
{
if (lean_obj_tag(v_x_232_) == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_mk_io_user_error(v___x_231_);
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
return v___x_234_;
}
else
{
lean_object* v_val_235_; 
lean_dec_ref(v___x_231_);
v_val_235_ = lean_ctor_get(v_x_232_, 0);
lean_inc(v_val_235_);
return v_val_235_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__0___boxed(lean_object* v___x_236_, lean_object* v_x_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__0(v___x_236_, v_x_237_);
lean_dec(v_x_237_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__1(lean_object* v___f_239_, uint8_t v___x_240_, lean_object* v_x_241_){
_start:
{
if (lean_obj_tag(v_x_241_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_251_; 
lean_dec_ref(v___f_239_);
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
lean_object* v_a_252_; 
v_a_252_ = lean_ctor_get(v_x_241_, 0);
lean_inc(v_a_252_);
lean_dec_ref(v_x_241_);
if (lean_obj_tag(v_a_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_261_; 
lean_dec_ref(v___f_239_);
v_a_253_ = lean_ctor_get(v_a_252_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v_a_252_);
if (v_isSharedCheck_261_ == 0)
{
v___x_255_ = v_a_252_;
v_isShared_256_ = v_isSharedCheck_261_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v_a_252_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_261_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_253_);
v___x_258_ = v_reuseFailAlloc_260_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_259_; 
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
return v___x_259_;
}
}
}
else
{
lean_object* v_a_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v_a_262_ = lean_ctor_get(v_a_252_, 0);
lean_inc(v_a_262_);
lean_dec_ref(v_a_252_);
v___x_263_ = lean_io_promise_result_opt(v_a_262_);
lean_dec(v_a_262_);
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_265_ = lean_task_map(v___f_239_, v___x_263_, v___x_264_, v___x_240_);
v___x_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
return v___x_266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__1___boxed(lean_object* v___f_267_, lean_object* v___x_268_, lean_object* v_x_269_, lean_object* v___y_270_){
_start:
{
uint8_t v___x_7540__boxed_271_; lean_object* v_res_272_; 
v___x_7540__boxed_271_ = lean_unbox(v___x_268_);
v_res_272_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__1(v___f_267_, v___x_7540__boxed_271_, v_x_269_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2(uint8_t v___x_276_, lean_object* v_x_277_, lean_object* v_x_278_){
_start:
{
if (lean_obj_tag(v_x_278_) == 0)
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_288_; 
lean_dec_ref(v_x_277_);
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
lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_301_; 
v_isSharedCheck_301_ = !lean_is_exclusive(v_x_278_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; 
v_unused_302_ = lean_ctor_get(v_x_278_, 0);
lean_dec(v_unused_302_);
v___x_290_ = v_x_278_;
v_isShared_291_ = v_isSharedCheck_301_;
goto v_resetjp_289_;
}
else
{
lean_dec(v_x_278_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_301_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___f_292_; lean_object* v___x_293_; lean_object* v___f_294_; lean_object* v___x_296_; 
v___f_292_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___closed__1));
v___x_293_ = lean_box(v___x_276_);
v___f_294_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_294_, 0, v___f_292_);
lean_closure_set(v___f_294_, 1, v___x_293_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v_x_277_);
v___x_296_ = v___x_290_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_x_277_);
v___x_296_ = v_reuseFailAlloc_300_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_298_, v___x_276_, v___x_297_, v___f_294_);
return v___x_299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___boxed(lean_object* v___x_303_, lean_object* v_x_304_, lean_object* v_x_305_, lean_object* v___y_306_){
_start:
{
uint8_t v___x_7605__boxed_307_; lean_object* v_res_308_; 
v___x_7605__boxed_307_ = lean_unbox(v___x_303_);
v_res_308_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2(v___x_7605__boxed_307_, v_x_304_, v_x_305_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__4(lean_object* v___x_309_, uint8_t v___x_310_, lean_object* v___f_311_, lean_object* v___f_312_, lean_object* v_a_313_){
_start:
{
lean_object* v_val_316_; 
if (lean_obj_tag(v_a_313_) == 0)
{
lean_object* v___x_324_; lean_object* v___x_325_; 
lean_dec_ref(v___f_312_);
lean_dec_ref(v___f_311_);
v___x_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_309_);
v___x_325_ = lean_task_pure(v___x_324_);
return v___x_325_;
}
else
{
lean_object* v_val_326_; lean_object* v___x_327_; 
v_val_326_ = lean_ctor_get(v_a_313_, 0);
lean_inc(v_val_326_);
lean_dec_ref(v_a_313_);
v___x_327_ = l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg(v_val_326_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
v_a_328_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_327_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_327_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
lean_ctor_set_tag(v___x_330_, 1);
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
v_val_316_ = v___x_333_;
goto v___jp_315_;
}
}
}
else
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
v_a_336_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_327_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_327_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
lean_ctor_set_tag(v___x_338_, 0);
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
v_val_316_ = v___x_341_;
goto v___jp_315_;
}
}
}
}
v___jp_315_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v_val_316_);
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_318_, v___x_310_, v___x_317_, v___f_311_);
v___x_320_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_318_, v___x_310_, v___x_319_, v___f_312_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_322_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_a_321_);
lean_dec_ref(v___x_320_);
v___x_322_ = lean_task_pure(v_a_321_);
return v___x_322_;
}
else
{
lean_object* v_a_323_; 
v_a_323_ = lean_ctor_get(v___x_320_, 0);
lean_inc_ref(v_a_323_);
lean_dec_ref(v___x_320_);
return v_a_323_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__4___boxed(lean_object* v___x_344_, lean_object* v___x_345_, lean_object* v___f_346_, lean_object* v___f_347_, lean_object* v_a_348_, lean_object* v___y_349_){
_start:
{
uint8_t v___x_7668__boxed_350_; lean_object* v_res_351_; 
v___x_7668__boxed_350_ = lean_unbox(v___x_345_);
v_res_351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__4(v___x_344_, v___x_7668__boxed_350_, v___f_346_, v___f_347_, v_a_348_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__0(lean_object* v_a_352_, lean_object* v_x_353_){
_start:
{
if (lean_obj_tag(v_x_353_) == 0)
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_365_; 
v_a_355_ = lean_ctor_get(v_x_353_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v_x_353_);
if (v_isSharedCheck_365_ == 0)
{
v___x_357_ = v_x_353_;
v_isShared_358_ = v_isSharedCheck_365_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v_x_353_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_365_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_355_);
v___x_360_ = v_reuseFailAlloc_364_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_361_ = lean_io_promise_resolve(v___x_360_, v_a_352_);
v___x_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
return v___x_363_;
}
}
}
else
{
lean_object* v___x_366_; 
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v_x_353_);
return v___x_366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__0___boxed(lean_object* v_a_367_, lean_object* v_x_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__0(v_a_367_, v_x_368_);
lean_dec(v_a_367_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__0(lean_object* v___x_371_, lean_object* v_x_372_){
_start:
{
if (lean_obj_tag(v_x_372_) == 0)
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_382_; 
v_a_374_ = lean_ctor_get(v_x_372_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v_x_372_);
if (v_isSharedCheck_382_ == 0)
{
v___x_376_ = v_x_372_;
v_isShared_377_ = v_isSharedCheck_382_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v_x_372_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_382_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_381_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_380_; 
v___x_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
return v___x_380_;
}
}
}
else
{
lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_391_; 
v_isSharedCheck_391_ = !lean_is_exclusive(v_x_372_);
if (v_isSharedCheck_391_ == 0)
{
lean_object* v_unused_392_; 
v_unused_392_ = lean_ctor_get(v_x_372_, 0);
lean_dec(v_unused_392_);
v___x_384_ = v_x_372_;
v_isShared_385_ = v_isSharedCheck_391_;
goto v_resetjp_383_;
}
else
{
lean_dec(v_x_372_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_391_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_371_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_386_);
v___x_388_ = v___x_384_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_390_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_object* v___x_389_; 
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
return v___x_389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__0___boxed(lean_object* v___x_393_, lean_object* v_x_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__0(v___x_393_, v_x_394_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__3(lean_object* v_a_397_, lean_object* v_a_398_, uint8_t v___x_399_, lean_object* v___f_400_, lean_object* v_x_401_){
_start:
{
if (lean_obj_tag(v_x_401_) == 0)
{
lean_object* v___x_403_; 
lean_dec_ref(v___f_400_);
lean_dec(v_a_398_);
lean_dec_ref(v_a_397_);
v___x_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_403_, 0, v_x_401_);
return v___x_403_;
}
else
{
lean_object* v_cont_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
lean_dec_ref(v_x_401_);
v_cont_404_ = lean_ctor_get(v_a_397_, 1);
lean_inc_ref(v_cont_404_);
lean_dec_ref(v_a_397_);
v___x_405_ = lean_apply_2(v_cont_404_, v_a_398_, lean_box(0));
v___x_406_ = lean_unsigned_to_nat(0u);
v___x_407_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_406_, v___x_399_, v___x_405_, v___f_400_);
return v___x_407_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__3___boxed(lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v___x_410_, lean_object* v___f_411_, lean_object* v_x_412_, lean_object* v___y_413_){
_start:
{
uint8_t v___x_7823__boxed_414_; lean_object* v_res_415_; 
v___x_7823__boxed_414_ = lean_unbox(v___x_410_);
v_res_415_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__3(v_a_408_, v_a_409_, v___x_7823__boxed_414_, v___f_411_, v_x_412_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__1___boxed(lean_object* v_i_418_, lean_object* v_as_419_, lean_object* v_sz_420_, lean_object* v_x_421_, lean_object* v___y_422_){
_start:
{
size_t v_i_boxed_423_; size_t v_sz_boxed_424_; lean_object* v_res_425_; 
v_i_boxed_423_ = lean_unbox_usize(v_i_418_);
lean_dec(v_i_418_);
v_sz_boxed_424_ = lean_unbox_usize(v_sz_420_);
lean_dec(v_sz_420_);
v_res_425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__1(v_i_boxed_423_, v_as_419_, v_sz_boxed_424_, v_x_421_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg(lean_object* v_as_426_, size_t v_sz_427_, size_t v_i_428_, lean_object* v_b_429_){
_start:
{
uint8_t v___x_431_; 
v___x_431_ = lean_usize_dec_lt(v_i_428_, v_sz_427_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; lean_object* v___x_433_; 
lean_dec_ref(v_as_426_);
v___x_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_432_, 0, v_b_429_);
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
return v___x_433_;
}
else
{
lean_object* v_a_434_; lean_object* v_selector_435_; lean_object* v_unregisterFn_436_; lean_object* v___x_437_; lean_object* v___f_438_; lean_object* v___x_439_; uint8_t v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___f_444_; lean_object* v___x_445_; 
v_a_434_ = lean_array_uget_borrowed(v_as_426_, v_i_428_);
v_selector_435_ = lean_ctor_get(v_a_434_, 0);
v_unregisterFn_436_ = lean_ctor_get(v_selector_435_, 2);
lean_inc_ref(v_unregisterFn_436_);
v___x_437_ = lean_apply_1(v_unregisterFn_436_, lean_box(0));
v___f_438_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___closed__0));
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = 0;
v___x_441_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_439_, v___x_440_, v___x_437_, v___f_438_);
v___x_442_ = lean_box_usize(v_i_428_);
v___x_443_ = lean_box_usize(v_sz_427_);
v___f_444_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_444_, 0, v___x_442_);
lean_closure_set(v___f_444_, 1, v_as_426_);
lean_closure_set(v___f_444_, 2, v___x_443_);
v___x_445_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_439_, v___x_440_, v___x_441_, v___f_444_);
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__1(size_t v_i_446_, lean_object* v_as_447_, size_t v_sz_448_, lean_object* v_x_449_){
_start:
{
if (lean_obj_tag(v_x_449_) == 0)
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_459_; 
lean_dec_ref(v_as_447_);
v_a_451_ = lean_ctor_get(v_x_449_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v_x_449_);
if (v_isSharedCheck_459_ == 0)
{
v___x_453_ = v_x_449_;
v_isShared_454_ = v_isSharedCheck_459_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v_x_449_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_459_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_458_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_457_; 
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
}
}
else
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_479_; 
v_a_460_ = lean_ctor_get(v_x_449_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v_x_449_);
if (v_isSharedCheck_479_ == 0)
{
v___x_462_ = v_x_449_;
v_isShared_463_ = v_isSharedCheck_479_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v_x_449_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_479_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
if (lean_obj_tag(v_a_460_) == 0)
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_474_; 
lean_dec_ref(v_as_447_);
v_a_464_ = lean_ctor_get(v_a_460_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v_a_460_);
if (v_isSharedCheck_474_ == 0)
{
v___x_466_ = v_a_460_;
v_isShared_467_ = v_isSharedCheck_474_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v_a_460_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_474_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v_a_464_);
v___x_469_ = v___x_462_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_473_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_471_; 
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v___x_469_);
v___x_471_ = v___x_466_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_469_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
else
{
lean_object* v_a_475_; size_t v___x_476_; size_t v___x_477_; lean_object* v___x_478_; 
lean_del_object(v___x_462_);
v_a_475_ = lean_ctor_get(v_a_460_, 0);
lean_inc(v_a_475_);
lean_dec_ref(v_a_460_);
v___x_476_ = ((size_t)1ULL);
v___x_477_ = lean_usize_add(v_i_446_, v___x_476_);
v___x_478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg(v_as_447_, v_sz_448_, v___x_477_, v_a_475_);
return v___x_478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___boxed(lean_object* v_as_480_, lean_object* v_sz_481_, lean_object* v_i_482_, lean_object* v_b_483_, lean_object* v___y_484_){
_start:
{
size_t v_sz_boxed_485_; size_t v_i_boxed_486_; lean_object* v_res_487_; 
v_sz_boxed_485_ = lean_unbox_usize(v_sz_481_);
lean_dec(v_sz_481_);
v_i_boxed_486_ = lean_unbox_usize(v_i_482_);
lean_dec(v_i_482_);
v_res_487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg(v_as_480_, v_sz_boxed_485_, v_i_boxed_486_, v_b_483_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__2(lean_object* v___x_488_, lean_object* v___x_489_, lean_object* v_a_490_, uint8_t v___x_491_, lean_object* v___f_492_, lean_object* v_x_493_){
_start:
{
if (lean_obj_tag(v_x_493_) == 0)
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_503_; 
lean_dec_ref(v___f_492_);
lean_dec_ref(v_a_490_);
lean_dec_ref(v___x_488_);
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
lean_object* v_a_504_; size_t v_sz_505_; size_t v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___f_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v_a_504_ = lean_ctor_get(v_x_493_, 0);
lean_inc(v_a_504_);
lean_dec_ref(v_x_493_);
v_sz_505_ = lean_array_size(v___x_488_);
v___x_506_ = ((size_t)0ULL);
v___x_507_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg(v___x_488_, v_sz_505_, v___x_506_, v___x_489_);
v___x_508_ = lean_box(v___x_491_);
v___f_509_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_509_, 0, v_a_490_);
lean_closure_set(v___f_509_, 1, v_a_504_);
lean_closure_set(v___f_509_, 2, v___x_508_);
lean_closure_set(v___f_509_, 3, v___f_492_);
v___x_510_ = lean_unsigned_to_nat(0u);
v___x_511_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_510_, v___x_491_, v___x_507_, v___f_509_);
return v___x_511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__2___boxed(lean_object* v___x_512_, lean_object* v___x_513_, lean_object* v_a_514_, lean_object* v___x_515_, lean_object* v___f_516_, lean_object* v_x_517_, lean_object* v___y_518_){
_start:
{
uint8_t v___x_7945__boxed_519_; lean_object* v_res_520_; 
v___x_7945__boxed_519_ = lean_unbox(v___x_515_);
v_res_520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__2(v___x_512_, v___x_513_, v_a_514_, v___x_7945__boxed_519_, v___f_516_, v_x_517_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__1(lean_object* v_a_521_, lean_object* v_x_522_){
_start:
{
if (lean_obj_tag(v_x_522_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_532_; 
v_a_524_ = lean_ctor_get(v_x_522_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v_x_522_);
if (v_isSharedCheck_532_ == 0)
{
v___x_526_ = v_x_522_;
v_isShared_527_ = v_isSharedCheck_532_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v_x_522_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_532_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_531_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
lean_object* v___x_530_; 
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
}
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_533_ = lean_io_promise_resolve(v_x_522_, v_a_521_);
v___x_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
v___x_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__1___boxed(lean_object* v_a_536_, lean_object* v_x_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__1(v_a_536_, v_x_537_);
lean_dec(v_a_536_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__5(lean_object* v_a_540_, lean_object* v___f_541_, uint8_t v___x_542_, lean_object* v___x_543_, lean_object* v___f_544_, lean_object* v_x_545_){
_start:
{
if (lean_obj_tag(v_x_545_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_555_; 
lean_dec_ref(v___f_544_);
lean_dec_ref(v___f_541_);
v_a_547_ = lean_ctor_get(v_x_545_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v_x_545_);
if (v_isSharedCheck_555_ == 0)
{
v___x_549_ = v_x_545_;
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v_x_545_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_554_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_553_; 
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
return v___x_553_;
}
}
}
else
{
lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_567_; 
v_isSharedCheck_567_ = !lean_is_exclusive(v_x_545_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; 
v_unused_568_ = lean_ctor_get(v_x_545_, 0);
lean_dec(v_unused_568_);
v___x_557_ = v_x_545_;
v_isShared_558_ = v_isSharedCheck_567_;
goto v_resetjp_556_;
}
else
{
lean_dec(v_x_545_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_567_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_559_ = lean_io_promise_result_opt(v_a_540_);
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = lean_io_bind_task(v___x_559_, v___f_541_, v___x_560_, v___x_542_);
lean_dec_ref(v___x_561_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_543_);
v___x_563_ = v___x_557_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_543_);
v___x_563_ = v_reuseFailAlloc_566_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
v___x_565_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_560_, v___x_542_, v___x_564_, v___f_544_);
return v___x_565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__5___boxed(lean_object* v_a_569_, lean_object* v___f_570_, lean_object* v___x_571_, lean_object* v___x_572_, lean_object* v___f_573_, lean_object* v_x_574_, lean_object* v___y_575_){
_start:
{
uint8_t v___x_8029__boxed_576_; lean_object* v_res_577_; 
v___x_8029__boxed_576_ = lean_unbox(v___x_571_);
v_res_577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__5(v_a_569_, v___f_570_, v___x_8029__boxed_576_, v___x_572_, v___f_573_, v_x_574_);
lean_dec(v_a_569_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__6(lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v___f_580_, uint8_t v___x_581_, lean_object* v___x_582_, lean_object* v___f_583_, lean_object* v_x_584_){
_start:
{
if (lean_obj_tag(v_x_584_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_594_; 
lean_dec_ref(v___f_583_);
lean_dec_ref(v___f_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
v_a_586_ = lean_ctor_get(v_x_584_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v_x_584_);
if (v_isSharedCheck_594_ == 0)
{
v___x_588_ = v_x_584_;
v_isShared_589_ = v_isSharedCheck_594_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v_x_584_);
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
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
return v___x_592_;
}
}
}
else
{
lean_object* v_selector_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_609_; 
v_selector_595_ = lean_ctor_get(v_a_578_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v_a_578_);
if (v_isSharedCheck_609_ == 0)
{
lean_object* v_unused_610_; 
v_unused_610_ = lean_ctor_get(v_a_578_, 1);
lean_dec(v_unused_610_);
v___x_597_ = v_a_578_;
v_isShared_598_ = v_isSharedCheck_609_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_selector_595_);
lean_dec(v_a_578_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_609_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v_a_599_; lean_object* v_registerFn_600_; lean_object* v___x_602_; 
v_a_599_ = lean_ctor_get(v_x_584_, 0);
lean_inc(v_a_599_);
lean_dec_ref(v_x_584_);
v_registerFn_600_ = lean_ctor_get(v_selector_595_, 1);
lean_inc_ref(v_registerFn_600_);
lean_dec_ref(v_selector_595_);
lean_inc(v_a_599_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 1, v_a_599_);
lean_ctor_set(v___x_597_, 0, v_a_579_);
v___x_602_ = v___x_597_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_579_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_a_599_);
v___x_602_ = v_reuseFailAlloc_608_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___f_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_603_ = lean_apply_2(v_registerFn_600_, v___x_602_, lean_box(0));
v___x_604_ = lean_box(v___x_581_);
v___f_605_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__5___boxed), 7, 5);
lean_closure_set(v___f_605_, 0, v_a_599_);
lean_closure_set(v___f_605_, 1, v___f_580_);
lean_closure_set(v___f_605_, 2, v___x_604_);
lean_closure_set(v___f_605_, 3, v___x_582_);
lean_closure_set(v___f_605_, 4, v___f_583_);
v___x_606_ = lean_unsigned_to_nat(0u);
v___x_607_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_606_, v___x_581_, v___x_603_, v___f_605_);
return v___x_607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__6___boxed(lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v___f_613_, lean_object* v___x_614_, lean_object* v___x_615_, lean_object* v___f_616_, lean_object* v_x_617_, lean_object* v___y_618_){
_start:
{
uint8_t v___x_8095__boxed_619_; lean_object* v_res_620_; 
v___x_8095__boxed_619_ = lean_unbox(v___x_614_);
v_res_620_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__6(v_a_611_, v_a_612_, v___f_613_, v___x_8095__boxed_619_, v___x_615_, v___f_616_, v_x_617_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__7___boxed(lean_object* v_i_621_, lean_object* v_a_622_, lean_object* v___x_623_, lean_object* v_a_624_, lean_object* v_as_625_, lean_object* v_sz_626_, lean_object* v_x_627_, lean_object* v___y_628_){
_start:
{
size_t v_i_boxed_629_; size_t v_sz_boxed_630_; lean_object* v_res_631_; 
v_i_boxed_629_ = lean_unbox_usize(v_i_621_);
lean_dec(v_i_621_);
v_sz_boxed_630_ = lean_unbox_usize(v_sz_626_);
lean_dec(v_sz_626_);
v_res_631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__7(v_i_boxed_629_, v_a_622_, v___x_623_, v_a_624_, v_as_625_, v_sz_boxed_630_, v_x_627_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg(lean_object* v_a_632_, lean_object* v___x_633_, lean_object* v_a_634_, lean_object* v_as_635_, size_t v_sz_636_, size_t v_i_637_, lean_object* v_b_638_){
_start:
{
uint8_t v___x_640_; 
v___x_640_ = lean_usize_dec_lt(v_i_637_, v_sz_636_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; lean_object* v___x_642_; 
lean_dec_ref(v_as_635_);
lean_dec(v_a_634_);
lean_dec_ref(v___x_633_);
lean_dec(v_a_632_);
v___x_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_641_, 0, v_b_638_);
v___x_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
return v___x_642_;
}
else
{
lean_object* v___x_643_; lean_object* v___f_644_; lean_object* v___f_645_; lean_object* v___x_646_; lean_object* v___f_647_; uint8_t v___x_648_; lean_object* v_a_649_; lean_object* v___x_650_; lean_object* v___f_651_; lean_object* v___x_652_; lean_object* v___f_653_; lean_object* v___x_654_; lean_object* v___f_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___f_662_; lean_object* v___x_663_; 
v___x_643_ = lean_io_promise_new();
lean_inc(v_a_632_);
v___f_644_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_644_, 0, v_a_632_);
lean_inc(v_a_632_);
v___f_645_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_645_, 0, v_a_632_);
v___x_646_ = lean_box(0);
v___f_647_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___closed__0));
v___x_648_ = 0;
v_a_649_ = lean_array_uget_borrowed(v_as_635_, v_i_637_);
v___x_650_ = lean_box(v___x_648_);
lean_inc(v_a_649_);
lean_inc_ref(v___x_633_);
v___f_651_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__2___boxed), 7, 5);
lean_closure_set(v___f_651_, 0, v___x_633_);
lean_closure_set(v___f_651_, 1, v___x_646_);
lean_closure_set(v___f_651_, 2, v_a_649_);
lean_closure_set(v___f_651_, 3, v___x_650_);
lean_closure_set(v___f_651_, 4, v___f_645_);
v___x_652_ = lean_box(v___x_648_);
v___f_653_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_653_, 0, v___x_646_);
lean_closure_set(v___f_653_, 1, v___x_652_);
lean_closure_set(v___f_653_, 2, v___f_651_);
lean_closure_set(v___f_653_, 3, v___f_644_);
v___x_654_ = lean_box(v___x_648_);
lean_inc(v_a_634_);
lean_inc(v_a_649_);
v___f_655_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__6___boxed), 8, 6);
lean_closure_set(v___f_655_, 0, v_a_649_);
lean_closure_set(v___f_655_, 1, v_a_634_);
lean_closure_set(v___f_655_, 2, v___f_653_);
lean_closure_set(v___f_655_, 3, v___x_654_);
lean_closure_set(v___f_655_, 4, v___x_646_);
lean_closure_set(v___f_655_, 5, v___f_647_);
v___x_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_643_);
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
v___x_658_ = lean_unsigned_to_nat(0u);
v___x_659_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_658_, v___x_648_, v___x_657_, v___f_655_);
v___x_660_ = lean_box_usize(v_i_637_);
v___x_661_ = lean_box_usize(v_sz_636_);
v___f_662_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__7___boxed), 8, 6);
lean_closure_set(v___f_662_, 0, v___x_660_);
lean_closure_set(v___f_662_, 1, v_a_632_);
lean_closure_set(v___f_662_, 2, v___x_633_);
lean_closure_set(v___f_662_, 3, v_a_634_);
lean_closure_set(v___f_662_, 4, v_as_635_);
lean_closure_set(v___f_662_, 5, v___x_661_);
v___x_663_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_658_, v___x_648_, v___x_659_, v___f_662_);
return v___x_663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__7(size_t v_i_664_, lean_object* v_a_665_, lean_object* v___x_666_, lean_object* v_a_667_, lean_object* v_as_668_, size_t v_sz_669_, lean_object* v_x_670_){
_start:
{
if (lean_obj_tag(v_x_670_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_680_; 
lean_dec_ref(v_as_668_);
lean_dec(v_a_667_);
lean_dec_ref(v___x_666_);
lean_dec(v_a_665_);
v_a_672_ = lean_ctor_get(v_x_670_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v_x_670_);
if (v_isSharedCheck_680_ == 0)
{
v___x_674_ = v_x_670_;
v_isShared_675_ = v_isSharedCheck_680_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v_x_670_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_680_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_679_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_678_; 
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
return v___x_678_;
}
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_700_; 
v_a_681_ = lean_ctor_get(v_x_670_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v_x_670_);
if (v_isSharedCheck_700_ == 0)
{
v___x_683_ = v_x_670_;
v_isShared_684_ = v_isSharedCheck_700_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v_x_670_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_700_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
if (lean_obj_tag(v_a_681_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_695_; 
lean_dec_ref(v_as_668_);
lean_dec(v_a_667_);
lean_dec_ref(v___x_666_);
lean_dec(v_a_665_);
v_a_685_ = lean_ctor_get(v_a_681_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v_a_681_);
if (v_isSharedCheck_695_ == 0)
{
v___x_687_ = v_a_681_;
v_isShared_688_ = v_isSharedCheck_695_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v_a_681_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_695_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_690_; 
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v_a_685_);
v___x_690_ = v___x_683_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_685_);
v___x_690_ = v_reuseFailAlloc_694_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_692_; 
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_690_);
v___x_692_ = v___x_687_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_690_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
else
{
lean_object* v_a_696_; size_t v___x_697_; size_t v___x_698_; lean_object* v___x_699_; 
lean_del_object(v___x_683_);
v_a_696_ = lean_ctor_get(v_a_681_, 0);
lean_inc(v_a_696_);
lean_dec_ref(v_a_681_);
v___x_697_ = ((size_t)1ULL);
v___x_698_ = lean_usize_add(v_i_664_, v___x_697_);
v___x_699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg(v_a_665_, v___x_666_, v_a_667_, v_as_668_, v_sz_669_, v___x_698_, v_a_696_);
return v___x_699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___boxed(lean_object* v_a_701_, lean_object* v___x_702_, lean_object* v_a_703_, lean_object* v_as_704_, lean_object* v_sz_705_, lean_object* v_i_706_, lean_object* v_b_707_, lean_object* v___y_708_){
_start:
{
size_t v_sz_boxed_709_; size_t v_i_boxed_710_; lean_object* v_res_711_; 
v_sz_boxed_709_ = lean_unbox_usize(v_sz_705_);
lean_dec(v_sz_705_);
v_i_boxed_710_ = lean_unbox_usize(v_i_706_);
lean_dec(v_i_706_);
v_res_711_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg(v_a_701_, v___x_702_, v_a_703_, v_as_704_, v_sz_boxed_709_, v_i_boxed_710_, v_b_707_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__3(lean_object* v___x_712_, lean_object* v_a_713_, lean_object* v___x_714_, uint8_t v___x_715_, lean_object* v_x_716_){
_start:
{
if (lean_obj_tag(v_x_716_) == 0)
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_726_; 
lean_dec(v_a_713_);
lean_dec_ref(v___x_712_);
v_a_718_ = lean_ctor_get(v_x_716_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v_x_716_);
if (v_isSharedCheck_726_ == 0)
{
v___x_720_ = v_x_716_;
v_isShared_721_ = v_isSharedCheck_726_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v_x_716_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_726_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_725_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_724_; 
v___x_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
return v___x_724_;
}
}
}
else
{
lean_object* v_a_727_; size_t v_sz_728_; size_t v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___f_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_a_727_ = lean_ctor_get(v_x_716_, 0);
v_sz_728_ = lean_array_size(v___x_712_);
v___x_729_ = ((size_t)0ULL);
lean_inc_ref(v___x_712_);
lean_inc(v_a_727_);
v___x_730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg(v_a_727_, v___x_712_, v_a_713_, v___x_712_, v_sz_728_, v___x_729_, v___x_714_);
v___x_731_ = lean_box(v___x_715_);
v___f_732_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_732_, 0, v___x_731_);
lean_closure_set(v___f_732_, 1, v_x_716_);
v___x_733_ = lean_unsigned_to_nat(0u);
v___x_734_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_733_, v___x_715_, v___x_730_, v___f_732_);
return v___x_734_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__3___boxed(lean_object* v___x_735_, lean_object* v_a_736_, lean_object* v___x_737_, lean_object* v___x_738_, lean_object* v_x_739_, lean_object* v___y_740_){
_start:
{
uint8_t v___x_8296__boxed_741_; lean_object* v_res_742_; 
v___x_8296__boxed_741_ = lean_unbox(v___x_738_);
v_res_742_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__3(v___x_735_, v_a_736_, v___x_737_, v___x_8296__boxed_741_, v_x_739_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__4(lean_object* v___x_743_, lean_object* v___x_744_, uint8_t v___x_745_, lean_object* v_x_746_){
_start:
{
if (lean_obj_tag(v_x_746_) == 0)
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_756_; 
lean_dec_ref(v___x_743_);
v_a_748_ = lean_ctor_get(v_x_746_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v_x_746_);
if (v_isSharedCheck_756_ == 0)
{
v___x_750_ = v_x_746_;
v_isShared_751_ = v_isSharedCheck_756_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v_x_746_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_756_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_755_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_754_; 
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
return v___x_754_;
}
}
}
else
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_770_; 
v_a_757_ = lean_ctor_get(v_x_746_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v_x_746_);
if (v_isSharedCheck_770_ == 0)
{
v___x_759_ = v_x_746_;
v_isShared_760_ = v_isSharedCheck_770_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v_x_746_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_770_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___f_763_; lean_object* v___x_765_; 
v___x_761_ = lean_io_promise_new();
v___x_762_ = lean_box(v___x_745_);
v___f_763_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_763_, 0, v___x_743_);
lean_closure_set(v___f_763_, 1, v_a_757_);
lean_closure_set(v___f_763_, 2, v___x_744_);
lean_closure_set(v___f_763_, 3, v___x_762_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v___x_761_);
v___x_765_ = v___x_759_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_761_);
v___x_765_ = v_reuseFailAlloc_769_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
v___x_767_ = lean_unsigned_to_nat(0u);
v___x_768_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_767_, v___x_745_, v___x_766_, v___f_763_);
return v___x_768_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__4___boxed(lean_object* v___x_771_, lean_object* v___x_772_, lean_object* v___x_773_, lean_object* v_x_774_, lean_object* v___y_775_){
_start:
{
uint8_t v___x_8345__boxed_776_; lean_object* v_res_777_; 
v___x_8345__boxed_776_ = lean_unbox(v___x_773_);
v_res_777_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__4(v___x_771_, v___x_772_, v___x_8345__boxed_776_, v_x_774_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__5(lean_object* v___x_778_, lean_object* v___x_779_, lean_object* v_x_780_){
_start:
{
if (lean_obj_tag(v_x_780_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_790_; 
lean_dec_ref(v___x_778_);
v_a_782_ = lean_ctor_get(v_x_780_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v_x_780_);
if (v_isSharedCheck_790_ == 0)
{
v___x_784_ = v_x_780_;
v_isShared_785_ = v_isSharedCheck_790_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v_x_780_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_790_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_782_);
v___x_787_ = v_reuseFailAlloc_789_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
lean_object* v___x_788_; 
v___x_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
return v___x_788_;
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_818_; 
v_a_791_ = lean_ctor_get(v_x_780_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v_x_780_);
if (v_isSharedCheck_818_ == 0)
{
v___x_793_ = v_x_780_;
v_isShared_794_ = v_isSharedCheck_818_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v_x_780_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_818_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v_fst_795_; 
v_fst_795_ = lean_ctor_get(v_a_791_, 0);
lean_inc(v_fst_795_);
lean_dec(v_a_791_);
if (lean_obj_tag(v_fst_795_) == 0)
{
uint8_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___f_800_; lean_object* v___x_802_; 
v___x_796_ = 0;
v___x_797_ = lean_box(v___x_796_);
v___x_798_ = lean_st_mk_ref(v___x_797_);
v___x_799_ = lean_box(v___x_796_);
v___f_800_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_800_, 0, v___x_778_);
lean_closure_set(v___f_800_, 1, v___x_779_);
lean_closure_set(v___f_800_, 2, v___x_799_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_798_);
v___x_802_ = v___x_793_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_798_);
v___x_802_ = v_reuseFailAlloc_806_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
v___x_804_ = lean_unsigned_to_nat(0u);
v___x_805_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_804_, v___x_796_, v___x_803_, v___f_800_);
return v___x_805_;
}
}
else
{
lean_object* v_val_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_817_; 
lean_dec_ref(v___x_778_);
v_val_807_ = lean_ctor_get(v_fst_795_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v_fst_795_);
if (v_isSharedCheck_817_ == 0)
{
v___x_809_ = v_fst_795_;
v_isShared_810_ = v_isSharedCheck_817_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_val_807_);
lean_dec(v_fst_795_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_817_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v_val_807_);
v___x_812_ = v___x_793_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_val_807_);
v___x_812_ = v_reuseFailAlloc_816_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_814_; 
if (v_isShared_810_ == 0)
{
lean_ctor_set_tag(v___x_809_, 0);
lean_ctor_set(v___x_809_, 0, v___x_812_);
v___x_814_ = v___x_809_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_812_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__5___boxed(lean_object* v___x_819_, lean_object* v___x_820_, lean_object* v_x_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__5(v___x_819_, v___x_820_, v_x_821_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__0(lean_object* v___x_824_, lean_object* v_x_825_){
_start:
{
if (lean_obj_tag(v_x_825_) == 0)
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_835_; 
v_a_827_ = lean_ctor_get(v_x_825_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v_x_825_);
if (v_isSharedCheck_835_ == 0)
{
v___x_829_ = v_x_825_;
v_isShared_830_ = v_isSharedCheck_835_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v_x_825_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_835_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_834_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v___x_833_; 
v___x_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
return v___x_833_;
}
}
}
else
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_847_; 
v_a_836_ = lean_ctor_get(v_x_825_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v_x_825_);
if (v_isSharedCheck_847_ == 0)
{
v___x_838_ = v_x_825_;
v_isShared_839_ = v_isSharedCheck_847_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v_x_825_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_847_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_844_; 
v___x_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_840_, 0, v_a_836_);
v___x_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
lean_ctor_set(v___x_841_, 1, v___x_824_);
v___x_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_842_);
v___x_844_ = v___x_838_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_842_);
v___x_844_ = v_reuseFailAlloc_846_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
lean_object* v___x_845_; 
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
return v___x_845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__0___boxed(lean_object* v___x_848_, lean_object* v_x_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__0(v___x_848_, v_x_849_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__1(lean_object* v_a_852_, lean_object* v___f_853_, lean_object* v___x_854_, lean_object* v_x_855_){
_start:
{
if (lean_obj_tag(v_x_855_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_865_; 
lean_dec_ref(v___x_854_);
lean_dec_ref(v___f_853_);
lean_dec_ref(v_a_852_);
v_a_857_ = lean_ctor_get(v_x_855_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v_x_855_);
if (v_isSharedCheck_865_ == 0)
{
v___x_859_ = v_x_855_;
v_isShared_860_ = v_isSharedCheck_865_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v_x_855_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_865_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_857_);
v___x_862_ = v_reuseFailAlloc_864_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v___x_863_; 
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
return v___x_863_;
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_881_; 
v_a_866_ = lean_ctor_get(v_x_855_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v_x_855_);
if (v_isSharedCheck_881_ == 0)
{
v___x_868_ = v_x_855_;
v_isShared_869_ = v_isSharedCheck_881_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v_x_855_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_881_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
if (lean_obj_tag(v_a_866_) == 1)
{
lean_object* v_val_870_; lean_object* v_cont_871_; lean_object* v___x_872_; lean_object* v___x_873_; uint8_t v___x_874_; lean_object* v___x_875_; 
lean_del_object(v___x_868_);
lean_dec_ref(v___x_854_);
v_val_870_ = lean_ctor_get(v_a_866_, 0);
lean_inc(v_val_870_);
lean_dec_ref(v_a_866_);
v_cont_871_ = lean_ctor_get(v_a_852_, 1);
lean_inc_ref(v_cont_871_);
lean_dec_ref(v_a_852_);
v___x_872_ = lean_apply_2(v_cont_871_, v_val_870_, lean_box(0));
v___x_873_ = lean_unsigned_to_nat(0u);
v___x_874_ = 0;
v___x_875_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_873_, v___x_874_, v___x_872_, v___f_853_);
return v___x_875_;
}
else
{
lean_object* v___x_876_; lean_object* v___x_878_; 
lean_dec(v_a_866_);
lean_dec_ref(v___f_853_);
lean_dec_ref(v_a_852_);
v___x_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_876_, 0, v___x_854_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_876_);
v___x_878_ = v___x_868_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_876_);
v___x_878_ = v_reuseFailAlloc_880_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_879_; 
v___x_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
return v___x_879_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__1___boxed(lean_object* v_a_882_, lean_object* v___f_883_, lean_object* v___x_884_, lean_object* v_x_885_, lean_object* v___y_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__1(v_a_882_, v___f_883_, v___x_884_, v_x_885_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__2___boxed(lean_object* v_i_893_, lean_object* v_as_894_, lean_object* v_sz_895_, lean_object* v_x_896_, lean_object* v___y_897_){
_start:
{
size_t v_i_boxed_898_; size_t v_sz_boxed_899_; lean_object* v_res_900_; 
v_i_boxed_898_ = lean_unbox_usize(v_i_893_);
lean_dec(v_i_893_);
v_sz_boxed_899_ = lean_unbox_usize(v_sz_895_);
lean_dec(v_sz_895_);
v_res_900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__2(v_i_boxed_898_, v_as_894_, v_sz_boxed_899_, v_x_896_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg(lean_object* v_as_901_, size_t v_sz_902_, size_t v_i_903_, lean_object* v_b_904_){
_start:
{
uint8_t v___x_906_; 
v___x_906_ = lean_usize_dec_lt(v_i_903_, v_sz_902_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; lean_object* v___x_908_; 
lean_dec_ref(v_as_901_);
v___x_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_907_, 0, v_b_904_);
v___x_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
return v___x_908_;
}
else
{
lean_object* v_a_909_; lean_object* v_selector_910_; lean_object* v_tryFn_911_; lean_object* v___x_912_; lean_object* v___f_913_; lean_object* v___x_914_; lean_object* v___f_915_; lean_object* v___x_916_; uint8_t v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___f_921_; lean_object* v___x_922_; 
lean_dec_ref(v_b_904_);
v_a_909_ = lean_array_uget_borrowed(v_as_901_, v_i_903_);
v_selector_910_ = lean_ctor_get(v_a_909_, 0);
v_tryFn_911_ = lean_ctor_get(v_selector_910_, 0);
lean_inc_ref(v_tryFn_911_);
v___x_912_ = lean_apply_1(v_tryFn_911_, lean_box(0));
v___f_913_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__0));
v___x_914_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__1));
lean_inc(v_a_909_);
v___f_915_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_915_, 0, v_a_909_);
lean_closure_set(v___f_915_, 1, v___f_913_);
lean_closure_set(v___f_915_, 2, v___x_914_);
v___x_916_ = lean_unsigned_to_nat(0u);
v___x_917_ = 0;
v___x_918_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_916_, v___x_917_, v___x_912_, v___f_915_);
v___x_919_ = lean_box_usize(v_i_903_);
v___x_920_ = lean_box_usize(v_sz_902_);
v___f_921_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_921_, 0, v___x_919_);
lean_closure_set(v___f_921_, 1, v_as_901_);
lean_closure_set(v___f_921_, 2, v___x_920_);
v___x_922_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_916_, v___x_917_, v___x_918_, v___f_921_);
return v___x_922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__2(size_t v_i_923_, lean_object* v_as_924_, size_t v_sz_925_, lean_object* v_x_926_){
_start:
{
if (lean_obj_tag(v_x_926_) == 0)
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_936_; 
lean_dec_ref(v_as_924_);
v_a_928_ = lean_ctor_get(v_x_926_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v_x_926_);
if (v_isSharedCheck_936_ == 0)
{
v___x_930_ = v_x_926_;
v_isShared_931_ = v_isSharedCheck_936_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v_x_926_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_936_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_935_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_934_; 
v___x_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
return v___x_934_;
}
}
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_956_; 
v_a_937_ = lean_ctor_get(v_x_926_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v_x_926_);
if (v_isSharedCheck_956_ == 0)
{
v___x_939_ = v_x_926_;
v_isShared_940_ = v_isSharedCheck_956_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v_x_926_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_956_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
if (lean_obj_tag(v_a_937_) == 0)
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_951_; 
lean_dec_ref(v_as_924_);
v_a_941_ = lean_ctor_get(v_a_937_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v_a_937_);
if (v_isSharedCheck_951_ == 0)
{
v___x_943_ = v_a_937_;
v_isShared_944_ = v_isSharedCheck_951_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v_a_937_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_951_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v_a_941_);
v___x_946_ = v___x_939_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_950_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_948_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v___x_946_);
v___x_948_ = v___x_943_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
else
{
lean_object* v_a_952_; size_t v___x_953_; size_t v___x_954_; lean_object* v___x_955_; 
lean_del_object(v___x_939_);
v_a_952_ = lean_ctor_get(v_a_937_, 0);
lean_inc(v_a_952_);
lean_dec_ref(v_a_937_);
v___x_953_ = ((size_t)1ULL);
v___x_954_ = lean_usize_add(v_i_923_, v___x_953_);
v___x_955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg(v_as_924_, v_sz_925_, v___x_954_, v_a_952_);
return v___x_955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___boxed(lean_object* v_as_957_, lean_object* v_sz_958_, lean_object* v_i_959_, lean_object* v_b_960_, lean_object* v___y_961_){
_start:
{
size_t v_sz_boxed_962_; size_t v_i_boxed_963_; lean_object* v_res_964_; 
v_sz_boxed_962_ = lean_unbox_usize(v_sz_958_);
lean_dec(v_sz_958_);
v_i_boxed_963_ = lean_unbox_usize(v_i_959_);
lean_dec(v_i_959_);
v_res_964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg(v_as_957_, v_sz_boxed_962_, v_i_boxed_963_, v_b_960_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__6(lean_object* v_selectables_965_, lean_object* v_x_966_){
_start:
{
if (lean_obj_tag(v_x_966_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_976_; 
lean_dec_ref(v_selectables_965_);
v_a_968_ = lean_ctor_get(v_x_966_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v_x_966_);
if (v_isSharedCheck_976_ == 0)
{
v___x_970_ = v_x_966_;
v_isShared_971_ = v_isSharedCheck_976_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v_x_966_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_976_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_975_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_974_; 
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
return v___x_974_;
}
}
}
else
{
lean_object* v_a_977_; uint64_t v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; size_t v_sz_984_; size_t v___x_985_; lean_object* v___x_986_; lean_object* v___f_987_; lean_object* v___x_988_; uint8_t v___x_989_; lean_object* v___x_990_; 
v_a_977_ = lean_ctor_get(v_x_966_, 0);
lean_inc(v_a_977_);
lean_dec_ref(v_x_966_);
v___x_978_ = l_ByteArray_toUInt64LE_x21(v_a_977_);
lean_dec(v_a_977_);
v___x_979_ = lean_uint64_to_nat(v___x_978_);
v___x_980_ = l_mkStdGen(v___x_979_);
lean_dec(v___x_979_);
v___x_981_ = l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt___redArg(v_selectables_965_, v___x_980_);
v___x_982_ = lean_box(0);
v___x_983_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__1));
v_sz_984_ = lean_array_size(v___x_981_);
v___x_985_ = ((size_t)0ULL);
lean_inc_ref(v___x_981_);
v___x_986_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg(v___x_981_, v_sz_984_, v___x_985_, v___x_983_);
v___f_987_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_987_, 0, v___x_981_);
lean_closure_set(v___f_987_, 1, v___x_982_);
v___x_988_ = lean_unsigned_to_nat(0u);
v___x_989_ = 0;
v___x_990_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_988_, v___x_989_, v___x_986_, v___f_987_);
return v___x_990_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__6___boxed(lean_object* v_selectables_991_, lean_object* v_x_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__6(v_selectables_991_, v_x_992_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__7(lean_object* v___f_995_, lean_object* v_____r_996_){
_start:
{
lean_object* v_val_999_; size_t v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = ((size_t)8ULL);
v___x_1005_ = lean_io_get_random_bytes(v___x_1004_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
lean_ctor_set_tag(v___x_1008_, 1);
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
v_val_999_ = v___x_1011_;
goto v___jp_998_;
}
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
v_a_1014_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_1005_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1005_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
lean_ctor_set_tag(v___x_1016_, 0);
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
v_val_999_ = v___x_1019_;
goto v___jp_998_;
}
}
}
v___jp_998_:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; uint8_t v___x_1002_; lean_object* v___x_1003_; 
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v_val_999_);
v___x_1001_ = lean_unsigned_to_nat(0u);
v___x_1002_ = 0;
v___x_1003_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1001_, v___x_1002_, v___x_1000_, v___f_995_);
return v___x_1003_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__7___boxed(lean_object* v___f_1022_, lean_object* v_____r_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__7(v___f_1022_, v_____r_1023_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__8(lean_object* v___f_1026_, lean_object* v_x_1027_){
_start:
{
if (lean_obj_tag(v_x_1027_) == 0)
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1037_; 
lean_dec_ref(v___f_1026_);
v_a_1029_ = lean_ctor_get(v_x_1027_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_x_1027_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1031_ = v_x_1027_;
v_isShared_1032_ = v_isSharedCheck_1037_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v_x_1027_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1037_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1035_; 
v___x_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
return v___x_1035_;
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1039_; 
v_a_1038_ = lean_ctor_get(v_x_1027_, 0);
lean_inc(v_a_1038_);
lean_dec_ref(v_x_1027_);
v___x_1039_ = lean_apply_2(v___f_1026_, v_a_1038_, lean_box(0));
return v___x_1039_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__8___boxed(lean_object* v___f_1040_, lean_object* v_x_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__8(v___f_1040_, v_x_1041_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg(lean_object* v_selectables_1051_){
_start:
{
lean_object* v___f_1053_; lean_object* v___f_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; uint8_t v___x_1057_; 
lean_inc_ref(v_selectables_1051_);
v___f_1053_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__6___boxed), 3, 1);
lean_closure_set(v___f_1053_, 0, v_selectables_1051_);
lean_inc_ref(v___f_1053_);
v___f_1054_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_1054_, 0, v___f_1053_);
v___x_1055_ = lean_array_get_size(v_selectables_1051_);
lean_dec_ref(v_selectables_1051_);
v___x_1056_ = lean_unsigned_to_nat(0u);
v___x_1057_ = lean_nat_dec_eq(v___x_1055_, v___x_1056_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
lean_dec_ref(v___f_1054_);
v___x_1058_ = lean_box(0);
v___x_1059_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__7(v___f_1053_, v___x_1058_);
return v___x_1059_;
}
else
{
lean_object* v___f_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; lean_object* v___x_1063_; 
lean_dec_ref(v___f_1053_);
v___f_1060_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__8___boxed), 3, 1);
lean_closure_set(v___f_1060_, 0, v___f_1054_);
v___x_1061_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_one___redArg___closed__3));
v___x_1062_ = 0;
v___x_1063_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1056_, v___x_1062_, v___x_1061_, v___f_1060_);
return v___x_1063_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___boxed(lean_object* v_selectables_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Std_Internal_IO_Async_Selectable_one___redArg(v_selectables_1064_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one(lean_object* v_00_u03b1_1067_, lean_object* v_selectables_1068_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_Std_Internal_IO_Async_Selectable_one___redArg(v_selectables_1068_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___boxed(lean_object* v_00_u03b1_1071_, lean_object* v_selectables_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Std_Internal_IO_Async_Selectable_one(v_00_u03b1_1071_, v_selectables_1072_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0(lean_object* v_00_u03b1_1075_, lean_object* v_as_1076_, size_t v_sz_1077_, size_t v_i_1078_, lean_object* v_b_1079_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg(v_as_1076_, v_sz_1077_, v_i_1078_, v_b_1079_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___boxed(lean_object* v_00_u03b1_1082_, lean_object* v_as_1083_, lean_object* v_sz_1084_, lean_object* v_i_1085_, lean_object* v_b_1086_, lean_object* v___y_1087_){
_start:
{
size_t v_sz_boxed_1088_; size_t v_i_boxed_1089_; lean_object* v_res_1090_; 
v_sz_boxed_1088_ = lean_unbox_usize(v_sz_1084_);
lean_dec(v_sz_1084_);
v_i_boxed_1089_ = lean_unbox_usize(v_i_1085_);
lean_dec(v_i_1085_);
v_res_1090_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0(v_00_u03b1_1082_, v_as_1083_, v_sz_boxed_1088_, v_i_boxed_1089_, v_b_1086_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2(lean_object* v_00_u03b1_1091_, lean_object* v_a_1092_, lean_object* v___x_1093_, lean_object* v_a_1094_, lean_object* v_as_1095_, size_t v_sz_1096_, size_t v_i_1097_, lean_object* v_b_1098_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg(v_a_1092_, v___x_1093_, v_a_1094_, v_as_1095_, v_sz_1096_, v_i_1097_, v_b_1098_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___boxed(lean_object* v_00_u03b1_1101_, lean_object* v_a_1102_, lean_object* v___x_1103_, lean_object* v_a_1104_, lean_object* v_as_1105_, lean_object* v_sz_1106_, lean_object* v_i_1107_, lean_object* v_b_1108_, lean_object* v___y_1109_){
_start:
{
size_t v_sz_boxed_1110_; size_t v_i_boxed_1111_; lean_object* v_res_1112_; 
v_sz_boxed_1110_ = lean_unbox_usize(v_sz_1106_);
lean_dec(v_sz_1106_);
v_i_boxed_1111_ = lean_unbox_usize(v_i_1107_);
lean_dec(v_i_1107_);
v_res_1112_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2(v_00_u03b1_1101_, v_a_1102_, v___x_1103_, v_a_1104_, v_as_1105_, v_sz_boxed_1110_, v_i_boxed_1111_, v_b_1108_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3(lean_object* v_00_u03b1_1113_, lean_object* v_as_1114_, size_t v_sz_1115_, size_t v_i_1116_, lean_object* v_b_1117_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg(v_as_1114_, v_sz_1115_, v_i_1116_, v_b_1117_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___boxed(lean_object* v_00_u03b1_1120_, lean_object* v_as_1121_, lean_object* v_sz_1122_, lean_object* v_i_1123_, lean_object* v_b_1124_, lean_object* v___y_1125_){
_start:
{
size_t v_sz_boxed_1126_; size_t v_i_boxed_1127_; lean_object* v_res_1128_; 
v_sz_boxed_1126_ = lean_unbox_usize(v_sz_1122_);
lean_dec(v_sz_1122_);
v_i_boxed_1127_ = lean_unbox_usize(v_i_1123_);
lean_dec(v_i_1123_);
v_res_1128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3(v_00_u03b1_1120_, v_as_1121_, v_sz_boxed_1126_, v_i_boxed_1127_, v_b_1124_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0(lean_object* v_x_1133_){
_start:
{
if (lean_obj_tag(v_x_1133_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1143_; 
v_a_1135_ = lean_ctor_get(v_x_1133_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_x_1133_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1137_ = v_x_1133_;
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v_x_1133_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
return v___x_1141_;
}
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1161_; 
v_a_1144_ = lean_ctor_get(v_x_1133_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v_x_1133_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1146_ = v_x_1133_;
v_isShared_1147_ = v_isSharedCheck_1161_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v_x_1133_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1161_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v_fst_1148_; 
v_fst_1148_ = lean_ctor_get(v_a_1144_, 0);
lean_inc(v_fst_1148_);
lean_dec(v_a_1144_);
if (lean_obj_tag(v_fst_1148_) == 0)
{
lean_object* v___x_1149_; 
lean_del_object(v___x_1146_);
v___x_1149_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0___closed__1));
return v___x_1149_;
}
else
{
lean_object* v_val_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1160_; 
v_val_1150_ = lean_ctor_get(v_fst_1148_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_fst_1148_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1152_ = v_fst_1148_;
v_isShared_1153_ = v_isSharedCheck_1160_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_val_1150_);
lean_dec(v_fst_1148_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1160_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v_val_1150_);
v___x_1155_ = v___x_1146_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_val_1150_);
v___x_1155_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1157_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set_tag(v___x_1152_, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1155_);
v___x_1157_ = v___x_1152_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0___boxed(lean_object* v_x_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0(v_x_1162_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__1(lean_object* v_a_1165_, lean_object* v___x_1166_, uint8_t v___x_1167_, lean_object* v___f_1168_, lean_object* v___x_1169_, lean_object* v_x_1170_){
_start:
{
if (lean_obj_tag(v_x_1170_) == 0)
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1180_; 
lean_dec_ref(v___x_1169_);
lean_dec_ref(v___f_1168_);
lean_dec(v___x_1166_);
lean_dec_ref(v_a_1165_);
v_a_1172_ = lean_ctor_get(v_x_1170_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_x_1170_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1174_ = v_x_1170_;
v_isShared_1175_ = v_isSharedCheck_1180_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v_x_1170_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1180_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
return v___x_1178_;
}
}
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1194_; 
v_a_1181_ = lean_ctor_get(v_x_1170_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_x_1170_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1183_ = v_x_1170_;
v_isShared_1184_ = v_isSharedCheck_1194_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v_x_1170_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1194_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
if (lean_obj_tag(v_a_1181_) == 1)
{
lean_object* v_val_1185_; lean_object* v_cont_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_del_object(v___x_1183_);
lean_dec_ref(v___x_1169_);
v_val_1185_ = lean_ctor_get(v_a_1181_, 0);
lean_inc(v_val_1185_);
lean_dec_ref(v_a_1181_);
v_cont_1186_ = lean_ctor_get(v_a_1165_, 1);
lean_inc_ref(v_cont_1186_);
lean_dec_ref(v_a_1165_);
v___x_1187_ = lean_apply_2(v_cont_1186_, v_val_1185_, lean_box(0));
v___x_1188_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1166_, v___x_1167_, v___x_1187_, v___f_1168_);
return v___x_1188_;
}
else
{
lean_object* v___x_1189_; lean_object* v___x_1191_; 
lean_dec(v_a_1181_);
lean_dec_ref(v___f_1168_);
lean_dec(v___x_1166_);
lean_dec_ref(v_a_1165_);
v___x_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1169_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 0, v___x_1189_);
v___x_1191_ = v___x_1183_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1192_; 
v___x_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
return v___x_1192_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__1___boxed(lean_object* v_a_1195_, lean_object* v___x_1196_, lean_object* v___x_1197_, lean_object* v___f_1198_, lean_object* v___x_1199_, lean_object* v_x_1200_, lean_object* v___y_1201_){
_start:
{
uint8_t v___x_2272__boxed_1202_; lean_object* v_res_1203_; 
v___x_2272__boxed_1202_ = lean_unbox(v___x_1197_);
v_res_1203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__1(v_a_1195_, v___x_1196_, v___x_2272__boxed_1202_, v___f_1198_, v___x_1199_, v_x_1200_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__0(lean_object* v___x_1204_, lean_object* v_x_1205_){
_start:
{
if (lean_obj_tag(v_x_1205_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1215_; 
v_a_1207_ = lean_ctor_get(v_x_1205_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_x_1205_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1209_ = v_x_1205_;
v_isShared_1210_ = v_isSharedCheck_1215_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v_x_1205_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1215_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v___x_1213_; 
v___x_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
return v___x_1213_;
}
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1228_; 
v_a_1216_ = lean_ctor_get(v_x_1205_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_x_1205_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1218_ = v_x_1205_;
v_isShared_1219_ = v_isSharedCheck_1228_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v_x_1205_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1228_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1220_, 0, v_a_1216_);
v___x_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
lean_ctor_set(v___x_1222_, 1, v___x_1204_);
v___x_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 0, v___x_1223_);
v___x_1225_ = v___x_1218_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1226_; 
v___x_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
return v___x_1226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__0___boxed(lean_object* v___x_1229_, lean_object* v_x_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__0(v___x_1229_, v_x_1230_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__2___boxed(lean_object* v_i_1238_, lean_object* v___x_1239_, lean_object* v_as_1240_, lean_object* v_sz_1241_, lean_object* v_x_1242_, lean_object* v___y_1243_){
_start:
{
size_t v_i_boxed_1244_; size_t v_sz_boxed_1245_; lean_object* v_res_1246_; 
v_i_boxed_1244_ = lean_unbox_usize(v_i_1238_);
lean_dec(v_i_1238_);
v_sz_boxed_1245_ = lean_unbox_usize(v_sz_1241_);
lean_dec(v_sz_1241_);
v_res_1246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__2(v_i_boxed_1244_, v___x_1239_, v_as_1240_, v_sz_boxed_1245_, v_x_1242_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(lean_object* v___x_1247_, lean_object* v_as_1248_, size_t v_sz_1249_, size_t v_i_1250_, lean_object* v_b_1251_){
_start:
{
uint8_t v___x_1253_; 
v___x_1253_ = lean_usize_dec_lt(v_i_1250_, v_sz_1249_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
lean_dec_ref(v_as_1248_);
lean_dec(v___x_1247_);
v___x_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1254_, 0, v_b_1251_);
v___x_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
return v___x_1255_;
}
else
{
lean_object* v_a_1256_; lean_object* v_selector_1257_; lean_object* v_tryFn_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; lean_object* v___f_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___f_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___f_1269_; uint8_t v___x_1270_; lean_object* v___x_1271_; 
lean_dec_ref(v_b_1251_);
v_a_1256_ = lean_array_uget_borrowed(v_as_1248_, v_i_1250_);
v_selector_1257_ = lean_ctor_get(v_a_1256_, 0);
v_tryFn_1258_ = lean_ctor_get(v_selector_1257_, 0);
lean_inc_ref(v_tryFn_1258_);
v___x_1259_ = lean_apply_1(v_tryFn_1258_, lean_box(0));
v___x_1260_ = lean_unsigned_to_nat(0u);
v___x_1261_ = lean_nat_dec_eq(v___x_1247_, v___x_1260_);
v___f_1262_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__0));
v___x_1263_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__1));
v___x_1264_ = lean_box(v___x_1261_);
lean_inc(v_a_1256_);
v___f_1265_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_1265_, 0, v_a_1256_);
lean_closure_set(v___f_1265_, 1, v___x_1260_);
lean_closure_set(v___f_1265_, 2, v___x_1264_);
lean_closure_set(v___f_1265_, 3, v___f_1262_);
lean_closure_set(v___f_1265_, 4, v___x_1263_);
v___x_1266_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1260_, v___x_1261_, v___x_1259_, v___f_1265_);
v___x_1267_ = lean_box_usize(v_i_1250_);
v___x_1268_ = lean_box_usize(v_sz_1249_);
v___f_1269_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_1269_, 0, v___x_1267_);
lean_closure_set(v___f_1269_, 1, v___x_1247_);
lean_closure_set(v___f_1269_, 2, v_as_1248_);
lean_closure_set(v___f_1269_, 3, v___x_1268_);
v___x_1270_ = 0;
v___x_1271_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1260_, v___x_1270_, v___x_1266_, v___f_1269_);
return v___x_1271_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__2(size_t v_i_1272_, lean_object* v___x_1273_, lean_object* v_as_1274_, size_t v_sz_1275_, lean_object* v_x_1276_){
_start:
{
if (lean_obj_tag(v_x_1276_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1286_; 
lean_dec_ref(v_as_1274_);
lean_dec(v___x_1273_);
v_a_1278_ = lean_ctor_get(v_x_1276_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_x_1276_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1280_ = v_x_1276_;
v_isShared_1281_ = v_isSharedCheck_1286_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v_x_1276_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1286_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1284_; 
v___x_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
return v___x_1284_;
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1306_; 
v_a_1287_ = lean_ctor_get(v_x_1276_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_x_1276_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1289_ = v_x_1276_;
v_isShared_1290_ = v_isSharedCheck_1306_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v_x_1276_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1306_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
if (lean_obj_tag(v_a_1287_) == 0)
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1301_; 
lean_dec_ref(v_as_1274_);
lean_dec(v___x_1273_);
v_a_1291_ = lean_ctor_get(v_a_1287_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v_a_1287_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1293_ = v_a_1287_;
v_isShared_1294_ = v_isSharedCheck_1301_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v_a_1287_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1301_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v_a_1291_);
v___x_1296_ = v___x_1289_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
lean_object* v___x_1298_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v___x_1296_);
v___x_1298_ = v___x_1293_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
else
{
lean_object* v_a_1302_; size_t v___x_1303_; size_t v___x_1304_; lean_object* v___x_1305_; 
lean_del_object(v___x_1289_);
v_a_1302_ = lean_ctor_get(v_a_1287_, 0);
lean_inc(v_a_1302_);
lean_dec_ref(v_a_1287_);
v___x_1303_ = ((size_t)1ULL);
v___x_1304_ = lean_usize_add(v_i_1272_, v___x_1303_);
v___x_1305_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(v___x_1273_, v_as_1274_, v_sz_1275_, v___x_1304_, v_a_1302_);
return v___x_1305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___boxed(lean_object* v___x_1307_, lean_object* v_as_1308_, lean_object* v_sz_1309_, lean_object* v_i_1310_, lean_object* v_b_1311_, lean_object* v___y_1312_){
_start:
{
size_t v_sz_boxed_1313_; size_t v_i_boxed_1314_; lean_object* v_res_1315_; 
v_sz_boxed_1313_ = lean_unbox_usize(v_sz_1309_);
lean_dec(v_sz_1309_);
v_i_boxed_1314_ = lean_unbox_usize(v_i_1310_);
lean_dec(v_i_1310_);
v_res_1315_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(v___x_1307_, v_as_1308_, v_sz_boxed_1313_, v_i_boxed_1314_, v_b_1311_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__1(lean_object* v_selectables_1316_, lean_object* v___x_1317_, lean_object* v___x_1318_, uint8_t v___x_1319_, lean_object* v___f_1320_, lean_object* v_x_1321_){
_start:
{
if (lean_obj_tag(v_x_1321_) == 0)
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1331_; 
lean_dec_ref(v___f_1320_);
lean_dec(v___x_1318_);
lean_dec(v___x_1317_);
lean_dec_ref(v_selectables_1316_);
v_a_1323_ = lean_ctor_get(v_x_1321_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_x_1321_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1325_ = v_x_1321_;
v_isShared_1326_ = v_isSharedCheck_1331_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v_x_1321_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1331_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1323_);
v___x_1328_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
lean_object* v___x_1329_; 
v___x_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
return v___x_1329_;
}
}
}
else
{
lean_object* v_a_1332_; uint64_t v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; size_t v_sz_1338_; size_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v_a_1332_ = lean_ctor_get(v_x_1321_, 0);
lean_inc(v_a_1332_);
lean_dec_ref(v_x_1321_);
v___x_1333_ = l_ByteArray_toUInt64LE_x21(v_a_1332_);
lean_dec(v_a_1332_);
v___x_1334_ = lean_uint64_to_nat(v___x_1333_);
v___x_1335_ = l_mkStdGen(v___x_1334_);
lean_dec(v___x_1334_);
v___x_1336_ = l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt___redArg(v_selectables_1316_, v___x_1335_);
v___x_1337_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__1));
v_sz_1338_ = lean_array_size(v___x_1336_);
v___x_1339_ = ((size_t)0ULL);
v___x_1340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(v___x_1317_, v___x_1336_, v_sz_1338_, v___x_1339_, v___x_1337_);
v___x_1341_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1318_, v___x_1319_, v___x_1340_, v___f_1320_);
return v___x_1341_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__1___boxed(lean_object* v_selectables_1342_, lean_object* v___x_1343_, lean_object* v___x_1344_, lean_object* v___x_1345_, lean_object* v___f_1346_, lean_object* v_x_1347_, lean_object* v___y_1348_){
_start:
{
uint8_t v___x_2511__boxed_1349_; lean_object* v_res_1350_; 
v___x_2511__boxed_1349_ = lean_unbox(v___x_1345_);
v_res_1350_ = l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__1(v_selectables_1342_, v___x_1343_, v___x_1344_, v___x_2511__boxed_1349_, v___f_1346_, v_x_1347_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg(lean_object* v_selectables_1352_){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; uint8_t v___x_1356_; 
v___x_1354_ = lean_array_get_size(v_selectables_1352_);
v___x_1355_ = lean_unsigned_to_nat(0u);
v___x_1356_ = lean_nat_dec_eq(v___x_1354_, v___x_1355_);
if (v___x_1356_ == 0)
{
lean_object* v___f_1357_; lean_object* v___x_1358_; lean_object* v___f_1359_; lean_object* v_val_1361_; size_t v___x_1364_; lean_object* v___x_1365_; 
v___f_1357_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_tryOne___redArg___closed__0));
v___x_1358_ = lean_box(v___x_1356_);
v___f_1359_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_1359_, 0, v_selectables_1352_);
lean_closure_set(v___f_1359_, 1, v___x_1354_);
lean_closure_set(v___f_1359_, 2, v___x_1355_);
lean_closure_set(v___f_1359_, 3, v___x_1358_);
lean_closure_set(v___f_1359_, 4, v___f_1357_);
v___x_1364_ = ((size_t)8ULL);
v___x_1365_ = lean_io_get_random_bytes(v___x_1364_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1365_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1365_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
lean_ctor_set_tag(v___x_1368_, 1);
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
v_val_1361_ = v___x_1371_;
goto v___jp_1360_;
}
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
v_a_1374_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1365_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1365_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
lean_ctor_set_tag(v___x_1376_, 0);
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
v_val_1361_ = v___x_1379_;
goto v___jp_1360_;
}
}
}
v___jp_1360_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v_val_1361_);
v___x_1363_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1355_, v___x_1356_, v___x_1362_, v___f_1359_);
return v___x_1363_;
}
}
else
{
lean_object* v___x_1382_; 
lean_dec_ref(v_selectables_1352_);
v___x_1382_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0___closed__1));
return v___x_1382_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___boxed(lean_object* v_selectables_1383_, lean_object* v_a_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Std_Internal_IO_Async_Selectable_tryOne___redArg(v_selectables_1383_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne(lean_object* v_00_u03b1_1386_, lean_object* v_selectables_1387_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Std_Internal_IO_Async_Selectable_tryOne___redArg(v_selectables_1387_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___boxed(lean_object* v_00_u03b1_1390_, lean_object* v_selectables_1391_, lean_object* v_a_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Std_Internal_IO_Async_Selectable_tryOne(v_00_u03b1_1390_, v_selectables_1391_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0(lean_object* v_00_u03b1_1394_, lean_object* v___x_1395_, lean_object* v_as_1396_, size_t v_sz_1397_, size_t v_i_1398_, lean_object* v_b_1399_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(v___x_1395_, v_as_1396_, v_sz_1397_, v_i_1398_, v_b_1399_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___boxed(lean_object* v_00_u03b1_1402_, lean_object* v___x_1403_, lean_object* v_as_1404_, lean_object* v_sz_1405_, lean_object* v_i_1406_, lean_object* v_b_1407_, lean_object* v___y_1408_){
_start:
{
size_t v_sz_boxed_1409_; size_t v_i_boxed_1410_; lean_object* v_res_1411_; 
v_sz_boxed_1409_ = lean_unbox_usize(v_sz_1405_);
lean_dec(v_sz_1405_);
v_i_boxed_1410_ = lean_unbox_usize(v_i_1406_);
lean_dec(v_i_1406_);
v_res_1411_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0(v_00_u03b1_1402_, v___x_1403_, v_as_1404_, v_sz_boxed_1409_, v_i_boxed_1410_, v_b_1407_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__1(lean_object* v___x_1412_, lean_object* v_x_1413_){
_start:
{
if (lean_obj_tag(v_x_1413_) == 0)
{
lean_object* v___x_1415_; 
v___x_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1415_, 0, v_x_1413_);
return v___x_1415_;
}
else
{
lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1423_; 
v_isSharedCheck_1423_ = !lean_is_exclusive(v_x_1413_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; 
v_unused_1424_ = lean_ctor_get(v_x_1413_, 0);
lean_dec(v_unused_1424_);
v___x_1417_ = v_x_1413_;
v_isShared_1418_ = v_isSharedCheck_1423_;
goto v_resetjp_1416_;
}
else
{
lean_dec(v_x_1413_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1423_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1412_);
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1412_);
v___x_1420_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1421_; 
v___x_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1420_);
return v___x_1421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__1___boxed(lean_object* v___x_1425_, lean_object* v_x_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__1(v___x_1425_, v_x_1426_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__5(lean_object* v_a_1429_, lean_object* v___f_1430_, lean_object* v___x_1431_, uint8_t v___x_1432_, lean_object* v___x_1433_, lean_object* v___f_1434_, lean_object* v_x_1435_){
_start:
{
if (lean_obj_tag(v_x_1435_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1445_; 
lean_dec_ref(v___f_1434_);
lean_dec(v___x_1431_);
lean_dec_ref(v___f_1430_);
v_a_1437_ = lean_ctor_get(v_x_1435_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_x_1435_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1439_ = v_x_1435_;
v_isShared_1440_ = v_isSharedCheck_1445_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v_x_1435_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1445_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1443_; 
v___x_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
return v___x_1443_;
}
}
}
else
{
lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1456_; 
v_isSharedCheck_1456_ = !lean_is_exclusive(v_x_1435_);
if (v_isSharedCheck_1456_ == 0)
{
lean_object* v_unused_1457_; 
v_unused_1457_ = lean_ctor_get(v_x_1435_, 0);
lean_dec(v_unused_1457_);
v___x_1447_ = v_x_1435_;
v_isShared_1448_ = v_isSharedCheck_1456_;
goto v_resetjp_1446_;
}
else
{
lean_dec(v_x_1435_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1456_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1452_; 
v___x_1449_ = lean_io_promise_result_opt(v_a_1429_);
lean_inc(v___x_1431_);
v___x_1450_ = lean_io_bind_task(v___x_1449_, v___f_1430_, v___x_1431_, v___x_1432_);
lean_dec_ref(v___x_1450_);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 0, v___x_1433_);
v___x_1452_ = v___x_1447_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1433_);
v___x_1452_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
v___x_1454_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1431_, v___x_1432_, v___x_1453_, v___f_1434_);
return v___x_1454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__5___boxed(lean_object* v_a_1458_, lean_object* v___f_1459_, lean_object* v___x_1460_, lean_object* v___x_1461_, lean_object* v___x_1462_, lean_object* v___f_1463_, lean_object* v_x_1464_, lean_object* v___y_1465_){
_start:
{
uint8_t v___x_6642__boxed_1466_; lean_object* v_res_1467_; 
v___x_6642__boxed_1466_ = lean_unbox(v___x_1461_);
v_res_1467_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__5(v_a_1458_, v___f_1459_, v___x_1460_, v___x_6642__boxed_1466_, v___x_1462_, v___f_1463_, v_x_1464_);
lean_dec(v_a_1458_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__6(lean_object* v_waiter_1468_, lean_object* v_a_1469_, lean_object* v___f_1470_, lean_object* v___x_1471_, uint8_t v___x_1472_, lean_object* v___x_1473_, lean_object* v___f_1474_, lean_object* v_x_1475_){
_start:
{
if (lean_obj_tag(v_x_1475_) == 0)
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1485_; 
lean_dec_ref(v___f_1474_);
lean_dec(v___x_1471_);
lean_dec_ref(v___f_1470_);
lean_dec_ref(v_a_1469_);
lean_dec_ref(v_waiter_1468_);
v_a_1477_ = lean_ctor_get(v_x_1475_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v_x_1475_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1479_ = v_x_1475_;
v_isShared_1480_ = v_isSharedCheck_1485_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v_x_1475_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1485_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1477_);
v___x_1482_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
lean_object* v___x_1483_; 
v___x_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
return v___x_1483_;
}
}
}
else
{
lean_object* v_selector_1486_; lean_object* v_a_1487_; lean_object* v_finished_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1500_; 
v_selector_1486_ = lean_ctor_get(v_a_1469_, 0);
lean_inc_ref(v_selector_1486_);
lean_dec_ref(v_a_1469_);
v_a_1487_ = lean_ctor_get(v_x_1475_, 0);
lean_inc(v_a_1487_);
lean_dec_ref(v_x_1475_);
v_finished_1488_ = lean_ctor_get(v_waiter_1468_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_waiter_1468_);
if (v_isSharedCheck_1500_ == 0)
{
lean_object* v_unused_1501_; 
v_unused_1501_ = lean_ctor_get(v_waiter_1468_, 1);
lean_dec(v_unused_1501_);
v___x_1490_ = v_waiter_1468_;
v_isShared_1491_ = v_isSharedCheck_1500_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_finished_1488_);
lean_dec(v_waiter_1468_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1500_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v_registerFn_1492_; lean_object* v___x_1494_; 
v_registerFn_1492_ = lean_ctor_get(v_selector_1486_, 1);
lean_inc_ref(v_registerFn_1492_);
lean_dec_ref(v_selector_1486_);
lean_inc(v_a_1487_);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 1, v_a_1487_);
v___x_1494_ = v___x_1490_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_finished_1488_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_a_1487_);
v___x_1494_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___f_1497_; lean_object* v___x_1498_; 
v___x_1495_ = lean_apply_2(v_registerFn_1492_, v___x_1494_, lean_box(0));
v___x_1496_ = lean_box(v___x_1472_);
lean_inc(v___x_1471_);
v___f_1497_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__5___boxed), 8, 6);
lean_closure_set(v___f_1497_, 0, v_a_1487_);
lean_closure_set(v___f_1497_, 1, v___f_1470_);
lean_closure_set(v___f_1497_, 2, v___x_1471_);
lean_closure_set(v___f_1497_, 3, v___x_1496_);
lean_closure_set(v___f_1497_, 4, v___x_1473_);
lean_closure_set(v___f_1497_, 5, v___f_1474_);
v___x_1498_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1471_, v___x_1472_, v___x_1495_, v___f_1497_);
return v___x_1498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__6___boxed(lean_object* v_waiter_1502_, lean_object* v_a_1503_, lean_object* v___f_1504_, lean_object* v___x_1505_, lean_object* v___x_1506_, lean_object* v___x_1507_, lean_object* v___f_1508_, lean_object* v_x_1509_, lean_object* v___y_1510_){
_start:
{
uint8_t v___x_6708__boxed_1511_; lean_object* v_res_1512_; 
v___x_6708__boxed_1511_ = lean_unbox(v___x_1506_);
v_res_1512_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__6(v_waiter_1502_, v_a_1503_, v___f_1504_, v___x_1505_, v___x_6708__boxed_1511_, v___x_1507_, v___f_1508_, v_x_1509_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg___lam__1___boxed(lean_object* v_i_1513_, lean_object* v___x_1514_, lean_object* v_as_1515_, lean_object* v_sz_1516_, lean_object* v_x_1517_, lean_object* v___y_1518_){
_start:
{
size_t v_i_boxed_1519_; size_t v_sz_boxed_1520_; lean_object* v_res_1521_; 
v_i_boxed_1519_ = lean_unbox_usize(v_i_1513_);
lean_dec(v_i_1513_);
v_sz_boxed_1520_ = lean_unbox_usize(v_sz_1516_);
lean_dec(v_sz_1516_);
v_res_1521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg___lam__1(v_i_boxed_1519_, v___x_1514_, v_as_1515_, v_sz_boxed_1520_, v_x_1517_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(lean_object* v___x_1522_, lean_object* v_as_1523_, size_t v_sz_1524_, size_t v_i_1525_, lean_object* v_b_1526_){
_start:
{
uint8_t v___x_1528_; 
v___x_1528_ = lean_usize_dec_lt(v_i_1525_, v_sz_1524_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_dec_ref(v_as_1523_);
lean_dec(v___x_1522_);
v___x_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1529_, 0, v_b_1526_);
v___x_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
return v___x_1530_;
}
else
{
lean_object* v_a_1531_; lean_object* v_selector_1532_; lean_object* v_unregisterFn_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; lean_object* v___f_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___f_1541_; uint8_t v___x_1542_; lean_object* v___x_1543_; 
v_a_1531_ = lean_array_uget_borrowed(v_as_1523_, v_i_1525_);
v_selector_1532_ = lean_ctor_get(v_a_1531_, 0);
v_unregisterFn_1533_ = lean_ctor_get(v_selector_1532_, 2);
lean_inc_ref(v_unregisterFn_1533_);
v___x_1534_ = lean_apply_1(v_unregisterFn_1533_, lean_box(0));
v___x_1535_ = lean_unsigned_to_nat(0u);
v___x_1536_ = lean_nat_dec_eq(v___x_1522_, v___x_1535_);
v___f_1537_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___closed__0));
v___x_1538_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1535_, v___x_1536_, v___x_1534_, v___f_1537_);
v___x_1539_ = lean_box_usize(v_i_1525_);
v___x_1540_ = lean_box_usize(v_sz_1524_);
v___f_1541_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg___lam__1___boxed), 6, 4);
lean_closure_set(v___f_1541_, 0, v___x_1539_);
lean_closure_set(v___f_1541_, 1, v___x_1522_);
lean_closure_set(v___f_1541_, 2, v_as_1523_);
lean_closure_set(v___f_1541_, 3, v___x_1540_);
v___x_1542_ = 0;
v___x_1543_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1535_, v___x_1542_, v___x_1538_, v___f_1541_);
return v___x_1543_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg___lam__1(size_t v_i_1544_, lean_object* v___x_1545_, lean_object* v_as_1546_, size_t v_sz_1547_, lean_object* v_x_1548_){
_start:
{
if (lean_obj_tag(v_x_1548_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1558_; 
lean_dec_ref(v_as_1546_);
lean_dec(v___x_1545_);
v_a_1550_ = lean_ctor_get(v_x_1548_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v_x_1548_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1552_ = v_x_1548_;
v_isShared_1553_ = v_isSharedCheck_1558_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v_x_1548_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1558_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1556_; 
v___x_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
return v___x_1556_;
}
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1578_; 
v_a_1559_ = lean_ctor_get(v_x_1548_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v_x_1548_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1561_ = v_x_1548_;
v_isShared_1562_ = v_isSharedCheck_1578_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v_x_1548_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1578_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
if (lean_obj_tag(v_a_1559_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1573_; 
lean_dec_ref(v_as_1546_);
lean_dec(v___x_1545_);
v_a_1563_ = lean_ctor_get(v_a_1559_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_a_1559_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1565_ = v_a_1559_;
v_isShared_1566_ = v_isSharedCheck_1573_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v_a_1559_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1573_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v_a_1563_);
v___x_1568_ = v___x_1561_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
lean_object* v___x_1570_; 
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v___x_1568_);
v___x_1570_ = v___x_1565_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
else
{
lean_object* v_a_1574_; size_t v___x_1575_; size_t v___x_1576_; lean_object* v___x_1577_; 
lean_del_object(v___x_1561_);
v_a_1574_ = lean_ctor_get(v_a_1559_, 0);
lean_inc(v_a_1574_);
lean_dec_ref(v_a_1559_);
v___x_1575_ = ((size_t)1ULL);
v___x_1576_ = lean_usize_add(v_i_1544_, v___x_1575_);
v___x_1577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(v___x_1545_, v_as_1546_, v_sz_1547_, v___x_1576_, v_a_1574_);
return v___x_1577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg___boxed(lean_object* v___x_1579_, lean_object* v_as_1580_, lean_object* v_sz_1581_, lean_object* v_i_1582_, lean_object* v_b_1583_, lean_object* v___y_1584_){
_start:
{
size_t v_sz_boxed_1585_; size_t v_i_boxed_1586_; lean_object* v_res_1587_; 
v_sz_boxed_1585_ = lean_unbox_usize(v_sz_1581_);
lean_dec(v_sz_1581_);
v_i_boxed_1586_ = lean_unbox_usize(v_i_1582_);
lean_dec(v_i_1582_);
v_res_1587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(v___x_1579_, v_as_1580_, v_sz_boxed_1585_, v_i_boxed_1586_, v_b_1583_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__3(lean_object* v___x_1588_, uint8_t v___x_1589_, lean_object* v___f_1590_, lean_object* v___f_1591_, lean_object* v_val_1592_, lean_object* v_x_1593_){
_start:
{
lean_object* v_val_1596_; 
if (lean_obj_tag(v_x_1593_) == 0)
{
lean_object* v___x_1600_; 
lean_dec_ref(v_val_1592_);
lean_dec_ref(v___f_1591_);
lean_dec_ref(v___f_1590_);
lean_dec(v___x_1588_);
v___x_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1600_, 0, v_x_1593_);
return v___x_1600_;
}
else
{
lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1613_; 
v_isSharedCheck_1613_ = !lean_is_exclusive(v_x_1593_);
if (v_isSharedCheck_1613_ == 0)
{
lean_object* v_unused_1614_; 
v_unused_1614_ = lean_ctor_get(v_x_1593_, 0);
lean_dec(v_unused_1614_);
v___x_1602_ = v_x_1593_;
v_isShared_1603_ = v_isSharedCheck_1613_;
goto v_resetjp_1601_;
}
else
{
lean_dec(v_x_1593_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1613_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg(v_val_1592_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; lean_object* v___x_1607_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1605_);
lean_dec_ref(v___x_1604_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 0, v_a_1605_);
v___x_1607_ = v___x_1602_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
v_val_1596_ = v___x_1607_;
goto v___jp_1595_;
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; 
v_a_1609_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1609_);
lean_dec_ref(v___x_1604_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set_tag(v___x_1602_, 0);
lean_ctor_set(v___x_1602_, 0, v_a_1609_);
v___x_1611_ = v___x_1602_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1609_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
v_val_1596_ = v___x_1611_;
goto v___jp_1595_;
}
}
}
}
v___jp_1595_:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1597_, 0, v_val_1596_);
lean_inc(v___x_1588_);
v___x_1598_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1588_, v___x_1589_, v___x_1597_, v___f_1590_);
v___x_1599_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1588_, v___x_1589_, v___x_1598_, v___f_1591_);
return v___x_1599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__3___boxed(lean_object* v___x_1615_, lean_object* v___x_1616_, lean_object* v___f_1617_, lean_object* v___f_1618_, lean_object* v_val_1619_, lean_object* v_x_1620_, lean_object* v___y_1621_){
_start:
{
uint8_t v___x_6874__boxed_1622_; lean_object* v_res_1623_; 
v___x_6874__boxed_1622_ = lean_unbox(v___x_1616_);
v_res_1623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__3(v___x_1615_, v___x_6874__boxed_1622_, v___f_1617_, v___f_1618_, v_val_1619_, v_x_1620_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__2(lean_object* v_a_1624_, lean_object* v___x_1625_, uint8_t v___x_1626_, lean_object* v___f_1627_, lean_object* v_x_1628_){
_start:
{
if (lean_obj_tag(v_x_1628_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1638_; 
lean_dec_ref(v___f_1627_);
lean_dec(v___x_1625_);
lean_dec_ref(v_a_1624_);
v_a_1630_ = lean_ctor_get(v_x_1628_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v_x_1628_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1632_ = v_x_1628_;
v_isShared_1633_ = v_isSharedCheck_1638_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v_x_1628_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1638_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1636_; 
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
return v___x_1636_;
}
}
}
else
{
lean_object* v_a_1639_; lean_object* v_cont_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v_a_1639_ = lean_ctor_get(v_x_1628_, 0);
lean_inc(v_a_1639_);
lean_dec_ref(v_x_1628_);
v_cont_1640_ = lean_ctor_get(v_a_1624_, 1);
lean_inc_ref(v_cont_1640_);
lean_dec_ref(v_a_1624_);
v___x_1641_ = lean_apply_2(v_cont_1640_, v_a_1639_, lean_box(0));
v___x_1642_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1625_, v___x_1626_, v___x_1641_, v___f_1627_);
return v___x_1642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__2___boxed(lean_object* v_a_1643_, lean_object* v___x_1644_, lean_object* v___x_1645_, lean_object* v___f_1646_, lean_object* v_x_1647_, lean_object* v___y_1648_){
_start:
{
uint8_t v___x_6937__boxed_1649_; lean_object* v_res_1650_; 
v___x_6937__boxed_1649_ = lean_unbox(v___x_1645_);
v_res_1650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__2(v_a_1643_, v___x_1644_, v___x_6937__boxed_1649_, v___f_1646_, v_x_1647_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__0(lean_object* v_promise_1651_, lean_object* v_x_1652_){
_start:
{
if (lean_obj_tag(v_x_1652_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1662_; 
v_a_1654_ = lean_ctor_get(v_x_1652_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v_x_1652_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1656_ = v_x_1652_;
v_isShared_1657_ = v_isSharedCheck_1662_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v_x_1652_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1662_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
lean_object* v___x_1660_; 
v___x_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1659_);
return v___x_1660_;
}
}
}
else
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1663_ = lean_io_promise_resolve(v_x_1652_, v_promise_1651_);
v___x_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1663_);
v___x_1665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
return v___x_1665_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__0___boxed(lean_object* v_promise_1666_, lean_object* v_x_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__0(v_promise_1666_, v_x_1667_);
lean_dec(v_promise_1666_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__1(lean_object* v_promise_1670_, lean_object* v_x_1671_){
_start:
{
if (lean_obj_tag(v_x_1671_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1683_; 
v_a_1673_ = lean_ctor_get(v_x_1671_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v_x_1671_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1675_ = v_x_1671_;
v_isShared_1676_ = v_isSharedCheck_1683_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v_x_1671_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1683_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = lean_io_promise_resolve(v___x_1678_, v_promise_1670_);
v___x_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
v___x_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
return v___x_1681_;
}
}
}
else
{
lean_object* v___x_1684_; 
v___x_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1684_, 0, v_x_1671_);
return v___x_1684_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__1___boxed(lean_object* v_promise_1685_, lean_object* v_x_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__1(v_promise_1685_, v_x_1686_);
lean_dec(v_promise_1685_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__4(lean_object* v___x_1689_, lean_object* v___x_1690_, lean_object* v___x_1691_, lean_object* v_waiter_1692_, lean_object* v_a_1693_, lean_object* v___x_1694_, uint8_t v___x_1695_, lean_object* v_a_1696_){
_start:
{
if (lean_obj_tag(v_a_1696_) == 0)
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
lean_dec(v___x_1694_);
lean_dec_ref(v_a_1693_);
lean_dec_ref(v_waiter_1692_);
lean_dec(v___x_1691_);
lean_dec_ref(v___x_1690_);
v___x_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1689_);
v___x_1699_ = lean_task_pure(v___x_1698_);
return v___x_1699_;
}
else
{
lean_object* v_val_1700_; size_t v_sz_1701_; size_t v___x_1702_; lean_object* v___x_1703_; lean_object* v_promise_1704_; lean_object* v___f_1705_; lean_object* v___f_1706_; lean_object* v___x_1707_; lean_object* v___f_1708_; lean_object* v___x_1709_; lean_object* v___f_1710_; lean_object* v___x_1711_; 
v_val_1700_ = lean_ctor_get(v_a_1696_, 0);
lean_inc(v_val_1700_);
lean_dec_ref(v_a_1696_);
v_sz_1701_ = lean_array_size(v___x_1690_);
v___x_1702_ = ((size_t)0ULL);
v___x_1703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(v___x_1691_, v___x_1690_, v_sz_1701_, v___x_1702_, v___x_1689_);
v_promise_1704_ = lean_ctor_get(v_waiter_1692_, 1);
lean_inc(v_promise_1704_);
lean_dec_ref(v_waiter_1692_);
lean_inc(v_promise_1704_);
v___f_1705_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1705_, 0, v_promise_1704_);
v___f_1706_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1706_, 0, v_promise_1704_);
v___x_1707_ = lean_box(v___x_1695_);
lean_inc(v___x_1694_);
v___f_1708_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_1708_, 0, v_a_1693_);
lean_closure_set(v___f_1708_, 1, v___x_1694_);
lean_closure_set(v___f_1708_, 2, v___x_1707_);
lean_closure_set(v___f_1708_, 3, v___f_1706_);
v___x_1709_ = lean_box(v___x_1695_);
lean_inc(v___x_1694_);
v___f_1710_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__3___boxed), 7, 5);
lean_closure_set(v___f_1710_, 0, v___x_1694_);
lean_closure_set(v___f_1710_, 1, v___x_1709_);
lean_closure_set(v___f_1710_, 2, v___f_1708_);
lean_closure_set(v___f_1710_, 3, v___f_1705_);
lean_closure_set(v___f_1710_, 4, v_val_1700_);
v___x_1711_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1694_, v___x_1695_, v___x_1703_, v___f_1710_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v___x_1713_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_a_1712_);
lean_dec_ref(v___x_1711_);
v___x_1713_ = lean_task_pure(v_a_1712_);
return v___x_1713_;
}
else
{
lean_object* v_a_1714_; 
v_a_1714_ = lean_ctor_get(v___x_1711_, 0);
lean_inc_ref(v_a_1714_);
lean_dec_ref(v___x_1711_);
return v_a_1714_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__4___boxed(lean_object* v___x_1715_, lean_object* v___x_1716_, lean_object* v___x_1717_, lean_object* v_waiter_1718_, lean_object* v_a_1719_, lean_object* v___x_1720_, lean_object* v___x_1721_, lean_object* v_a_1722_, lean_object* v___y_1723_){
_start:
{
uint8_t v___x_7041__boxed_1724_; lean_object* v_res_1725_; 
v___x_7041__boxed_1724_ = lean_unbox(v___x_1721_);
v_res_1725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__4(v___x_1715_, v___x_1716_, v___x_1717_, v_waiter_1718_, v_a_1719_, v___x_1720_, v___x_7041__boxed_1724_, v_a_1722_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__7___boxed(lean_object* v_i_1726_, lean_object* v___x_1727_, lean_object* v___x_1728_, lean_object* v_waiter_1729_, lean_object* v_as_1730_, lean_object* v_sz_1731_, lean_object* v_x_1732_, lean_object* v___y_1733_){
_start:
{
size_t v_i_boxed_1734_; size_t v_sz_boxed_1735_; lean_object* v_res_1736_; 
v_i_boxed_1734_ = lean_unbox_usize(v_i_1726_);
lean_dec(v_i_1726_);
v_sz_boxed_1735_ = lean_unbox_usize(v_sz_1731_);
lean_dec(v_sz_1731_);
v_res_1736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__7(v_i_boxed_1734_, v___x_1727_, v___x_1728_, v_waiter_1729_, v_as_1730_, v_sz_boxed_1735_, v_x_1732_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg(lean_object* v___x_1737_, lean_object* v___x_1738_, lean_object* v_waiter_1739_, lean_object* v_as_1740_, size_t v_sz_1741_, size_t v_i_1742_, lean_object* v_b_1743_){
_start:
{
uint8_t v___x_1745_; 
v___x_1745_ = lean_usize_dec_lt(v_i_1742_, v_sz_1741_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_dec_ref(v_as_1740_);
lean_dec_ref(v_waiter_1739_);
lean_dec(v___x_1738_);
lean_dec_ref(v___x_1737_);
v___x_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1746_, 0, v_b_1743_);
v___x_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
return v___x_1747_;
}
else
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___f_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; lean_object* v_a_1753_; lean_object* v___x_1754_; lean_object* v___f_1755_; lean_object* v___x_1756_; lean_object* v___f_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___f_1763_; uint8_t v___x_1764_; lean_object* v___x_1765_; 
v___x_1748_ = lean_io_promise_new();
v___x_1749_ = lean_box(0);
v___f_1750_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___closed__0));
v___x_1751_ = lean_unsigned_to_nat(0u);
v___x_1752_ = lean_nat_dec_eq(v___x_1738_, v___x_1751_);
v_a_1753_ = lean_array_uget_borrowed(v_as_1740_, v_i_1742_);
v___x_1754_ = lean_box(v___x_1752_);
lean_inc(v_a_1753_);
lean_inc_ref(v_waiter_1739_);
lean_inc(v___x_1738_);
lean_inc_ref(v___x_1737_);
v___f_1755_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__4___boxed), 9, 7);
lean_closure_set(v___f_1755_, 0, v___x_1749_);
lean_closure_set(v___f_1755_, 1, v___x_1737_);
lean_closure_set(v___f_1755_, 2, v___x_1738_);
lean_closure_set(v___f_1755_, 3, v_waiter_1739_);
lean_closure_set(v___f_1755_, 4, v_a_1753_);
lean_closure_set(v___f_1755_, 5, v___x_1751_);
lean_closure_set(v___f_1755_, 6, v___x_1754_);
v___x_1756_ = lean_box(v___x_1752_);
lean_inc(v_a_1753_);
lean_inc_ref(v_waiter_1739_);
v___f_1757_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__6___boxed), 9, 7);
lean_closure_set(v___f_1757_, 0, v_waiter_1739_);
lean_closure_set(v___f_1757_, 1, v_a_1753_);
lean_closure_set(v___f_1757_, 2, v___f_1755_);
lean_closure_set(v___f_1757_, 3, v___x_1751_);
lean_closure_set(v___f_1757_, 4, v___x_1756_);
lean_closure_set(v___f_1757_, 5, v___x_1749_);
lean_closure_set(v___f_1757_, 6, v___f_1750_);
v___x_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1748_);
v___x_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
v___x_1760_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1751_, v___x_1752_, v___x_1759_, v___f_1757_);
v___x_1761_ = lean_box_usize(v_i_1742_);
v___x_1762_ = lean_box_usize(v_sz_1741_);
v___f_1763_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__7___boxed), 8, 6);
lean_closure_set(v___f_1763_, 0, v___x_1761_);
lean_closure_set(v___f_1763_, 1, v___x_1737_);
lean_closure_set(v___f_1763_, 2, v___x_1738_);
lean_closure_set(v___f_1763_, 3, v_waiter_1739_);
lean_closure_set(v___f_1763_, 4, v_as_1740_);
lean_closure_set(v___f_1763_, 5, v___x_1762_);
v___x_1764_ = 0;
v___x_1765_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1751_, v___x_1764_, v___x_1760_, v___f_1763_);
return v___x_1765_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__7(size_t v_i_1766_, lean_object* v___x_1767_, lean_object* v___x_1768_, lean_object* v_waiter_1769_, lean_object* v_as_1770_, size_t v_sz_1771_, lean_object* v_x_1772_){
_start:
{
if (lean_obj_tag(v_x_1772_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1782_; 
lean_dec_ref(v_as_1770_);
lean_dec_ref(v_waiter_1769_);
lean_dec(v___x_1768_);
lean_dec_ref(v___x_1767_);
v_a_1774_ = lean_ctor_get(v_x_1772_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v_x_1772_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1776_ = v_x_1772_;
v_isShared_1777_ = v_isSharedCheck_1782_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v_x_1772_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1782_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_a_1774_);
v___x_1779_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v___x_1780_; 
v___x_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1779_);
return v___x_1780_;
}
}
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1802_; 
v_a_1783_ = lean_ctor_get(v_x_1772_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_x_1772_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1785_ = v_x_1772_;
v_isShared_1786_ = v_isSharedCheck_1802_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v_x_1772_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1802_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
if (lean_obj_tag(v_a_1783_) == 0)
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1797_; 
lean_dec_ref(v_as_1770_);
lean_dec_ref(v_waiter_1769_);
lean_dec(v___x_1768_);
lean_dec_ref(v___x_1767_);
v_a_1787_ = lean_ctor_get(v_a_1783_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v_a_1783_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1789_ = v_a_1783_;
v_isShared_1790_ = v_isSharedCheck_1797_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v_a_1783_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1797_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 0, v_a_1787_);
v___x_1792_ = v___x_1785_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
lean_object* v___x_1794_; 
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1792_);
v___x_1794_ = v___x_1789_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1792_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
else
{
lean_object* v_a_1798_; size_t v___x_1799_; size_t v___x_1800_; lean_object* v___x_1801_; 
lean_del_object(v___x_1785_);
v_a_1798_ = lean_ctor_get(v_a_1783_, 0);
lean_inc(v_a_1798_);
lean_dec_ref(v_a_1783_);
v___x_1799_ = ((size_t)1ULL);
v___x_1800_ = lean_usize_add(v_i_1766_, v___x_1799_);
v___x_1801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg(v___x_1767_, v___x_1768_, v_waiter_1769_, v_as_1770_, v_sz_1771_, v___x_1800_, v_a_1798_);
return v___x_1801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___boxed(lean_object* v___x_1803_, lean_object* v___x_1804_, lean_object* v_waiter_1805_, lean_object* v_as_1806_, lean_object* v_sz_1807_, lean_object* v_i_1808_, lean_object* v_b_1809_, lean_object* v___y_1810_){
_start:
{
size_t v_sz_boxed_1811_; size_t v_i_boxed_1812_; lean_object* v_res_1813_; 
v_sz_boxed_1811_ = lean_unbox_usize(v_sz_1807_);
lean_dec(v_sz_1807_);
v_i_boxed_1812_ = lean_unbox_usize(v_i_1808_);
lean_dec(v_i_1808_);
v_res_1813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg(v___x_1803_, v___x_1804_, v_waiter_1805_, v_as_1806_, v_sz_boxed_1811_, v_i_boxed_1812_, v_b_1809_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__0(lean_object* v___x_1814_, lean_object* v___x_1815_, lean_object* v___x_1816_, lean_object* v___x_1817_, uint8_t v___x_1818_, lean_object* v___f_1819_, lean_object* v_waiter_1820_){
_start:
{
size_t v_sz_1822_; size_t v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v_sz_1822_ = lean_array_size(v___x_1814_);
v___x_1823_ = ((size_t)0ULL);
lean_inc_ref(v___x_1814_);
v___x_1824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg(v___x_1814_, v___x_1815_, v_waiter_1820_, v___x_1814_, v_sz_1822_, v___x_1823_, v___x_1816_);
v___x_1825_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1817_, v___x_1818_, v___x_1824_, v___f_1819_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__0___boxed(lean_object* v___x_1826_, lean_object* v___x_1827_, lean_object* v___x_1828_, lean_object* v___x_1829_, lean_object* v___x_1830_, lean_object* v___f_1831_, lean_object* v_waiter_1832_, lean_object* v___y_1833_){
_start:
{
uint8_t v___x_7210__boxed_1834_; lean_object* v_res_1835_; 
v___x_7210__boxed_1834_ = lean_unbox(v___x_1830_);
v_res_1835_ = l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__0(v___x_1826_, v___x_1827_, v___x_1828_, v___x_1829_, v___x_7210__boxed_1834_, v___f_1831_, v_waiter_1832_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__3(lean_object* v___x_1836_, lean_object* v___x_1837_, size_t v_sz_1838_, size_t v___x_1839_, lean_object* v___x_1840_, lean_object* v___x_1841_, uint8_t v___x_1842_, lean_object* v___f_1843_){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(v___x_1836_, v___x_1837_, v_sz_1838_, v___x_1839_, v___x_1840_);
v___x_1846_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1841_, v___x_1842_, v___x_1845_, v___f_1843_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__3___boxed(lean_object* v___x_1847_, lean_object* v___x_1848_, lean_object* v_sz_1849_, lean_object* v___x_1850_, lean_object* v___x_1851_, lean_object* v___x_1852_, lean_object* v___x_1853_, lean_object* v___f_1854_, lean_object* v___y_1855_){
_start:
{
size_t v_sz_boxed_1856_; size_t v___x_7235__boxed_1857_; uint8_t v___x_7238__boxed_1858_; lean_object* v_res_1859_; 
v_sz_boxed_1856_ = lean_unbox_usize(v_sz_1849_);
lean_dec(v_sz_1849_);
v___x_7235__boxed_1857_ = lean_unbox_usize(v___x_1850_);
lean_dec(v___x_1850_);
v___x_7238__boxed_1858_ = lean_unbox(v___x_1853_);
v_res_1859_ = l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__3(v___x_1847_, v___x_1848_, v_sz_boxed_1856_, v___x_7235__boxed_1857_, v___x_1851_, v___x_1852_, v___x_7238__boxed_1858_, v___f_1854_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__2(lean_object* v___x_1860_, lean_object* v___x_1861_, size_t v_sz_1862_, size_t v___x_1863_, lean_object* v___x_1864_, lean_object* v___x_1865_, uint8_t v___x_1866_, lean_object* v___f_1867_){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(v___x_1860_, v___x_1861_, v_sz_1862_, v___x_1863_, v___x_1864_);
v___x_1870_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1865_, v___x_1866_, v___x_1869_, v___f_1867_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__2___boxed(lean_object* v___x_1871_, lean_object* v___x_1872_, lean_object* v_sz_1873_, lean_object* v___x_1874_, lean_object* v___x_1875_, lean_object* v___x_1876_, lean_object* v___x_1877_, lean_object* v___f_1878_, lean_object* v___y_1879_){
_start:
{
size_t v_sz_boxed_1880_; size_t v___x_7263__boxed_1881_; uint8_t v___x_7266__boxed_1882_; lean_object* v_res_1883_; 
v_sz_boxed_1880_ = lean_unbox_usize(v_sz_1873_);
lean_dec(v_sz_1873_);
v___x_7263__boxed_1881_ = lean_unbox_usize(v___x_1874_);
lean_dec(v___x_1874_);
v___x_7266__boxed_1882_ = lean_unbox(v___x_1877_);
v_res_1883_ = l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__2(v___x_1871_, v___x_1872_, v_sz_boxed_1880_, v___x_7263__boxed_1881_, v___x_1875_, v___x_1876_, v___x_7266__boxed_1882_, v___f_1878_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg(lean_object* v_selectables_1888_){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; uint8_t v___x_1892_; 
v___x_1890_ = lean_array_get_size(v_selectables_1888_);
v___x_1891_ = lean_unsigned_to_nat(0u);
v___x_1892_ = lean_nat_dec_eq(v___x_1890_, v___x_1891_);
if (v___x_1892_ == 0)
{
size_t v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = ((size_t)8ULL);
v___x_1894_ = lean_io_get_random_bytes(v___x_1893_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1922_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1897_ = v___x_1894_;
v_isShared_1898_ = v_isSharedCheck_1922_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1894_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1922_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___f_1899_; uint64_t v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___f_1905_; lean_object* v___x_1906_; lean_object* v___f_1907_; lean_object* v___x_1908_; size_t v_sz_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___f_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___f_1917_; lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___f_1899_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_tryOne___redArg___closed__0));
v___x_1900_ = l_ByteArray_toUInt64LE_x21(v_a_1895_);
lean_dec(v_a_1895_);
v___x_1901_ = lean_uint64_to_nat(v___x_1900_);
v___x_1902_ = l_mkStdGen(v___x_1901_);
lean_dec(v___x_1901_);
v___x_1903_ = l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt___redArg(v_selectables_1888_, v___x_1902_);
v___x_1904_ = lean_box(0);
v___f_1905_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_combine___redArg___closed__0));
v___x_1906_ = lean_box(v___x_1892_);
lean_inc_ref(v___x_1903_);
v___f_1907_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_1907_, 0, v___x_1903_);
lean_closure_set(v___f_1907_, 1, v___x_1890_);
lean_closure_set(v___f_1907_, 2, v___x_1904_);
lean_closure_set(v___f_1907_, 3, v___x_1891_);
lean_closure_set(v___f_1907_, 4, v___x_1906_);
lean_closure_set(v___f_1907_, 5, v___f_1905_);
v___x_1908_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__1));
v_sz_1909_ = lean_array_size(v___x_1903_);
v___x_1910_ = lean_box_usize(v_sz_1909_);
v___x_1911_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_combine___redArg___boxed__const__1));
v___x_1912_ = lean_box(v___x_1892_);
lean_inc_ref(v___x_1903_);
v___f_1913_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_1913_, 0, v___x_1890_);
lean_closure_set(v___f_1913_, 1, v___x_1903_);
lean_closure_set(v___f_1913_, 2, v___x_1910_);
lean_closure_set(v___f_1913_, 3, v___x_1911_);
lean_closure_set(v___f_1913_, 4, v___x_1904_);
lean_closure_set(v___f_1913_, 5, v___x_1891_);
lean_closure_set(v___f_1913_, 6, v___x_1912_);
lean_closure_set(v___f_1913_, 7, v___f_1905_);
v___x_1914_ = lean_box_usize(v_sz_1909_);
v___x_1915_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_combine___redArg___boxed__const__1));
v___x_1916_ = lean_box(v___x_1892_);
v___f_1917_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_1917_, 0, v___x_1890_);
lean_closure_set(v___f_1917_, 1, v___x_1903_);
lean_closure_set(v___f_1917_, 2, v___x_1914_);
lean_closure_set(v___f_1917_, 3, v___x_1915_);
lean_closure_set(v___f_1917_, 4, v___x_1908_);
lean_closure_set(v___f_1917_, 5, v___x_1891_);
lean_closure_set(v___f_1917_, 6, v___x_1916_);
lean_closure_set(v___f_1917_, 7, v___f_1899_);
v___x_1918_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1918_, 0, v___f_1917_);
lean_ctor_set(v___x_1918_, 1, v___f_1907_);
lean_ctor_set(v___x_1918_, 2, v___f_1913_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v___x_1918_);
v___x_1920_ = v___x_1897_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
lean_dec_ref(v_selectables_1888_);
v_a_1923_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v___x_1894_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1894_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_a_1923_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
else
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
lean_dec_ref(v_selectables_1888_);
v___x_1931_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_one___redArg___closed__1));
v___x_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
return v___x_1932_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___boxed(lean_object* v_selectables_1933_, lean_object* v_a_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Std_Internal_IO_Async_Selectable_combine___redArg(v_selectables_1933_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine(lean_object* v_00_u03b1_1936_, lean_object* v_selectables_1937_){
_start:
{
lean_object* v___x_1939_; 
v___x_1939_ = l_Std_Internal_IO_Async_Selectable_combine___redArg(v_selectables_1937_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___boxed(lean_object* v_00_u03b1_1940_, lean_object* v_selectables_1941_, lean_object* v_a_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Std_Internal_IO_Async_Selectable_combine(v_00_u03b1_1940_, v_selectables_1941_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0(lean_object* v_00_u03b1_1944_, lean_object* v___x_1945_, lean_object* v_as_1946_, size_t v_sz_1947_, size_t v_i_1948_, lean_object* v_b_1949_){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(v___x_1945_, v_as_1946_, v_sz_1947_, v_i_1948_, v_b_1949_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___boxed(lean_object* v_00_u03b1_1952_, lean_object* v___x_1953_, lean_object* v_as_1954_, lean_object* v_sz_1955_, lean_object* v_i_1956_, lean_object* v_b_1957_, lean_object* v___y_1958_){
_start:
{
size_t v_sz_boxed_1959_; size_t v_i_boxed_1960_; lean_object* v_res_1961_; 
v_sz_boxed_1959_ = lean_unbox_usize(v_sz_1955_);
lean_dec(v_sz_1955_);
v_i_boxed_1960_ = lean_unbox_usize(v_i_1956_);
lean_dec(v_i_1956_);
v_res_1961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0(v_00_u03b1_1952_, v___x_1953_, v_as_1954_, v_sz_boxed_1959_, v_i_boxed_1960_, v_b_1957_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1(lean_object* v_00_u03b1_1962_, lean_object* v___x_1963_, lean_object* v___x_1964_, lean_object* v_waiter_1965_, lean_object* v_as_1966_, size_t v_sz_1967_, size_t v_i_1968_, lean_object* v_b_1969_){
_start:
{
lean_object* v___x_1971_; 
v___x_1971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg(v___x_1963_, v___x_1964_, v_waiter_1965_, v_as_1966_, v_sz_1967_, v_i_1968_, v_b_1969_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___boxed(lean_object* v_00_u03b1_1972_, lean_object* v___x_1973_, lean_object* v___x_1974_, lean_object* v_waiter_1975_, lean_object* v_as_1976_, lean_object* v_sz_1977_, lean_object* v_i_1978_, lean_object* v_b_1979_, lean_object* v___y_1980_){
_start:
{
size_t v_sz_boxed_1981_; size_t v_i_boxed_1982_; lean_object* v_res_1983_; 
v_sz_boxed_1981_ = lean_unbox_usize(v_sz_1977_);
lean_dec(v_sz_1977_);
v_i_boxed_1982_ = lean_unbox_usize(v_i_1978_);
lean_dec(v_i_1978_);
v_res_1983_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1(v_00_u03b1_1972_, v___x_1973_, v___x_1974_, v_waiter_1975_, v_as_1976_, v_sz_boxed_1981_, v_i_boxed_1982_, v_b_1979_);
return v_res_1983_;
}
}
lean_object* runtime_initialize_Init_Data_Random(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Async_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray_Extra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Async_Select(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Random(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Async_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ByteArray_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Async_Select(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Std_Internal_Async_Select(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Async_Select(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Async_Select(builtin);
}
#ifdef __cplusplus
}
#endif
