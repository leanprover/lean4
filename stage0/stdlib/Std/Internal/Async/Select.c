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
lean_object* v___y_124_; lean_object* v___y_125_; uint8_t v___x_150_; lean_object* v___y_152_; 
v___x_150_ = lean_nat_dec_lt(v_hi_122_, v_lo_121_);
if (v___x_150_ == 0)
{
v___y_152_ = v_lo_121_;
goto v___jp_151_;
}
else
{
v___y_152_ = v_hi_122_;
goto v___jp_151_;
}
v___jp_123_:
{
lean_object* v___x_126_; lean_object* v_fst_127_; lean_object* v_snd_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v_genMag_131_; lean_object* v_q_132_; lean_object* v___x_133_; lean_object* v_k_134_; lean_object* v_tgtMag_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v_fst_139_; lean_object* v_snd_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_149_; 
v___x_126_ = l_stdRange;
v_fst_127_ = lean_ctor_get(v___x_126_, 0);
v_snd_128_ = lean_ctor_get(v___x_126_, 1);
v___x_129_ = lean_nat_sub(v_snd_128_, v_fst_127_);
v___x_130_ = lean_unsigned_to_nat(1u);
v_genMag_131_ = lean_nat_add(v___x_129_, v___x_130_);
lean_dec(v___x_129_);
v_q_132_ = lean_unsigned_to_nat(1000u);
v___x_133_ = lean_nat_sub(v___y_125_, v___y_124_);
v_k_134_ = lean_nat_add(v___x_133_, v___x_130_);
lean_dec(v___x_133_);
v_tgtMag_135_ = lean_nat_mul(v_k_134_, v_q_132_);
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v_g_120_);
v___x_138_ = l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0_spec__0(v_fst_127_, v_genMag_131_, v_tgtMag_135_, v___x_137_);
lean_dec(v_genMag_131_);
v_fst_139_ = lean_ctor_get(v___x_138_, 0);
v_snd_140_ = lean_ctor_get(v___x_138_, 1);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_149_ == 0)
{
v___x_142_ = v___x_138_;
v_isShared_143_ = v_isSharedCheck_149_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_snd_140_);
lean_inc(v_fst_139_);
lean_dec(v___x_138_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_149_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_144_; lean_object* v_v_x27_145_; lean_object* v___x_147_; 
v___x_144_ = lean_nat_mod(v_fst_139_, v_k_134_);
lean_dec(v_k_134_);
lean_dec(v_fst_139_);
v_v_x27_145_ = lean_nat_add(v___y_124_, v___x_144_);
lean_dec(v___x_144_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v_v_x27_145_);
v___x_147_ = v___x_142_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_v_x27_145_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_snd_140_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
v___jp_151_:
{
if (v___x_150_ == 0)
{
v___y_124_ = v___y_152_;
v___y_125_ = v_hi_122_;
goto v___jp_123_;
}
else
{
v___y_124_ = v___y_152_;
v___y_125_ = v_lo_121_;
goto v___jp_123_;
}
}
}
}
LEAN_EXPORT lean_object* l_randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0___boxed(lean_object* v_g_153_, lean_object* v_lo_154_, lean_object* v_hi_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0(v_g_153_, v_lo_154_, v_hi_155_);
lean_dec(v_hi_155_);
lean_dec(v_lo_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go___redArg(lean_object* v_xs_157_, lean_object* v_gen_158_, lean_object* v_i_159_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_160_ = lean_array_get_size(v_xs_157_);
v___x_161_ = lean_unsigned_to_nat(1u);
v___x_162_ = lean_nat_sub(v___x_160_, v___x_161_);
v___x_163_ = lean_nat_dec_lt(v_i_159_, v___x_162_);
if (v___x_163_ == 0)
{
lean_dec(v___x_162_);
lean_dec(v_i_159_);
lean_dec_ref(v_gen_158_);
return v_xs_157_;
}
else
{
lean_object* v___x_164_; lean_object* v_fst_165_; lean_object* v_snd_166_; lean_object* v_xs_167_; lean_object* v___x_168_; 
v___x_164_ = l_randNat___at___00__private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_spec__0(v_gen_158_, v_i_159_, v___x_162_);
lean_dec(v___x_162_);
v_fst_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_fst_165_);
v_snd_166_ = lean_ctor_get(v___x_164_, 1);
lean_inc(v_snd_166_);
lean_dec_ref(v___x_164_);
v_xs_167_ = lean_array_swap(v_xs_157_, v_i_159_, v_fst_165_);
lean_dec(v_fst_165_);
v___x_168_ = lean_nat_add(v_i_159_, v___x_161_);
lean_dec(v_i_159_);
v_xs_157_ = v_xs_167_;
v_gen_158_ = v_snd_166_;
v_i_159_ = v___x_168_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go(lean_object* v_00_u03b1_170_, lean_object* v_xs_171_, lean_object* v_gen_172_, lean_object* v_i_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go___redArg(v_xs_171_, v_gen_172_, v_i_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_match__1_splitter___redArg(lean_object* v_x_175_, lean_object* v_h__1_176_){
_start:
{
lean_object* v_fst_177_; lean_object* v_snd_178_; lean_object* v___x_179_; 
v_fst_177_ = lean_ctor_get(v_x_175_, 0);
lean_inc(v_fst_177_);
v_snd_178_ = lean_ctor_get(v_x_175_, 1);
lean_inc(v_snd_178_);
lean_dec_ref(v_x_175_);
v___x_179_ = lean_apply_2(v_h__1_176_, v_fst_177_, v_snd_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go_match__1_splitter(lean_object* v_motive_180_, lean_object* v_x_181_, lean_object* v_h__1_182_){
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt___redArg(lean_object* v_xs_186_, lean_object* v_gen_187_){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt_go___redArg(v_xs_186_, v_gen_187_, v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt(lean_object* v_00_u03b1_190_, lean_object* v_xs_191_, lean_object* v_gen_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt___redArg(v_xs_191_, v_gen_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg(lean_object* v_e_194_){
_start:
{
if (lean_obj_tag(v_e_194_) == 0)
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_205_; 
v_a_196_ = lean_ctor_get(v_e_194_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v_e_194_);
if (v_isSharedCheck_205_ == 0)
{
v___x_198_ = v_e_194_;
v_isShared_199_ = v_isSharedCheck_205_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v_e_194_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_205_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_200_ = lean_io_error_to_string(v_a_196_);
v___x_201_ = lean_mk_io_user_error(v___x_200_);
if (v_isShared_199_ == 0)
{
lean_ctor_set_tag(v___x_198_, 1);
lean_ctor_set(v___x_198_, 0, v___x_201_);
v___x_203_ = v___x_198_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_201_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
else
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
v_a_206_ = lean_ctor_get(v_e_194_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v_e_194_);
if (v_isSharedCheck_213_ == 0)
{
v___x_208_ = v_e_194_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v_e_194_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
lean_ctor_set_tag(v___x_208_, 0);
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_a_206_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg___boxed(lean_object* v_e_214_, lean_object* v_a_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg(v_e_214_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1(lean_object* v_00_u03b1_217_, lean_object* v_e_218_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg(v_e_218_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___boxed(lean_object* v_00_u03b1_221_, lean_object* v_e_222_, lean_object* v_a_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1(v_00_u03b1_221_, v_e_222_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__0(lean_object* v___x_225_, lean_object* v_x_226_){
_start:
{
if (lean_obj_tag(v_x_226_) == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_mk_io_user_error(v___x_225_);
v___x_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
return v___x_228_;
}
else
{
lean_object* v_val_229_; 
lean_dec_ref(v___x_225_);
v_val_229_ = lean_ctor_get(v_x_226_, 0);
lean_inc(v_val_229_);
return v_val_229_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__0___boxed(lean_object* v___x_230_, lean_object* v_x_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__0(v___x_230_, v_x_231_);
lean_dec(v_x_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__1(lean_object* v___f_233_, uint8_t v___x_234_, lean_object* v_x_235_){
_start:
{
if (lean_obj_tag(v_x_235_) == 0)
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_245_; 
lean_dec_ref(v___f_233_);
v_a_237_ = lean_ctor_get(v_x_235_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v_x_235_);
if (v_isSharedCheck_245_ == 0)
{
v___x_239_ = v_x_235_;
v_isShared_240_ = v_isSharedCheck_245_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v_x_235_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_245_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_237_);
v___x_242_ = v_reuseFailAlloc_244_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_243_; 
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
}
}
else
{
lean_object* v_a_246_; 
v_a_246_ = lean_ctor_get(v_x_235_, 0);
lean_inc(v_a_246_);
lean_dec_ref(v_x_235_);
if (lean_obj_tag(v_a_246_) == 0)
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_255_; 
lean_dec_ref(v___f_233_);
v_a_247_ = lean_ctor_get(v_a_246_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v_a_246_);
if (v_isSharedCheck_255_ == 0)
{
v___x_249_ = v_a_246_;
v_isShared_250_ = v_isSharedCheck_255_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v_a_246_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_255_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_254_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_253_; 
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
}
}
else
{
lean_object* v_a_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v_a_256_ = lean_ctor_get(v_a_246_, 0);
lean_inc(v_a_256_);
lean_dec_ref(v_a_246_);
v___x_257_ = lean_io_promise_result_opt(v_a_256_);
lean_dec(v_a_256_);
v___x_258_ = lean_unsigned_to_nat(0u);
v___x_259_ = lean_task_map(v___f_233_, v___x_257_, v___x_258_, v___x_234_);
v___x_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
return v___x_260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__1___boxed(lean_object* v___f_261_, lean_object* v___x_262_, lean_object* v_x_263_, lean_object* v___y_264_){
_start:
{
uint8_t v___x_7540__boxed_265_; lean_object* v_res_266_; 
v___x_7540__boxed_265_ = lean_unbox(v___x_262_);
v_res_266_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__1(v___f_261_, v___x_7540__boxed_265_, v_x_263_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2(uint8_t v___x_270_, lean_object* v_x_271_, lean_object* v_x_272_){
_start:
{
if (lean_obj_tag(v_x_272_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_282_; 
lean_dec_ref(v_x_271_);
v_a_274_ = lean_ctor_get(v_x_272_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v_x_272_);
if (v_isSharedCheck_282_ == 0)
{
v___x_276_ = v_x_272_;
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v_x_272_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_281_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_280_; 
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
}
else
{
lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_295_; 
v_isSharedCheck_295_ = !lean_is_exclusive(v_x_272_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; 
v_unused_296_ = lean_ctor_get(v_x_272_, 0);
lean_dec(v_unused_296_);
v___x_284_ = v_x_272_;
v_isShared_285_ = v_isSharedCheck_295_;
goto v_resetjp_283_;
}
else
{
lean_dec(v_x_272_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_295_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___f_286_; lean_object* v___x_287_; lean_object* v___f_288_; lean_object* v___x_290_; 
v___f_286_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___closed__1));
v___x_287_ = lean_box(v___x_270_);
v___f_288_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_288_, 0, v___f_286_);
lean_closure_set(v___f_288_, 1, v___x_287_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v_x_271_);
v___x_290_ = v___x_284_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_x_271_);
v___x_290_ = v_reuseFailAlloc_294_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_292_, v___x_270_, v___x_291_, v___f_288_);
return v___x_293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___boxed(lean_object* v___x_297_, lean_object* v_x_298_, lean_object* v_x_299_, lean_object* v___y_300_){
_start:
{
uint8_t v___x_7605__boxed_301_; lean_object* v_res_302_; 
v___x_7605__boxed_301_ = lean_unbox(v___x_297_);
v_res_302_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2(v___x_7605__boxed_301_, v_x_298_, v_x_299_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__4(lean_object* v___x_303_, uint8_t v___x_304_, lean_object* v___f_305_, lean_object* v___f_306_, lean_object* v_a_307_){
_start:
{
lean_object* v_val_310_; 
if (lean_obj_tag(v_a_307_) == 0)
{
lean_object* v___x_318_; lean_object* v___x_319_; 
lean_dec_ref(v___f_306_);
lean_dec_ref(v___f_305_);
v___x_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_303_);
v___x_319_ = lean_task_pure(v___x_318_);
return v___x_319_;
}
else
{
lean_object* v_val_320_; lean_object* v___x_321_; 
v_val_320_ = lean_ctor_get(v_a_307_, 0);
lean_inc(v_val_320_);
lean_dec_ref(v_a_307_);
v___x_321_ = l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg(v_val_320_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___x_321_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_321_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
lean_ctor_set_tag(v___x_324_, 1);
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
v_val_310_ = v___x_327_;
goto v___jp_309_;
}
}
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
v_a_330_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_321_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_321_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
lean_ctor_set_tag(v___x_332_, 0);
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
v_val_310_ = v___x_335_;
goto v___jp_309_;
}
}
}
}
v___jp_309_:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_311_, 0, v_val_310_);
v___x_312_ = lean_unsigned_to_nat(0u);
v___x_313_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_312_, v___x_304_, v___x_311_, v___f_305_);
v___x_314_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_312_, v___x_304_, v___x_313_, v___f_306_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v___x_316_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_a_315_);
lean_dec_ref(v___x_314_);
v___x_316_ = lean_task_pure(v_a_315_);
return v___x_316_;
}
else
{
lean_object* v_a_317_; 
v_a_317_ = lean_ctor_get(v___x_314_, 0);
lean_inc_ref(v_a_317_);
lean_dec_ref(v___x_314_);
return v_a_317_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__4___boxed(lean_object* v___x_338_, lean_object* v___x_339_, lean_object* v___f_340_, lean_object* v___f_341_, lean_object* v_a_342_, lean_object* v___y_343_){
_start:
{
uint8_t v___x_7668__boxed_344_; lean_object* v_res_345_; 
v___x_7668__boxed_344_ = lean_unbox(v___x_339_);
v_res_345_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__4(v___x_338_, v___x_7668__boxed_344_, v___f_340_, v___f_341_, v_a_342_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__0(lean_object* v_a_346_, lean_object* v_x_347_){
_start:
{
if (lean_obj_tag(v_x_347_) == 0)
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_359_; 
v_a_349_ = lean_ctor_get(v_x_347_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v_x_347_);
if (v_isSharedCheck_359_ == 0)
{
v___x_351_ = v_x_347_;
v_isShared_352_ = v_isSharedCheck_359_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v_x_347_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_359_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_349_);
v___x_354_ = v_reuseFailAlloc_358_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_355_ = lean_io_promise_resolve(v___x_354_, v_a_346_);
v___x_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
return v___x_357_;
}
}
}
else
{
lean_object* v___x_360_; 
v___x_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_360_, 0, v_x_347_);
return v___x_360_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__0___boxed(lean_object* v_a_361_, lean_object* v_x_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__0(v_a_361_, v_x_362_);
lean_dec(v_a_361_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__0(lean_object* v___x_365_, lean_object* v_x_366_){
_start:
{
if (lean_obj_tag(v_x_366_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_376_; 
v_a_368_ = lean_ctor_get(v_x_366_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v_x_366_);
if (v_isSharedCheck_376_ == 0)
{
v___x_370_ = v_x_366_;
v_isShared_371_ = v_isSharedCheck_376_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v_x_366_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_376_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_368_);
v___x_373_ = v_reuseFailAlloc_375_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_374_; 
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
return v___x_374_;
}
}
}
else
{
lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_385_; 
v_isSharedCheck_385_ = !lean_is_exclusive(v_x_366_);
if (v_isSharedCheck_385_ == 0)
{
lean_object* v_unused_386_; 
v_unused_386_ = lean_ctor_get(v_x_366_, 0);
lean_dec(v_unused_386_);
v___x_378_ = v_x_366_;
v_isShared_379_ = v_isSharedCheck_385_;
goto v_resetjp_377_;
}
else
{
lean_dec(v_x_366_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_385_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_365_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_380_);
v___x_382_ = v___x_378_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_380_);
v___x_382_ = v_reuseFailAlloc_384_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_383_; 
v___x_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
return v___x_383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__0___boxed(lean_object* v___x_387_, lean_object* v_x_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__0(v___x_387_, v_x_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__3(lean_object* v_a_391_, lean_object* v_a_392_, uint8_t v___x_393_, lean_object* v___f_394_, lean_object* v_x_395_){
_start:
{
if (lean_obj_tag(v_x_395_) == 0)
{
lean_object* v___x_397_; 
lean_dec_ref(v___f_394_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v_x_395_);
return v___x_397_;
}
else
{
lean_object* v_cont_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
lean_dec_ref(v_x_395_);
v_cont_398_ = lean_ctor_get(v_a_391_, 1);
lean_inc_ref(v_cont_398_);
lean_dec_ref(v_a_391_);
v___x_399_ = lean_apply_2(v_cont_398_, v_a_392_, lean_box(0));
v___x_400_ = lean_unsigned_to_nat(0u);
v___x_401_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_400_, v___x_393_, v___x_399_, v___f_394_);
return v___x_401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__3___boxed(lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v___x_404_, lean_object* v___f_405_, lean_object* v_x_406_, lean_object* v___y_407_){
_start:
{
uint8_t v___x_7823__boxed_408_; lean_object* v_res_409_; 
v___x_7823__boxed_408_ = lean_unbox(v___x_404_);
v_res_409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__3(v_a_402_, v_a_403_, v___x_7823__boxed_408_, v___f_405_, v_x_406_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__1___boxed(lean_object* v_i_412_, lean_object* v_as_413_, lean_object* v_sz_414_, lean_object* v_x_415_, lean_object* v___y_416_){
_start:
{
size_t v_i_boxed_417_; size_t v_sz_boxed_418_; lean_object* v_res_419_; 
v_i_boxed_417_ = lean_unbox_usize(v_i_412_);
lean_dec(v_i_412_);
v_sz_boxed_418_ = lean_unbox_usize(v_sz_414_);
lean_dec(v_sz_414_);
v_res_419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__1(v_i_boxed_417_, v_as_413_, v_sz_boxed_418_, v_x_415_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg(lean_object* v_as_420_, size_t v_sz_421_, size_t v_i_422_, lean_object* v_b_423_){
_start:
{
uint8_t v___x_425_; 
v___x_425_ = lean_usize_dec_lt(v_i_422_, v_sz_421_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; 
lean_dec_ref(v_as_420_);
v___x_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_426_, 0, v_b_423_);
v___x_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
return v___x_427_;
}
else
{
lean_object* v_a_428_; lean_object* v_selector_429_; lean_object* v_unregisterFn_430_; lean_object* v___x_431_; lean_object* v___f_432_; lean_object* v___x_433_; uint8_t v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___f_438_; lean_object* v___x_439_; 
v_a_428_ = lean_array_uget_borrowed(v_as_420_, v_i_422_);
v_selector_429_ = lean_ctor_get(v_a_428_, 0);
v_unregisterFn_430_ = lean_ctor_get(v_selector_429_, 2);
lean_inc_ref(v_unregisterFn_430_);
v___x_431_ = lean_apply_1(v_unregisterFn_430_, lean_box(0));
v___f_432_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___closed__0));
v___x_433_ = lean_unsigned_to_nat(0u);
v___x_434_ = 0;
v___x_435_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_433_, v___x_434_, v___x_431_, v___f_432_);
v___x_436_ = lean_box_usize(v_i_422_);
v___x_437_ = lean_box_usize(v_sz_421_);
v___f_438_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_438_, 0, v___x_436_);
lean_closure_set(v___f_438_, 1, v_as_420_);
lean_closure_set(v___f_438_, 2, v___x_437_);
v___x_439_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_433_, v___x_434_, v___x_435_, v___f_438_);
return v___x_439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___lam__1(size_t v_i_440_, lean_object* v_as_441_, size_t v_sz_442_, lean_object* v_x_443_){
_start:
{
if (lean_obj_tag(v_x_443_) == 0)
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_453_; 
lean_dec_ref(v_as_441_);
v_a_445_ = lean_ctor_get(v_x_443_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v_x_443_);
if (v_isSharedCheck_453_ == 0)
{
v___x_447_ = v_x_443_;
v_isShared_448_ = v_isSharedCheck_453_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v_x_443_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_453_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_452_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_451_; 
v___x_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
return v___x_451_;
}
}
}
else
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_473_; 
v_a_454_ = lean_ctor_get(v_x_443_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v_x_443_);
if (v_isSharedCheck_473_ == 0)
{
v___x_456_ = v_x_443_;
v_isShared_457_ = v_isSharedCheck_473_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v_x_443_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_473_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
if (lean_obj_tag(v_a_454_) == 0)
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_468_; 
lean_dec_ref(v_as_441_);
v_a_458_ = lean_ctor_get(v_a_454_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v_a_454_);
if (v_isSharedCheck_468_ == 0)
{
v___x_460_ = v_a_454_;
v_isShared_461_ = v_isSharedCheck_468_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v_a_454_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_468_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v_a_458_);
v___x_463_ = v___x_456_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_458_);
v___x_463_ = v_reuseFailAlloc_467_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_465_; 
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v___x_463_);
v___x_465_ = v___x_460_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
else
{
lean_object* v_a_469_; size_t v___x_470_; size_t v___x_471_; lean_object* v___x_472_; 
lean_del_object(v___x_456_);
v_a_469_ = lean_ctor_get(v_a_454_, 0);
lean_inc(v_a_469_);
lean_dec_ref(v_a_454_);
v___x_470_ = ((size_t)1ULL);
v___x_471_ = lean_usize_add(v_i_440_, v___x_470_);
v___x_472_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg(v_as_441_, v_sz_442_, v___x_471_, v_a_469_);
return v___x_472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___boxed(lean_object* v_as_474_, lean_object* v_sz_475_, lean_object* v_i_476_, lean_object* v_b_477_, lean_object* v___y_478_){
_start:
{
size_t v_sz_boxed_479_; size_t v_i_boxed_480_; lean_object* v_res_481_; 
v_sz_boxed_479_ = lean_unbox_usize(v_sz_475_);
lean_dec(v_sz_475_);
v_i_boxed_480_ = lean_unbox_usize(v_i_476_);
lean_dec(v_i_476_);
v_res_481_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg(v_as_474_, v_sz_boxed_479_, v_i_boxed_480_, v_b_477_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__2(lean_object* v___x_482_, lean_object* v___x_483_, lean_object* v_a_484_, uint8_t v___x_485_, lean_object* v___f_486_, lean_object* v_x_487_){
_start:
{
if (lean_obj_tag(v_x_487_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_497_; 
lean_dec_ref(v___f_486_);
lean_dec_ref(v_a_484_);
lean_dec_ref(v___x_482_);
v_a_489_ = lean_ctor_get(v_x_487_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v_x_487_);
if (v_isSharedCheck_497_ == 0)
{
v___x_491_ = v_x_487_;
v_isShared_492_ = v_isSharedCheck_497_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v_x_487_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_497_;
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
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_489_);
v___x_494_ = v_reuseFailAlloc_496_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
lean_object* v___x_495_; 
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
}
}
else
{
lean_object* v_a_498_; size_t v_sz_499_; size_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___f_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_a_498_ = lean_ctor_get(v_x_487_, 0);
lean_inc(v_a_498_);
lean_dec_ref(v_x_487_);
v_sz_499_ = lean_array_size(v___x_482_);
v___x_500_ = ((size_t)0ULL);
v___x_501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg(v___x_482_, v_sz_499_, v___x_500_, v___x_483_);
v___x_502_ = lean_box(v___x_485_);
v___f_503_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_503_, 0, v_a_484_);
lean_closure_set(v___f_503_, 1, v_a_498_);
lean_closure_set(v___f_503_, 2, v___x_502_);
lean_closure_set(v___f_503_, 3, v___f_486_);
v___x_504_ = lean_unsigned_to_nat(0u);
v___x_505_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_504_, v___x_485_, v___x_501_, v___f_503_);
return v___x_505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__2___boxed(lean_object* v___x_506_, lean_object* v___x_507_, lean_object* v_a_508_, lean_object* v___x_509_, lean_object* v___f_510_, lean_object* v_x_511_, lean_object* v___y_512_){
_start:
{
uint8_t v___x_7945__boxed_513_; lean_object* v_res_514_; 
v___x_7945__boxed_513_ = lean_unbox(v___x_509_);
v_res_514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__2(v___x_506_, v___x_507_, v_a_508_, v___x_7945__boxed_513_, v___f_510_, v_x_511_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__1(lean_object* v_a_515_, lean_object* v_x_516_){
_start:
{
if (lean_obj_tag(v_x_516_) == 0)
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_526_; 
v_a_518_ = lean_ctor_get(v_x_516_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v_x_516_);
if (v_isSharedCheck_526_ == 0)
{
v___x_520_ = v_x_516_;
v_isShared_521_ = v_isSharedCheck_526_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v_x_516_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_526_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_525_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
lean_object* v___x_524_; 
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
return v___x_524_;
}
}
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_527_ = lean_io_promise_resolve(v_x_516_, v_a_515_);
v___x_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
v___x_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
return v___x_529_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__1___boxed(lean_object* v_a_530_, lean_object* v_x_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__1(v_a_530_, v_x_531_);
lean_dec(v_a_530_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__5(lean_object* v_a_534_, lean_object* v___f_535_, uint8_t v___x_536_, lean_object* v___x_537_, lean_object* v___f_538_, lean_object* v_x_539_){
_start:
{
if (lean_obj_tag(v_x_539_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_549_; 
lean_dec_ref(v___f_538_);
lean_dec_ref(v___f_535_);
v_a_541_ = lean_ctor_get(v_x_539_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v_x_539_);
if (v_isSharedCheck_549_ == 0)
{
v___x_543_ = v_x_539_;
v_isShared_544_ = v_isSharedCheck_549_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v_x_539_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_549_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_548_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
lean_object* v___x_547_; 
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
}
}
else
{
lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_561_; 
v_isSharedCheck_561_ = !lean_is_exclusive(v_x_539_);
if (v_isSharedCheck_561_ == 0)
{
lean_object* v_unused_562_; 
v_unused_562_ = lean_ctor_get(v_x_539_, 0);
lean_dec(v_unused_562_);
v___x_551_ = v_x_539_;
v_isShared_552_ = v_isSharedCheck_561_;
goto v_resetjp_550_;
}
else
{
lean_dec(v_x_539_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_561_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_553_ = lean_io_promise_result_opt(v_a_534_);
v___x_554_ = lean_unsigned_to_nat(0u);
v___x_555_ = lean_io_bind_task(v___x_553_, v___f_535_, v___x_554_, v___x_536_);
lean_dec_ref(v___x_555_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_537_);
v___x_557_ = v___x_551_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_537_);
v___x_557_ = v_reuseFailAlloc_560_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
v___x_559_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_554_, v___x_536_, v___x_558_, v___f_538_);
return v___x_559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__5___boxed(lean_object* v_a_563_, lean_object* v___f_564_, lean_object* v___x_565_, lean_object* v___x_566_, lean_object* v___f_567_, lean_object* v_x_568_, lean_object* v___y_569_){
_start:
{
uint8_t v___x_8029__boxed_570_; lean_object* v_res_571_; 
v___x_8029__boxed_570_ = lean_unbox(v___x_565_);
v_res_571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__5(v_a_563_, v___f_564_, v___x_8029__boxed_570_, v___x_566_, v___f_567_, v_x_568_);
lean_dec(v_a_563_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__6(lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v___f_574_, uint8_t v___x_575_, lean_object* v___x_576_, lean_object* v___f_577_, lean_object* v_x_578_){
_start:
{
if (lean_obj_tag(v_x_578_) == 0)
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_588_; 
lean_dec_ref(v___f_577_);
lean_dec_ref(v___f_574_);
lean_dec(v_a_573_);
lean_dec_ref(v_a_572_);
v_a_580_ = lean_ctor_get(v_x_578_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v_x_578_);
if (v_isSharedCheck_588_ == 0)
{
v___x_582_ = v_x_578_;
v_isShared_583_ = v_isSharedCheck_588_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v_x_578_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_588_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_587_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_586_; 
v___x_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
return v___x_586_;
}
}
}
else
{
lean_object* v_selector_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_603_; 
v_selector_589_ = lean_ctor_get(v_a_572_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v_a_572_);
if (v_isSharedCheck_603_ == 0)
{
lean_object* v_unused_604_; 
v_unused_604_ = lean_ctor_get(v_a_572_, 1);
lean_dec(v_unused_604_);
v___x_591_ = v_a_572_;
v_isShared_592_ = v_isSharedCheck_603_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_selector_589_);
lean_dec(v_a_572_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_603_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v_a_593_; lean_object* v_registerFn_594_; lean_object* v___x_596_; 
v_a_593_ = lean_ctor_get(v_x_578_, 0);
lean_inc_n(v_a_593_, 2);
lean_dec_ref(v_x_578_);
v_registerFn_594_ = lean_ctor_get(v_selector_589_, 1);
lean_inc_ref(v_registerFn_594_);
lean_dec_ref(v_selector_589_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 1, v_a_593_);
lean_ctor_set(v___x_591_, 0, v_a_573_);
v___x_596_ = v___x_591_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_573_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_a_593_);
v___x_596_ = v_reuseFailAlloc_602_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___f_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_597_ = lean_apply_2(v_registerFn_594_, v___x_596_, lean_box(0));
v___x_598_ = lean_box(v___x_575_);
v___f_599_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__5___boxed), 7, 5);
lean_closure_set(v___f_599_, 0, v_a_593_);
lean_closure_set(v___f_599_, 1, v___f_574_);
lean_closure_set(v___f_599_, 2, v___x_598_);
lean_closure_set(v___f_599_, 3, v___x_576_);
lean_closure_set(v___f_599_, 4, v___f_577_);
v___x_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_600_, v___x_575_, v___x_597_, v___f_599_);
return v___x_601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__6___boxed(lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v___f_607_, lean_object* v___x_608_, lean_object* v___x_609_, lean_object* v___f_610_, lean_object* v_x_611_, lean_object* v___y_612_){
_start:
{
uint8_t v___x_8095__boxed_613_; lean_object* v_res_614_; 
v___x_8095__boxed_613_ = lean_unbox(v___x_608_);
v_res_614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__6(v_a_605_, v_a_606_, v___f_607_, v___x_8095__boxed_613_, v___x_609_, v___f_610_, v_x_611_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__7___boxed(lean_object* v_i_615_, lean_object* v_a_616_, lean_object* v___x_617_, lean_object* v_a_618_, lean_object* v_as_619_, lean_object* v_sz_620_, lean_object* v_x_621_, lean_object* v___y_622_){
_start:
{
size_t v_i_boxed_623_; size_t v_sz_boxed_624_; lean_object* v_res_625_; 
v_i_boxed_623_ = lean_unbox_usize(v_i_615_);
lean_dec(v_i_615_);
v_sz_boxed_624_ = lean_unbox_usize(v_sz_620_);
lean_dec(v_sz_620_);
v_res_625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__7(v_i_boxed_623_, v_a_616_, v___x_617_, v_a_618_, v_as_619_, v_sz_boxed_624_, v_x_621_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg(lean_object* v_a_626_, lean_object* v___x_627_, lean_object* v_a_628_, lean_object* v_as_629_, size_t v_sz_630_, size_t v_i_631_, lean_object* v_b_632_){
_start:
{
uint8_t v___x_634_; 
v___x_634_ = lean_usize_dec_lt(v_i_631_, v_sz_630_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; 
lean_dec_ref(v_as_629_);
lean_dec(v_a_628_);
lean_dec_ref(v___x_627_);
lean_dec(v_a_626_);
v___x_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_635_, 0, v_b_632_);
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
return v___x_636_;
}
else
{
lean_object* v___x_637_; lean_object* v___f_638_; lean_object* v___f_639_; lean_object* v___x_640_; lean_object* v___f_641_; uint8_t v___x_642_; lean_object* v_a_643_; lean_object* v___x_644_; lean_object* v___f_645_; lean_object* v___x_646_; lean_object* v___f_647_; lean_object* v___x_648_; lean_object* v___f_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___f_656_; lean_object* v___x_657_; 
v___x_637_ = lean_io_promise_new();
lean_inc_n(v_a_626_, 2);
v___f_638_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_638_, 0, v_a_626_);
v___f_639_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_639_, 0, v_a_626_);
v___x_640_ = lean_box(0);
v___f_641_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___closed__0));
v___x_642_ = 0;
v_a_643_ = lean_array_uget_borrowed(v_as_629_, v_i_631_);
v___x_644_ = lean_box(v___x_642_);
lean_inc_n(v_a_643_, 2);
lean_inc_ref(v___x_627_);
v___f_645_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__2___boxed), 7, 5);
lean_closure_set(v___f_645_, 0, v___x_627_);
lean_closure_set(v___f_645_, 1, v___x_640_);
lean_closure_set(v___f_645_, 2, v_a_643_);
lean_closure_set(v___f_645_, 3, v___x_644_);
lean_closure_set(v___f_645_, 4, v___f_639_);
v___x_646_ = lean_box(v___x_642_);
v___f_647_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_647_, 0, v___x_640_);
lean_closure_set(v___f_647_, 1, v___x_646_);
lean_closure_set(v___f_647_, 2, v___f_645_);
lean_closure_set(v___f_647_, 3, v___f_638_);
v___x_648_ = lean_box(v___x_642_);
lean_inc(v_a_628_);
v___f_649_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__6___boxed), 8, 6);
lean_closure_set(v___f_649_, 0, v_a_643_);
lean_closure_set(v___f_649_, 1, v_a_628_);
lean_closure_set(v___f_649_, 2, v___f_647_);
lean_closure_set(v___f_649_, 3, v___x_648_);
lean_closure_set(v___f_649_, 4, v___x_640_);
lean_closure_set(v___f_649_, 5, v___f_641_);
v___x_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_637_);
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
v___x_652_ = lean_unsigned_to_nat(0u);
v___x_653_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_652_, v___x_642_, v___x_651_, v___f_649_);
v___x_654_ = lean_box_usize(v_i_631_);
v___x_655_ = lean_box_usize(v_sz_630_);
v___f_656_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__7___boxed), 8, 6);
lean_closure_set(v___f_656_, 0, v___x_654_);
lean_closure_set(v___f_656_, 1, v_a_626_);
lean_closure_set(v___f_656_, 2, v___x_627_);
lean_closure_set(v___f_656_, 3, v_a_628_);
lean_closure_set(v___f_656_, 4, v_as_629_);
lean_closure_set(v___f_656_, 5, v___x_655_);
v___x_657_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_652_, v___x_642_, v___x_653_, v___f_656_);
return v___x_657_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___lam__7(size_t v_i_658_, lean_object* v_a_659_, lean_object* v___x_660_, lean_object* v_a_661_, lean_object* v_as_662_, size_t v_sz_663_, lean_object* v_x_664_){
_start:
{
if (lean_obj_tag(v_x_664_) == 0)
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_674_; 
lean_dec_ref(v_as_662_);
lean_dec(v_a_661_);
lean_dec_ref(v___x_660_);
lean_dec(v_a_659_);
v_a_666_ = lean_ctor_get(v_x_664_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v_x_664_);
if (v_isSharedCheck_674_ == 0)
{
v___x_668_ = v_x_664_;
v_isShared_669_ = v_isSharedCheck_674_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v_x_664_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_674_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_673_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_672_; 
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
}
}
else
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_694_; 
v_a_675_ = lean_ctor_get(v_x_664_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v_x_664_);
if (v_isSharedCheck_694_ == 0)
{
v___x_677_ = v_x_664_;
v_isShared_678_ = v_isSharedCheck_694_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v_x_664_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_694_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
if (lean_obj_tag(v_a_675_) == 0)
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_689_; 
lean_dec_ref(v_as_662_);
lean_dec(v_a_661_);
lean_dec_ref(v___x_660_);
lean_dec(v_a_659_);
v_a_679_ = lean_ctor_get(v_a_675_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v_a_675_);
if (v_isSharedCheck_689_ == 0)
{
v___x_681_ = v_a_675_;
v_isShared_682_ = v_isSharedCheck_689_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v_a_675_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_689_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v_a_679_);
v___x_684_ = v___x_677_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_688_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
lean_object* v___x_686_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_684_);
v___x_686_ = v___x_681_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
else
{
lean_object* v_a_690_; size_t v___x_691_; size_t v___x_692_; lean_object* v___x_693_; 
lean_del_object(v___x_677_);
v_a_690_ = lean_ctor_get(v_a_675_, 0);
lean_inc(v_a_690_);
lean_dec_ref(v_a_675_);
v___x_691_ = ((size_t)1ULL);
v___x_692_ = lean_usize_add(v_i_658_, v___x_691_);
v___x_693_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg(v_a_659_, v___x_660_, v_a_661_, v_as_662_, v_sz_663_, v___x_692_, v_a_690_);
return v___x_693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg___boxed(lean_object* v_a_695_, lean_object* v___x_696_, lean_object* v_a_697_, lean_object* v_as_698_, lean_object* v_sz_699_, lean_object* v_i_700_, lean_object* v_b_701_, lean_object* v___y_702_){
_start:
{
size_t v_sz_boxed_703_; size_t v_i_boxed_704_; lean_object* v_res_705_; 
v_sz_boxed_703_ = lean_unbox_usize(v_sz_699_);
lean_dec(v_sz_699_);
v_i_boxed_704_ = lean_unbox_usize(v_i_700_);
lean_dec(v_i_700_);
v_res_705_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg(v_a_695_, v___x_696_, v_a_697_, v_as_698_, v_sz_boxed_703_, v_i_boxed_704_, v_b_701_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__3(lean_object* v___x_706_, lean_object* v_a_707_, lean_object* v___x_708_, uint8_t v___x_709_, lean_object* v_x_710_){
_start:
{
if (lean_obj_tag(v_x_710_) == 0)
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_720_; 
lean_dec(v_a_707_);
lean_dec_ref(v___x_706_);
v_a_712_ = lean_ctor_get(v_x_710_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v_x_710_);
if (v_isSharedCheck_720_ == 0)
{
v___x_714_ = v_x_710_;
v_isShared_715_ = v_isSharedCheck_720_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v_x_710_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_720_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_719_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_718_; 
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
return v___x_718_;
}
}
}
else
{
lean_object* v_a_721_; size_t v_sz_722_; size_t v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___f_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v_a_721_ = lean_ctor_get(v_x_710_, 0);
v_sz_722_ = lean_array_size(v___x_706_);
v___x_723_ = ((size_t)0ULL);
lean_inc_ref(v___x_706_);
lean_inc(v_a_721_);
v___x_724_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg(v_a_721_, v___x_706_, v_a_707_, v___x_706_, v_sz_722_, v___x_723_, v___x_708_);
v___x_725_ = lean_box(v___x_709_);
v___f_726_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_726_, 0, v___x_725_);
lean_closure_set(v___f_726_, 1, v_x_710_);
v___x_727_ = lean_unsigned_to_nat(0u);
v___x_728_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_727_, v___x_709_, v___x_724_, v___f_726_);
return v___x_728_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__3___boxed(lean_object* v___x_729_, lean_object* v_a_730_, lean_object* v___x_731_, lean_object* v___x_732_, lean_object* v_x_733_, lean_object* v___y_734_){
_start:
{
uint8_t v___x_8296__boxed_735_; lean_object* v_res_736_; 
v___x_8296__boxed_735_ = lean_unbox(v___x_732_);
v_res_736_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__3(v___x_729_, v_a_730_, v___x_731_, v___x_8296__boxed_735_, v_x_733_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__4(lean_object* v___x_737_, lean_object* v___x_738_, uint8_t v___x_739_, lean_object* v_x_740_){
_start:
{
if (lean_obj_tag(v_x_740_) == 0)
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_750_; 
lean_dec_ref(v___x_737_);
v_a_742_ = lean_ctor_get(v_x_740_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v_x_740_);
if (v_isSharedCheck_750_ == 0)
{
v___x_744_ = v_x_740_;
v_isShared_745_ = v_isSharedCheck_750_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v_x_740_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_750_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_749_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v___x_748_; 
v___x_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
return v___x_748_;
}
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_764_; 
v_a_751_ = lean_ctor_get(v_x_740_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v_x_740_);
if (v_isSharedCheck_764_ == 0)
{
v___x_753_ = v_x_740_;
v_isShared_754_ = v_isSharedCheck_764_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v_x_740_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_764_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___f_757_; lean_object* v___x_759_; 
v___x_755_ = lean_io_promise_new();
v___x_756_ = lean_box(v___x_739_);
v___f_757_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_757_, 0, v___x_737_);
lean_closure_set(v___f_757_, 1, v_a_751_);
lean_closure_set(v___f_757_, 2, v___x_738_);
lean_closure_set(v___f_757_, 3, v___x_756_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v___x_755_);
v___x_759_ = v___x_753_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_755_);
v___x_759_ = v_reuseFailAlloc_763_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
v___x_761_ = lean_unsigned_to_nat(0u);
v___x_762_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_761_, v___x_739_, v___x_760_, v___f_757_);
return v___x_762_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__4___boxed(lean_object* v___x_765_, lean_object* v___x_766_, lean_object* v___x_767_, lean_object* v_x_768_, lean_object* v___y_769_){
_start:
{
uint8_t v___x_8345__boxed_770_; lean_object* v_res_771_; 
v___x_8345__boxed_770_ = lean_unbox(v___x_767_);
v_res_771_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__4(v___x_765_, v___x_766_, v___x_8345__boxed_770_, v_x_768_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__5(lean_object* v___x_772_, lean_object* v___x_773_, lean_object* v_x_774_){
_start:
{
if (lean_obj_tag(v_x_774_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_784_; 
lean_dec_ref(v___x_772_);
v_a_776_ = lean_ctor_get(v_x_774_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v_x_774_);
if (v_isSharedCheck_784_ == 0)
{
v___x_778_ = v_x_774_;
v_isShared_779_ = v_isSharedCheck_784_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v_x_774_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_784_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_783_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; 
v___x_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
return v___x_782_;
}
}
}
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_812_; 
v_a_785_ = lean_ctor_get(v_x_774_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v_x_774_);
if (v_isSharedCheck_812_ == 0)
{
v___x_787_ = v_x_774_;
v_isShared_788_ = v_isSharedCheck_812_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v_x_774_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_812_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v_fst_789_; 
v_fst_789_ = lean_ctor_get(v_a_785_, 0);
lean_inc(v_fst_789_);
lean_dec(v_a_785_);
if (lean_obj_tag(v_fst_789_) == 0)
{
uint8_t v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___f_794_; lean_object* v___x_796_; 
v___x_790_ = 0;
v___x_791_ = lean_box(v___x_790_);
v___x_792_ = lean_st_mk_ref(v___x_791_);
v___x_793_ = lean_box(v___x_790_);
v___f_794_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_794_, 0, v___x_772_);
lean_closure_set(v___f_794_, 1, v___x_773_);
lean_closure_set(v___f_794_, 2, v___x_793_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_792_);
v___x_796_ = v___x_787_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_792_);
v___x_796_ = v_reuseFailAlloc_800_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_798_, v___x_790_, v___x_797_, v___f_794_);
return v___x_799_;
}
}
else
{
lean_object* v_val_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_811_; 
lean_dec_ref(v___x_772_);
v_val_801_ = lean_ctor_get(v_fst_789_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v_fst_789_);
if (v_isSharedCheck_811_ == 0)
{
v___x_803_ = v_fst_789_;
v_isShared_804_ = v_isSharedCheck_811_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_val_801_);
lean_dec(v_fst_789_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_811_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v_val_801_);
v___x_806_ = v___x_787_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_val_801_);
v___x_806_ = v_reuseFailAlloc_810_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_808_; 
if (v_isShared_804_ == 0)
{
lean_ctor_set_tag(v___x_803_, 0);
lean_ctor_set(v___x_803_, 0, v___x_806_);
v___x_808_ = v___x_803_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__5___boxed(lean_object* v___x_813_, lean_object* v___x_814_, lean_object* v_x_815_, lean_object* v___y_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__5(v___x_813_, v___x_814_, v_x_815_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__0(lean_object* v___x_818_, lean_object* v_x_819_){
_start:
{
if (lean_obj_tag(v_x_819_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_829_; 
v_a_821_ = lean_ctor_get(v_x_819_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v_x_819_);
if (v_isSharedCheck_829_ == 0)
{
v___x_823_ = v_x_819_;
v_isShared_824_ = v_isSharedCheck_829_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v_x_819_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_829_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_828_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_827_; 
v___x_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
return v___x_827_;
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_841_; 
v_a_830_ = lean_ctor_get(v_x_819_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v_x_819_);
if (v_isSharedCheck_841_ == 0)
{
v___x_832_ = v_x_819_;
v_isShared_833_ = v_isSharedCheck_841_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v_x_819_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_841_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_834_, 0, v_a_830_);
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v___x_818_);
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 0, v___x_836_);
v___x_838_ = v___x_832_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_836_);
v___x_838_ = v_reuseFailAlloc_840_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_839_; 
v___x_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
return v___x_839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__0___boxed(lean_object* v___x_842_, lean_object* v_x_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__0(v___x_842_, v_x_843_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__1(lean_object* v_a_846_, lean_object* v___f_847_, lean_object* v___x_848_, lean_object* v_x_849_){
_start:
{
if (lean_obj_tag(v_x_849_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_859_; 
lean_dec_ref(v___x_848_);
lean_dec_ref(v___f_847_);
lean_dec_ref(v_a_846_);
v_a_851_ = lean_ctor_get(v_x_849_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v_x_849_);
if (v_isSharedCheck_859_ == 0)
{
v___x_853_ = v_x_849_;
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v_x_849_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_858_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_857_; 
v___x_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
return v___x_857_;
}
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_875_; 
v_a_860_ = lean_ctor_get(v_x_849_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v_x_849_);
if (v_isSharedCheck_875_ == 0)
{
v___x_862_ = v_x_849_;
v_isShared_863_ = v_isSharedCheck_875_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v_x_849_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_875_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
if (lean_obj_tag(v_a_860_) == 1)
{
lean_object* v_val_864_; lean_object* v_cont_865_; lean_object* v___x_866_; lean_object* v___x_867_; uint8_t v___x_868_; lean_object* v___x_869_; 
lean_del_object(v___x_862_);
lean_dec_ref(v___x_848_);
v_val_864_ = lean_ctor_get(v_a_860_, 0);
lean_inc(v_val_864_);
lean_dec_ref(v_a_860_);
v_cont_865_ = lean_ctor_get(v_a_846_, 1);
lean_inc_ref(v_cont_865_);
lean_dec_ref(v_a_846_);
v___x_866_ = lean_apply_2(v_cont_865_, v_val_864_, lean_box(0));
v___x_867_ = lean_unsigned_to_nat(0u);
v___x_868_ = 0;
v___x_869_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_867_, v___x_868_, v___x_866_, v___f_847_);
return v___x_869_;
}
else
{
lean_object* v___x_870_; lean_object* v___x_872_; 
lean_dec(v_a_860_);
lean_dec_ref(v___f_847_);
lean_dec_ref(v_a_846_);
v___x_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_848_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v___x_870_);
v___x_872_ = v___x_862_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_874_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_873_; 
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
return v___x_873_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__1___boxed(lean_object* v_a_876_, lean_object* v___f_877_, lean_object* v___x_878_, lean_object* v_x_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__1(v_a_876_, v___f_877_, v___x_878_, v_x_879_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__2___boxed(lean_object* v_i_887_, lean_object* v_as_888_, lean_object* v_sz_889_, lean_object* v_x_890_, lean_object* v___y_891_){
_start:
{
size_t v_i_boxed_892_; size_t v_sz_boxed_893_; lean_object* v_res_894_; 
v_i_boxed_892_ = lean_unbox_usize(v_i_887_);
lean_dec(v_i_887_);
v_sz_boxed_893_ = lean_unbox_usize(v_sz_889_);
lean_dec(v_sz_889_);
v_res_894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__2(v_i_boxed_892_, v_as_888_, v_sz_boxed_893_, v_x_890_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg(lean_object* v_as_895_, size_t v_sz_896_, size_t v_i_897_, lean_object* v_b_898_){
_start:
{
uint8_t v___x_900_; 
v___x_900_ = lean_usize_dec_lt(v_i_897_, v_sz_896_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; lean_object* v___x_902_; 
lean_dec_ref(v_as_895_);
v___x_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_901_, 0, v_b_898_);
v___x_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
return v___x_902_;
}
else
{
lean_object* v_a_903_; lean_object* v_selector_904_; lean_object* v_tryFn_905_; lean_object* v___x_906_; lean_object* v___f_907_; lean_object* v___x_908_; lean_object* v___f_909_; lean_object* v___x_910_; uint8_t v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___f_915_; lean_object* v___x_916_; 
lean_dec_ref(v_b_898_);
v_a_903_ = lean_array_uget_borrowed(v_as_895_, v_i_897_);
v_selector_904_ = lean_ctor_get(v_a_903_, 0);
v_tryFn_905_ = lean_ctor_get(v_selector_904_, 0);
lean_inc_ref(v_tryFn_905_);
v___x_906_ = lean_apply_1(v_tryFn_905_, lean_box(0));
v___f_907_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__0));
v___x_908_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__1));
lean_inc(v_a_903_);
v___f_909_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_909_, 0, v_a_903_);
lean_closure_set(v___f_909_, 1, v___f_907_);
lean_closure_set(v___f_909_, 2, v___x_908_);
v___x_910_ = lean_unsigned_to_nat(0u);
v___x_911_ = 0;
v___x_912_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_910_, v___x_911_, v___x_906_, v___f_909_);
v___x_913_ = lean_box_usize(v_i_897_);
v___x_914_ = lean_box_usize(v_sz_896_);
v___f_915_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_915_, 0, v___x_913_);
lean_closure_set(v___f_915_, 1, v_as_895_);
lean_closure_set(v___f_915_, 2, v___x_914_);
v___x_916_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_910_, v___x_911_, v___x_912_, v___f_915_);
return v___x_916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___lam__2(size_t v_i_917_, lean_object* v_as_918_, size_t v_sz_919_, lean_object* v_x_920_){
_start:
{
if (lean_obj_tag(v_x_920_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_930_; 
lean_dec_ref(v_as_918_);
v_a_922_ = lean_ctor_get(v_x_920_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v_x_920_);
if (v_isSharedCheck_930_ == 0)
{
v___x_924_ = v_x_920_;
v_isShared_925_ = v_isSharedCheck_930_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v_x_920_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_930_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_929_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_928_; 
v___x_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
return v___x_928_;
}
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_950_; 
v_a_931_ = lean_ctor_get(v_x_920_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v_x_920_);
if (v_isSharedCheck_950_ == 0)
{
v___x_933_ = v_x_920_;
v_isShared_934_ = v_isSharedCheck_950_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v_x_920_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_950_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
if (lean_obj_tag(v_a_931_) == 0)
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_945_; 
lean_dec_ref(v_as_918_);
v_a_935_ = lean_ctor_get(v_a_931_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v_a_931_);
if (v_isSharedCheck_945_ == 0)
{
v___x_937_ = v_a_931_;
v_isShared_938_ = v_isSharedCheck_945_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v_a_931_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_945_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v_a_935_);
v___x_940_ = v___x_933_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_944_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_942_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v___x_940_);
v___x_942_ = v___x_937_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_940_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
else
{
lean_object* v_a_946_; size_t v___x_947_; size_t v___x_948_; lean_object* v___x_949_; 
lean_del_object(v___x_933_);
v_a_946_ = lean_ctor_get(v_a_931_, 0);
lean_inc(v_a_946_);
lean_dec_ref(v_a_931_);
v___x_947_ = ((size_t)1ULL);
v___x_948_ = lean_usize_add(v_i_917_, v___x_947_);
v___x_949_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg(v_as_918_, v_sz_919_, v___x_948_, v_a_946_);
return v___x_949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___boxed(lean_object* v_as_951_, lean_object* v_sz_952_, lean_object* v_i_953_, lean_object* v_b_954_, lean_object* v___y_955_){
_start:
{
size_t v_sz_boxed_956_; size_t v_i_boxed_957_; lean_object* v_res_958_; 
v_sz_boxed_956_ = lean_unbox_usize(v_sz_952_);
lean_dec(v_sz_952_);
v_i_boxed_957_ = lean_unbox_usize(v_i_953_);
lean_dec(v_i_953_);
v_res_958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg(v_as_951_, v_sz_boxed_956_, v_i_boxed_957_, v_b_954_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__6(lean_object* v_selectables_959_, lean_object* v_x_960_){
_start:
{
if (lean_obj_tag(v_x_960_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_970_; 
lean_dec_ref(v_selectables_959_);
v_a_962_ = lean_ctor_get(v_x_960_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v_x_960_);
if (v_isSharedCheck_970_ == 0)
{
v___x_964_ = v_x_960_;
v_isShared_965_ = v_isSharedCheck_970_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v_x_960_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_970_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_969_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
lean_object* v___x_968_; 
v___x_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
return v___x_968_;
}
}
}
else
{
lean_object* v_a_971_; uint64_t v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; size_t v_sz_978_; size_t v___x_979_; lean_object* v___x_980_; lean_object* v___f_981_; lean_object* v___x_982_; uint8_t v___x_983_; lean_object* v___x_984_; 
v_a_971_ = lean_ctor_get(v_x_960_, 0);
lean_inc(v_a_971_);
lean_dec_ref(v_x_960_);
v___x_972_ = l_ByteArray_toUInt64LE_x21(v_a_971_);
lean_dec(v_a_971_);
v___x_973_ = lean_uint64_to_nat(v___x_972_);
v___x_974_ = l_mkStdGen(v___x_973_);
lean_dec(v___x_973_);
v___x_975_ = l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt___redArg(v_selectables_959_, v___x_974_);
v___x_976_ = lean_box(0);
v___x_977_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg___closed__1));
v_sz_978_ = lean_array_size(v___x_975_);
v___x_979_ = ((size_t)0ULL);
lean_inc_ref(v___x_975_);
v___x_980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg(v___x_975_, v_sz_978_, v___x_979_, v___x_977_);
v___f_981_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_981_, 0, v___x_975_);
lean_closure_set(v___f_981_, 1, v___x_976_);
v___x_982_ = lean_unsigned_to_nat(0u);
v___x_983_ = 0;
v___x_984_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_982_, v___x_983_, v___x_980_, v___f_981_);
return v___x_984_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__6___boxed(lean_object* v_selectables_985_, lean_object* v_x_986_, lean_object* v___y_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__6(v_selectables_985_, v_x_986_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__7(lean_object* v___f_989_, lean_object* v_____r_990_){
_start:
{
lean_object* v_val_993_; size_t v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((size_t)8ULL);
v___x_999_ = lean_io_get_random_bytes(v___x_998_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
lean_ctor_set_tag(v___x_1002_, 1);
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
v_val_993_ = v___x_1005_;
goto v___jp_992_;
}
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
v_a_1008_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_999_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_999_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
lean_ctor_set_tag(v___x_1010_, 0);
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
v_val_993_ = v___x_1013_;
goto v___jp_992_;
}
}
}
v___jp_992_:
{
lean_object* v___x_994_; lean_object* v___x_995_; uint8_t v___x_996_; lean_object* v___x_997_; 
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v_val_993_);
v___x_995_ = lean_unsigned_to_nat(0u);
v___x_996_ = 0;
v___x_997_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_995_, v___x_996_, v___x_994_, v___f_989_);
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__7___boxed(lean_object* v___f_1016_, lean_object* v_____r_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__7(v___f_1016_, v_____r_1017_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__8(lean_object* v___f_1020_, lean_object* v_x_1021_){
_start:
{
if (lean_obj_tag(v_x_1021_) == 0)
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1031_; 
lean_dec_ref(v___f_1020_);
v_a_1023_ = lean_ctor_get(v_x_1021_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_x_1021_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1025_ = v_x_1021_;
v_isShared_1026_ = v_isSharedCheck_1031_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v_x_1021_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1031_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
return v___x_1029_;
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1033_; 
v_a_1032_ = lean_ctor_get(v_x_1021_, 0);
lean_inc(v_a_1032_);
lean_dec_ref(v_x_1021_);
v___x_1033_ = lean_apply_2(v___f_1020_, v_a_1032_, lean_box(0));
return v___x_1033_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___lam__8___boxed(lean_object* v___f_1034_, lean_object* v_x_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__8(v___f_1034_, v_x_1035_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg(lean_object* v_selectables_1045_){
_start:
{
lean_object* v___f_1047_; lean_object* v___f_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; uint8_t v___x_1051_; 
lean_inc_ref(v_selectables_1045_);
v___f_1047_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__6___boxed), 3, 1);
lean_closure_set(v___f_1047_, 0, v_selectables_1045_);
lean_inc_ref(v___f_1047_);
v___f_1048_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_1048_, 0, v___f_1047_);
v___x_1049_ = lean_array_get_size(v_selectables_1045_);
lean_dec_ref(v_selectables_1045_);
v___x_1050_ = lean_unsigned_to_nat(0u);
v___x_1051_ = lean_nat_dec_eq(v___x_1049_, v___x_1050_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
lean_dec_ref(v___f_1048_);
v___x_1052_ = lean_box(0);
v___x_1053_ = l_Std_Internal_IO_Async_Selectable_one___redArg___lam__7(v___f_1047_, v___x_1052_);
return v___x_1053_;
}
else
{
lean_object* v___f_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; lean_object* v___x_1057_; 
lean_dec_ref(v___f_1047_);
v___f_1054_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_one___redArg___lam__8___boxed), 3, 1);
lean_closure_set(v___f_1054_, 0, v___f_1048_);
v___x_1055_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_one___redArg___closed__3));
v___x_1056_ = 0;
v___x_1057_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1050_, v___x_1056_, v___x_1055_, v___f_1054_);
return v___x_1057_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___redArg___boxed(lean_object* v_selectables_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Std_Internal_IO_Async_Selectable_one___redArg(v_selectables_1058_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one(lean_object* v_00_u03b1_1061_, lean_object* v_selectables_1062_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Std_Internal_IO_Async_Selectable_one___redArg(v_selectables_1062_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_one___boxed(lean_object* v_00_u03b1_1065_, lean_object* v_selectables_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Std_Internal_IO_Async_Selectable_one(v_00_u03b1_1065_, v_selectables_1066_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0(lean_object* v_00_u03b1_1069_, lean_object* v_as_1070_, size_t v_sz_1071_, size_t v_i_1072_, lean_object* v_b_1073_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg(v_as_1070_, v_sz_1071_, v_i_1072_, v_b_1073_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___boxed(lean_object* v_00_u03b1_1076_, lean_object* v_as_1077_, lean_object* v_sz_1078_, lean_object* v_i_1079_, lean_object* v_b_1080_, lean_object* v___y_1081_){
_start:
{
size_t v_sz_boxed_1082_; size_t v_i_boxed_1083_; lean_object* v_res_1084_; 
v_sz_boxed_1082_ = lean_unbox_usize(v_sz_1078_);
lean_dec(v_sz_1078_);
v_i_boxed_1083_ = lean_unbox_usize(v_i_1079_);
lean_dec(v_i_1079_);
v_res_1084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0(v_00_u03b1_1076_, v_as_1077_, v_sz_boxed_1082_, v_i_boxed_1083_, v_b_1080_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2(lean_object* v_00_u03b1_1085_, lean_object* v_a_1086_, lean_object* v___x_1087_, lean_object* v_a_1088_, lean_object* v_as_1089_, size_t v_sz_1090_, size_t v_i_1091_, lean_object* v_b_1092_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___redArg(v_a_1086_, v___x_1087_, v_a_1088_, v_as_1089_, v_sz_1090_, v_i_1091_, v_b_1092_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2___boxed(lean_object* v_00_u03b1_1095_, lean_object* v_a_1096_, lean_object* v___x_1097_, lean_object* v_a_1098_, lean_object* v_as_1099_, lean_object* v_sz_1100_, lean_object* v_i_1101_, lean_object* v_b_1102_, lean_object* v___y_1103_){
_start:
{
size_t v_sz_boxed_1104_; size_t v_i_boxed_1105_; lean_object* v_res_1106_; 
v_sz_boxed_1104_ = lean_unbox_usize(v_sz_1100_);
lean_dec(v_sz_1100_);
v_i_boxed_1105_ = lean_unbox_usize(v_i_1101_);
lean_dec(v_i_1101_);
v_res_1106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__2(v_00_u03b1_1095_, v_a_1096_, v___x_1097_, v_a_1098_, v_as_1099_, v_sz_boxed_1104_, v_i_boxed_1105_, v_b_1102_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3(lean_object* v_00_u03b1_1107_, lean_object* v_as_1108_, size_t v_sz_1109_, size_t v_i_1110_, lean_object* v_b_1111_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___redArg(v_as_1108_, v_sz_1109_, v_i_1110_, v_b_1111_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3___boxed(lean_object* v_00_u03b1_1114_, lean_object* v_as_1115_, lean_object* v_sz_1116_, lean_object* v_i_1117_, lean_object* v_b_1118_, lean_object* v___y_1119_){
_start:
{
size_t v_sz_boxed_1120_; size_t v_i_boxed_1121_; lean_object* v_res_1122_; 
v_sz_boxed_1120_ = lean_unbox_usize(v_sz_1116_);
lean_dec(v_sz_1116_);
v_i_boxed_1121_ = lean_unbox_usize(v_i_1117_);
lean_dec(v_i_1117_);
v_res_1122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__3(v_00_u03b1_1114_, v_as_1115_, v_sz_boxed_1120_, v_i_boxed_1121_, v_b_1118_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0(lean_object* v_x_1127_){
_start:
{
if (lean_obj_tag(v_x_1127_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1137_; 
v_a_1129_ = lean_ctor_get(v_x_1127_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_x_1127_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1131_ = v_x_1127_;
v_isShared_1132_ = v_isSharedCheck_1137_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v_x_1127_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1137_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
return v___x_1135_;
}
}
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1155_; 
v_a_1138_ = lean_ctor_get(v_x_1127_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_x_1127_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1140_ = v_x_1127_;
v_isShared_1141_ = v_isSharedCheck_1155_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v_x_1127_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1155_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v_fst_1142_; 
v_fst_1142_ = lean_ctor_get(v_a_1138_, 0);
lean_inc(v_fst_1142_);
lean_dec(v_a_1138_);
if (lean_obj_tag(v_fst_1142_) == 0)
{
lean_object* v___x_1143_; 
lean_del_object(v___x_1140_);
v___x_1143_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0___closed__1));
return v___x_1143_;
}
else
{
lean_object* v_val_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1154_; 
v_val_1144_ = lean_ctor_get(v_fst_1142_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_fst_1142_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1146_ = v_fst_1142_;
v_isShared_1147_ = v_isSharedCheck_1154_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_val_1144_);
lean_dec(v_fst_1142_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1154_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v_val_1144_);
v___x_1149_ = v___x_1140_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_val_1144_);
v___x_1149_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1151_; 
if (v_isShared_1147_ == 0)
{
lean_ctor_set_tag(v___x_1146_, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1149_);
v___x_1151_ = v___x_1146_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0___boxed(lean_object* v_x_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0(v_x_1156_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__1(lean_object* v_a_1159_, lean_object* v___x_1160_, uint8_t v___x_1161_, lean_object* v___f_1162_, lean_object* v___x_1163_, lean_object* v_x_1164_){
_start:
{
if (lean_obj_tag(v_x_1164_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1174_; 
lean_dec_ref(v___x_1163_);
lean_dec_ref(v___f_1162_);
lean_dec(v___x_1160_);
lean_dec_ref(v_a_1159_);
v_a_1166_ = lean_ctor_get(v_x_1164_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_x_1164_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1168_ = v_x_1164_;
v_isShared_1169_ = v_isSharedCheck_1174_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v_x_1164_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1174_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
lean_object* v___x_1172_; 
v___x_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
return v___x_1172_;
}
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1188_; 
v_a_1175_ = lean_ctor_get(v_x_1164_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v_x_1164_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1177_ = v_x_1164_;
v_isShared_1178_ = v_isSharedCheck_1188_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v_x_1164_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1188_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
if (lean_obj_tag(v_a_1175_) == 1)
{
lean_object* v_val_1179_; lean_object* v_cont_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
lean_del_object(v___x_1177_);
lean_dec_ref(v___x_1163_);
v_val_1179_ = lean_ctor_get(v_a_1175_, 0);
lean_inc(v_val_1179_);
lean_dec_ref(v_a_1175_);
v_cont_1180_ = lean_ctor_get(v_a_1159_, 1);
lean_inc_ref(v_cont_1180_);
lean_dec_ref(v_a_1159_);
v___x_1181_ = lean_apply_2(v_cont_1180_, v_val_1179_, lean_box(0));
v___x_1182_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1160_, v___x_1161_, v___x_1181_, v___f_1162_);
return v___x_1182_;
}
else
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
lean_dec(v_a_1175_);
lean_dec_ref(v___f_1162_);
lean_dec(v___x_1160_);
lean_dec_ref(v_a_1159_);
v___x_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1163_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v___x_1183_);
v___x_1185_ = v___x_1177_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
lean_object* v___x_1186_; 
v___x_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
return v___x_1186_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__1___boxed(lean_object* v_a_1189_, lean_object* v___x_1190_, lean_object* v___x_1191_, lean_object* v___f_1192_, lean_object* v___x_1193_, lean_object* v_x_1194_, lean_object* v___y_1195_){
_start:
{
uint8_t v___x_2272__boxed_1196_; lean_object* v_res_1197_; 
v___x_2272__boxed_1196_ = lean_unbox(v___x_1191_);
v_res_1197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__1(v_a_1189_, v___x_1190_, v___x_2272__boxed_1196_, v___f_1192_, v___x_1193_, v_x_1194_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__0(lean_object* v___x_1198_, lean_object* v_x_1199_){
_start:
{
if (lean_obj_tag(v_x_1199_) == 0)
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1209_; 
v_a_1201_ = lean_ctor_get(v_x_1199_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_x_1199_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1203_ = v_x_1199_;
v_isShared_1204_ = v_isSharedCheck_1209_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v_x_1199_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1209_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
return v___x_1207_;
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1222_; 
v_a_1210_ = lean_ctor_get(v_x_1199_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_x_1199_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1212_ = v_x_1199_;
v_isShared_1213_ = v_isSharedCheck_1222_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v_x_1199_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1222_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1214_, 0, v_a_1210_);
v___x_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
lean_ctor_set(v___x_1216_, 1, v___x_1198_);
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 0, v___x_1217_);
v___x_1219_ = v___x_1212_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v___x_1220_; 
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__0___boxed(lean_object* v___x_1223_, lean_object* v_x_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__0(v___x_1223_, v_x_1224_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__2___boxed(lean_object* v_i_1232_, lean_object* v___x_1233_, lean_object* v_as_1234_, lean_object* v_sz_1235_, lean_object* v_x_1236_, lean_object* v___y_1237_){
_start:
{
size_t v_i_boxed_1238_; size_t v_sz_boxed_1239_; lean_object* v_res_1240_; 
v_i_boxed_1238_ = lean_unbox_usize(v_i_1232_);
lean_dec(v_i_1232_);
v_sz_boxed_1239_ = lean_unbox_usize(v_sz_1235_);
lean_dec(v_sz_1235_);
v_res_1240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__2(v_i_boxed_1238_, v___x_1233_, v_as_1234_, v_sz_boxed_1239_, v_x_1236_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(lean_object* v___x_1241_, lean_object* v_as_1242_, size_t v_sz_1243_, size_t v_i_1244_, lean_object* v_b_1245_){
_start:
{
uint8_t v___x_1247_; 
v___x_1247_ = lean_usize_dec_lt(v_i_1244_, v_sz_1243_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
lean_dec_ref(v_as_1242_);
lean_dec(v___x_1241_);
v___x_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1248_, 0, v_b_1245_);
v___x_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
return v___x_1249_;
}
else
{
lean_object* v_a_1250_; lean_object* v_selector_1251_; lean_object* v_tryFn_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; lean_object* v___f_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___f_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___f_1263_; uint8_t v___x_1264_; lean_object* v___x_1265_; 
lean_dec_ref(v_b_1245_);
v_a_1250_ = lean_array_uget_borrowed(v_as_1242_, v_i_1244_);
v_selector_1251_ = lean_ctor_get(v_a_1250_, 0);
v_tryFn_1252_ = lean_ctor_get(v_selector_1251_, 0);
lean_inc_ref(v_tryFn_1252_);
v___x_1253_ = lean_apply_1(v_tryFn_1252_, lean_box(0));
v___x_1254_ = lean_unsigned_to_nat(0u);
v___x_1255_ = lean_nat_dec_eq(v___x_1241_, v___x_1254_);
v___f_1256_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__0));
v___x_1257_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__1));
v___x_1258_ = lean_box(v___x_1255_);
lean_inc(v_a_1250_);
v___f_1259_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_1259_, 0, v_a_1250_);
lean_closure_set(v___f_1259_, 1, v___x_1254_);
lean_closure_set(v___f_1259_, 2, v___x_1258_);
lean_closure_set(v___f_1259_, 3, v___f_1256_);
lean_closure_set(v___f_1259_, 4, v___x_1257_);
v___x_1260_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1254_, v___x_1255_, v___x_1253_, v___f_1259_);
v___x_1261_ = lean_box_usize(v_i_1244_);
v___x_1262_ = lean_box_usize(v_sz_1243_);
v___f_1263_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_1263_, 0, v___x_1261_);
lean_closure_set(v___f_1263_, 1, v___x_1241_);
lean_closure_set(v___f_1263_, 2, v_as_1242_);
lean_closure_set(v___f_1263_, 3, v___x_1262_);
v___x_1264_ = 0;
v___x_1265_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1254_, v___x_1264_, v___x_1260_, v___f_1263_);
return v___x_1265_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___lam__2(size_t v_i_1266_, lean_object* v___x_1267_, lean_object* v_as_1268_, size_t v_sz_1269_, lean_object* v_x_1270_){
_start:
{
if (lean_obj_tag(v_x_1270_) == 0)
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1280_; 
lean_dec_ref(v_as_1268_);
lean_dec(v___x_1267_);
v_a_1272_ = lean_ctor_get(v_x_1270_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_x_1270_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1274_ = v_x_1270_;
v_isShared_1275_ = v_isSharedCheck_1280_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v_x_1270_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1280_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
lean_object* v___x_1278_; 
v___x_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
return v___x_1278_;
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1300_; 
v_a_1281_ = lean_ctor_get(v_x_1270_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_x_1270_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1283_ = v_x_1270_;
v_isShared_1284_ = v_isSharedCheck_1300_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v_x_1270_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1300_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
if (lean_obj_tag(v_a_1281_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v_as_1268_);
lean_dec(v___x_1267_);
v_a_1285_ = lean_ctor_get(v_a_1281_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_a_1281_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1287_ = v_a_1281_;
v_isShared_1288_ = v_isSharedCheck_1295_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v_a_1281_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1295_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v_a_1285_);
v___x_1290_ = v___x_1283_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
lean_object* v___x_1292_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v___x_1290_);
v___x_1292_ = v___x_1287_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1290_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
else
{
lean_object* v_a_1296_; size_t v___x_1297_; size_t v___x_1298_; lean_object* v___x_1299_; 
lean_del_object(v___x_1283_);
v_a_1296_ = lean_ctor_get(v_a_1281_, 0);
lean_inc(v_a_1296_);
lean_dec_ref(v_a_1281_);
v___x_1297_ = ((size_t)1ULL);
v___x_1298_ = lean_usize_add(v_i_1266_, v___x_1297_);
v___x_1299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(v___x_1267_, v_as_1268_, v_sz_1269_, v___x_1298_, v_a_1296_);
return v___x_1299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___boxed(lean_object* v___x_1301_, lean_object* v_as_1302_, lean_object* v_sz_1303_, lean_object* v_i_1304_, lean_object* v_b_1305_, lean_object* v___y_1306_){
_start:
{
size_t v_sz_boxed_1307_; size_t v_i_boxed_1308_; lean_object* v_res_1309_; 
v_sz_boxed_1307_ = lean_unbox_usize(v_sz_1303_);
lean_dec(v_sz_1303_);
v_i_boxed_1308_ = lean_unbox_usize(v_i_1304_);
lean_dec(v_i_1304_);
v_res_1309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(v___x_1301_, v_as_1302_, v_sz_boxed_1307_, v_i_boxed_1308_, v_b_1305_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__1(lean_object* v_selectables_1310_, lean_object* v___x_1311_, lean_object* v___x_1312_, uint8_t v___x_1313_, lean_object* v___f_1314_, lean_object* v_x_1315_){
_start:
{
if (lean_obj_tag(v_x_1315_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1325_; 
lean_dec_ref(v___f_1314_);
lean_dec(v___x_1312_);
lean_dec(v___x_1311_);
lean_dec_ref(v_selectables_1310_);
v_a_1317_ = lean_ctor_get(v_x_1315_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_x_1315_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1319_ = v_x_1315_;
v_isShared_1320_ = v_isSharedCheck_1325_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v_x_1315_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1325_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
lean_object* v___x_1323_; 
v___x_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
return v___x_1323_;
}
}
}
else
{
lean_object* v_a_1326_; uint64_t v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; size_t v_sz_1332_; size_t v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v_a_1326_ = lean_ctor_get(v_x_1315_, 0);
lean_inc(v_a_1326_);
lean_dec_ref(v_x_1315_);
v___x_1327_ = l_ByteArray_toUInt64LE_x21(v_a_1326_);
lean_dec(v_a_1326_);
v___x_1328_ = lean_uint64_to_nat(v___x_1327_);
v___x_1329_ = l_mkStdGen(v___x_1328_);
lean_dec(v___x_1328_);
v___x_1330_ = l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt___redArg(v_selectables_1310_, v___x_1329_);
v___x_1331_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__1));
v_sz_1332_ = lean_array_size(v___x_1330_);
v___x_1333_ = ((size_t)0ULL);
v___x_1334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(v___x_1311_, v___x_1330_, v_sz_1332_, v___x_1333_, v___x_1331_);
v___x_1335_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1312_, v___x_1313_, v___x_1334_, v___f_1314_);
return v___x_1335_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__1___boxed(lean_object* v_selectables_1336_, lean_object* v___x_1337_, lean_object* v___x_1338_, lean_object* v___x_1339_, lean_object* v___f_1340_, lean_object* v_x_1341_, lean_object* v___y_1342_){
_start:
{
uint8_t v___x_2511__boxed_1343_; lean_object* v_res_1344_; 
v___x_2511__boxed_1343_ = lean_unbox(v___x_1339_);
v_res_1344_ = l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__1(v_selectables_1336_, v___x_1337_, v___x_1338_, v___x_2511__boxed_1343_, v___f_1340_, v_x_1341_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg(lean_object* v_selectables_1346_){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; uint8_t v___x_1350_; 
v___x_1348_ = lean_array_get_size(v_selectables_1346_);
v___x_1349_ = lean_unsigned_to_nat(0u);
v___x_1350_ = lean_nat_dec_eq(v___x_1348_, v___x_1349_);
if (v___x_1350_ == 0)
{
lean_object* v___f_1351_; lean_object* v___x_1352_; lean_object* v___f_1353_; lean_object* v_val_1355_; size_t v___x_1358_; lean_object* v___x_1359_; 
v___f_1351_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_tryOne___redArg___closed__0));
v___x_1352_ = lean_box(v___x_1350_);
v___f_1353_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_1353_, 0, v_selectables_1346_);
lean_closure_set(v___f_1353_, 1, v___x_1348_);
lean_closure_set(v___f_1353_, 2, v___x_1349_);
lean_closure_set(v___f_1353_, 3, v___x_1352_);
lean_closure_set(v___f_1353_, 4, v___f_1351_);
v___x_1358_ = ((size_t)8ULL);
v___x_1359_ = lean_io_get_random_bytes(v___x_1358_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1359_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1359_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
lean_ctor_set_tag(v___x_1362_, 1);
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
v_val_1355_ = v___x_1365_;
goto v___jp_1354_;
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
v_a_1368_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1359_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1359_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
lean_ctor_set_tag(v___x_1370_, 0);
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
v_val_1355_ = v___x_1373_;
goto v___jp_1354_;
}
}
}
v___jp_1354_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v_val_1355_);
v___x_1357_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1349_, v___x_1350_, v___x_1356_, v___f_1353_);
return v___x_1357_;
}
}
else
{
lean_object* v___x_1376_; 
lean_dec_ref(v_selectables_1346_);
v___x_1376_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_tryOne___redArg___lam__0___closed__1));
return v___x_1376_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___redArg___boxed(lean_object* v_selectables_1377_, lean_object* v_a_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Std_Internal_IO_Async_Selectable_tryOne___redArg(v_selectables_1377_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne(lean_object* v_00_u03b1_1380_, lean_object* v_selectables_1381_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Std_Internal_IO_Async_Selectable_tryOne___redArg(v_selectables_1381_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_tryOne___boxed(lean_object* v_00_u03b1_1384_, lean_object* v_selectables_1385_, lean_object* v_a_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Std_Internal_IO_Async_Selectable_tryOne(v_00_u03b1_1384_, v_selectables_1385_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0(lean_object* v_00_u03b1_1388_, lean_object* v___x_1389_, lean_object* v_as_1390_, size_t v_sz_1391_, size_t v_i_1392_, lean_object* v_b_1393_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(v___x_1389_, v_as_1390_, v_sz_1391_, v_i_1392_, v_b_1393_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___boxed(lean_object* v_00_u03b1_1396_, lean_object* v___x_1397_, lean_object* v_as_1398_, lean_object* v_sz_1399_, lean_object* v_i_1400_, lean_object* v_b_1401_, lean_object* v___y_1402_){
_start:
{
size_t v_sz_boxed_1403_; size_t v_i_boxed_1404_; lean_object* v_res_1405_; 
v_sz_boxed_1403_ = lean_unbox_usize(v_sz_1399_);
lean_dec(v_sz_1399_);
v_i_boxed_1404_ = lean_unbox_usize(v_i_1400_);
lean_dec(v_i_1400_);
v_res_1405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0(v_00_u03b1_1396_, v___x_1397_, v_as_1398_, v_sz_boxed_1403_, v_i_boxed_1404_, v_b_1401_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__1(lean_object* v___x_1406_, lean_object* v_x_1407_){
_start:
{
if (lean_obj_tag(v_x_1407_) == 0)
{
lean_object* v___x_1409_; 
v___x_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1409_, 0, v_x_1407_);
return v___x_1409_;
}
else
{
lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1417_; 
v_isSharedCheck_1417_ = !lean_is_exclusive(v_x_1407_);
if (v_isSharedCheck_1417_ == 0)
{
lean_object* v_unused_1418_; 
v_unused_1418_ = lean_ctor_get(v_x_1407_, 0);
lean_dec(v_unused_1418_);
v___x_1411_ = v_x_1407_;
v_isShared_1412_ = v_isSharedCheck_1417_;
goto v_resetjp_1410_;
}
else
{
lean_dec(v_x_1407_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1417_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 0, v___x_1406_);
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1406_);
v___x_1414_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1415_; 
v___x_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
return v___x_1415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__1___boxed(lean_object* v___x_1419_, lean_object* v_x_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__1(v___x_1419_, v_x_1420_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__5(lean_object* v_a_1423_, lean_object* v___f_1424_, lean_object* v___x_1425_, uint8_t v___x_1426_, lean_object* v___x_1427_, lean_object* v___f_1428_, lean_object* v_x_1429_){
_start:
{
if (lean_obj_tag(v_x_1429_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1439_; 
lean_dec_ref(v___f_1428_);
lean_dec(v___x_1425_);
lean_dec_ref(v___f_1424_);
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
lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1450_; 
v_isSharedCheck_1450_ = !lean_is_exclusive(v_x_1429_);
if (v_isSharedCheck_1450_ == 0)
{
lean_object* v_unused_1451_; 
v_unused_1451_ = lean_ctor_get(v_x_1429_, 0);
lean_dec(v_unused_1451_);
v___x_1441_ = v_x_1429_;
v_isShared_1442_ = v_isSharedCheck_1450_;
goto v_resetjp_1440_;
}
else
{
lean_dec(v_x_1429_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1450_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1443_ = lean_io_promise_result_opt(v_a_1423_);
lean_inc(v___x_1425_);
v___x_1444_ = lean_io_bind_task(v___x_1443_, v___f_1424_, v___x_1425_, v___x_1426_);
lean_dec_ref(v___x_1444_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v___x_1427_);
v___x_1446_ = v___x_1441_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1427_);
v___x_1446_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1446_);
v___x_1448_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1425_, v___x_1426_, v___x_1447_, v___f_1428_);
return v___x_1448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__5___boxed(lean_object* v_a_1452_, lean_object* v___f_1453_, lean_object* v___x_1454_, lean_object* v___x_1455_, lean_object* v___x_1456_, lean_object* v___f_1457_, lean_object* v_x_1458_, lean_object* v___y_1459_){
_start:
{
uint8_t v___x_6642__boxed_1460_; lean_object* v_res_1461_; 
v___x_6642__boxed_1460_ = lean_unbox(v___x_1455_);
v_res_1461_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__5(v_a_1452_, v___f_1453_, v___x_1454_, v___x_6642__boxed_1460_, v___x_1456_, v___f_1457_, v_x_1458_);
lean_dec(v_a_1452_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__6(lean_object* v_waiter_1462_, lean_object* v_a_1463_, lean_object* v___f_1464_, lean_object* v___x_1465_, uint8_t v___x_1466_, lean_object* v___x_1467_, lean_object* v___f_1468_, lean_object* v_x_1469_){
_start:
{
if (lean_obj_tag(v_x_1469_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1479_; 
lean_dec_ref(v___f_1468_);
lean_dec(v___x_1465_);
lean_dec_ref(v___f_1464_);
lean_dec_ref(v_a_1463_);
lean_dec_ref(v_waiter_1462_);
v_a_1471_ = lean_ctor_get(v_x_1469_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_x_1469_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1473_ = v_x_1469_;
v_isShared_1474_ = v_isSharedCheck_1479_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v_x_1469_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1479_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_object* v___x_1477_; 
v___x_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
return v___x_1477_;
}
}
}
else
{
lean_object* v_selector_1480_; lean_object* v_a_1481_; lean_object* v_finished_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1494_; 
v_selector_1480_ = lean_ctor_get(v_a_1463_, 0);
lean_inc_ref(v_selector_1480_);
lean_dec_ref(v_a_1463_);
v_a_1481_ = lean_ctor_get(v_x_1469_, 0);
lean_inc(v_a_1481_);
lean_dec_ref(v_x_1469_);
v_finished_1482_ = lean_ctor_get(v_waiter_1462_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v_waiter_1462_);
if (v_isSharedCheck_1494_ == 0)
{
lean_object* v_unused_1495_; 
v_unused_1495_ = lean_ctor_get(v_waiter_1462_, 1);
lean_dec(v_unused_1495_);
v___x_1484_ = v_waiter_1462_;
v_isShared_1485_ = v_isSharedCheck_1494_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_finished_1482_);
lean_dec(v_waiter_1462_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1494_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v_registerFn_1486_; lean_object* v___x_1488_; 
v_registerFn_1486_ = lean_ctor_get(v_selector_1480_, 1);
lean_inc_ref(v_registerFn_1486_);
lean_dec_ref(v_selector_1480_);
lean_inc(v_a_1481_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 1, v_a_1481_);
v___x_1488_ = v___x_1484_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_finished_1482_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v_a_1481_);
v___x_1488_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___f_1491_; lean_object* v___x_1492_; 
v___x_1489_ = lean_apply_2(v_registerFn_1486_, v___x_1488_, lean_box(0));
v___x_1490_ = lean_box(v___x_1466_);
lean_inc(v___x_1465_);
v___f_1491_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__5___boxed), 8, 6);
lean_closure_set(v___f_1491_, 0, v_a_1481_);
lean_closure_set(v___f_1491_, 1, v___f_1464_);
lean_closure_set(v___f_1491_, 2, v___x_1465_);
lean_closure_set(v___f_1491_, 3, v___x_1490_);
lean_closure_set(v___f_1491_, 4, v___x_1467_);
lean_closure_set(v___f_1491_, 5, v___f_1468_);
v___x_1492_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1465_, v___x_1466_, v___x_1489_, v___f_1491_);
return v___x_1492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__6___boxed(lean_object* v_waiter_1496_, lean_object* v_a_1497_, lean_object* v___f_1498_, lean_object* v___x_1499_, lean_object* v___x_1500_, lean_object* v___x_1501_, lean_object* v___f_1502_, lean_object* v_x_1503_, lean_object* v___y_1504_){
_start:
{
uint8_t v___x_6708__boxed_1505_; lean_object* v_res_1506_; 
v___x_6708__boxed_1505_ = lean_unbox(v___x_1500_);
v_res_1506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__6(v_waiter_1496_, v_a_1497_, v___f_1498_, v___x_1499_, v___x_6708__boxed_1505_, v___x_1501_, v___f_1502_, v_x_1503_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg___lam__1___boxed(lean_object* v_i_1507_, lean_object* v___x_1508_, lean_object* v_as_1509_, lean_object* v_sz_1510_, lean_object* v_x_1511_, lean_object* v___y_1512_){
_start:
{
size_t v_i_boxed_1513_; size_t v_sz_boxed_1514_; lean_object* v_res_1515_; 
v_i_boxed_1513_ = lean_unbox_usize(v_i_1507_);
lean_dec(v_i_1507_);
v_sz_boxed_1514_ = lean_unbox_usize(v_sz_1510_);
lean_dec(v_sz_1510_);
v_res_1515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg___lam__1(v_i_boxed_1513_, v___x_1508_, v_as_1509_, v_sz_boxed_1514_, v_x_1511_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(lean_object* v___x_1516_, lean_object* v_as_1517_, size_t v_sz_1518_, size_t v_i_1519_, lean_object* v_b_1520_){
_start:
{
uint8_t v___x_1522_; 
v___x_1522_ = lean_usize_dec_lt(v_i_1519_, v_sz_1518_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
lean_dec_ref(v_as_1517_);
lean_dec(v___x_1516_);
v___x_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1523_, 0, v_b_1520_);
v___x_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
return v___x_1524_;
}
else
{
lean_object* v_a_1525_; lean_object* v_selector_1526_; lean_object* v_unregisterFn_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; lean_object* v___f_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___f_1535_; uint8_t v___x_1536_; lean_object* v___x_1537_; 
v_a_1525_ = lean_array_uget_borrowed(v_as_1517_, v_i_1519_);
v_selector_1526_ = lean_ctor_get(v_a_1525_, 0);
v_unregisterFn_1527_ = lean_ctor_get(v_selector_1526_, 2);
lean_inc_ref(v_unregisterFn_1527_);
v___x_1528_ = lean_apply_1(v_unregisterFn_1527_, lean_box(0));
v___x_1529_ = lean_unsigned_to_nat(0u);
v___x_1530_ = lean_nat_dec_eq(v___x_1516_, v___x_1529_);
v___f_1531_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___closed__0));
v___x_1532_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1529_, v___x_1530_, v___x_1528_, v___f_1531_);
v___x_1533_ = lean_box_usize(v_i_1519_);
v___x_1534_ = lean_box_usize(v_sz_1518_);
v___f_1535_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg___lam__1___boxed), 6, 4);
lean_closure_set(v___f_1535_, 0, v___x_1533_);
lean_closure_set(v___f_1535_, 1, v___x_1516_);
lean_closure_set(v___f_1535_, 2, v_as_1517_);
lean_closure_set(v___f_1535_, 3, v___x_1534_);
v___x_1536_ = 0;
v___x_1537_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1529_, v___x_1536_, v___x_1532_, v___f_1535_);
return v___x_1537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg___lam__1(size_t v_i_1538_, lean_object* v___x_1539_, lean_object* v_as_1540_, size_t v_sz_1541_, lean_object* v_x_1542_){
_start:
{
if (lean_obj_tag(v_x_1542_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1552_; 
lean_dec_ref(v_as_1540_);
lean_dec(v___x_1539_);
v_a_1544_ = lean_ctor_get(v_x_1542_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v_x_1542_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1546_ = v_x_1542_;
v_isShared_1547_ = v_isSharedCheck_1552_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v_x_1542_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1552_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1549_; 
if (v_isShared_1547_ == 0)
{
v___x_1549_ = v___x_1546_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1544_);
v___x_1549_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
lean_object* v___x_1550_; 
v___x_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
return v___x_1550_;
}
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1572_; 
v_a_1553_ = lean_ctor_get(v_x_1542_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_x_1542_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1555_ = v_x_1542_;
v_isShared_1556_ = v_isSharedCheck_1572_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v_x_1542_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1572_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
if (lean_obj_tag(v_a_1553_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1567_; 
lean_dec_ref(v_as_1540_);
lean_dec(v___x_1539_);
v_a_1557_ = lean_ctor_get(v_a_1553_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v_a_1553_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1559_ = v_a_1553_;
v_isShared_1560_ = v_isSharedCheck_1567_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v_a_1553_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1567_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v_a_1557_);
v___x_1562_ = v___x_1555_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
lean_object* v___x_1564_; 
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v___x_1562_);
v___x_1564_ = v___x_1559_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1562_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
else
{
lean_object* v_a_1568_; size_t v___x_1569_; size_t v___x_1570_; lean_object* v___x_1571_; 
lean_del_object(v___x_1555_);
v_a_1568_ = lean_ctor_get(v_a_1553_, 0);
lean_inc(v_a_1568_);
lean_dec_ref(v_a_1553_);
v___x_1569_ = ((size_t)1ULL);
v___x_1570_ = lean_usize_add(v_i_1538_, v___x_1569_);
v___x_1571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(v___x_1539_, v_as_1540_, v_sz_1541_, v___x_1570_, v_a_1568_);
return v___x_1571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg___boxed(lean_object* v___x_1573_, lean_object* v_as_1574_, lean_object* v_sz_1575_, lean_object* v_i_1576_, lean_object* v_b_1577_, lean_object* v___y_1578_){
_start:
{
size_t v_sz_boxed_1579_; size_t v_i_boxed_1580_; lean_object* v_res_1581_; 
v_sz_boxed_1579_ = lean_unbox_usize(v_sz_1575_);
lean_dec(v_sz_1575_);
v_i_boxed_1580_ = lean_unbox_usize(v_i_1576_);
lean_dec(v_i_1576_);
v_res_1581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(v___x_1573_, v_as_1574_, v_sz_boxed_1579_, v_i_boxed_1580_, v_b_1577_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__3(lean_object* v___x_1582_, uint8_t v___x_1583_, lean_object* v___f_1584_, lean_object* v___f_1585_, lean_object* v_val_1586_, lean_object* v_x_1587_){
_start:
{
lean_object* v_val_1590_; 
if (lean_obj_tag(v_x_1587_) == 0)
{
lean_object* v___x_1594_; 
lean_dec_ref(v_val_1586_);
lean_dec_ref(v___f_1585_);
lean_dec_ref(v___f_1584_);
lean_dec(v___x_1582_);
v___x_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1594_, 0, v_x_1587_);
return v___x_1594_;
}
else
{
lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1607_; 
v_isSharedCheck_1607_ = !lean_is_exclusive(v_x_1587_);
if (v_isSharedCheck_1607_ == 0)
{
lean_object* v_unused_1608_; 
v_unused_1608_ = lean_ctor_get(v_x_1587_, 0);
lean_dec(v_unused_1608_);
v___x_1596_ = v_x_1587_;
v_isShared_1597_ = v_isSharedCheck_1607_;
goto v_resetjp_1595_;
}
else
{
lean_dec(v_x_1587_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1607_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_IO_ofExcept___at___00Std_Internal_IO_Async_Selectable_one_spec__1___redArg(v_val_1586_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1601_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref(v___x_1598_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v_a_1599_);
v___x_1601_ = v___x_1596_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1599_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
v_val_1590_ = v___x_1601_;
goto v___jp_1589_;
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; 
v_a_1603_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1603_);
lean_dec_ref(v___x_1598_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set_tag(v___x_1596_, 0);
lean_ctor_set(v___x_1596_, 0, v_a_1603_);
v___x_1605_ = v___x_1596_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
v_val_1590_ = v___x_1605_;
goto v___jp_1589_;
}
}
}
}
v___jp_1589_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1591_, 0, v_val_1590_);
lean_inc(v___x_1582_);
v___x_1592_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1582_, v___x_1583_, v___x_1591_, v___f_1584_);
v___x_1593_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1582_, v___x_1583_, v___x_1592_, v___f_1585_);
return v___x_1593_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__3___boxed(lean_object* v___x_1609_, lean_object* v___x_1610_, lean_object* v___f_1611_, lean_object* v___f_1612_, lean_object* v_val_1613_, lean_object* v_x_1614_, lean_object* v___y_1615_){
_start:
{
uint8_t v___x_6874__boxed_1616_; lean_object* v_res_1617_; 
v___x_6874__boxed_1616_ = lean_unbox(v___x_1610_);
v_res_1617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__3(v___x_1609_, v___x_6874__boxed_1616_, v___f_1611_, v___f_1612_, v_val_1613_, v_x_1614_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__2(lean_object* v_a_1618_, lean_object* v___x_1619_, uint8_t v___x_1620_, lean_object* v___f_1621_, lean_object* v_x_1622_){
_start:
{
if (lean_obj_tag(v_x_1622_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1632_; 
lean_dec_ref(v___f_1621_);
lean_dec(v___x_1619_);
lean_dec_ref(v_a_1618_);
v_a_1624_ = lean_ctor_get(v_x_1622_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v_x_1622_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1626_ = v_x_1622_;
v_isShared_1627_ = v_isSharedCheck_1632_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v_x_1622_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1632_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
return v___x_1630_;
}
}
}
else
{
lean_object* v_a_1633_; lean_object* v_cont_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v_a_1633_ = lean_ctor_get(v_x_1622_, 0);
lean_inc(v_a_1633_);
lean_dec_ref(v_x_1622_);
v_cont_1634_ = lean_ctor_get(v_a_1618_, 1);
lean_inc_ref(v_cont_1634_);
lean_dec_ref(v_a_1618_);
v___x_1635_ = lean_apply_2(v_cont_1634_, v_a_1633_, lean_box(0));
v___x_1636_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1619_, v___x_1620_, v___x_1635_, v___f_1621_);
return v___x_1636_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__2___boxed(lean_object* v_a_1637_, lean_object* v___x_1638_, lean_object* v___x_1639_, lean_object* v___f_1640_, lean_object* v_x_1641_, lean_object* v___y_1642_){
_start:
{
uint8_t v___x_6937__boxed_1643_; lean_object* v_res_1644_; 
v___x_6937__boxed_1643_ = lean_unbox(v___x_1639_);
v_res_1644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__2(v_a_1637_, v___x_1638_, v___x_6937__boxed_1643_, v___f_1640_, v_x_1641_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__0(lean_object* v_promise_1645_, lean_object* v_x_1646_){
_start:
{
if (lean_obj_tag(v_x_1646_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1656_; 
v_a_1648_ = lean_ctor_get(v_x_1646_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_x_1646_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1650_ = v_x_1646_;
v_isShared_1651_ = v_isSharedCheck_1656_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v_x_1646_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1656_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
return v___x_1654_;
}
}
}
else
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1657_ = lean_io_promise_resolve(v_x_1646_, v_promise_1645_);
v___x_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
v___x_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
return v___x_1659_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__0___boxed(lean_object* v_promise_1660_, lean_object* v_x_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__0(v_promise_1660_, v_x_1661_);
lean_dec(v_promise_1660_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__1(lean_object* v_promise_1664_, lean_object* v_x_1665_){
_start:
{
if (lean_obj_tag(v_x_1665_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1677_; 
v_a_1667_ = lean_ctor_get(v_x_1665_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_x_1665_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1669_ = v_x_1665_;
v_isShared_1670_ = v_isSharedCheck_1677_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v_x_1665_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1677_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1673_ = lean_io_promise_resolve(v___x_1672_, v_promise_1664_);
v___x_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
v___x_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
return v___x_1675_;
}
}
}
else
{
lean_object* v___x_1678_; 
v___x_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1678_, 0, v_x_1665_);
return v___x_1678_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__1___boxed(lean_object* v_promise_1679_, lean_object* v_x_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__1(v_promise_1679_, v_x_1680_);
lean_dec(v_promise_1679_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__4(lean_object* v___x_1683_, lean_object* v___x_1684_, lean_object* v___x_1685_, lean_object* v_waiter_1686_, lean_object* v_a_1687_, lean_object* v___x_1688_, uint8_t v___x_1689_, lean_object* v_a_1690_){
_start:
{
if (lean_obj_tag(v_a_1690_) == 0)
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
lean_dec(v___x_1688_);
lean_dec_ref(v_a_1687_);
lean_dec_ref(v_waiter_1686_);
lean_dec(v___x_1685_);
lean_dec_ref(v___x_1684_);
v___x_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1683_);
v___x_1693_ = lean_task_pure(v___x_1692_);
return v___x_1693_;
}
else
{
lean_object* v_val_1694_; size_t v_sz_1695_; size_t v___x_1696_; lean_object* v___x_1697_; lean_object* v_promise_1698_; lean_object* v___f_1699_; lean_object* v___f_1700_; lean_object* v___x_1701_; lean_object* v___f_1702_; lean_object* v___x_1703_; lean_object* v___f_1704_; lean_object* v___x_1705_; 
v_val_1694_ = lean_ctor_get(v_a_1690_, 0);
lean_inc(v_val_1694_);
lean_dec_ref(v_a_1690_);
v_sz_1695_ = lean_array_size(v___x_1684_);
v___x_1696_ = ((size_t)0ULL);
v___x_1697_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(v___x_1685_, v___x_1684_, v_sz_1695_, v___x_1696_, v___x_1683_);
v_promise_1698_ = lean_ctor_get(v_waiter_1686_, 1);
lean_inc_n(v_promise_1698_, 2);
lean_dec_ref(v_waiter_1686_);
v___f_1699_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1699_, 0, v_promise_1698_);
v___f_1700_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1700_, 0, v_promise_1698_);
v___x_1701_ = lean_box(v___x_1689_);
lean_inc_n(v___x_1688_, 2);
v___f_1702_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_1702_, 0, v_a_1687_);
lean_closure_set(v___f_1702_, 1, v___x_1688_);
lean_closure_set(v___f_1702_, 2, v___x_1701_);
lean_closure_set(v___f_1702_, 3, v___f_1700_);
v___x_1703_ = lean_box(v___x_1689_);
v___f_1704_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__3___boxed), 7, 5);
lean_closure_set(v___f_1704_, 0, v___x_1688_);
lean_closure_set(v___f_1704_, 1, v___x_1703_);
lean_closure_set(v___f_1704_, 2, v___f_1702_);
lean_closure_set(v___f_1704_, 3, v___f_1699_);
lean_closure_set(v___f_1704_, 4, v_val_1694_);
v___x_1705_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1688_, v___x_1689_, v___x_1697_, v___f_1704_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v___x_1707_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref(v___x_1705_);
v___x_1707_ = lean_task_pure(v_a_1706_);
return v___x_1707_;
}
else
{
lean_object* v_a_1708_; 
v_a_1708_ = lean_ctor_get(v___x_1705_, 0);
lean_inc_ref(v_a_1708_);
lean_dec_ref(v___x_1705_);
return v_a_1708_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__4___boxed(lean_object* v___x_1709_, lean_object* v___x_1710_, lean_object* v___x_1711_, lean_object* v_waiter_1712_, lean_object* v_a_1713_, lean_object* v___x_1714_, lean_object* v___x_1715_, lean_object* v_a_1716_, lean_object* v___y_1717_){
_start:
{
uint8_t v___x_7041__boxed_1718_; lean_object* v_res_1719_; 
v___x_7041__boxed_1718_ = lean_unbox(v___x_1715_);
v_res_1719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__4(v___x_1709_, v___x_1710_, v___x_1711_, v_waiter_1712_, v_a_1713_, v___x_1714_, v___x_7041__boxed_1718_, v_a_1716_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__7___boxed(lean_object* v_i_1720_, lean_object* v___x_1721_, lean_object* v___x_1722_, lean_object* v_waiter_1723_, lean_object* v_as_1724_, lean_object* v_sz_1725_, lean_object* v_x_1726_, lean_object* v___y_1727_){
_start:
{
size_t v_i_boxed_1728_; size_t v_sz_boxed_1729_; lean_object* v_res_1730_; 
v_i_boxed_1728_ = lean_unbox_usize(v_i_1720_);
lean_dec(v_i_1720_);
v_sz_boxed_1729_ = lean_unbox_usize(v_sz_1725_);
lean_dec(v_sz_1725_);
v_res_1730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__7(v_i_boxed_1728_, v___x_1721_, v___x_1722_, v_waiter_1723_, v_as_1724_, v_sz_boxed_1729_, v_x_1726_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg(lean_object* v___x_1731_, lean_object* v___x_1732_, lean_object* v_waiter_1733_, lean_object* v_as_1734_, size_t v_sz_1735_, size_t v_i_1736_, lean_object* v_b_1737_){
_start:
{
uint8_t v___x_1739_; 
v___x_1739_ = lean_usize_dec_lt(v_i_1736_, v_sz_1735_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
lean_dec_ref(v_as_1734_);
lean_dec_ref(v_waiter_1733_);
lean_dec(v___x_1732_);
lean_dec_ref(v___x_1731_);
v___x_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1740_, 0, v_b_1737_);
v___x_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
return v___x_1741_;
}
else
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___f_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; lean_object* v_a_1747_; lean_object* v___x_1748_; lean_object* v___f_1749_; lean_object* v___x_1750_; lean_object* v___f_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___f_1757_; uint8_t v___x_1758_; lean_object* v___x_1759_; 
v___x_1742_ = lean_io_promise_new();
v___x_1743_ = lean_box(0);
v___f_1744_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_one_spec__0___redArg___closed__0));
v___x_1745_ = lean_unsigned_to_nat(0u);
v___x_1746_ = lean_nat_dec_eq(v___x_1732_, v___x_1745_);
v_a_1747_ = lean_array_uget_borrowed(v_as_1734_, v_i_1736_);
v___x_1748_ = lean_box(v___x_1746_);
lean_inc_n(v_a_1747_, 2);
lean_inc_ref_n(v_waiter_1733_, 2);
lean_inc(v___x_1732_);
lean_inc_ref(v___x_1731_);
v___f_1749_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__4___boxed), 9, 7);
lean_closure_set(v___f_1749_, 0, v___x_1743_);
lean_closure_set(v___f_1749_, 1, v___x_1731_);
lean_closure_set(v___f_1749_, 2, v___x_1732_);
lean_closure_set(v___f_1749_, 3, v_waiter_1733_);
lean_closure_set(v___f_1749_, 4, v_a_1747_);
lean_closure_set(v___f_1749_, 5, v___x_1745_);
lean_closure_set(v___f_1749_, 6, v___x_1748_);
v___x_1750_ = lean_box(v___x_1746_);
v___f_1751_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__6___boxed), 9, 7);
lean_closure_set(v___f_1751_, 0, v_waiter_1733_);
lean_closure_set(v___f_1751_, 1, v_a_1747_);
lean_closure_set(v___f_1751_, 2, v___f_1749_);
lean_closure_set(v___f_1751_, 3, v___x_1745_);
lean_closure_set(v___f_1751_, 4, v___x_1750_);
lean_closure_set(v___f_1751_, 5, v___x_1743_);
lean_closure_set(v___f_1751_, 6, v___f_1744_);
v___x_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1742_);
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
v___x_1754_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1745_, v___x_1746_, v___x_1753_, v___f_1751_);
v___x_1755_ = lean_box_usize(v_i_1736_);
v___x_1756_ = lean_box_usize(v_sz_1735_);
v___f_1757_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__7___boxed), 8, 6);
lean_closure_set(v___f_1757_, 0, v___x_1755_);
lean_closure_set(v___f_1757_, 1, v___x_1731_);
lean_closure_set(v___f_1757_, 2, v___x_1732_);
lean_closure_set(v___f_1757_, 3, v_waiter_1733_);
lean_closure_set(v___f_1757_, 4, v_as_1734_);
lean_closure_set(v___f_1757_, 5, v___x_1756_);
v___x_1758_ = 0;
v___x_1759_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1745_, v___x_1758_, v___x_1754_, v___f_1757_);
return v___x_1759_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___lam__7(size_t v_i_1760_, lean_object* v___x_1761_, lean_object* v___x_1762_, lean_object* v_waiter_1763_, lean_object* v_as_1764_, size_t v_sz_1765_, lean_object* v_x_1766_){
_start:
{
if (lean_obj_tag(v_x_1766_) == 0)
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1776_; 
lean_dec_ref(v_as_1764_);
lean_dec_ref(v_waiter_1763_);
lean_dec(v___x_1762_);
lean_dec_ref(v___x_1761_);
v_a_1768_ = lean_ctor_get(v_x_1766_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v_x_1766_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1770_ = v_x_1766_;
v_isShared_1771_ = v_isSharedCheck_1776_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v_x_1766_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1776_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
lean_object* v___x_1774_; 
v___x_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1773_);
return v___x_1774_;
}
}
}
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1796_; 
v_a_1777_ = lean_ctor_get(v_x_1766_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_x_1766_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1779_ = v_x_1766_;
v_isShared_1780_ = v_isSharedCheck_1796_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v_x_1766_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1796_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
if (lean_obj_tag(v_a_1777_) == 0)
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1791_; 
lean_dec_ref(v_as_1764_);
lean_dec_ref(v_waiter_1763_);
lean_dec(v___x_1762_);
lean_dec_ref(v___x_1761_);
v_a_1781_ = lean_ctor_get(v_a_1777_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_a_1777_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1783_ = v_a_1777_;
v_isShared_1784_ = v_isSharedCheck_1791_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v_a_1777_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1791_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v_a_1781_);
v___x_1786_ = v___x_1779_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
lean_object* v___x_1788_; 
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 0, v___x_1786_);
v___x_1788_ = v___x_1783_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1786_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
else
{
lean_object* v_a_1792_; size_t v___x_1793_; size_t v___x_1794_; lean_object* v___x_1795_; 
lean_del_object(v___x_1779_);
v_a_1792_ = lean_ctor_get(v_a_1777_, 0);
lean_inc(v_a_1792_);
lean_dec_ref(v_a_1777_);
v___x_1793_ = ((size_t)1ULL);
v___x_1794_ = lean_usize_add(v_i_1760_, v___x_1793_);
v___x_1795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg(v___x_1761_, v___x_1762_, v_waiter_1763_, v_as_1764_, v_sz_1765_, v___x_1794_, v_a_1792_);
return v___x_1795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg___boxed(lean_object* v___x_1797_, lean_object* v___x_1798_, lean_object* v_waiter_1799_, lean_object* v_as_1800_, lean_object* v_sz_1801_, lean_object* v_i_1802_, lean_object* v_b_1803_, lean_object* v___y_1804_){
_start:
{
size_t v_sz_boxed_1805_; size_t v_i_boxed_1806_; lean_object* v_res_1807_; 
v_sz_boxed_1805_ = lean_unbox_usize(v_sz_1801_);
lean_dec(v_sz_1801_);
v_i_boxed_1806_ = lean_unbox_usize(v_i_1802_);
lean_dec(v_i_1802_);
v_res_1807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg(v___x_1797_, v___x_1798_, v_waiter_1799_, v_as_1800_, v_sz_boxed_1805_, v_i_boxed_1806_, v_b_1803_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__0(lean_object* v___x_1808_, lean_object* v___x_1809_, lean_object* v___x_1810_, lean_object* v___x_1811_, uint8_t v___x_1812_, lean_object* v___f_1813_, lean_object* v_waiter_1814_){
_start:
{
size_t v_sz_1816_; size_t v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v_sz_1816_ = lean_array_size(v___x_1808_);
v___x_1817_ = ((size_t)0ULL);
lean_inc_ref(v___x_1808_);
v___x_1818_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg(v___x_1808_, v___x_1809_, v_waiter_1814_, v___x_1808_, v_sz_1816_, v___x_1817_, v___x_1810_);
v___x_1819_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1811_, v___x_1812_, v___x_1818_, v___f_1813_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__0___boxed(lean_object* v___x_1820_, lean_object* v___x_1821_, lean_object* v___x_1822_, lean_object* v___x_1823_, lean_object* v___x_1824_, lean_object* v___f_1825_, lean_object* v_waiter_1826_, lean_object* v___y_1827_){
_start:
{
uint8_t v___x_7210__boxed_1828_; lean_object* v_res_1829_; 
v___x_7210__boxed_1828_ = lean_unbox(v___x_1824_);
v_res_1829_ = l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__0(v___x_1820_, v___x_1821_, v___x_1822_, v___x_1823_, v___x_7210__boxed_1828_, v___f_1825_, v_waiter_1826_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__3(lean_object* v___x_1830_, lean_object* v___x_1831_, size_t v_sz_1832_, size_t v___x_1833_, lean_object* v___x_1834_, lean_object* v___x_1835_, uint8_t v___x_1836_, lean_object* v___f_1837_){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(v___x_1830_, v___x_1831_, v_sz_1832_, v___x_1833_, v___x_1834_);
v___x_1840_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1835_, v___x_1836_, v___x_1839_, v___f_1837_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__3___boxed(lean_object* v___x_1841_, lean_object* v___x_1842_, lean_object* v_sz_1843_, lean_object* v___x_1844_, lean_object* v___x_1845_, lean_object* v___x_1846_, lean_object* v___x_1847_, lean_object* v___f_1848_, lean_object* v___y_1849_){
_start:
{
size_t v_sz_boxed_1850_; size_t v___x_7235__boxed_1851_; uint8_t v___x_7238__boxed_1852_; lean_object* v_res_1853_; 
v_sz_boxed_1850_ = lean_unbox_usize(v_sz_1843_);
lean_dec(v_sz_1843_);
v___x_7235__boxed_1851_ = lean_unbox_usize(v___x_1844_);
lean_dec(v___x_1844_);
v___x_7238__boxed_1852_ = lean_unbox(v___x_1847_);
v_res_1853_ = l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__3(v___x_1841_, v___x_1842_, v_sz_boxed_1850_, v___x_7235__boxed_1851_, v___x_1845_, v___x_1846_, v___x_7238__boxed_1852_, v___f_1848_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__2(lean_object* v___x_1854_, lean_object* v___x_1855_, size_t v_sz_1856_, size_t v___x_1857_, lean_object* v___x_1858_, lean_object* v___x_1859_, uint8_t v___x_1860_, lean_object* v___f_1861_){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg(v___x_1854_, v___x_1855_, v_sz_1856_, v___x_1857_, v___x_1858_);
v___x_1864_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1859_, v___x_1860_, v___x_1863_, v___f_1861_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__2___boxed(lean_object* v___x_1865_, lean_object* v___x_1866_, lean_object* v_sz_1867_, lean_object* v___x_1868_, lean_object* v___x_1869_, lean_object* v___x_1870_, lean_object* v___x_1871_, lean_object* v___f_1872_, lean_object* v___y_1873_){
_start:
{
size_t v_sz_boxed_1874_; size_t v___x_7263__boxed_1875_; uint8_t v___x_7266__boxed_1876_; lean_object* v_res_1877_; 
v_sz_boxed_1874_ = lean_unbox_usize(v_sz_1867_);
lean_dec(v_sz_1867_);
v___x_7263__boxed_1875_ = lean_unbox_usize(v___x_1868_);
lean_dec(v___x_1868_);
v___x_7266__boxed_1876_ = lean_unbox(v___x_1871_);
v_res_1877_ = l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__2(v___x_1865_, v___x_1866_, v_sz_boxed_1874_, v___x_7263__boxed_1875_, v___x_1869_, v___x_1870_, v___x_7266__boxed_1876_, v___f_1872_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg(lean_object* v_selectables_1882_){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; uint8_t v___x_1886_; 
v___x_1884_ = lean_array_get_size(v_selectables_1882_);
v___x_1885_ = lean_unsigned_to_nat(0u);
v___x_1886_ = lean_nat_dec_eq(v___x_1884_, v___x_1885_);
if (v___x_1886_ == 0)
{
size_t v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = ((size_t)8ULL);
v___x_1888_ = lean_io_get_random_bytes(v___x_1887_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1916_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1891_ = v___x_1888_;
v_isShared_1892_ = v_isSharedCheck_1916_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1888_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1916_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___f_1893_; uint64_t v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___f_1899_; lean_object* v___x_1900_; lean_object* v___f_1901_; lean_object* v___x_1902_; size_t v_sz_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___f_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___f_1911_; lean_object* v___x_1912_; lean_object* v___x_1914_; 
v___f_1893_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_tryOne___redArg___closed__0));
v___x_1894_ = l_ByteArray_toUInt64LE_x21(v_a_1889_);
lean_dec(v_a_1889_);
v___x_1895_ = lean_uint64_to_nat(v___x_1894_);
v___x_1896_ = l_mkStdGen(v___x_1895_);
lean_dec(v___x_1895_);
v___x_1897_ = l___private_Std_Internal_Async_Select_0__Std_Internal_IO_Async_shuffleIt___redArg(v_selectables_1882_, v___x_1896_);
v___x_1898_ = lean_box(0);
v___f_1899_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_combine___redArg___closed__0));
v___x_1900_ = lean_box(v___x_1886_);
lean_inc_ref_n(v___x_1897_, 2);
v___f_1901_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_1901_, 0, v___x_1897_);
lean_closure_set(v___f_1901_, 1, v___x_1884_);
lean_closure_set(v___f_1901_, 2, v___x_1898_);
lean_closure_set(v___f_1901_, 3, v___x_1885_);
lean_closure_set(v___f_1901_, 4, v___x_1900_);
lean_closure_set(v___f_1901_, 5, v___f_1899_);
v___x_1902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_tryOne_spec__0___redArg___closed__1));
v_sz_1903_ = lean_array_size(v___x_1897_);
v___x_1904_ = lean_box_usize(v_sz_1903_);
v___x_1905_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_combine___redArg___boxed__const__1));
v___x_1906_ = lean_box(v___x_1886_);
v___f_1907_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_1907_, 0, v___x_1884_);
lean_closure_set(v___f_1907_, 1, v___x_1897_);
lean_closure_set(v___f_1907_, 2, v___x_1904_);
lean_closure_set(v___f_1907_, 3, v___x_1905_);
lean_closure_set(v___f_1907_, 4, v___x_1898_);
lean_closure_set(v___f_1907_, 5, v___x_1885_);
lean_closure_set(v___f_1907_, 6, v___x_1906_);
lean_closure_set(v___f_1907_, 7, v___f_1899_);
v___x_1908_ = lean_box_usize(v_sz_1903_);
v___x_1909_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_combine___redArg___boxed__const__1));
v___x_1910_ = lean_box(v___x_1886_);
v___f_1911_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selectable_combine___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_1911_, 0, v___x_1884_);
lean_closure_set(v___f_1911_, 1, v___x_1897_);
lean_closure_set(v___f_1911_, 2, v___x_1908_);
lean_closure_set(v___f_1911_, 3, v___x_1909_);
lean_closure_set(v___f_1911_, 4, v___x_1902_);
lean_closure_set(v___f_1911_, 5, v___x_1885_);
lean_closure_set(v___f_1911_, 6, v___x_1910_);
lean_closure_set(v___f_1911_, 7, v___f_1893_);
v___x_1912_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1912_, 0, v___f_1911_);
lean_ctor_set(v___x_1912_, 1, v___f_1901_);
lean_ctor_set(v___x_1912_, 2, v___f_1907_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v___x_1912_);
v___x_1914_ = v___x_1891_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1912_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec_ref(v_selectables_1882_);
v_a_1917_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1888_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1888_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
else
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
lean_dec_ref(v_selectables_1882_);
v___x_1925_ = ((lean_object*)(l_Std_Internal_IO_Async_Selectable_one___redArg___closed__1));
v___x_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
return v___x_1926_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___redArg___boxed(lean_object* v_selectables_1927_, lean_object* v_a_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Std_Internal_IO_Async_Selectable_combine___redArg(v_selectables_1927_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine(lean_object* v_00_u03b1_1930_, lean_object* v_selectables_1931_){
_start:
{
lean_object* v___x_1933_; 
v___x_1933_ = l_Std_Internal_IO_Async_Selectable_combine___redArg(v_selectables_1931_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selectable_combine___boxed(lean_object* v_00_u03b1_1934_, lean_object* v_selectables_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_Std_Internal_IO_Async_Selectable_combine(v_00_u03b1_1934_, v_selectables_1935_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0(lean_object* v_00_u03b1_1938_, lean_object* v___x_1939_, lean_object* v_as_1940_, size_t v_sz_1941_, size_t v_i_1942_, lean_object* v_b_1943_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___redArg(v___x_1939_, v_as_1940_, v_sz_1941_, v_i_1942_, v_b_1943_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0___boxed(lean_object* v_00_u03b1_1946_, lean_object* v___x_1947_, lean_object* v_as_1948_, lean_object* v_sz_1949_, lean_object* v_i_1950_, lean_object* v_b_1951_, lean_object* v___y_1952_){
_start:
{
size_t v_sz_boxed_1953_; size_t v_i_boxed_1954_; lean_object* v_res_1955_; 
v_sz_boxed_1953_ = lean_unbox_usize(v_sz_1949_);
lean_dec(v_sz_1949_);
v_i_boxed_1954_ = lean_unbox_usize(v_i_1950_);
lean_dec(v_i_1950_);
v_res_1955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__0(v_00_u03b1_1946_, v___x_1947_, v_as_1948_, v_sz_boxed_1953_, v_i_boxed_1954_, v_b_1951_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1(lean_object* v_00_u03b1_1956_, lean_object* v___x_1957_, lean_object* v___x_1958_, lean_object* v_waiter_1959_, lean_object* v_as_1960_, size_t v_sz_1961_, size_t v_i_1962_, lean_object* v_b_1963_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___redArg(v___x_1957_, v___x_1958_, v_waiter_1959_, v_as_1960_, v_sz_1961_, v_i_1962_, v_b_1963_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1___boxed(lean_object* v_00_u03b1_1966_, lean_object* v___x_1967_, lean_object* v___x_1968_, lean_object* v_waiter_1969_, lean_object* v_as_1970_, lean_object* v_sz_1971_, lean_object* v_i_1972_, lean_object* v_b_1973_, lean_object* v___y_1974_){
_start:
{
size_t v_sz_boxed_1975_; size_t v_i_boxed_1976_; lean_object* v_res_1977_; 
v_sz_boxed_1975_ = lean_unbox_usize(v_sz_1971_);
lean_dec(v_sz_1971_);
v_i_boxed_1976_ = lean_unbox_usize(v_i_1972_);
lean_dec(v_i_1972_);
v_res_1977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Internal_IO_Async_Selectable_combine_spec__1(v_00_u03b1_1966_, v___x_1967_, v___x_1968_, v_waiter_1969_, v_as_1970_, v_sz_boxed_1975_, v_i_boxed_1976_, v_b_1973_);
return v_res_1977_;
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
